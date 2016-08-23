/// Relaxed Radix Balanced Vector
///
/// Original concept: Phil Bagwell and Tiark Rompf
/// https://infoscience.epfl.ch/record/169879/files/RMTrees.pdf
///
/// Partly based on work by Jean Niklas L'orange: http://hypirion.com/thesis

module FSharpx.Collections.Experimental.RRBVectorRecord

// open FSharpx.Collections  // Once we add the Node class to PersistentVector.fsi, we can do this to get at the Node class.

module internal Literals =
    [<Literal>]
    let internal blockSizeShift = 3

    [<Literal>]
    let internal radixSearchErrorMax = 2  // Number of extra search steps to allow; 2 is a good balance

    [<Literal>]
    let internal blockSize = 8  // 2 ** blockSizeShift

    [<Literal>]
    let internal blockBitMask = 7  // 2 ** blockSizeShift - 1. Use with &&& to get the current level's index

    [<Literal>]
    let internal blockSizeMin = 7  // blockSize - (radixSearchErrorMax / 2). Set to 2 (blockSize - radixSearchError) for faster concatenation but slower indexing, but UNIT TEST that one thoroughly.

module internal Literals4 =
    [<Literal>]
    let internal blockSizeShift = 2

    [<Literal>]
    let internal radixSearchErrorMax = 2  // Number of extra search steps to allow; 2 is a good balance

    [<Literal>]
    let internal blockSize = 4  // 2 ** blockSizeShift

    [<Literal>]
    let internal blockBitMask = 3  // 2 ** blockSizeShift - 1. Use with &&& to get the current level's index

    [<Literal>]
    let internal blockSizeMin = 3  // blockSize - (radixSearchErrorMax / 2). Set to 2 (blockSize - radixSearchError) for faster concatenation but slower indexing, but UNIT TEST that one thoroughly.

module internal Literals32 =
    [<Literal>]
    let internal blockSizeShift = 5

    [<Literal>]
    let internal radixSearchErrorMax = 2  // Number of extra search steps to allow; 2 is a good balance

    [<Literal>]
    let internal blockSize = 32  // 2 ** blockSizeShift

    [<Literal>]
    let internal blockBitMask = 31  // 2 ** blockSizeShift - 1. Use with &&& to get the current level's index

    [<Literal>]
    let internal blockSizeMin = 31  // blockSize - (radixSearchErrorMax / 2). Set to 30 (blockSize - radixSearchError) for faster concatenation but slower indexing, but UNIT TEST that one thoroughly.

    // TODO: Analyze whether having blockSizeMin at 30 instead of 31 will have any effect on the M(M-1) calculations for merging...

module Array =

    // TODO: Write functions to copy an array with a new item appended at the end,
    // and also to copy an array with a new item inserted into index i. No bounds-checking on i.
    let (*inline*) internal copyAndAppend newItem oldArr =
        let len = Array.length oldArr
        let newArr = Array.zeroCreate (len + 1) // Is zeroCreate the most efficient?
        Array.blit oldArr 0 newArr 0 len
        newArr.[len] <- newItem
        newArr

    // NOTE: No bounds-checking on idx. It's caller's responsibility to set it properly.
    let (*inline*) internal copyAndInsertAt idx newItem oldArr =
        let oldLen = Array.length oldArr
        let newArr = Array.zeroCreate (oldLen + 1) // Is zeroCreate the most efficient?
        Array.blit oldArr 0 newArr 0 idx
        newArr.[idx] <- newItem
        Array.blit oldArr idx newArr (idx + 1) (oldLen - idx)
        newArr

    // NOTE: No bounds-checking on idx. It's caller's responsibility to set it properly.
    let (*inline*) internal copyAndSet idx newItem oldArr =
        let newArr = Array.copy oldArr
        newArr.[idx] <- newItem
        newArr

    // NOTE: No bounds-checking on idx. It's caller's responsibility to set it properly.
    let (*inline*) internal copyAndRemoveAt idx oldArr =
        let newLen = Array.length oldArr - 1
        let newArr = Array.zeroCreate newLen // Is zeroCreate the most efficient?
        Array.blit oldArr 0 newArr 0 idx
        Array.blit oldArr (idx + 1) newArr idx (newLen - idx)
        newArr

    // Special case of the above for removing the first item
    let (*inline*) internal copyAndRemoveFirst oldArr =
        Array.sub oldArr 1 (Array.length oldArr - 1)

    // Special case of the above for removing the last item
    let (*inline*) internal copyAndPop oldArr =
        Array.sub oldArr 0 (Array.length oldArr - 1)

    // Special case of copyAndSet for setting the last item (makes for a slightly nicer calling syntax)
    let (*inline*) internal copyAndSetLast newItem oldArr =
        copyAndSet (Array.length oldArr - 1) newItem oldArr

    // NOTE: No bounds-checking on idx. It's caller's responsibility to set it properly.
    let (*inline*) internal splitAt idx oldArr =
        let newL = Array.sub oldArr 0 idx
        let newR = Array.sub oldArr idx (Array.length oldArr - idx)
        (newL,newR)
    // TODO: Actually, Array.splitAt now exists in F# 4.0. And the library has been updated to require F# 4.0, so we're fine here.

    /// Like Array.append left right |> Array.splitAt splitIdx, but without creating an intermediate array
    let appendAndSplit splitIdx (left, right) =
        let lenL = Array.length left
        let lenR = Array.length right
        let totalLen = lenL + lenR
        if lenL = splitIdx then
            left, right
        elif lenL < splitIdx then
            let resultL = Array.zeroCreate splitIdx
            Array.blit left 0 resultL 0 lenL
            Array.blit right 0 resultL lenL (splitIdx - lenL)
            let resultR = Array.sub right (splitIdx - lenL) (totalLen - splitIdx)
            resultL, resultR
        else // lenL > splitIdx
            let resultL = Array.sub left 0 splitIdx
            let resultR = Array.zeroCreate (totalLen - splitIdx)
            Array.blit left splitIdx resultR 0 (lenL - splitIdx)
            Array.blit right 0 resultR (lenL - splitIdx) lenR
            resultL, resultR

    // Like Array.append, but for three arrays at once. Equivalent to Array.concat [|left;middle;right|] but more efficient.
    let (*inline*) internal append3 left middle right =
        let lenL = Array.length left
        let lenM = Array.length middle
        let lenR = Array.length right
        let newArr = Array.zeroCreate (lenL + lenM + lenR)
        Array.blit left   0 newArr 0    lenL
        Array.blit middle 0 newArr lenL lenM
        Array.blit right  0 newArr (lenL+lenM) lenR
        newArr

    // Like Array.append3, but the "middle" is an item rather than an array. Equivalent to Array.concat [|left;[|middle|];right|] but more efficient.
    let (*inline*) internal append3' left middleItem right =
        let lenL = Array.length left
        let lenR = Array.length right
        let newArr = Array.zeroCreate (lenL + 1 + lenR)
        Array.blit left   0 newArr 0    lenL
        newArr.[lenL] <- middleItem
        Array.blit right  0 newArr (lenL+1) lenR
        newArr

    // Concatenate two arrays and insert an item at position `idx` in the resulting array, without creating an intermediate array
    let concatAndInsertAt idx item a1 a2 =
        let len1 = Array.length a1
        let len2 = Array.length a2
        let totalLen = len1 + len2 + 1
        let result = Array.zeroCreate totalLen
        if idx >= len1 then
            Array.blit a1 0 result 0 len1
            Array.blit a2 0 result len1 (idx - len1)
            result.[idx] <- item
            Array.blit a2 (idx - len1) result (idx + 1) (len2 - (idx - len1))
        else
            Array.blit a1 0 result 0 idx
            result.[idx] <- item
            Array.blit a1 idx result (idx + 1) (len1 - idx)
            Array.blit a2 0 result (len1 + 1) len2
        result

    // This is sort of like a chunkBySize for arrays-of-arrays, with the size hardcoded to Literals.blockSize
    // It will be used in the tree-merging algorithm, but it's a general enough algorithm that I moved its code out here
    // TODO: Examine whether it might be better to simply pass in the Literals.blockSize part as a parameter, to make this more generic.
    let (*inline*) internal appendMany start len (getArray: int -> 'a[]) =
        let lens = Array.init len (fun i -> getArray (start + i) |> Array.length)
        let mutable i = start
        let mutable srcIdx = 0
        let mutable dstIdx = 0
        let endLoop = start + len
        let rec loop countToGo = seq {
            let dstLen = min countToGo Literals.blockSize
            let dst = Array.zeroCreate dstLen
            while i < endLoop && dstIdx < dstLen do
                let src = getArray i
                let srcLen = lens.[i]
                let count = min (srcLen - srcIdx) (dstLen - dstIdx)
                Array.blit src srcIdx dst dstIdx count
                dstIdx <- dstIdx + count
                srcIdx <- srcIdx + count
                if srcIdx >= srcLen then
                    i <- i + 1
                    srcIdx <- 0
            yield dst
            dstIdx <- 0
            let countToGo' = countToGo - dstLen
            if countToGo' > 0 then yield! loop countToGo'
        }
        loop (Array.sum lens)
    // TODO: Experiment with speeding up the merge algorithm by using this. If this isn't useful, get rid of it.

// NOTE: Using records during development, but will switch to classes once I've
// gotten an implementation up and working. Do it right, THEN do it fast.

// type RRBNodeAsClass(thread,array,sizeTable: int[]) =  // Name will be just RRBNode once I'm ready to use it
//     inherit Node(thread,array)
// ... more stuff goes here

type [<Measure>] globalIdx  // Index into the vector
type [<Measure>] treeIdx    // Index into the subtree at this node
type [<Measure>] nodeIdx    // Index into this node's array

/// Used for finding the index at this level
let inline notAsGoodRadixIndex idx level =
    (idx >>> (level * Literals.blockSizeShift)) &&& Literals.blockBitMask

/// Shift is just (level * Literals.blockSizeShift), but stored as shift in each node so we can save a multiplication step
/// In other words, for nodes at height 1 we store 5 as the "height shift value", because that's what we need to shift by to form the radix index.
/// For nodes at height 2 we store 10 as the "height shift value", because that's what we need to shift by to form the radix index.
/// For nodes at height 3 we store 15 as the "height shift value", and so on.
let inline radixIndex (idx:int<treeIdx>) shift =
    ((int idx >>> shift) &&& Literals.blockBitMask) * 1<nodeIdx>

// TERMINOLOGY:
// "Item" is the things that are stored in the vector, i.e. the things of type 'T.
// "Entry" (or "Child", I have yet to decide) are of type node, not type 'T.
// So if you're a LeafNode, you have "items". If you aren't a LeafNode, you do NOT have "items";
// you instead have either "entries" or "children", once I make up my mind which term to use.

type SizeTable = int<treeIdx> []

type LeafNode<'T> =
    { items: 'T []
      // No sizeTable needed in a leaf node
      // No shift needed either: the shift of a leaf node is 0
    }

type TreeNode<'T> =
    { // shift: int // We can probably track shift in the *functions*, not the nodes themselves!
      entries: Node<'T> []  // TODO: Rename "entries" to "children"?
      sizeTable: SizeTable
    }

and FullNode<'T> =
    { // shift: int // We can probably track shift in the *functions*, not the nodes themselves!
      entries: Node<'T> []  // TODO: Rename "entries" to "children"?
    }

and Node<'T> =
    | TreeNode of TreeNode<'T>
    | LeafNode of LeafNode<'T>
    | FullNode of FullNode<'T>

// Utility functions for doing conversions when you expect a certain type (based on, say, current shift level)
exception LeafNodeInWrongPlaceException of string
let invalidLeaf () = raise <| LeafNodeInWrongPlaceException("Leaf node found at non-0 shift")

let toLeaf = function
    | LeafNode n -> n
    | TreeNode n -> sprintf "Expected leaf node, got tree %A" n |> invalidArg "node"
    | FullNode n -> sprintf "Expected leaf node, got full %A" n |> invalidArg "node"

let toTree = function
    | TreeNode n -> n
    | LeafNode n -> sprintf "Expected tree node, got leaf %A" n |> invalidArg "node"
    | FullNode n -> sprintf "Expected tree node, got full %A" n |> invalidArg "node"

let toFull = function
    | FullNode n -> n
    | LeafNode n -> sprintf "Expected full node, got leaf %A" n |> invalidArg "node"
    | TreeNode n -> sprintf "Expected full node, got tree %A" n |> invalidArg "node"

let mkLeaf items = LeafNode { items = items }

// Utility function to get the entries array from either a FullNode or TreeNode, regardless of which it is
let nodeEntries = function
    | LeafNode _ -> invalidLeaf()
    | TreeNode n -> n.entries
    | FullNode n -> n.entries
// TODO: Rename to childNodes?

let leafItems n = (toLeaf n).items

// Utility function to get a child node from either a FullNode or TreeNode, regardless of which it is
let getChildNode (idx:int<nodeIdx>) node = (nodeEntries node).[int idx]

type RRBVector<'T> =
    { root: Node<'T>
      tail: LeafNode<'T>
      tailOffset: int<globalIdx> // If we need tailLen, we'll calculate it from vecLen - tailOffset
      vecLen: int<globalIdx> // Or should I call this "size"?
      shift: int // See above for what this is
    }

let emptyLeaf = { items = [||] }  // Do I need to declare this as <'T> ?? Apparently not.
let emptyNode = FullNode { entries = [||] }  // This is technically not a violation of the FullNode promise that its last child slot will be the only non-full one.

let emptyVec =
    { root = emptyNode
      tail = emptyLeaf
      tailOffset = 0<globalIdx>
      vecLen = 0<globalIdx>
      shift = Literals.blockSizeShift }

let mkVec() = emptyVec

// *** BASIC OPERATIONS ***

/// Look up an index via radix search
let inline radixSearch idx curShift (sizeTbl:SizeTable) =
    let mutable i = radixIndex idx curShift
    while sizeTbl.[int i] <= idx do
        i <- i + 1<nodeIdx>
    i

/// Split a leaf into two parts (useful in split and insert operations)
let (*inline*) splitLeafAt splitIdx leaf =
    let itemsA, itemsB = leaf.items |> Array.splitAt splitIdx
    { items = itemsA }, { items = itemsB }

let nodeSize = function
    | LeafNode n -> n.items.Length * 1<nodeIdx>
    | TreeNode n -> n.entries.Length * 1<nodeIdx>
    | FullNode n -> n.entries.Length * 1<nodeIdx>

/// Size of this node two levels deep. I.e., if it has N children that all have M entries, this will return (M*N).
let grandchildSize node = nodeEntries node |> Array.sumBy nodeSize

// TODO: This could be renamed to "slotCount" to match the terminology used in Jean Niklas L'orange's thesis...
// BUT see the slotCount function I wrote below. We don't actually need the grandchildSize function after all.

let isEmpty node = nodeSize node = 0<nodeIdx>

let (|EmptyNode|_|) node =
    let length = match node with
                 | LeafNode n -> n.items.Length
                 | FullNode n -> n.entries.Length
                 | TreeNode n -> n.entries.Length
    if length = 0 then Some () else None

let rec getLeftmostLeaf root =
    match root with
    | LeafNode n -> n
    | EmptyNode -> sprintf "Empty node found in tree: %A" root |> invalidOp
    | TreeNode n -> n.entries.[0] |> getLeftmostLeaf
    | FullNode n -> n.entries.[0] |> getLeftmostLeaf

let rec getRightmostLeaf root =
    match root with
    | LeafNode n -> n
    | EmptyNode -> sprintf "Empty node found in tree: %A" root |> invalidOp
    | TreeNode n -> n.entries |> Array.last |> getRightmostLeaf
    | FullNode n -> n.entries |> Array.last |> getRightmostLeaf

let rec getRightmostTwig root =
    match root with
    | LeafNode n -> root
    | EmptyNode -> sprintf "Empty node found in tree: %A" root |> invalidOp
    | TreeNode n -> let child = n.entries |> Array.last
                    match child with
                    | LeafNode _ -> root
                    | _ -> getRightmostTwig child
    | FullNode n -> let child = n.entries |> Array.last
                    match child with
                    | LeafNode _ -> root
                    | _ -> getRightmostTwig child

let rec getLeftmostTwig root =
    match root with
    | LeafNode n -> root
    | EmptyNode -> sprintf "Empty node found in tree: %A" root |> invalidOp
    | TreeNode n -> let child = n.entries.[0]
                    match child with
                    | LeafNode _ -> root
                    | _ -> getLeftmostTwig child
    | FullNode n -> let child = n.entries.[0]
                    match child with
                    | LeafNode _ -> root
                    | _ -> getLeftmostTwig child

let isSameNode = LanguagePrimitives.PhysicalEquality  // Used in split operation

let notImpl msg = raise <| new System.NotImplementedException(msg)

let rec treeSize shift node : int<treeIdx> =
    if shift = 0 then
        (leafItems node).Length * 1<treeIdx>
    else
        match node with
        | LeafNode _ -> invalidLeaf()
        | EmptyNode -> 0<treeIdx>
        | FullNode n ->
            // A full node is allowed to have an incomplete rightmost entry, but all but its rightmost entry must be complete.
            // Therefore, we can shortcut this calculation for most of the nodes, but we do need to calculate the rightmost node.
            ((n.entries.Length - 1) <<< shift) * 1<treeIdx> + treeSize (shift - Literals.blockSizeShift) (Array.last n.entries)
        | TreeNode n ->
            // We'll assume the size table is correct. If it isn't, this function will be buggy.
            // TODO: Write some unit tests to exercise this and find out if that assumption holds...
            Array.last n.sizeTable

// Returns a triple: (local index at this node, node/item at next level, index to use in searching next level)
let appropriateIndexSearch idx shift node =
    match node with
    | LeafNode _ -> invalidLeaf()
    | TreeNode n ->
        let localIdx = radixSearch idx shift n.sizeTable
        let child = n.entries.[int localIdx]
        let nextIdx = if localIdx = 0<nodeIdx> then idx else idx - n.sizeTable.[int localIdx - 1]
        localIdx, child, nextIdx
    | FullNode n ->
        let localIdx = radixIndex idx shift
        let child = n.entries.[int localIdx]
        let antimask = ~~~(Literals.blockBitMask <<< shift)
        let nextIdx = (int idx &&& antimask) * 1<treeIdx>
        localIdx, child, nextIdx

// Find the node containing index `idx`
// Alternate version: find the node pair containing `idx` and `idx-1`.
let rec findNodeAtIdx idx targetShift origShift node =
    if origShift = targetShift then
        node, idx
    else
        match node with
        | LeafNode _ -> invalidLeaf() // TODO: Can just drop this since appropriateIndexSearch checks for this
        | _ ->
            let i, n', idx' = appropriateIndexSearch idx origShift node
            findNodeAtIdx idx' targetShift (origShift - Literals.blockSizeShift) n'

// Should be useful in split function
/// Returns (nodeL, localIndexL), (nodeR, localIndexR)
let rec findNodePairAtIdx (idxL,idxR) targetShift origShift (nodeL,nodeR) =
    if origShift = 0 then
        // At leaf level, tree indices *are* node indices
        (nodeL, idxL / 1<treeIdx> * 1<nodeIdx>), (nodeR, idxR / 1<treeIdx> * 1<nodeIdx>)
    else
        let iL, nL', idxL' = appropriateIndexSearch idxL origShift nodeL
        let iR, nR', idxR' = appropriateIndexSearch idxR origShift nodeR
        if origShift = targetShift then
            (nodeL, iL), (nodeR, iR)
        else
            findNodePairAtIdx (idxL',idxR') targetShift (origShift - Literals.blockSizeShift) (nL',nR')
            // TODO: I'm REALLY not sure about this one. Need unit tests BADLY.

// Test code for the above function (kind of misplaced since we're relying on ofList, but
// I was just using Alt+Enter to run it, and we can move it over to the RRBVectorTest.fs file at some point).

// let bigTestVec = [0..1092] |> ofList
// bigTestVec.shift
// let a,b = (bigTestVec.root, bigTestVec.root) |> findNodePairAtIdx (191,192) 6 bigTestVec.shift
// (bigTestVec.root, bigTestVec.root) |> findNodePairAtIdx (206,207) 4 bigTestVec.shift
// isSameNode (fst a) (fst b)

/// Find leaf at vector index `idx`. TODO: Needs a unit test or three.
/// Returns a tuple of (leaf node, index within leaf node)
let rec findLeafIdx idx shift node =
    let foundNode, foundIdx = findNodeAtIdx idx 0 shift node
    toLeaf foundNode, foundIdx

/// Find item at vector index `idx`. TODO: Needs a unit test or three.
let rec findIdx (idx) shift node =
    let leaf, leafIdx = findLeafIdx idx shift node
    leaf.items.[int leafIdx]

let rec replaceItemAt (idx:int<treeIdx>) newItem shift rootNode =
    if shift = 0 then
        leafItems rootNode |> Array.copyAndSet (int idx) newItem |> mkLeaf
    else
        match rootNode with
        | LeafNode _ -> invalidLeaf()
        | TreeNode n ->
            let thisIdx = n.sizeTable |> radixSearch idx shift
            let size = if thisIdx = 0<nodeIdx> then 0<treeIdx> else n.sizeTable.[int thisIdx-1] // TODO: make sure it really *is* thisIdx - 1
            let newNode = replaceItemAt (idx - size) newItem (shift - Literals.blockSizeShift) n.entries.[int thisIdx]
            TreeNode { n with entries = n.entries |> Array.copyAndSet (int thisIdx) newNode }
            // TODO: Or make it a FullNode if it turns out that that level really is full... but I don't think this can happen when just replacing an item.
            // Now, when replacing a NODE... that's a different story.
        | FullNode n ->
            let thisIdx = radixIndex idx shift
            let newNode = replaceItemAt idx newItem (shift - Literals.blockSizeShift) n.entries.[int thisIdx]
            FullNode { n with entries = n.entries |> Array.copyAndSet (int thisIdx) newNode }

/// Compare efficiency with createSizeTable version that uses Array.scan. Is one or the other better?
/// TODO: Perhaps wait to compare efficiency until we've switched to the class version. But
/// maybe not; the record version will still give us some useful information.
let createSizeTable<'T> shift (entries:Node<'T> []) =
    let sizeTbl = Array.zeroCreate entries.Length
    let mutable total = 0<treeIdx>
    for i = 0 to entries.Length - 1 do
        total <- total + treeSize shift entries.[i]
        sizeTbl.[i] <- total
    sizeTbl

// TODO: Write some functions for updating one entry in a TreeNode, taking advantage of
// the size table's properties so we don't have to recalculate the entire size table.
// That might speed things up a bit. BUT... wait until we've finished implementing everything
// and have measured performance, because we should not prematurely optimize.

/// A node is full if all of its trees except the rightmost are fully populated. For
/// a first-level node (one whose children are leaves), that means its size table will
/// look like [|32;64;96;...|]. For a second-level node, its size table looks like
/// [|1024;2048;3072;...|]. And so on. As a general rule, in a full node, the size table
/// entry at index `i` will be equal to `(i+1) * 2^shift`. Since size tables are cumulative,
/// that means we can check the last-but-one node to verify the entire size table.
///
/// ... Except that the above doesn't quite work. Because if the block size is 4 but the
/// node is [|1;2;3|], this will consider it full. Which means that it will turn into
/// something like FullNode [| LeafNode [|1;2;3|] |]... and the NEXT time that the tail gets
/// pushed down, that becomes FullNode [| LeafNode [|1;2;3|]; LeafNode [|4;5;6;7|] |]. Which
/// is wrong. THEREFORE, I'm changing the logic to be "Check the last node, and it must be
/// the appropriate multiple of the block size. EXCEPT if the FullNode is all-but-full, in
/// which case the genuinely-last slot may be partial." In other words, [|32;60|] does NOT
/// qualify. But [|32;64;96;...;992;1013|] DOES qualify.
let (*inline*) isSizeTableFullAtShift shift sizeTbl =
    let len = Array.length sizeTbl
    if len = 0 then true else
    let checkIdx = if len = Literals.blockSize then len - 2 else len - 1
    sizeTbl.[checkIdx] = ((checkIdx + 1) <<< shift) * 1<treeIdx>

// isSizeTableFullAtShift 2 [|4;8;12;13|]

// let mkTreeNodeRecord shift entries =
//   { entries = entries
//     sizeTable = createSizeTable shift entries }

// NOTE: Will convert to a FullNode if appropriate
let (*inline*) mkTreeNodeWithTbl shift entries sizeTable =
    // printfn "Creating tree node at shift %d with entries %A" shift entries
    if isSizeTableFullAtShift shift sizeTable then
        // FullNode { entries = entries } |> printfn "Returning full node rather than tree node: %A"
        FullNode { entries = entries }
    else
        // TreeNode { entries = entries; sizeTable = sizeTable } |> printfn "Returning tree node: %A"
        TreeNode { entries = entries; sizeTable = sizeTable }
// TODO: In instance-based version of Node, the TreeNode *constructor* should be the one deciding whether to make a FullNode or a TreeNode.
// Or else it should be the static mkAppropriateNode function, that returns either a FullNode or a TreeNode (a Node or an RRBNode) according to the size table.
// Hmm. Gotta think about this one.

let (*inline*) mkTreeNode shift entries =
    createSizeTable (shift - Literals.blockSizeShift) entries
    |> mkTreeNodeWithTbl shift entries

// Form a new path from node up to level shift
let newPathFrom node startShift endShift =
    let rec loop s node =
        if s = endShift then
            node
        else
            let s' = s + Literals.blockSizeShift
            let node' = mkTreeNode s' [|node|]
            loop s' node'
    loop startShift node

let newPath node shift = newPathFrom node 0 shift

/// If the root of a vector is a length-1 node, and its child is not a leaf, then
/// shorten it by moving its child node up to the root. The child node's size table
/// will not have to be recalculated because it's already appropriate for that level.
/// Also, if the root of the vector has just become empty, then adjust the shift to be blockSizeShift. (NOT 0, as that messes a few things up)
let rec shortenVec vec =
    if vec.shift <= Literals.blockSizeShift then vec
    elif nodeSize vec.root > 1<nodeIdx> then vec
    elif nodeSize vec.root = 0<nodeIdx> then
        { vec with shift = Literals.blockSizeShift }  // Empty tree is arbitrarily defined to have shift = blockSizeShift
    else
        let child = vec.root |> getChildNode 0<nodeIdx>
        match child with
        | LeafNode _ -> { vec with shift = Literals.blockSizeShift }
        | TreeNode _
        | FullNode _ ->
            { vec with root = vec.root |> getChildNode 0<nodeIdx>
                       shift = vec.shift - Literals.blockSizeShift } // That's it. No other things (tail offset, length, etc.) need changing.
            |> shortenVec  // It's possible for this to be true for two or even three levels, such as if
                           // a 1-item slice was taken from the left edge of a very large (and tall) vector

/// Copy a size table, then increment every entry by 1 starting at index incIdx
/// Make sure incIdx isn't negative! This function does NOT check for negative incIdx! (To save time)
/// This is used when rebuilding size tables after inserting an item in the middle of this node's descendants
let (*inline*) internal copyAndIncSizeTable incIdx oldST =
    let newST = Array.copy oldST
    for i = incIdx to oldST.Length - 1 do
        newST.[i] <- newST.[i] + 1
    newST

/// This is used when rebuilding size tables after removing an item from the middle of this node's descendants
let (*inline*) internal copyAndDecSizeTable decIdx oldST =
    let newST = Array.copy oldST
    for i = decIdx to oldST.Length - 1 do
        newST.[i] <- newST.[i] - 1
    newST

/// This is used when rebuilding size tables after removing a *node* (or a leaf) from this node's entries
let (*inline*) internal copySizeTableMinusOneIndex idx oldST =
    let oldVal = Array.item idx oldST
    let newLen = Array.length oldST - 1
    let newST  = Array.zeroCreate newLen // Is zeroCreate the most efficient?
    Array.blit oldST 0 newST 0 idx
    for i = idx to newLen - 1 do
        newST.[i] <- oldST.[i+1] - oldVal
    newST

/// Special case of the above for removing the first item (no need for the first Array.blit call in that case)
let (*inline*) internal copySizeTableMinusFirstItem oldST =
    let oldVal = Array.item 0 oldST
    let newLen = Array.length oldST - 1
    let newST  = Array.zeroCreate newLen
    for i = 0 to newLen - 1 do
        newST.[i] <- oldST.[i+1] - oldVal
    newST

/// This is probably just as efficient, but is easier to read. Maybe use this one instead? TODO: Measure efficiency using this vs. the above, once we've implemented everything.
let (*inline*) internal copySizeTableMinusFirstItemUsingStdlibFunctions oldST =
    let oldVal = Array.item 0 oldST
    Array.init (Array.length oldST - 1) (fun idx -> oldST.[idx+1] - oldVal)

/// This is used when rebuilding size tables after inserting several items in the middle of this node's descendants
let (*inline*) internal copyAndAddNToSizeTable incIdx n oldST =
    let newST = Array.copy oldST
    for i = incIdx to oldST.Length - 1 do
        newST.[i] <- newST.[i] + n
    newST

/// This is used when rebuilding size tables after removing several items in the middle of this node's descendants
let (*inline*) internal copyAndSubtractNFromSizeTable decIdx n oldST =
    copyAndAddNToSizeTable decIdx (-n) oldST

/// Copy `len` entries from two arrays a1 and a2, which should be considered adjacent.
/// We copy entries starting at idx1 from a1 and continuing on into a2 once we hit the end of a1.
/// This is used when merging two nodes (for example, during rebalancing).
/// This is equivalent to Array.append a1 a2 |> Array.sub idx1 len, but should be more efficient as it doesn't create a temporary array in the process.
let copyEntriesFromTwoArrays idx1 len a1 a2 =
    let a1Count = Array.length a1 - idx1
    let a2Count = min (Array.length a2) (len - a1Count)
    let result = Array.zeroCreate (a1Count + a2Count)
    Array.blit a1 idx1 result 0 a1Count
    Array.blit a2 0 result a1Count a2Count
    result

// If tree is not full, return Some (tree with new leaf appended)
// If tree is full, return None, and caller (which should be pushTailDown) should create new root path to hold new leaf
// XYZZY Maybe we can extract parts of this to make a new pushTailDown implementation for the merge scenario.
// The basic idea is you follow the rightmost spine, appending at the lowest place where there's room.
// And if there's no room, you make a new root. Just like this one, except that we don't assume
// anything about the size of newLeaf (it might not be full).
let rec appendLeafAtEndOfTree newLeaf leafLen shift rootNode =
    if shift = Literals.blockSizeShift then
        if nodeSize rootNode = Literals.blockSize * 1<nodeIdx> then None else
        match rootNode with
        | LeafNode _ -> invalidLeaf()
        | TreeNode n ->
            mkTreeNodeWithTbl shift (n.entries |> Array.copyAndAppend newLeaf) (n.sizeTable |> Array.copyAndAppend (Array.last n.sizeTable + leafLen * 1<treeIdx>)) |> Some
        | FullNode n ->
            // Because of the "last leaf must be full" invariant, we know that this will
            // remain a FullNode after we append the new leaf. It's possible that the new
            // leaf was not full, but this can only happen when we're pushing the tail into
            // the tree during a tree merge. If that's the case, the merge algorithm is either
            // going to put another node to the right of this one so it won't be the last leaf,
            // or else if this node DOES remain the last leaf (if vector B of the merge was a
            // very small vector), then shifting its nodes into the tail will be handled in the
            // merge operation.
            FullNode { n with entries = n.entries |> Array.copyAndAppend newLeaf } |> Some
    else
        match rootNode with
        | LeafNode _ -> invalidLeaf()
        | TreeNode n ->
            match appendLeafAtEndOfTree newLeaf leafLen (shift - Literals.blockSizeShift) (Array.last n.entries) with
            | Some result ->
                n.entries |> Array.copyAndSetLast result |> mkTreeNode shift |> Some
                // TreeNode { n with entries   = n.entries   |> Array.copyAndSetLast result
                //                   sizeTable = n.sizeTable |> Array.copyAndSetLast (n.sizeTable.[n.entries.Length - 2] + nodeSize result) }  // TODO: This will FAIL if this is the first entry in the TreeNode, and I'm not quite sure how to handle that scenario.
                // TODO: See comment on previous line and rewrite this one once I figure it out. Could be simpler, but need to calculate size table correctly.
                // MAYBE the constructor for an RRBNode object will be assigned the job of taking care of it? But there are scenarios
                // where I want the size table to be "just like this other size table except for one change", so a specialized constructor might be desired?
                // DESIGN NOTES: No. The RRBNode constructor should be dead simple. What I want is some *factory functions* to build RRBNodes
                // in common scenarios: add a node at the end, replace a node in the middle, insert a node at index I.
            | None -> // Rightmost subtree was full
                if nodeSize rootNode = Literals.blockSize * 1<nodeIdx> then None else
                let newNode = newPath newLeaf (shift - Literals.blockSizeShift)
                n.entries |> Array.copyAndAppend newNode |> mkTreeNode shift |> Some
                // TreeNode { n with entries   = n.entries   |> Array.copyAndAppend newNode
                //                   sizeTable = n.sizeTable |> Array.copyAndAppend (Array.last n.sizeTable + nodeSize newLeaf) }
        | FullNode n ->
            match appendLeafAtEndOfTree newLeaf leafLen (shift - Literals.blockSizeShift) (Array.last n.entries) with
            | Some result ->
                let entries = n.entries |> Array.copyAndSetLast result
                if (leafLen = Literals.blockSize) then
                    FullNode { n with entries = entries } |> Some
                else
                    mkTreeNode shift entries |> Some
            | None -> // Rightmost subtree was full
                if nodeSize rootNode = Literals.blockSize * 1<nodeIdx> then None else
                let newNode = newPath newLeaf (shift - Literals.blockSizeShift)
                n.entries |> Array.copyAndAppend newNode |> mkTreeNode shift |> Some

let keepOnlyNChildren (keepCnt:int<nodeIdx>) shift = function
    | LeafNode _ -> invalidLeaf()
    | TreeNode n ->
        let entries' = Array.sub n.entries 0 (int keepCnt)
        let sizeTable' = Array.sub n.sizeTable 0 (int keepCnt)
        mkTreeNodeWithTbl shift entries' sizeTable'
    | FullNode n ->
        // This is becoming a tree node, so recalculate the size table via mkTreeNode
        Array.sub n.entries 0 (int keepCnt) |> mkTreeNode shift

// Note: childSize should be *tree* size, not *node* size. In other words, something appropriate for the size table at this level.
let replaceChildAt (localIdx:int<nodeIdx>) newChild childSize shift = function
    | LeafNode _ -> invalidLeaf()
    | TreeNode n ->
        let oldSize = if localIdx = 0<nodeIdx> then n.sizeTable.[0]
                                               else n.sizeTable.[int localIdx] - n.sizeTable.[int localIdx - 1]
        let sizeDiff = childSize - oldSize
        let entries' = n.entries |> Array.copyAndSet (int localIdx) newChild
        let sizeTable' = if sizeDiff = 0<treeIdx> then n.sizeTable
                                                  else n.sizeTable |> copyAndAddNToSizeTable (int localIdx) sizeDiff
        mkTreeNodeWithTbl shift entries' sizeTable'
    | FullNode n ->
        let childIsFull = (childSize = (1 <<< shift) * 1<treeIdx>)  // TOCHECK: Should this be "1 <<< (shift-1)"? Which shift are we talking about here? I think this is right, but check it.
        if childIsFull then
            // This is still a full node
            FullNode { entries = n.entries |> Array.copyAndSet (int localIdx) newChild }
        else
            // This has become a tree node, so recalculate the size table via mkTreeNode
            n.entries |> Array.copyAndSet (int localIdx) newChild |> mkTreeNode shift

let rec replaceLeafAt idx newItem shift root =
    notImpl "TODO: Write this"  // Would use appropriateIndexSearch at each level

let rec replaceLastLeaf newLeaf shift root =
    if shift <= Literals.blockSizeShift then
        root |> replaceChildAt (nodeSize root - 1<nodeIdx>) newLeaf (treeSize 0 newLeaf) shift
    else
        let downShift = shift - Literals.blockSizeShift
        let lastIdx = (nodeSize root - 1<nodeIdx>)
        let newChild = root |> getChildNode lastIdx |> replaceLastLeaf newLeaf downShift
        root |> replaceChildAt lastIdx newChild (treeSize downShift newChild) shift

// APPEND ALGORITHM

// First note: Append, in F# world, means "put two arrays together", which is what I think "concat" means.
// And "concat" in F# world means "put ALL of these arrays together", which I don't have a name for.
// So this function should NOT be called "append". Instead I will call it "push". (Aka "conj" for those who have a Clojure background).
// Or appendItem, or addTail, or just add... the naming possibilities are confusing, especially since Array didn't
// give me a nice easy thing to copy. And List gave me an operator instead of a function. And Seq doesn't have it.
// So there isn't really a "standard" F# name.

// Anyway, the append algorithm. First question is, is the tail full?
// 1) No, the tail is not full.
//    This one's easy. Do a copy-and-append on the tail node to append the new item. Then clone the root node into a new root node, with length +1 and the new tail node.
// 2) Yes, the tail is full. We're going to "push the tail down".
//    Look at the rightmost internal node. (Might be a TreeNode, might be a FullNode). Does it have 32 children?
//    2a) No, it has fewer than 32 children.
//        Copy-and-append its children array, adding the tail node at the end.
//        Walk the rightmost path of internal nodes, recursively(?) so we can operate from the bottom up.
//            At each level, copy the node and update its children array (at the bottom level that's a copy-and-append, as you go up that's a copy-and-update) with the new rightmost child.
//            Also update the size table when the new node has its children array in place. Or if we determine that this node is FULL (I think we'll be able to tell by the way the size table has nothing but powers of 2 appropriate to the level?) then convert it to a FullNode.
//    2b) Yes, it has 32 children. We need a new root node. (WAIT... not quite a new root node, not necessarily. Could need a new node at that level, and the tail will be its first child.)
//        TODO: Write this branch of the algorithm. Right now I don't know how to do it.
//        But I think the new root node has two children; left is the old root node, and right is a singleton node.
//        Then you have as many singleton nodes as it takes to get down to the correct level for the leaves. (I.e.,
//     R
//    / \
//   X   Y
// where R is the root. X has lots of children, and Y has nothing but a single leftmost child. And its child, if not a leaf, has a single leftmost child, and so on.

// Rather than use Literals.blockSize-1 (or -2) in the nodeWillOverflow function, let's define a few more literals
[<Literal>]
// let blockSizeMinus1 = 31  // Should be Literals.blockSize - 1
let blockSizeMinus1 = 3  // Currently blockSize is 4 for testing
[<Literal>]
// let blockSizeMinus2 = 30  // Should be Literals.blockSize - 2
let blockSizeMinus2 = 2  // Currently blockSize is 4 for testing

// TODO: Currently unused. In ClojureScript implementation, this was used in
// pushTailDown, but we've implemented pushTailDown differently and thus don't
// need this implementation any more. Let's keep it around for a bit, though,
// in case it turns out to be useful in some other functions. If it's still
// unused after we implement the whole data structure, then we'll trim it.
// let rec nodeWillOverflow node shift count =
//     match node with
//     | LeafNode _
//     | FullNode _ -> (count >>> Literals.blockSizeShift) > (1 <<< shift)
//     | TreeNode n ->
//         let sizeT = n.sizeTable
//         let nodeLen = n.entries.Length
//         (nodeLen = Literals.blockSize) && (shift = Literals.blockSizeShift || (nodeWillOverflow n.entries.[blockSizeMinus1] (shift - Literals.blockSizeShift) (sizeT.[blockSizeMinus1] - sizeT.[blockSizeMinus2] + Literals.blockSize)))

// let inline rootWillOverflow vec = nodeWillOverflow vec.root vec.shift (int vec.vecLen)

// Returns a new root, but not a vector
// NOTE: Assumes that the vector's tail is full. Only call this with a full tail! XYZZY: Not anymore. Now it can be called from the merge algorithm as well.
let pushTailDown vec =
    match appendLeafAtEndOfTree (LeafNode vec.tail) (vec.tail.items.Length) vec.shift vec.root with
    | Some root' -> root', vec.shift
    | None ->
        let left = vec.root
        let right = newPath (LeafNode vec.tail) vec.shift
        if vec.shift = 0 then
            FullNode { entries = [|left; right|] }, vec.shift + Literals.blockSizeShift
        else
            match vec.root with
            | TreeNode n ->
                let oldSize = Array.last n.sizeTable
                TreeNode { n with entries = [|left; right|]
                                  sizeTable = [|oldSize; oldSize + vec.tail.items.Length * 1<treeIdx>|] }, vec.shift + Literals.blockSizeShift
            | FullNode n ->
                FullNode { n with entries = [|left; right|] }, vec.shift + Literals.blockSizeShift
            | LeafNode _ -> invalidLeaf()

/// Add one item to the end of the tree
let push item vec =
    if int (vec.vecLen - vec.tailOffset) < Literals.blockSize then
        // Easy: just add new item in tail and we're done
        { vec with tail = { items = Array.copyAndAppend item vec.tail.items }
                   vecLen = vec.vecLen + 1<globalIdx> }
    else
        let root', shift' = pushTailDown vec  // This does all the work
        { root = root'
          tail = { items = [|item|] }
          tailOffset = vec.tailOffset + Literals.blockSize * 1<globalIdx>
          vecLen = vec.vecLen + 1<globalIdx>
          shift = shift' }

let insertIntoTail tailIdx item vec =
    // Almost just like push, but with copyAndInsertAt instead of copyAndAppend
    if int (vec.vecLen - vec.tailOffset) < Literals.blockSize then
        // Easy: just add new item in tail and we're done
        { vec with tail = { items = Array.copyAndInsertAt tailIdx item vec.tail.items }
                   vecLen = vec.vecLen + 1<globalIdx> }
    else
        let tailItemsToPush, remaining =
            vec.tail.items
            |> Array.copyAndInsertAt tailIdx item
            |> Array.splitAt (Literals.blockSize)
        // TODO: Rewrite pushTailDown so that it takes a root and a new leaf, instead of a vector. Better API for what we need here.
        let tempVec = { vec with tail = { items = tailItemsToPush } }
        let root', shift' = pushTailDown tempVec  // This does all the work
        { root = root'
          tail = { items = remaining }
          tailOffset = vec.tailOffset + Literals.blockSize * 1<globalIdx>
          vecLen = vec.vecLen + 1<globalIdx>
          shift = shift' }

// TODO: Write a "removeEntryFromNode" helper, which might simplify some of the logic here in removeLastLeaf.

// Returns a tuple of (leaf,newRoot). TODO: Rename this to "popLastLeaf" since we return the popped leaf
let rec removeLastLeaf shift root =
    if shift = Literals.blockSizeShift then
        // Children of this root node are leaves
        match root with
        | LeafNode _ -> invalidLeaf()
        | EmptyNode -> emptyLeaf,root
        | TreeNode n ->
            let leaf = Array.last n.entries |> toLeaf
            let root' = mkTreeNodeWithTbl shift (Array.copyAndPop n.entries) (Array.copyAndPop n.sizeTable)
            leaf,root'
        | FullNode n ->
            let leaf = Array.last n.entries |> toLeaf
            let root' = FullNode { n with entries = Array.copyAndPop n.entries } // Popping the last entry from a FullNode can't ever turn it into a TreeNode. TOCHECK: That this is true.
            leaf,root'
    else
        // Children are nodes, not leaves -- so we're going to take the rightmost and dig down into it.
        // And if the recursive call returns an empty node, we'll strip the entry off our node.
        // TODO: There's some common code between this function and pop() now. Can we refactor that into a common helper??
        // TODO: Maybe once we have instances as nodes. Right now, type inference would make that common helper a bit tricky, I think.
        match root with
        | LeafNode _ -> invalidLeaf()
        | TreeNode n ->
            let last = Array.last n.entries
            match removeLastLeaf (shift - Literals.blockSizeShift) last with
            | _,LeafNode _ -> invalidLeaf()
            | leaf,EmptyNode ->
                let root' = mkTreeNodeWithTbl shift (Array.copyAndPop n.entries) (Array.copyAndPop n.sizeTable)
                leaf,root'
            | leaf,TreeNode child' ->
                // let prevSize = if n.sizeTable.Length <= 1 then 0 else n.sizeTable.[n.sizeTable.Length - 2]
                // let node' = { entries   = n.entries   |> Array.copyAndSet (Array.length n.entries - 1) (FullNode child')
                //               sizeTable = n.sizeTable |> Array.copyAndSet (Array.length n.entries - 1) (prevSize + treeSize (shift - Literals.blockSizeShift) (FullNode child')) }
                // That's an ugly construction. Refactor that into some function dealing with updating things in a TreeNode. TODO: Check performance against:
                let root' = n.entries |> Array.copyAndSetLast (TreeNode child') |> mkTreeNode shift
                leaf,root'
            | leaf,FullNode child' ->
                // let prevSize = if n.sizeTable.Length <= 1 then 0 else n.sizeTable.[n.sizeTable.Length - 2]
                // let node' = { n with entries   = n.entries   |> Array.copyAndSet (Array.length n.entries - 1) (FullNode child')
                //                      sizeTable = n.sizeTable |> Array.copyAndSet (Array.length n.entries - 1) (prevSize + treeSize (shift - Literals.blockSizeShift) (FullNode child')) }
                // That's an ugly construction. Refactor that into some function dealing with updating things in a TreeNode. TODO: Check performance against:
                let root' = n.entries |> Array.copyAndSetLast (FullNode child') |> mkTreeNode shift
                leaf,root'
        | FullNode n ->
            let last = Array.last n.entries
            match removeLastLeaf (shift - Literals.blockSizeShift) last with
            | _,LeafNode _ -> invalidLeaf()
            | leaf,EmptyNode ->
                let root' = FullNode { entries = n.entries |> Array.copyAndPop }
                leaf,root'
            | leaf,TreeNode child' ->
                let root' = FullNode { entries = n.entries |> Array.copyAndSetLast (TreeNode child') }
                // TOCHECK: Wait, if the last entry of a FullNode becomes a TreeNode, doesn't it need to become a TreeNode now as well? This might be a bug.
                leaf,root'
            | leaf,FullNode child' ->
                let root' = FullNode { entries = n.entries |> Array.copyAndSetLast (FullNode child') }
                leaf,root'

let rec shiftNodesIntoTailIfNeeded vec =
    if int vec.vecLen <= Literals.blockSize * 2 then
        if isEmpty vec.root then vec else  // If vector root is already empty, we're golden
        let leaf = getRightmostLeaf vec.root
        if leaf.items.Length + vec.tail.items.Length <= Literals.blockSize then
            // Can fit entire last leaf into tail
            let tailItems' = Array.append leaf.items vec.tail.items
            { vec with root = snd (removeLastLeaf vec.shift vec.root)
                       tail = { items = tailItems' }
                       tailOffset = vec.tailOffset - leaf.items.Length * 1<globalIdx>
            } |> shiftNodesIntoTailIfNeeded // We might still need another go-around if the root had lots of small nodes in it
              |> shortenVec // TODO: This step makes it not tail-recursive. Split shiftNodesIntoTailIfNeeded into a helper function? Then a second function would be shift+shorten.
        elif leaf.items.Length < Literals.blockSize then
            // Leaf won't fit into tail, but needs fleshing out
            let leafItems', tailItems' = Array.append leaf.items vec.tail.items |> Array.splitAt Literals.blockSize
            let lastLeaf' = mkLeaf leafItems'
            { vec with root = vec.root |> replaceLastLeaf lastLeaf' vec.shift
                       tail = { items = tailItems' }
                       tailOffset = vec.vecLen - tailItems'.Length * 1<globalIdx> }
            |> shortenVec // TODO: This step makes it not tail-recursive. Split shiftNodesIntoTailIfNeeded into a helper function? Then a second function would be shift+shorten.
        else
            // No shifting needed
            vec
    else
        vec

let pop vec =
    if vec.vecLen <= 0<globalIdx> then invalidOp "Can't pop from an empty vector" else
    if vec.vecLen = 1<globalIdx> then emptyVec else
    if vec.vecLen - vec.tailOffset > 1<globalIdx> then
        // Easy: strip the last node off the tail and we're done
        { vec with tail = { items = Array.copyAndPop vec.tail.items }
                   vecLen = vec.vecLen - 1<globalIdx> }
    else
        let newTail, newRoot = removeLastLeaf vec.shift vec.root
        // If the new root has only one item in it, decrease the tree height
        let newRoot',newShift =
            match newRoot with
            // | None -> emptyNode,Literals.blockSizeShift
            | LeafNode _ -> invalidLeaf()
            | TreeNode n when n.entries.Length = 1 && vec.shift > Literals.blockSizeShift ->
                // Note that if vec.shift = Literals.blockSizeShift, then we now have a root node with just one child, which is a leaf.
                // In that case alone, we don't want to strip out a child of the root node. We want the root node to always be a full node or tree node.
                // TODO: Once we convert to using class-based nodes, revisit that decision since it might be okay to have a leaf node in the root
                // in that scenario. But I'm not sure I understand all the implications of that, so I'll have to think about it.
                n.entries.[0],vec.shift - Literals.blockSizeShift
            | TreeNode n -> (TreeNode n),vec.shift
            | FullNode n when n.entries.Length = 1 && vec.shift > Literals.blockSizeShift  ->
                n.entries.[0],vec.shift - Literals.blockSizeShift
            | FullNode n -> (FullNode n),vec.shift
        { tail = newTail
          root = newRoot'
          shift = newShift
          vecLen = vec.vecLen - 1<globalIdx>
          tailOffset = vec.tailOffset - newTail.items.Length * 1<globalIdx> }

let removeFromTailAtTailIdx idx vec =
    if vec.vecLen <= 0<globalIdx> then invalidOp "Can't remove from an empty vector" else
    if vec.vecLen = 1<globalIdx> then emptyVec else
    if vec.vecLen - vec.tailOffset > 1<globalIdx> then
        // Easy: strip the item off the tail and we're done
        { vec with tail = { items = Array.copyAndRemoveAt idx vec.tail.items }
                   vecLen = vec.vecLen - 1<globalIdx> }
    else
        let newTail, newRoot = removeLastLeaf vec.shift vec.root
        // If the new root has only one item in it, decrease the tree height
        let newRoot',newShift =
            match newRoot with
            // | None -> emptyNode,Literals.blockSizeShift
            | LeafNode _ -> invalidLeaf()
            | TreeNode n when n.entries.Length = 1 && vec.shift > Literals.blockSizeShift ->
                // Note that if vec.shift = Literals.blockSizeShift, then we now have a root node with just one child, which is a leaf.
                // In that case alone, we don't want to strip out a child of the root node. We want the root node to always be a full node or tree node.
                // TODO: Once we convert to using class-based nodes, revisit that decision since it might be okay to have a leaf node in the root
                // in that scenario. But I'm not sure I understand all the implications of that, so I'll have to think about it.
                n.entries.[0],vec.shift - Literals.blockSizeShift
            | TreeNode n -> (TreeNode n),vec.shift
            | FullNode n when n.entries.Length = 1 && vec.shift > Literals.blockSizeShift  ->
                n.entries.[0],vec.shift - Literals.blockSizeShift
            | FullNode n -> (FullNode n),vec.shift
        { tail = newTail
          root = newRoot'
          shift = newShift
          vecLen = vec.vecLen - 1<globalIdx>
          tailOffset = vec.tailOffset - newTail.items.Length * 1<globalIdx> }
// TODO: That's basically identical to pop except for the copyAndRemoveAt call (replacing copyAndPop). Refactor so the shared code isn't duplicated.

let peek vec =
    if vec.vecLen = 0<globalIdx> then invalidOp "An empty vector has no last item" else
    Array.last vec.tail.items

let length vec =
    vec.vecLen

let ofList list =
    let rec loop acc list =
        match list with
        | [] -> acc
        | x::xs -> loop (push x acc) xs
    loop emptyVec list

let ofSeq seq =
    let folder vec value =
        vec |> push value
    seq |> Seq.fold folder emptyVec

let ofArray arr =
    // TODO: A more efficient implementation is possible by chunking the array and then creating nodes from those chunks
    // For now, just reuse ofSeq
    ofSeq arr

let nth (idx:int<globalIdx>) vec =
    let idx' = if idx < 0<globalIdx> then idx + vec.vecLen else idx
    if (idx' < 0<globalIdx>) || (idx' >= vec.vecLen) then invalidOp "Index out of range" // TODO: Is there an "OutOfRangeException" we should use?
    elif (idx' >= vec.tailOffset) then
        vec.tail.items.[idx' - vec.tailOffset |> int]
    else
        findIdx (idx' * 1<treeIdx> / 1<globalIdx>) vec.shift vec.root  // At vec.shift level, tree indices are = to global indices

// We'll need a function/method called NewPath for making a new "path" of 1-child nodes from root to new tail
// Need to grok the height-of-each-node value first. It's called "shift", and it's 1 <<< (height * mask-bits).
// So in a tree with branching factor of 32, mask-bits is 5. So leaf nodes have a shift of 0. One level up,
// the shift is 5. So if we're a small tree, the root node has a height of 1, which means a shift of 5 (or 32?).
// Once that tree grows beyond 1024 items (32*32), the root pushes up a level and now has a height of 2, which
// means a shift of 10. But is the shift value 10, or is it (1 <<< 10) = 1024? Which is more convenient?


// ******************** SPLITTING INTO TWO TREES ********************

(*
    There are three different split functions we'll want to write: one that carves off a left chunk, one that
    carves off a right chunk, and one that splits into two distinct trees. We'll write the "split into two trees"
    function first, because the other two are merely special cases of that one (and probably aren't worth writing
    special code for. There are a few MINOR efficiency gains from not creating the second tree when you're just
    keeping one, but they're not really worth it.)

    Splitting into two trees has seven distinct cases. Six of them are easy, and one is hard. In the following list,
    the original vector is `vec` and the index on which to split is `idx`. The index should be considered as the first
    element that will belong to vector B (i.e., if you split on idx 3, vector A will be 0..2, and B will be 3..end):

    1) idx = vec.Length. Simple:
        A = original vector
        B = empty
    2) idx > vec.tailOffset
        A = original vector with unchanged root and new tail (with first part of old tail)
        B = tail-only vector (no root)
    3) idx = vec.tailOffset
        A = original vector with root |> promoteNewTail (old tail discarded from A)
        B = tail-only vector with old tail (unchanged) and no root
    4) idx = 0. Again, simple:
        A = empty
        B = original vector
    5) idx < leftmostLeaf.items.Length. Split that leaf.
        A = tail-only vector with left half of that leaf
        B = original vector with that leaf snipped a bit (and new path to root from leftmost leaf)
    6) idx = leftmostLeaf.items.Length. Do NOT split that leaf.
        A = tail-only vector with that leaf (unchanged) as the tail.
        B = original vector minus that leaf (and one fewer entry in leftmost node one level up, plus new path to root)
    7) idx > leftmostLeaf.items.Length and idx < vec.tailOffset. This one is actually a bit complicated.

*)

// Return a new root after removing leftmost leaf. Will not change the tree's height.
// Returns a 3-tuple (leaf:Node<'a>,newRoot:Node<'a>,leafSize:int). The leafSize will be used in updating size tables above,
// so we return it up the chain for the sake of efficiency. TODO: Or maybe we just use the leaf that we're returning up the tree. That's better, I think.
let rec removeLeftmostLeaf shift root =
    if shift = Literals.blockSizeShift then
        // Children of this root node are leaves
        match root with
        | LeafNode _ -> invalidLeaf()
        | EmptyNode -> sprintf "Empty node found in tree at shift %d: %A" shift root |> invalidOp
        | TreeNode n ->
            let leaf = n.entries.[0] |> toLeaf
            let root' = TreeNode { entries   = n.entries   |> Array.copyAndRemoveFirst
                                   sizeTable = n.sizeTable |> copySizeTableMinusFirstItem }
            leaf,root',leaf.items.Length * 1<treeIdx>
        | FullNode n -> // This node will NO LONGER BE FULL, so it is going to become a TreeNode
            let leaf = n.entries.[0] |> toLeaf
            let root' = n.entries |> Array.copyAndRemoveFirst |> mkTreeNode shift
            leaf,root',leaf.items.Length * 1<treeIdx>
    else
        // Children of this root node are other nodes
        match root with
        | LeafNode _ -> invalidLeaf()
        | EmptyNode -> sprintf "Empty node found in tree at shift %d: %A" shift root |> invalidOp
        | TreeNode n ->
            let leaf,newLeftMostChild,leafLen = n.entries.[0] |> removeLeftmostLeaf (shift - Literals.blockSizeShift)
            let root' =
                if isEmpty newLeftMostChild then
                    TreeNode { entries   = n.entries   |> Array.copyAndRemoveFirst
                               sizeTable = n.sizeTable |> copySizeTableMinusFirstItem }
                else
                    TreeNode { entries   = n.entries   |> Array.copyAndSet 0 newLeftMostChild
                               sizeTable = n.sizeTable |> copyAndSubtractNFromSizeTable 0 leafLen }
            leaf,root',leafLen
        | FullNode n -> // This node will NO LONGER BE FULL, so it is going to become a TreeNode
            let leaf,newLeftMostChild,leafLen = n.entries.[0] |> removeLeftmostLeaf (shift - Literals.blockSizeShift)
            let root' =
                if isEmpty newLeftMostChild then
                    n.entries |> Array.copyAndRemoveFirst |> mkTreeNode shift
                else
                    n.entries |> Array.copyAndSet 0 newLeftMostChild |> mkTreeNode shift
            leaf,root',leafLen

// Pass in newLeafSize = newLeaf.items.Length for efficiency's sake (so we don't have to recalculate it at every level)
let rec setLeftmostLeaf newLeaf newLeafSize shift root =
    if shift = Literals.blockSizeShift then
        // Children of this root node are leaves
        match root with
        | LeafNode _ -> invalidLeaf()
        | EmptyNode -> sprintf "Empty node found in tree at shift %d: %A" shift root |> invalidOp
        | TreeNode n ->
            let oldLeafSize = (leafItems n.entries.[0]).Length * 1<treeIdx>
            let root' =
                if oldLeafSize = newLeafSize then
                    TreeNode { n with entries   = n.entries |> Array.copyAndSet 0 (LeafNode newLeaf) } // Size table didn't change
                else
                    TreeNode { entries   = n.entries   |> Array.copyAndSet 0 (LeafNode newLeaf)
                               sizeTable = n.sizeTable |> copyAndAddNToSizeTable 0 (newLeafSize - oldLeafSize) }
            root',oldLeafSize
        | FullNode n -> // This node MAY no longer be full, if and ONLY if the new leaf size <> the old leaf size. Otherwise it remains full
            let oldLeafSize = (leafItems n.entries.[0]).Length * 1<treeIdx>
            let root' =
                if oldLeafSize = newLeafSize then
                    FullNode { entries = n.entries |> Array.copyAndSet 0 (LeafNode newLeaf) }
                else
                    n.entries |> Array.copyAndSet 0 (LeafNode newLeaf) |> mkTreeNode shift
            root',oldLeafSize
    else
        // Children of this root node are other nodes
        match root with
        | LeafNode _ -> invalidLeaf()
        | EmptyNode -> sprintf "Empty node found in tree at shift %d: %A" shift root |> invalidOp
        | TreeNode n ->
            let newLeftmostChild,oldLeafSize = n.entries.[0] |> setLeftmostLeaf newLeaf newLeafSize (shift - Literals.blockSizeShift)
            let root' =
                if oldLeafSize = newLeafSize then
                    TreeNode { n with entries   = n.entries |> Array.copyAndSet 0 newLeftmostChild } // Size table didn't change
                else
                    TreeNode { entries   = n.entries   |> Array.copyAndSet 0 newLeftmostChild
                               sizeTable = n.sizeTable |> copyAndAddNToSizeTable 0 (newLeafSize - oldLeafSize) }
            root',oldLeafSize
        | FullNode n -> // This node MAY no longer be full, if and ONLY if the new leaf size <> the old leaf size. Otherwise it remains full
            let newLeftmostChild,oldLeafSize = n.entries.[0] |> setLeftmostLeaf newLeaf newLeafSize (shift - Literals.blockSizeShift)
            let root' =
                if oldLeafSize = newLeafSize then
                    FullNode { entries = n.entries |> Array.copyAndSet 0 newLeftmostChild }
                else
                    n.entries |> Array.copyAndSet 0 newLeftmostChild |> mkTreeNode shift
            root',oldLeafSize

let shiftNodesFromTailIfNeeded tail shift root =
    if nodeSize root = 0<nodeIdx> then tail,root else  // Short-circuit since getRightmostTwig doesn't like finding an empty root
    let lastTwig = getRightmostTwig root
    match lastTwig with
    | FullNode _ ->
        let lastLeaf = nodeEntries lastTwig |> Array.last
        let shiftCount = Literals.blockSize * 1<nodeIdx> - nodeSize lastLeaf
        if shiftCount = 0<nodeIdx> then
            // printfn "No node-shifting needed"
            tail,root
        elif shiftCount >= Array.length tail.items * 1<nodeIdx> then
            // printfn "This would shift everything out of the tail, so instead we'll promote a new tail"
            let lastLeaf,root' = root |> removeLastLeaf shift
            let tail' = { items = Array.append lastLeaf.items tail.items }
            // Now there's a new rightmost leaf, which must be a full leaf since the parent was a FullNode.
            tail',root'
        else
            // printfn "Need to shift some nodes"
            let nodesToShift,tailItems' = tail.items |> Array.splitAt (int shiftCount)
            let lastLeaf' = Array.append (leafItems lastLeaf) nodesToShift |> mkLeaf
            let root' = root |> replaceLastLeaf lastLeaf' shift
            { items = tailItems' },root'
    | _ -> tail,root  // Only need to shift nodes from tail if the last twig was a full node

let split idx vec =
    if vec.vecLen = 0<globalIdx> then
        // Split of an empty vector produces two empty vectors
        emptyVec,emptyVec
    elif idx = vec.vecLen then
        // Right vector is empty
        let vecL = vec
        let vecR = emptyVec
        vecL, vecR
    elif idx = vec.tailOffset then
        // Right vector is tail-only, left vector promotes last leaf into tail position
        let tailL, rootL = removeLastLeaf vec.shift vec.root
        // Must maintain invariant that last leaf is full. In this split scenario, that can be needed on left side but not right.
        let tailL', rootL' = shiftNodesFromTailIfNeeded tailL vec.shift rootL
        let tailR, rootR = vec.tail, emptyNode
        let vecL = { root = rootL'
                     tail = tailL'
                     shift = vec.shift
                     vecLen = idx
                     tailOffset = idx - tailL'.items.Length * 1<globalIdx> }  // Which *should* be Literals.blockSize, but let's not assume
        let vecR = { root = rootR
                     tail = tailR
                     shift = Literals.blockSizeShift
                     vecLen = tailR.items.Length * 1<globalIdx>
                     tailOffset = 0<globalIdx> }
        // Depending on the structure of the original vector, vecL might now be "tall" and need to be shortened. For example,
        // an original vector that looked like "[4] [4] T1" would cause vecL to need to be shortened.
        shortenVec vecL |> shiftNodesIntoTailIfNeeded, vecR
    elif idx > vec.tailOffset then
        // Split the tail, and root of left vector is unchanged from original
        let tailSplitIdx = idx - vec.tailOffset
        let tailItemsL, tailItemsR = vec.tail.items |> Array.splitAt (int tailSplitIdx)
        let tailL = { items = tailItemsL }
        let tailR = { items = tailItemsR }
        // Must maintain invariant that last leaf is full. In this split scenario, that can be needed on left side but not right.
        let tailL', rootL' = shiftNodesFromTailIfNeeded tailL vec.shift vec.root
        // TODO: Would it be more efficient to just have shiftNodesFromTailIfNeeded operate on an entire vector? ... Maybe it would. Because now we ALSO have to adjust the new tail offset.
        let vecL = { vec with tail = tailL'; root = rootL'; vecLen = idx; tailOffset = vec.tailOffset + (tailL'.items.Length - tailL.items.Length) * 1<globalIdx> }
        // TODO: Or just copy the "vec.vecLen - lenL - tailR'.items.Length * 1<globalIdx>" bit from lower down, that works too.
        // TODO: Figure out if either one of those is more efficient
        let vecR = { emptyVec with tail = tailR; vecLen = vec.vecLen - idx }
        shortenVec vecL |> shiftNodesIntoTailIfNeeded, vecR
    elif idx = 0<globalIdx> then
        // Left vector is empty
        let vecL = emptyVec
        let vecR = vec
        vecL, vecR
    else
        let leftLeaf = getLeftmostLeaf vec.root
        let leftLeafLen = leftLeaf.items.Length * 1<globalIdx>
        if idx < leftLeafLen then
            // Split leftmost leaf. Left vector is tail-only, right vector gets that leaf as its new leftmost leaf and is otherwise unchanged
            // ... Unchanged, that is, unless it was a very short vector where the split leaf ended up as the only node, and was short.
            // In which case we'll rewrite it later with shiftNodesFromTailIfNeeded
            let leafItemsL, leafItemsR = leftLeaf.items |> Array.splitAt (int idx)
            let lenL = leafItemsL.Length * 1<globalIdx>
            let leafL = { items = leafItemsL }  // This will become the tail of the left vector
            let leafR = { items = leafItemsR }
            let rootR,_ = setLeftmostLeaf leafR (leafItemsR.Length * 1<treeIdx>) vec.shift vec.root
            // Must maintain invariant that last leaf is full. In this split scenario, that can be needed on right side but not left.
            let tailR', rootR' = shiftNodesFromTailIfNeeded vec.tail vec.shift rootR
            let vecL = { emptyVec with tail = leafL
                                       vecLen = lenL }
            let vecR = { vec with root = rootR'
                                  tail = tailR'
                                  vecLen = vec.vecLen - lenL
                                  tailOffset = vec.vecLen - lenL - tailR'.items.Length * 1<globalIdx> }  // Since we may or may not have shifted items out of tail, have to recalculate tail offset
                       |> shiftNodesIntoTailIfNeeded // TODO: Still buggy: the [1,2,8]-split-at-4 situation ends up failing property checks.
            vecL, vecR
        elif idx = leftLeafLen then
            // Don't split leftmost leaf. Left vector gets that leaf as a tail (and is tail-only); right vector removes that one leaf and is otherwise unchanged.
            let tailL,rootR,lenL = removeLeftmostLeaf vec.shift vec.root
            let vecL = { emptyVec with tail = tailL
                                       vecLen = (lenL / 1<treeIdx> * 1<globalIdx>) }
            let vecR = { vec with root = rootR
                                  vecLen = vec.vecLen - (lenL / 1<treeIdx> * 1<globalIdx>)
                                  tailOffset = vec.tailOffset - (lenL / 1<treeIdx> * 1<globalIdx>) }
            // Depending on the structure of the original vector, vecR might now be "tall" and need to be shortened. For example,
            // an original vector that looked like "[4] [4] T1" would cause vecR to need to be shortened.
            vecL, shortenVec vecR |> shiftNodesIntoTailIfNeeded
        else
            // This is the complicated part.
            // There are two, and in some cases three, leaf nodes that are going to be relevant:
            // lastLeafL  = the leaf that will end up becoming vecL's last non-tail leaf
            // newTailL   = the leaf that will end up becoming vecL's new tail
            // firstLeafR = the leaf that will end up becoming vecR's first (leftmost) leaf

            // First, we look up the leaf that contains the item at (idx). Then, we find the one that contains (idx-1),
            // and see if they are the SAME leaf (physical equality). If they are the same leaf, it will be split into
            // newTailL and firstLeafR. If they are different leaves, there's no need for a split; the left one becomes
            // newTailL, and the right one becomes firstLeafR. Finally, the leaf immediately left of newTailL will become
            // lastLeafL. Note that there is guaranteed to be at least one leaf immediately left of newTailL, because
            // we know that the split index is > leftLeafLen. I.e., if the leaves look like this:
            //     [|0 1 2 3|] [|4 5 6|] [|7 8|] ...
            // and the split index is 4 or less, that's equal to or less than leafLeafLen, so an earlier elif branch was
            // taken. If split index is 5, then lastLeafL = [|0 1 2 3|], newTailL = [|4|], and firstLeafR = [|5 6|].

            let leafAtSplitIdx, leafIdxAtSplitIdx = findLeafIdx (idx * 1<treeIdx> / 1<globalIdx>) vec.shift vec.root  // At vec.shift levels, tree indices are = to global indices
            let newTailL, firstLeafR =
                if leafIdxAtSplitIdx <> 0<treeIdx> then
                    // The leafAtSplitIdx leaf needs to be split into newTailL, firstLeafR
                    leafAtSplitIdx |> splitLeafAt (int leafIdxAtSplitIdx)
                else
                    // We don't need to split this node. Can we find the previous node? ... eh, probably not. Just look through the index again, it's O(log32 n).
                    let leafForTail, _ = findLeafIdx (idx * 1<treeIdx> / 1<globalIdx> - 1<treeIdx>) vec.shift vec.root
                    leafForTail, leafAtSplitIdx
            // Finally, the first leaf on the L side is going to be the one at (idx-1 - newTailL.items.Length)
            // Why? Well, look at the two possibilities. Either we split the node or we didn't.
            // If we didn't split the node, we have [a b c d] [e f g] [h i j]. (idx) points to h, and (idx-1) points to g. We want to find the index of d,
            // which is (idx-1 - [e f g].Length). If we did split the [e f g] node, let's say because (idx) pointed to g (and (idx-1) pointed to f), then
            // we have [a b c d] [e f] [g] [h i j]. (idx - 1) points to f, and we still want d, which is (idx-1 - [e f].Length).
            // Also note that the index of the last item of lastLeafL is going to be L's new tail offset minus 1, so we'll want to save that value.
            let lastLeafL, lastIdxL = findLeafIdx ((idx / 1<globalIdx> - 1 - newTailL.items.Length) * 1<treeIdx>) vec.shift vec.root
            let rec splitNode shift root =
                let treeIdx = (idx * 1<treeIdx> / 1<globalIdx>)  // At vec.shift levels, tree indices are = to global indices
                let (rootL,idxL), (rootR,idxR) = findNodePairAtIdx (treeIdx-1<treeIdx>,treeIdx) shift vec.shift (root,root)
                // printfn "At level %d of root %A, we split into idxL %d for rootL %A and idxR %d for rootR %A" shift root idxL rootL idxR rootR
                if shift = Literals.blockSizeShift then
                    // Children are leaves
                    let childLeafL = rootL |> getChildNode idxL
                    let childLeafR = rootR |> getChildNode idxR
                    // We already know that childLeafR is the same leaf node as firstLeafR... no, wait, we don't.
                    (*  CASE 1: We were splitting on index 7 in the example diagram.
                            - Then we have firstLeafR = [7;8], newTailL = [4;5;6], lastLeafL = [0;1;2;3]
                            - childLeafR = [7;8] and childLeafL = [4;5;6]
                        CASE 2: We were splitting on index 8 in the example diagram.
                            - Then we have firstLeafR = [8], newTailL = [7], lastLeafL = [4;5;6]
                            - childLeafR = [7;8] and childLeafL = [7;8]
                        CASE 3: We were splitting on index 9 in the example diagram.
                            - Then we have firstLeafR = [9;10], newTailL = [7;8], lastLeafL = [4;5;6]
                            - childLeafR = [9;10] and childLeafL = [7;8]
                        CASE 4: We were splitting on index 10 in the example diagram.
                            - Then we have firstLeafR = [10], newTailL = [9], lastLeafL = [7;8]
                            - childLeafR = [9;10] and childLeafL = [9;10]
                        CASE 5: We were splitting on index 11 in the example diagram.
                            - Then we have firstLeafR = [11;12;13], newTailL = [9;10], lastLeafL = [7;8]
                            - childLeafR = [11;12;13] and childLeafL = [9;10]
                        CASE 6: We were splitting on index 12 in the example diagram.
                            - Then we have firstLeafR = [12;13], newTailL = [11], lastLeafL = [9;10]
                            - childLeafR = [11;12;13] and childLeafL = [11;12;13]
                        CASE 7: We were splitting on index 13 in the example diagram.
                            - Then we have firstLeafR = [13], newTailL = [11;12], lastLeafL = [9;10]
                            - childLeafR = [11;12;13] and childLeafL = [11;12;13]
                        CASE 8: We were splitting on index 14 in the example diagram.
                            - Then we have firstLeafR = [14;15], newTailL = [11;12;13], lastLeafL = [9;10]
                            - childLeafR = [14;15] and childLeafL = [11;12;13]
                    *)
                    let leafNodesWereSplit = not (childLeafR |> toLeaf |> isSameNode firstLeafR)
                    // TODO: Consider using Array.splitAt in the true and false branches below -- I believe I wrote them before I implemented Array.splitAt
                    // Also consider whether leafItems would be useful in any of this algorithm
                    if leafNodesWereSplit then
                        // printfn "Leaf nodes were split. Therefore... what?"
                        // Let's say this is case 4. So rootL and rootR are the same node: the middle one.
                        // And childLeafL and childLeafR are both pointing to the *original* node that was split in order
                        // to make newTailL [9] and firstLeafR [10]. So we need to create rootL' by replacing the child
                        // at idxL with newTailL, and create rootR' by replacing the child at idxR with firstLeafR.

                        // Now let's look at case 5. In case 5 the leaf nodes were not split, so that's the other branch.

                        // Case 6. Again, we need to replace rootL's child at idxL with newTailL,and rootR needs to swap out idxR for newTailR.
                        // Okay, I think we've got this branch figured out. But is there a "setChild" function that deals with TreeNodes properly?
                        // ... Yes. NOW there is:
                        // let replaceChildAt localIdx newChild childSize shift = function
                        //     | LeafNode _ -> invalidLeaf()
                        let rootL' = rootL |> replaceChildAt idxL (LeafNode newTailL)     (newTailL.items.Length*1<treeIdx>) shift
                        let rootR' = rootR |> replaceChildAt idxR (LeafNode firstLeafR) (firstLeafR.items.Length*1<treeIdx>) shift
                        let entriesL' = nodeEntries rootL'
                        let rootL'' = Array.sub entriesL' 0 (int idxL) |> mkTreeNode shift  // We certainly need to make tree nodes here
                        let rootR'' =
                            if idxR = 0<nodeIdx> then
                                rootR'
                            else
                                let entriesR' = nodeEntries rootR'
                                entriesR'.[int idxR..] |> mkTreeNode shift
                        rootL'', rootR''
                    else
                        // printfn "Leaf nodes were NOT split. Therefore, I think we need to strip the last node off the left? Think about it some more."
                        // Let's say this is case 5:
                        // CASE 5: We were splitting on index 11 in the example diagram.
                        //     - Then we have firstLeafR = [11;12;13], newTailL = [9;10], lastLeafL = [7;8]
                        //     - childLeafR = [11;12;13] and childLeafL = [9;10]
                        // Here, rootL and rootR are both the middle yellow node.

                        // WAIT. Let's also look at case 3! In case 3, rootL and rootR are NOT the same node! Does that make a difference?
                        // CASE 3: We were splitting on index 9 in the example diagram.
                        //     - Then we have firstLeafR = [9;10], newTailL = [7;8], lastLeafL = [4;5;6]
                        //     - childLeafR = [9;10] and childLeafL = [7;8]
                        // Here, rootL is the left yellow node, and rootR is the middle yellow node.

                        // And we should also look at case 8:
                        // CASE 8: We were splitting on index 14 in the example diagram.
                        //     - Then we have firstLeafR = [14;15], newTailL = [11;12;13], lastLeafL = [9;10]
                        //     - childLeafR = [14;15] and childLeafL = [11;12;13]
                        // Here, rootL is the middle yellow node, and rootR is the right yellow node.

                        // And case 1:
                        // CASE 1: We were splitting on index 7 in the example diagram.
                        //     - Then we have firstLeafR = [7;8], newTailL = [4;5;6], lastLeafL = [0;1;2;3]
                        //     - childLeafR = [7;8] and childLeafL = [4;5;6]
                        // Here, rootL and rootR are both the left yellow node.

                        // In ALL cases, the new tail of L is the same node as childLeafL.

                        // We need to construct the new rootL by taking the previous rootL and copying all its children
                        // up to, but NOT including, the index where newTailL is to be found. We already know that newTaiL
                        // is the same node as childLeafL, so that index is idxL. There are two cases:
                        //     idxL = 0  (e.g., case 5 or case 8).
                        //         In this case, the rootL at this level will be *empty*, or None.
                        //         TODO: decide whether to return an empty node or None. I'm inclined towards empty node.
                        //     idxL > 0  (e.g., case 1 or case 3).
                        //         In this case, the rootL at this level will not be empty. Copy all entries up through (idxL - 1) inclusive.
                        //         That will get you the new, valid rootL'.
                        // Conveniently, Array.sub takes a start index (whcih will be 0) and a size, so passing idxL will copy notes up to (idxL - 1) inclusive.
                        // I.e., if idxL is 2, then Array.sub [|0;1;2;3|] 0 2 is [|0;1|], which is what we want.
                        // And that conveniently creates an empty node if we need to.

                        // As for the RIGHT root and idxR, let's take a look at those cases again.
                        // Let's say this is case 5:
                        // CASE 5: We were splitting on index 11 in the example diagram.
                        //     - Then we have firstLeafR = [11;12;13], newTailL = [9;10], lastLeafL = [7;8]
                        //     - childLeafR = [11;12;13] and childLeafL = [9;10]
                        // Here, rootL and rootR are both the middle yellow node.

                        // WAIT. Let's also look at case 3! In case 3, rootL and rootR are NOT the same node! Does that make a difference?
                        // CASE 3: We were splitting on index 9 in the example diagram.
                        //     - Then we have firstLeafR = [9;10], newTailL = [7;8], lastLeafL = [4;5;6]
                        //     - childLeafR = [9;10] and childLeafL = [7;8]
                        // Here, rootL is the left yellow node, and rootR is the middle yellow node.

                        // And we should also look at case 8:
                        // CASE 8: We were splitting on index 14 in the example diagram.
                        //     - Then we have firstLeafR = [14;15], newTailL = [11;12;13], lastLeafL = [9;10]
                        //     - childLeafR = [14;15] and childLeafL = [11;12;13]
                        // Here, rootL is the middle yellow node, and rootR is the right yellow node.

                        // And case 1:
                        // CASE 1: We were splitting on index 7 in the example diagram.
                        //     - Then we have firstLeafR = [7;8], newTailL = [4;5;6], lastLeafL = [0;1;2;3]
                        //     - childLeafR = [7;8] and childLeafL = [4;5;6]
                        // Here, rootL and rootR are both the left yellow node.
                        // In case 1, idxR is 2. And we want from idxR to the end of the node.
                        // In case 3, idxR is 0. And we want from idxR to the end of the node. SPECIAL CASE: idxR is 0, so rootR should be UNCHANGED rather than copied.
                        // In case 5, idxR is 1. And we want from idxR to the end of the node.
                        // In case 8, idxR is 0. And we want from idxR to the end of the node. SPECIAL CASE: idxR is 0, so rootR should be UNCHANGED rather than copied.

                        // So to make rootR', we want to take nR.entries.[idxR..] -- BUT if idxR is 0, then just take nR as it is.

                        let entriesL = nodeEntries rootL
                        let rootL' = Array.sub entriesL 0 (int idxL) |> mkTreeNode shift  // We certainly need to make tree nodes here
                        let rootR' =
                            if idxR = 0<nodeIdx> then
                                rootR
                            else
                                let entriesR = nodeEntries rootR
                                entriesR.[int idxR..] |> mkTreeNode shift
                        rootL', rootR'
                else
                    // Children are nodes. So we want to look at what came up from BELOW, and then deal with that.
                    // Which means that at this point, it looks like we need a recursive call.

                    let childNodeL = rootL |> getChildNode idxL
                    let childNodeR = rootR |> getChildNode idxR
                    // printfn "childNodeL = %A, childNodeR = %A" childNodeL childNodeR
                    let childL', childR' = splitNode (shift - Literals.blockSizeShift) root
                    // printfn "childL' = %A, childR' = %A" childL', childR'
                    let rootL' = if isSameNode childNodeL childL'
                                    then rootL
                                 elif isEmpty childL'
                                    // An empty node returned up from the lower level means "drop this index and *all subsequent indices* at this level"
                                    then rootL |> keepOnlyNChildren idxL shift
                                 else
                                    rootL |> replaceChildAt idxL childL' (treeSize (shift - Literals.blockSizeShift) childL') shift
                    // printfn "rootL' = %A" rootL'
                    // TODO: not quite happy about the treeSize there.
                    // Isn't there some way we could be returning that up the levels instead of calculating it?
                    let rootR' = if isSameNode childNodeR childR' then rootR
                                                                  else rootR |> replaceChildAt idxR childR' (treeSize (shift - Literals.blockSizeShift) childR') shift
                    // printfn "rootR' = %A" rootR'
                    // TODO: likewise, not quite happy about the treeSize there. But eh, it's an O(1) lookup or calculation, so whatever. Keep it.

                    // And we also need to trim: [0..idxL] and [idxR..]. In both cases, do some math first to see if we'd keep the original node or copy it.
                    let rootL'' =
                        if idxL = nodeSize rootL' then
                            rootL'
                        else
                            (nodeEntries rootL').[0..int idxL] |> mkTreeNode shift
                    // printfn "rootL'' = %A" rootL''
                    let rootR'' =
                        if idxR = 0<nodeIdx> then
                            rootR'
                        else
                            (nodeEntries rootR').[int idxR..] |> mkTreeNode shift
                    // printfn "rootR'' = %A" rootR''
                    rootL'', rootR''
                    // TODO: I am really not sure if that's correct. DESPERATELY need to unit test it.
                    // TODO: Or just draw a higher-level graph and look at it more closely.

            // Now we're back in the split function. Here's where we call splitNode to get us two new roots.
            let rootL, rootR = splitNode vec.shift vec.root
            // Must maintain invariant that last leaf is full. In this split scenario, that can be needed on either side.
            let tailL', rootL' = shiftNodesFromTailIfNeeded newTailL vec.shift rootL
            let tailR', rootR' = shiftNodesFromTailIfNeeded vec.tail vec.shift rootR
            let vecL = { root = rootL'
                         tail = tailL'
                         shift = vec.shift // Keep same height; shrink calculations are done in shortenVec function
                         vecLen = idx
                         tailOffset = idx - tailL'.items.Length * 1<globalIdx> }  // Or should that have a -1 attached??
            let vecR = { root = rootR'
                         tail = tailR'
                         shift = vec.shift // Keep same height; shrink calculations are done in shortenVec function
                         vecLen = vec.vecLen - idx   // The left tree took `idx` items, so this math is simple
                         tailOffset = vec.vecLen - idx - tailR'.items.Length * 1<globalIdx> }  // But this one isn't quite as simple, since we might have shifted items out of the tail
            shortenVec vecL |> shiftNodesIntoTailIfNeeded, shortenVec vecR |> shiftNodesIntoTailIfNeeded
            // Here's what we did further up for a tail-only right vector, and left promoting a leaf into tail position:
            // let vecL = { root = rootL
            //              tail = tailL
            //              shift = vec.shift
            //              vecLen = idx
            //              tailOffset = idx - tailL.items.Length }  // Which *should* be Literals.blockSize, but let's not assume
            // let vecR = { root = rootR
            //              tail = tailR
            //              shift = Literals.blockSizeShift
            //              vecLen = tailR.items.Length
            //              tailOffset = 0 }


            // Old notes follow:

            // For splitAt function, look up that index, and the index to its immediate left. The given idx will
            // become the first element of vector B, and the (idx-1) position will be the last element of vector A.
            // (The result is A,B such that (RRBVector.append A B) produces the original vector). We ultimately
            // need to get three leaf nodes: the one belonging to idx (will become firstLeafB), the one belonging
            // to idx-1 (will become newTailA), and the leaf immediately left of newTailA. If firstLeafB and
            // newTailA are the same leaf (which will happen quite often), it gets split so that they are separate
            // leaves. If they are already separate leaves, they don't need to be rewritten.

            // Here we need to find the three leaves mentioned earlier: lastLeafA, newTailA, and firstLeafB. It will often
            // happen that newTailA is in the same original leaf as firstLeafB, in which case that leaf gets split to produce these
            // two leaves. lastLeafA is always its own leaf, though: once newTailA is identified, go one leaf left to find lastLeafA.
            // Then we produce a new path to the root from lastLeafA, and a new path to the root from firstLeafB. (newTailA does
            // not have a path to the root). Some opportunities for efficiency occur here, if lastLeafA had a separate path-to-root
            // than newTailA did. In particular, if newTailA's path to the root would have been only 1-item nodes until we get to a
            // 2-item root, then that will become a 1-item root after removing newTailA, and thus the new tree will have one fewer level.

// Four (now six) primitives to make iterating over the tree more efficient:
// just iterate over every leaf node in order, either front-to-back
// or (to help with the "RandomAccessList" equivalent later) back-to-front.
// "Now six" because I just added iterFromIdx and revIterFromIdx. But I have
// not yet figured out if I want them to iterate over leaf nodes, or items.
// Actually, why not both? TODO: Move this module into its own file, and write a separate set of unit tests for it.
module TreeIteration =
    let rec iterLeafNodes node =
        seq {
            match node with
            | LeafNode n -> yield n  // Or else yield n.items...
            | TreeNode n ->
                for child in n.entries do
                    yield! iterLeafNodes child
            | FullNode n ->
                for child in n.entries do
                    yield! iterLeafNodes child
        }

    let rec revIterLeafNodes node =
        seq {
            match node with
            | LeafNode n -> yield n  // Or else yield n.items...
            | TreeNode n ->
                for i in n.entries.Length - 1 .. -1 .. 0 do
                    yield! revIterLeafNodes n.entries.[i]
            | FullNode n ->
                for i in n.entries.Length - 1 .. -1 .. 0 do
                    yield! revIterLeafNodes n.entries.[i]
        }

    let rec iterLeavesOfTree vec =
        seq {
            yield! iterLeafNodes vec.root
            yield vec.tail
        }

    let rec revIterLeavesOfTree vec =
        seq {
            yield vec.tail
            yield! revIterLeafNodes vec.root
        }

    // Returns tuples of (leaf,index-to-start-iterating-from). The latter index will
    // usually be 0, but for the leaf that we start from it might (and probably will) be non-0.
    // idx in this function is INCLUSIVE.
    let iterLeavesAndFirstIndexesFromIdxInTree idx vec =
        let rec iterLeavesAndFirstIndexesFromIdx idx shift root =
            if shift = 0 then
                // We're at the leaf level
                let leaf = toLeaf root
                Seq.singleton (leaf,idx / 1<treeIdx> * 1<nodeIdx>)
            else
                let localIdx, nextLevelNode, treeIdx = appropriateIndexSearch idx shift root
                seq {
                    yield! iterLeavesAndFirstIndexesFromIdx treeIdx (shift - Literals.blockSizeShift) nextLevelNode
                    // From this point on, we can iterate all the rest of the nodes
                    let entries = nodeEntries root
                    let len = Array.length entries
                    if len > (int localIdx + 1) then
                        for node in entries.[int localIdx + 1..] do
                            for leaf in iterLeafNodes node do
                                yield (leaf,0<nodeIdx>)
                }
        let idx' = if idx < 0<globalIdx> then (idx + vec.vecLen) else idx
        let treeIdx' = idx' / 1<globalIdx> * 1<treeIdx>
        seq {
            if idx' < vec.tailOffset then
                yield! iterLeavesAndFirstIndexesFromIdx treeIdx' vec.shift vec.root
                yield (vec.tail,0<nodeIdx>)
            else
                yield (vec.tail,(idx' - vec.tailOffset) / 1<globalIdx> * 1<nodeIdx>)
        }

    // Returns tuples of (leaf,index-to-start-iterating-from). The latter index will usually be the index
    // of the leaf node's last item, but for the leaf that we end at it might (and probably will) be non-0.
    // idx in this function is INCLUSIVE.
    let iterLeavesAndFirstIndexesUpToIdxInTree idx vec =
        // TODO: Edit this function
        let rec iterLeavesAndFirstIndexesUpToIdx idx shift root =
            if shift = 0 then
                // We're at the leaf level
                let leaf = toLeaf root
                Seq.singleton (leaf,idx / 1<treeIdx> * 1<nodeIdx>)
            else
                if isEmpty root then Seq.empty else
                let localIdx, nextLevelNode, treeIdx = appropriateIndexSearch idx shift root
                seq {
                    // From this point on, we can iterate all the rest of the nodes
                    let entries = nodeEntries root
                    if int localIdx > 0 then
                        for node in entries.[0..int localIdx - 1] do
                            for leaf in iterLeafNodes node do
                                yield (leaf,(Array.length leaf.items - 1) * 1<nodeIdx>)

                    yield! iterLeavesAndFirstIndexesUpToIdx treeIdx (shift - Literals.blockSizeShift) nextLevelNode
                }
        let idx' = if idx < 0<globalIdx> then (idx + vec.vecLen) else idx
        let treeIdx' = idx' / 1<globalIdx> * 1<treeIdx>
        seq {
            if idx' >= vec.tailOffset then
                yield! iterLeavesAndFirstIndexesUpToIdx (vec.tailOffset / 1<globalIdx> * 1<treeIdx> - 1<treeIdx>) vec.shift vec.root
                yield (vec.tail,(idx' - vec.tailOffset) / 1<globalIdx> * 1<nodeIdx>)
            else
                yield! iterLeavesAndFirstIndexesUpToIdx treeIdx' vec.shift vec.root
                // yield (vec.tail,(idx' - vec.tailOffset) / 1<globalIdx> * 1<nodeIdx>) // Pretty sure this line should be deleted
        }

    // Returns tuples of (leaf,index-to-stop-iterating-backwards-at). The latter index will
    // usually be 0, but on the "last" (leftmost) leaf node in the sequence it may be in the middle.
    // idx in this function is INCLUSIVE.
    let revIterLeavesAndLastIndexesFromIdxInTree idx vec =
        let rec revIterLeavesAndFirstIndexesFromIdx idx shift root =
            if shift = 0 then
                // We're at the leaf level
                let leaf = toLeaf root
                Seq.singleton (leaf,idx / 1<treeIdx> * 1<nodeIdx>)
            else
                let localIdx, nextLevelNode, treeIdx = appropriateIndexSearch idx shift root
                seq {
                    yield! revIterLeavesAndFirstIndexesFromIdx treeIdx (shift - Literals.blockSizeShift) nextLevelNode
                    // From this point on, we can iterate all the rest of the nodes
                    let entries = nodeEntries root
                    if int localIdx > 0 then
                        for i in (int localIdx - 1) .. -1 .. 0 do
                            let node = entries.[i]
                            for leaf in revIterLeafNodes node do
                                yield (leaf,(Array.length leaf.items - 1) * 1<nodeIdx>)
                }
        let idx' = if idx < 0<globalIdx> then (idx + vec.vecLen) else idx
        let treeIdx' = idx' / 1<globalIdx> * 1<treeIdx>
        seq {
            if idx' >= vec.tailOffset then
                yield (vec.tail,(idx' - vec.tailOffset) / 1<globalIdx> * 1<nodeIdx>)
                for leaf in revIterLeafNodes vec.root do
                    yield (leaf,(Array.length leaf.items - 1) * 1<nodeIdx>)
            else
                yield! revIterLeavesAndFirstIndexesFromIdx treeIdx' vec.shift vec.root
        }

    // Returns tuples of (leaf,index-to-start-iterating-backwards-from). The latter index will usually be the
    // index of the leaf node's last item, but on the first leaf node in the sequence it may be in the middle.
    // idx in this function is INCLUSIVE.
    let revIterLeavesAndLastIndexesUpToIdxInTree idx vec =
        let rec revIterLeavesAndFirstIndexesUpToIdx idx shift root =
            if shift = 0 then
                // We're at the leaf level
                let leaf = toLeaf root
                Seq.singleton (leaf,idx / 1<treeIdx> * 1<nodeIdx>)
            else
                let localIdx, nextLevelNode, treeIdx = appropriateIndexSearch idx shift root
                seq {
                    // From this point on, we can iterate all the rest of the nodes
                    let entries = nodeEntries root
                    let len = Array.length entries
                    if len > (int localIdx) then
                        for i in (len - 1) .. -1 .. (int localIdx + 1) do
                            let node = entries.[i]
                            for leaf in revIterLeafNodes node do
                                yield (leaf,0<nodeIdx>)
                    yield! revIterLeavesAndFirstIndexesUpToIdx treeIdx (shift - Literals.blockSizeShift) nextLevelNode
                }
        let idx' = if idx < 0<globalIdx> then (idx + vec.vecLen) else idx
        let treeIdx' = idx' / 1<globalIdx> * 1<treeIdx>
        seq {
            if idx' >= vec.tailOffset then
                yield (vec.tail,(idx' - vec.tailOffset) / 1<globalIdx> * 1<nodeIdx>)
            else
                yield (vec.tail,0<nodeIdx>)
                yield! revIterLeavesAndFirstIndexesUpToIdx treeIdx' vec.shift vec.root
        }

    let iterItemsFromIdx idx vec =
        seq {
            for (leaf, startIdx) in iterLeavesAndFirstIndexesFromIdxInTree idx vec do
                yield! leaf.items.[int startIdx..]
        }

    let revIterItemsFromIdx idx vec =
        seq {
            for (leaf, lastIdx) in revIterLeavesAndLastIndexesFromIdxInTree idx vec do
                for i in (int lastIdx) .. -1 .. 0 do
                    yield leaf.items.[i]
        }

    let iterItemsUpToIdx idx vec =
        seq {
            for (leaf, endIdx) in iterLeavesAndFirstIndexesUpToIdxInTree idx vec do
                yield! leaf.items.[..int endIdx]
        }

    let revIterItemsUpToIdx idx vec =
        seq {
            for (leaf, endIdx) in revIterLeavesAndLastIndexesUpToIdxInTree idx vec do
                for i in (leaf.items.Length - 1) .. -1 .. (int endIdx) do
                    yield leaf.items.[i]
        }

    let iterItems vec = seq { for leaf in iterLeavesOfTree vec do yield! leaf.items }

    let revIterItems vec =
        seq {
            for leaf in revIterLeavesOfTree vec do
                for i in (leaf.items.Length - 1) .. -1 .. 0 do
                    yield leaf.items.[i]
        }

let toSeq vec = seq {
                    for leaf in TreeIteration.iterLeavesOfTree vec do
                        yield! leaf.items
                }

let toList vec = [
                    for leaf in TreeIteration.iterLeavesOfTree vec do
                        yield! leaf.items
                 ]

let toArray vec = [|
                      for leaf in TreeIteration.iterLeavesOfTree vec do
                          yield! leaf.items
                  |]


let toArray2 vec =
    vec
    |> TreeIteration.iterLeavesOfTree
    |> Array.ofSeq
    |> Array.collect (fun l -> l.items)
// Let's see if that's any faster

// "Shift" items down in merging arrays, creating full arrays
// I.e., if M = 4, a is [1;2;3;4] and b is [5;6;7] and aIdx is 2,
// then the output will contain [3;4;5;6] and the new aIdx will be 2 because
// the next node will start at b's 7.
let shiftItemsDown a aIdx b =
    let aLen = Array.length a
    let bLen = Array.length b
    let aCnt = aLen - aIdx
    if aCnt + bLen > Literals.blockSize then
        let bCnt = Literals.blockSize - aCnt
        let dest = Array.zeroCreate Literals.blockSize
        Array.blit a aIdx dest    0 aCnt
        Array.blit b    0 dest aCnt bCnt
        dest,bCnt
    else
        let dest = Array.zeroCreate (aCnt + bLen)
        Array.blit a aIdx dest    0 aCnt
        Array.blit b    0 dest aCnt bLen
        dest,-1   // -1 signals STOP to the merge algorithm

/// Rebalance a set of nodes of level `shift` (whose children therefore live at `shift - Literals.blockSizeShift`)
let rebalance shift combined =
    let mergeStart = combined |> Array.tryFindIndex (fun node -> nodeSize node < Literals.blockSizeMin * 1<nodeIdx>)
    // TODO: Write a "safe findIndex" that returns -1 instead of None, or else simply trust that the caller checked before rebalancing? Nah, that's a bit too dangerous.
    // TODO: Or else change this function to "execute merge plan". Yeah, that could work. Then we're handed the combined array *and* the mergeStart and mergeLen values.
    if Option.isNone mergeStart then combined else
    let mergeStart = Option.get mergeStart
    let destLen = Array.length combined - 1
    let dest = Array.zeroCreate destLen
    Array.blit combined 0 dest 0 mergeStart
    let mutable workIdx = mergeStart
    let mutable i = 0
    // NOTE: This if/else statement probably won't be needed in the class version, where we can treat everything in these arrays as an opaque obj reference
    if shift <= Literals.blockSizeShift then
        while i >= 0 && workIdx < destLen do
            let arr,newI = shiftItemsDown (leafItems combined.[workIdx]) i (leafItems combined.[workIdx + 1])
            dest.[workIdx] <- mkLeaf arr
            i <- newI
            workIdx <- workIdx + 1
    else
        while i >= 0 && workIdx < destLen do
            let arr,newI = shiftItemsDown (nodeEntries combined.[workIdx]) i (nodeEntries combined.[workIdx + 1])
            dest.[workIdx] <- mkTreeNode shift arr
            i <- newI
            workIdx <- workIdx + 1
    Array.blit combined (workIdx+1) dest workIdx (destLen - workIdx)  // TODO: Double-check these indices against any possible off-by-one errors
    dest

let splitAtBlockSize combined =
    let cLen = Array.length combined
    if cLen > Literals.blockSize then
        combined |> Array.splitAt Literals.blockSize
    else
        combined,[||]

[<Literal>]
let eMaxPlusOne = 3 // Should be Literals.radixSearchErrorMax + 1

let inline doWeNeedToRebalance slotCount nodeCount =
    // Formula: If you have N completely full nodes, you have a maximum of N*M slots where M is the branching factor.
    // I.e., with the standard branching factor of 32, if you have a single full node, you have 32 slots.
    // Therefore, if you have 32 slots or less and your N is 3, your e will be 2, which is acceptable.
    // But if your N is 4, your e will be 3 and you'll have to rebalance.
    // Therefore, take your node count, and subtract (eMax + 1) from it. Multiply that number by M, and you'll have
    // the highest slot count for which your e would be greater than eMax. I.e., if you have 4 nodes, you need to
    // rebalance at M slots, but if you have M+1 slots across those 4 nodes, no need to rebalance.
    slotCount <= ((nodeCount - eMaxPlusOne) >>> Literals.blockBitMask)

let slotCount nodes =
    nodes |> Array.sumBy nodeSize

let twigSlotCount = function
    | LeafNode n -> invalidLeaf ()
    // TODO: Verify the FullNode math
    | FullNode n -> (n.entries.Length - 1) * Literals.blockSize * 1<nodeIdx> + (Array.last n.entries |> leafItems |> Array.length) * 1<nodeIdx>
    | TreeNode n -> (n.sizeTable |> Array.last) / 1<treeIdx> * 1<nodeIdx>

let doWeNeedToRebalance1 nodes =
    let slots = slotCount nodes |> int
    let nodeCount = Array.length nodes
    doWeNeedToRebalance slots nodeCount

let doWeNeedToRebalance2 a b =
    let slots = slotCount a + slotCount b |> int
    let nodeCount = Array.length a + Array.length b
    doWeNeedToRebalance slots nodeCount

let doWeNeedToRebalance3 a tail b =
    let nodeCount = Array.length a + 1 + Array.length b
    if nodeCount > 2 * Literals.blockSize then true else // A+tail+B scenario, and we already know there'll be enough room for the tail's items in the merged+rebalanced node
    let slots = slotCount a + nodeSize tail + slotCount b |> int // TODO: Improve this: since we know we're at the twig level, can we just use twigSlotCount? (But we'd need actual nodes, not arrays of leaves, as parameters.)
    doWeNeedToRebalance slots nodeCount

let merge shift a b =
    let shouldWeRebalance = doWeNeedToRebalance2 a b
    let result = if shouldWeRebalance then
                    Array.append a b |> rebalance shift
                 else
                    Array.append a b
    splitAtBlockSize result

let merge3WayWhereWeKnowThereIsRoom shift a tail b =
    let shouldWeRebalance = doWeNeedToRebalance3 a tail b
    let combined = if shouldWeRebalance then
                       Array.append3' a tail b |> rebalance shift
                   else
                       Array.append3' a tail b
    splitAtBlockSize combined

// TODO: Delete the functions above that aren't going to be used once we decide on the "push tail into tree" method
let merge3WayTwigs a tail b =  // TODO: This function is unused
    let aLen = nodeSize a
    let bLen = nodeSize b
    let tLen = nodeSize tail
    if  aLen < Literals.blockSize * 1<nodeIdx>
     || bLen < Literals.blockSize * 1<nodeIdx>
     || (twigSlotCount a) + tLen <= Literals.blockSize*(Literals.blockSize-1) * 1<nodeIdx>
     || (twigSlotCount b) + tLen <= Literals.blockSize*(Literals.blockSize-1) * 1<nodeIdx>
    then
        merge3WayWhereWeKnowThereIsRoom Literals.blockSizeShift (nodeEntries a) tail (nodeEntries b)
    else
        failwith "Oh dear, we shouldn't have tried the merge3way because there really wasn't room for it. Should have pushed the tail into the tree."

let inline isThereRoomToMergeTheTail aTwig bTwig tLen =
    // aTwig should be the rightmost twig of vector A
    // bTwig should be the  leftmost twig of vector B
    let aLen = nodeSize aTwig
    let bLen = nodeSize bTwig
    aLen < Literals.blockSize * 1<nodeIdx>
 || bLen < Literals.blockSize * 1<nodeIdx>
 || (twigSlotCount aTwig) + tLen <= Literals.blockSize*(Literals.blockSize-1) * 1<nodeIdx>
 || (twigSlotCount bTwig) + tLen <= Literals.blockSize*(Literals.blockSize-1) * 1<nodeIdx>

// New algorithm seems to be working better -- and it's cleaner-looking, too.
let rec mergeTree aShift a bShift b tail =
    if aShift <= Literals.blockSizeShift && bShift <= Literals.blockSizeShift then
        // At twig level on both nodes
        match tail with
        | None -> merge aShift (nodeEntries a) (nodeEntries b)
        | Some t -> merge3WayWhereWeKnowThereIsRoom aShift (nodeEntries a) t (nodeEntries b)
    else
        if aShift < bShift then
            let aR, bL = mergeTree aShift a (bShift - Literals.blockSizeShift) (nodeEntries b).[0] tail
            let a' = if aR |> Array.isEmpty then [||] else [|mkTreeNode (bShift - Literals.blockSizeShift) aR|]
            let b' = if bL |> Array.isEmpty then b |> nodeEntries |> Array.copyAndRemoveFirst
                                            else b |> nodeEntries |> Array.copyAndSet 0 (mkTreeNode (bShift - Literals.blockSizeShift) bL)
            merge bShift a' b'
        elif aShift > bShift then
            let aR, bL = mergeTree (aShift - Literals.blockSizeShift) (nodeEntries a |> Array.last) bShift b tail
            let a' = if aR |> Array.isEmpty then a |> nodeEntries |> Array.copyAndPop
                                            else a |> nodeEntries |> Array.copyAndSetLast (mkTreeNode (aShift - Literals.blockSizeShift) aR)
            let b' = if bL |> Array.isEmpty then [||] else [|mkTreeNode (aShift - Literals.blockSizeShift) bL|]
            merge aShift a' b'
        else
            let aR, bL  = Array.last (nodeEntries a), Array.item 0 (nodeEntries b)
            let aR', bL' = mergeTree (aShift - Literals.blockSizeShift) aR (bShift - Literals.blockSizeShift) bL tail
            // TODO: Refactor this "let a', let b'" code into some common helper, if it makes sense
            let a' = if aR' |> Array.isEmpty then a |> nodeEntries |> Array.copyAndPop
                                             else a |> nodeEntries |> Array.copyAndSetLast (mkTreeNode (aShift - Literals.blockSizeShift) aR')
            let b' = if bL' |> Array.isEmpty then b |> nodeEntries |> Array.copyAndRemoveFirst
                                             else b |> nodeEntries |> Array.copyAndSet 0 (mkTreeNode (bShift - Literals.blockSizeShift) bL')
            merge aShift a' b'

let mergeVec a b =
    if b.root |> isEmpty then  // Check B for empty root *first*, as this is asymmetrical.
        let newTailItems = Array.append a.tail.items b.tail.items
        if Array.length newTailItems <= Literals.blockSize then
            { a with vecLen = a.vecLen + b.vecLen
                     tail = { items = newTailItems } } // root, tailOffset, and shift are all unchanged
        else
            let newLeaf, newTailItems = splitAtBlockSize newTailItems
            // TODO: Rewrite pushTailDown so that it takes a root and a new leaf, instead of a vector. Better API for what we need here.
            // That would allow us to avoid creating this temporary vector here just for the sake of calculating A's new root.
            let tmp = { a with tail = { items = newLeaf } }
            let newRoot, newShift = pushTailDown tmp
            { tail = { items = newTailItems }
              vecLen = a.vecLen + b.vecLen
              shift = newShift
              root = newRoot
              tailOffset = a.tailOffset + Literals.blockSize * 1<globalIdx> }
    elif a.vecLen = 0<globalIdx> then
        b
    // elif a.root |> isEmpty then
    //     let bTwig = getLeftmostTwig b.root
    //     let lTwig,rTwig = merge3WayWhereWeKnowThereIsRoom Literals.blockSizeShift [||] (mkLeaf a.tail.items) (nodeEntries bTwig)   // TODO: This API is kind of ridiculous here
    //     failwith "What goes here?" // TODO: ... or just combine this with the algorithm below, where we climb a chain of 1-array paths???
    else
        let aShift = a.shift
        let bShift = b.shift
        let aRoot, aShift, bRoot, tail =
            let aTwig = if isEmpty a.root then a.root else getRightmostTwig a.root
            let bTwig = if isEmpty b.root then b.root else  getLeftmostTwig b.root
            if isThereRoomToMergeTheTail aTwig bTwig (a.tail.items.Length * 1<nodeIdx>) then
                a.root, a.shift, b.root, Some (LeafNode a.tail)
            else
                // Push a's tail down, then merge the resulting tree
                // NOTE: Can't re-use pushTailDown, because it assumes that the tail is full, which won't necessarily be true here.
                // BUT we know that if we got here, Rtwig(A) was full, so we'd just be creating a new path to the root anyway.
                // ...MAYBE. But what if the *parent* of Rtwig(A) was NOT full? Then there'd be room for the new path in the parent. Hmm.
                // TODO: Yeah, I think the lines below will work. Check them, then remove the note above since it's no longer true.
                let aRootAfterPush, aShift = pushTailDown a // Old implementation of pushTailDown assumed that the tail is full, but we rewrote it, so this is now safe.
                aRootAfterPush, aShift, b.root, None
        let higherShift = max aShift bShift
        // printfn "aRoot = %A with shift %d and bRoot = %A with shift %d and tail <%A>" aRoot aShift bRoot bShift tail
        // TODO
        match mergeTree aShift aRoot bShift bRoot tail with
        | [||], [||] -> emptyVec
        | root, [||]
        | [||], root -> { root = mkTreeNode higherShift root
                          tail = b.tail
                          tailOffset = a.vecLen + b.tailOffset
                          shift = higherShift
                          vecLen = a.vecLen + b.vecLen }
        | rootL, rootR ->
            let rootL = mkTreeNode higherShift rootL
            let rootR = mkTreeNode higherShift rootR
            let newShift = (higherShift + Literals.blockSizeShift)
            let newRoot = mkTreeNode newShift [|rootL;rootR|]
            { root = newRoot
              tail = b.tail
              tailOffset = a.vecLen + b.tailOffset
              shift = newShift
              vecLen = a.vecLen + b.vecLen }

// TODO: Should this be called concat? Or append?
let concat a b =
    // Shortcut empty vectors right away. TODO: Not sure we need the "vecLen = 0" check, given the empty-roots check above.
    if a.vecLen = 0<globalIdx> then
        b
    elif b.vecLen = 0<globalIdx> then
        a
    else
        mergeVec a b |> shiftNodesIntoTailIfNeeded
    // TODO: XYZZY The pushLeafDown function has ONE scenario, covered in L'orange's thesis, that we need to check on.
    // If A had a FullNode at the end, and a close-to-full-but-not-quite-full tail so that it couldn't be merged into
    // the leftmost twig of B... *AND* B was small enough that it could fit into A... then there might end up being
    // a "rightmost twig breaks the invariant now, oops" situation. TOCHECK: Write a unit test for that scenario. Need
    // to create a carefully-crafted left tree, but the right tree can be any sort of random thing. So the unit test
    // is an FsCheck test that takes a single RRBVector<int> argument, which gets appended to the carefully-crafted
    // left tree. (NOTE: the "join that could break the \"last leaf is full if parent is full\" invariant" test has
    // been written to try to exercise that scenario, but I don't yet know if it's correct.)

// TODO: Can probably do this more efficiently with a bit of cleverness around appending leaves:
// chunk the revIter seq into arrays of Literals.blockSize, then append each one as a leaf.
// That avoids doing all the tail copies. However, a transient vector would be even better.
let rev vec = vec |> TreeIteration.revIterItems |> ofSeq

// INSERT ALGORITHM

/// Inserts a new item into the vector before index `idx`. So `vec |> insert 0 x` will prepend
/// the item `x` to the vector, and `vec |> insert (RRBVector.length vec) x` will be the equivalent
/// of `vec |> RRBVector.push x`.

// TODO: Pull this into a module to hide the "internal" helper functions
let internal lookAtNeighbors parentNode childIdx = // TODO: Decided to reject this option and go with the leftAndRight API below, which takes arrays instead of nodes
    // Returns tuple of left-neighbor, right-neighbor. Both are options
    let entries = nodeEntries parentNode
    match childIdx / 1<nodeIdx>, entries.Length with
    | _, len when len <= 1   -> None, None
    | 0, len                 -> None, Some (entries.[1])
    | c, len when c >= len-1 -> Some (entries.[c-1]), None
    | c, _                   -> Some (entries.[c-1]), Some (entries.[c+1])

let internal leftAndRight (arr: 'a[]) idx =
    if arr.Length <= 1 then
        None, None
    elif idx <= 0 then
        None, Some (arr.[idx+1])
    elif idx >= arr.Length-1 then
        Some (arr.[idx-1]), None
    else
        Some (arr.[idx-1]), Some (arr.[idx+1])
// Equivalent logic; which is easier to read?
let internal leftAndRight' (arr: 'a[]) idx =
    match idx, arr.Length with
    | _, len when len <= 1   -> None, None
    | 0, len                 -> None, Some (arr.[1])
    | i, len when i >= len-1 -> Some (arr.[i-1]), None
    | i, _                   -> Some (arr.[i-1]), Some (arr.[i+1])

// let appendAndSplitInefficient splitIdx (left:'a[],right:'a[]) =
//     Array.append left right |> Array.splitAt splitIdx

type internal ShiftDir = Left | Right
let internal shiftItemsIfPossible shiftDir arr sibling =
    let sibSize = Array.length sibling
    if sibSize >= Literals.blockSize then
        None
    else
        let curSize = Array.length arr
        let newSize = (curSize + sibSize) >>> 1  // Half rounded down means that we'll shift at least 1 item to the sibling array
        let moveCount = (curSize - newSize)
        match shiftDir with
        | Left ->  Some (moveCount, (Array.append sibling arr |> Array.splitAt (sibSize + moveCount)))  // TODO: Implement an optimized version of this shift if it turns out to be useful
        | Right -> Some (moveCount, (Array.append arr sibling |> Array.splitAt newSize))  // TODO: Same

/// Returns a complex-ish tuple: (left, (current, split), right).
/// Left is (Some array) if the left neighbor was present *and* was changed, otherwise it is None.
/// Current is not an option, it's always an array. It will always be changed.
/// Split is (Some array) if shifting *failed* and the current node had to be split, otherwise it is None.
/// Right is (Some array) if the right neighbor was present *and* was changed, otherwise it is None.
/// Therefore, precisely *one* of Left,Split,Right will be Some. Wait, that sounds like a job for a DU.

type ShiftResult<'a> =
    | SimpleInsertion of newCurrent : 'a
    | ShiftedLeft of newLeft : 'a * newCurrent : 'a
    | ShiftedRight of newCurrent : 'a * newRight : 'a
    | SplitNode of newCurrent : 'a * newRight : 'a

let internal tryShiftAndInsert idx itemToInsert (leftOpt, arr, rightOpt) =
    let len = Array.length arr
#if DEBUG
    // TOCHECK: I'm pretty sure that idx is always going to be between 0 and nodeSize, but we should check that.
    if idx > len then
        failwithf "Assertion failed. idx should have been <= length, but it was %d and length was %d" idx len
#endif
    if len < Literals.blockSize then
        arr
        |> Array.copyAndInsertAt idx itemToInsert
        |> SimpleInsertion
    else
        match leftOpt, rightOpt with
        | (Some leftArr), _ when Array.length leftArr < Literals.blockSize ->
            let leftLen = Array.length leftArr
            let idx' = idx + Array.length leftArr
            Array.concatAndInsertAt idx' itemToInsert leftArr arr
            |> Array.splitAt ((leftLen + len + 2) >>> 1) // (x + 1) >>> 1 is equivalent to ceil (x / 2). Our new array length is (leftLen + len + 1), so by adding an extra 1 we ensure that the split will put any odd items on the left side.
            |> ShiftedLeft
        | _, (Some rightArr) when Array.length rightArr < Literals.blockSize ->
            let rightLen = Array.length rightArr
            Array.concatAndInsertAt idx itemToInsert arr rightArr
            |> Array.splitAt ((len + rightLen + 2) >>> 1)
            |> ShiftedRight
        | _ ->
            arr
            |> Array.copyAndInsertAt idx itemToInsert
            |> Array.splitAt ((len + 2) >>> 1)
            |> SplitNode

/// Helper function for insertAtShift, where there are two branches (for leaves and non-leaves) with almost-identical guts except for the type of the mkChildNode function.
let internal handleInsertionResult mkChildNode shift localIdx (nodeLeftSib, entries, nodeRightSib) = function
    | SimpleInsertion childItems' ->
        SimpleInsertion (entries |> Array.copyAndSet localIdx (mkChildNode childItems'))
    | ShiftedLeft (leftItems', childItems') ->
        let entries' = entries |> Array.copyAndSet localIdx (mkChildNode childItems')
        entries'.[localIdx - 1] <- mkChildNode leftItems'
        SimpleInsertion entries'
    | ShiftedRight (childItems', rightItems') ->
        let entries' = entries |> Array.copyAndSet localIdx (mkChildNode childItems')
        entries'.[localIdx + 1] <- mkChildNode rightItems'
        SimpleInsertion entries'
    | SplitNode (childItems', newSiblingItems) ->
        let child' = mkChildNode childItems'
        let newSibling = mkChildNode newSiblingItems
        let overstuffedEntries = entries |> Array.copyAndInsertAt (localIdx + 1) newSibling
        overstuffedEntries.[localIdx] <- child'
        // TODO: Might be able to be clever with twigSlotCount if we know we're at the twig level
        if doWeNeedToRebalance1 overstuffedEntries then
            SimpleInsertion (rebalance shift overstuffedEntries)
        else
            let entries' = entries |> Array.copyAndSet localIdx (mkChildNode childItems')
            let nodeLeft  = Option.map nodeEntries nodeLeftSib
            let nodeRight = Option.map nodeEntries nodeRightSib
            tryShiftAndInsert (localIdx + 1) newSibling (nodeLeft, entries', nodeRight)

let insert idx item vec =

    let rec insertAtShift shift thisLvlIdx item (nodeLeftSib, node, nodeRightSib) =
        let localIdx, child, nextLvlIdx = appropriateIndexSearch thisLvlIdx shift node
        let localIdx = (localIdx / 1<nodeIdx>)
        let entries = (nodeEntries node)
        let childLeftSib, childRightSib = leftAndRight entries localIdx

        if shift <= Literals.blockSizeShift then
            let left  = Option.map leafItems childLeftSib
            let right = Option.map leafItems childRightSib
            // Since child is a leaf node, the nextLvlIdx *is* a nodeIdx, so the conversion in the next line is correct.
            tryShiftAndInsert (nextLvlIdx / 1<treeIdx>) item (left, leafItems child, right)
            |> handleInsertionResult mkLeaf shift localIdx (nodeLeftSib, entries, nodeRightSib)
        else
            let lowerShift = shift - Literals.blockSizeShift
            insertAtShift lowerShift nextLvlIdx item (childLeftSib, child, childRightSib)
            |> handleInsertionResult (mkTreeNode lowerShift) shift localIdx (nodeLeftSib, entries, nodeRightSib)

    // Insert function proper starts here
    let idx = if idx < 0 then idx * 1<globalIdx> + vec.vecLen else idx * 1<globalIdx>
    if idx > vec.vecLen then
        invalidArg "idx" "Tried to insert past the end of the vector"
    elif idx = vec.vecLen then
        push item vec
    elif idx >= vec.tailOffset then
        insertIntoTail ((idx - vec.tailOffset) / 1<globalIdx>) item vec
    else
        match insertAtShift vec.shift (idx / 1<globalIdx> * 1<treeIdx>) item (None, vec.root, None) with
        | SimpleInsertion newRootItems ->
            { root = mkTreeNode vec.shift newRootItems
              shift = vec.shift
              tail = vec.tail
              tailOffset = vec.tailOffset + 1<globalIdx>
              vecLen = vec.vecLen + 1<globalIdx> } |> shiftNodesIntoTailIfNeeded
        | ShiftedLeft (l,r)
        | ShiftedRight (l,r)
        | SplitNode (l,r) ->
            let a = mkTreeNode vec.shift l
            let b = mkTreeNode vec.shift r
            let newShift = (vec.shift + Literals.blockSizeShift)
            let newRoot = mkTreeNode newShift [|a;b|]
            { root = newRoot
              shift = newShift
              tail = vec.tail
              tailOffset = vec.tailOffset + 1<globalIdx>
              vecLen = vec.vecLen + 1<globalIdx> } |> shiftNodesIntoTailIfNeeded


// DELETION / REMOVAL

let handleRemovalResult mkChildNode shift childIdx childNode thisNode result =
    let resultLen = Array.length result
    if resultLen <= 0 then
        // Child vanished
        Array.copyAndRemoveAt (childIdx / 1<nodeIdx>) (nodeEntries thisNode)
    elif resultLen < nodeSize childNode / 1<nodeIdx> then
        // Child shrank: check if rebalance needed
        let slotCount' = slotCount (nodeEntries thisNode) / 1<nodeIdx> - 1
        if doWeNeedToRebalance slotCount' (nodeSize thisNode / 1<nodeIdx>) then
            Array.copyAndSet (childIdx / 1<nodeIdx>) (mkChildNode result) (nodeEntries thisNode) |> rebalance shift
        else
            Array.copyAndSet (childIdx / 1<nodeIdx>) (mkChildNode result) (nodeEntries thisNode)
    else
        // Child did not shrink
        Array.copyAndSet (childIdx / 1<nodeIdx>) (mkChildNode result) (nodeEntries thisNode)
let remove idx vec =
    let rec inner shift thisLvlIdx thisNode =
        let childIdx, childNode, nextLvlIdx = appropriateIndexSearch thisLvlIdx shift thisNode
        if shift <= Literals.blockSizeShift then
            Array.copyAndRemoveAt (nextLvlIdx / 1<treeIdx>) (leafItems childNode)
            |> handleRemovalResult mkLeaf shift childIdx childNode thisNode
        else
            let lowerShift = (shift - Literals.blockSizeShift)
            inner lowerShift nextLvlIdx childNode
            |> handleRemovalResult (mkTreeNode lowerShift) shift childIdx childNode thisNode
    if (idx >= vec.tailOffset / 1<globalIdx>) then
        let tailIdx = idx - vec.tailOffset / 1<globalIdx>
        removeFromTailAtTailIdx (tailIdx) vec |> shiftNodesIntoTailIfNeeded
        // TODO: Handle the pop-from-near-leaf case (though that one may be covered by mkTreeNode - test that.)
    else
        let newRootEntries = inner vec.shift (idx * 1<treeIdx>) vec.root
        let newRoot, newShift =
            if Array.length newRootEntries <= 1 && vec.shift > Literals.blockSizeShift then
                newRootEntries.[0], vec.shift - Literals.blockSizeShift
            else
                mkTreeNode vec.shift newRootEntries, vec.shift
        { vec with root = newRoot
                   shift = newShift
                   vecLen = vec.vecLen - 1<globalIdx>
                   tailOffset = vec.tailOffset - 1<globalIdx> } |> shiftNodesIntoTailIfNeeded
