module FSharpx.Collections.Experimental.Tests.RRBVectorTest

open System
open FSharpx.Collections.Experimental
open FSharpx.Collections.Experimental.RRBArrayExtensions
open FSharpx.Collections.Experimental.RRBVector
open NUnit.Framework
open FsUnit
open FsCheck
open FsCheck.NUnit

// Properties of an RRB Vector:
//
//  1. All leaves should be at the same height.
//  2. The number of items in the leaf node should equal the vector length
//  3. Unless the vector is empty, the tail should never be empty.
//  4. The root should always contain a "real" node, not a leaf. (This one might change in the OOP implementation; I'll think about it.)
//  5. The number of items in each node should be <= the branching factor (Literals.blockSize).
//  6. The number of items in the tail  should be <= the branching factor (Literals.blockSize).
//  7. The size table of any tree node should match the number of items its descendent leaves contain.
//  8. The size table of any tree node should have as many entries as its # of direct child nodes.
//  9. Except under certain conditions, the rightmost leaf node of the vector should always be a full node. (What are those conditions? Write them out explicitly, and make a bool param in the checking function).
// 10. The tail offset should equal (vector length - tail length) at all times, even when the vector is empty.
// 11. (Not a real property): If the vector shift is > Literals.blockSizeShift, then the root node's length should be at least 2.
//     Making this a property allows for FsCheck tests to "fail" on trees where this is not the case, and thus give me useful knowledge on how to construct "real" tall trees in practice.
// 12. Leaf nodes' arrays should all contain items of type 'T (where 'T is the vector's generic parameter, i.e. it is an RRBVector<'T>). No other nodes should contain items of type 'T.
// 13. Internal nodes should all contain items of type Node or RRBNode (once RRBNode is descended from Node). In the record implementation, that will be FullNode, TreeNode, or LeafNode.
// 14. Internal nodes that are at shift > Literals.blockSizeShift should never contain LeafNodes. (Remove this property in the OOP implementation since then, leaves will just be Node instances.)
// 15. If vector length <= Literals.blockSize, the root node should be empty.
// 16. If vector length >  Literals.blockSize, the root node should NOT be empty.
// 17. If vector length > (Literals.blockSize * 2), the root node should contain more than one node. (NOTE: This is a restatement of property #11, and may be violated in practice sometimes.)
//     If it is, then that will give me useful data on how to build "tall" trees from basic vector operations like split and join.
// 18. No TreeNode should contain a "full" size table. If the size table was full, it should have been turned into a FullNode.
// 19. All nodes in an RRBVector, except the rightmost spine of the tree, should contain between (m-e) and m children, where e is the allowable flex factor. (2 in a "standard" 32-sized vector).
//     NOTE that this property will be *broken* by my planned insert algorithm. So make it a pseudo-property like #11.
// 20. If any nodes contain `null`, the nulls will never have a non-null to the right of them. (All nodes are a series of non-null children, then they MIGHT have nulls to fill them out to blockSize).
// 21. If the root node is empty, the shift is blockSizeShift, not 0.
// 22. The shift of a vector should always be greater than 0.
//
// Properties that depend on behavior (if X, then doing Y will result in Z):
//  X. If a vector has a full tail, pushing one item into it will produce a vector with a tail of length 1.
//  X. If a vector has a tail of length 1, popping one item from it will produce a vector with a tail of length Literals.blockSize.
//
// TODO: Add any extra properties that I think of later.

module RRBProperties =
    let isLeaf = function LeafNode _ -> true | _ -> false
    let isTree node = function TreeNode _ -> true | _ -> false
    let isFull node = function FullNode _ -> true | _ -> false
    let isNode node = not (isLeaf node)
    let items = function LeafNode n -> n.items | _ -> [||]
    let children = function TreeNode n -> n.entries | FullNode n -> n.entries | _ -> [||]

    let rec itemCount node =
        if node |> isLeaf then
            items node |> Array.length
        else
            children node |> Array.sumBy itemCount

    // Properties start here

    // Note that when I check the shift, I use <= 0, because in unit testing, we really might run into
    // some deformed trees where the shift isn't a proper multiple of Literals.blockSizeShift. If we
    // run into one of those, I don't want to loop forever because we skipped from 1 to -1 and never hit 0.
    let ``All leaves should be at the same height`` vec =
        let rec check shift node =
            if shift <= 0 && node |> isLeaf then true
            else node |> children |> Array.forall (check (shift - Literals.blockSizeShift))
        check vec.shift vec.root

    let ``The total number of items in all leaf nodes combined, plus the tail, should equal the vector length`` vec =
        itemCount vec.root + Array.length vec.tail.items = int vec.vecLen

    let ``Unless the vector is empty, the tail should never be empty`` vec =
        (int vec.vecLen = 0) = (vec.tail.items.Length = 0)

    let ``The root should always contain a "real" node, not a leaf`` vec =
        vec.root |> isNode

    let ``The number of items in each node should be <= the branching factor (Literals.blockSize)`` vec =
        let rec check node =
            children node |> Array.length <= Literals.blockSize &&
            children node |> Array.forall check
        check vec.root

    let ``The number of items in the tail  should be <= the branching factor (Literals.blockSize)`` vec =
        vec.tail.items.Length <= Literals.blockSize

    let ``The size table of any tree node should match the number of items its descendent leaves contain`` vec =
        let rec check node =
            match node with
            | TreeNode n ->
                let expectedSizeTable = children node |> Array.map itemCount |> Array.scan (+) 0 |> Array.skip 1
                n.sizeTable |> Array.map int = expectedSizeTable
            | _ -> true
        check vec.root

    let ``The size table of any tree node should have as many entries as its # of direct child nodes`` vec =
        let rec check node =
            match node with
            | TreeNode n ->
                Array.length n.sizeTable = Array.length n.entries
            | _ -> true
        check vec.root

    let ``The rightmost leaf node of the vector should always be a full node`` vec =
        // Except under certain conditions, that is... and I want to find out when this property turns out to be false
        // Right now, we say that this should be true as long as size >= 2*BS. But in fact, I think we need this to be
        // ALWAYS true as long as there's anything at all in the root, which means taking this into account in the slice algorithm.
        // Therefore, I need to tweak this property and then fix the cases where it's false.
        // NOTE: We still allow this to be false for trees of size BS or less, because those should be tail-only trees.
        let rec check node =
            if node |> isLeaf then
                node |> items |> Array.length = Literals.blockSize
            else
                let c = children node
                Array.length c > 0 && c |> Array.last |> check
        int vec.vecLen <= Literals.blockSize || check vec.root

    let ``The tail offset should equal (vector length - tail length) at all times, even when the vector is empty`` vec =
        int vec.vecLen - vec.tail.items.Length = int vec.tailOffset

    let ``If the vector shift is > Literals.blockSizeShift, then the root node's length should be at least 2`` vec =
        // Except under certain conditions, that is... and I want to find out when this property turns out to be false
        vec.shift <= Literals.blockSizeShift || children vec.root |> Array.length >= 2

    let ``Leaf nodes' arrays should all contain items of type 'T, and no other nodes should contain items of type 'T`` (vec:RRBVector<'T>) =
        let isOfTypeT x = (box x :? 'T)
        let rec check node =
            if node |> isLeaf then
                node |> items |> Array.forall isOfTypeT
            else
                node |> children |> Array.forall (not << isOfTypeT) &&
                node |> children |> Array.forall check
        check vec.root

    let ``Internal nodes should all contain items of type Node or RRBNode`` vec =
        // In the record implementation, that will be FullNode or TreeNode, but not LeafNode.
        let rec check shift node =
            if shift <= 0 then true else  // This property doesn't check shift 0
            node |> isNode && node |> children |> Array.forall (check (shift - Literals.blockSizeShift))
        check vec.shift vec.root

    let ``Internal nodes that are at shift > Literals.blockSizeShift should never contain LeafNodes`` vec =
        // In the OOP implementation, this property is pretty much meaningless
        let rec check shift node =
            if shift <= Literals.blockSizeShift then true else
            node |> isNode && node |> children |> Array.forall (fun child -> child |> isNode && child |> check (shift - Literals.blockSizeShift))
        check vec.shift vec.root

    let ``If vector length <= Literals.blockSize, the root node should be empty`` vec =
        if int vec.vecLen <= Literals.blockSize then
            vec.root |> children |> Array.length = 0
        else
            true // If vecLen > Literals.blockSize, this property always passes

    let ``If vector length >  Literals.blockSize, the root node should not be empty`` vec =
        if int vec.vecLen > Literals.blockSize then
            vec.root |> children |> Array.length > 0
        else
            true // If vecLen <= Literals.blockSize, this property always passes

    let ``If vector length >  Literals.blockSize, the tree should not contain any empty nodes`` vec =
        let rec check node =
            not (node |> isEmpty) && node |> children |> Array.forall check
        if int vec.vecLen > Literals.blockSize then
            check vec.root
        else
            true // If vecLen <= Literals.blockSize, this property always passes

    let ``If vector length > (Literals.blockSize * 2), the root node should contain more than one node`` vec =
        // NOTE: This is a restatement of property #11, and may be violated in practice sometimes.
        // If it is, then that will give me useful data on how to build "tall" trees from basic vector operations like split and join.
        if int vec.vecLen > Literals.blockSize * 2 then
            vec.root |> children |> Array.length > 1
        else
            true // If vecLen <= Literals.blockSize * 2, this property always passes

    let ``No TreeNode should contain a "full" size table. If the size table was full, it should have been turned into a FullNode.`` vec =
        true // Disabled for now until I figure out how to describe a "full" size table more accurately.

    let ``All nodes in an RRBVector, except the rightmost spine of the tree, should contain between (m-e) and m children, where e is the allowable flex factor`` vec =
        true // Not yet implemented. NOTE: This is a pseudo-property like the one about "If the vector shift is > Literals.blockSizeShift, then the root node's length should be at least 2",
             //                      because it can fail under certain conditions. When that happens, I want to know about it so I can improve efficiency -- but the code is NOT buggy, per se.

    let ``If any nodes contain `null`, the nulls will never have a non-null to the right of them`` vec =
        true // Not yet meaningful until we switch to the OOP implementation

    let ``If the root node is empty, the shift is blockSizeShift, not 0`` vec =
        if (vec.root |> isEmpty) then
            (vec.shift = Literals.blockSizeShift)
        else
            true

    let ``The shift of a vector should always be greater than 0`` vec =
        vec.shift > 0

    let properties = [
        "All leaves should be at the same height",``All leaves should be at the same height``
        "The total number of items in all leaf nodes combined, plus the tail, should equal the vector length",``The total number of items in all leaf nodes combined, plus the tail, should equal the vector length``
        "Unless the vector is empty, the tail should never be empty",``Unless the vector is empty, the tail should never be empty``
        "The root should always contain a \"real\" node, not a leaf",``The root should always contain a "real" node, not a leaf``
        "The number of items in each node should be <= the branching factor (Literals.blockSize)",``The number of items in each node should be <= the branching factor (Literals.blockSize)``
        "The number of items in the tail  should be <= the branching factor (Literals.blockSize)",``The number of items in the tail  should be <= the branching factor (Literals.blockSize)``
        "The size table of any tree node should match the number of items its descendent leaves contain",``The size table of any tree node should match the number of items its descendent leaves contain``
        "The size table of any tree node should have as many entries as its # of direct child nodes",``The size table of any tree node should have as many entries as its # of direct child nodes``
        "The rightmost leaf node of the vector should always be a full node",``The rightmost leaf node of the vector should always be a full node``  // TODO: Move to "sometimesProperties" list
        "The tail offset should equal (vector length - tail length) at all times, even when the vector is empty",``The tail offset should equal (vector length - tail length) at all times, even when the vector is empty``
        "If the vector shift is > Literals.blockSizeShift, then the root node's length should be at least 2",``If the vector shift is > Literals.blockSizeShift, then the root node's length should be at least 2``  // TODO: Move to "sometimesProperties" list
        "Leaf nodes' arrays should all contain items of type 'T, and no other nodes should contain items of type 'T",``Leaf nodes' arrays should all contain items of type 'T, and no other nodes should contain items of type 'T``
        "Internal nodes should all contain items of type Node or RRBNode",``Internal nodes should all contain items of type Node or RRBNode``
        "Internal nodes that are at shift > Literals.blockSizeShift should never contain LeafNodes",``Internal nodes that are at shift > Literals.blockSizeShift should never contain LeafNodes``  // Meaningless in the OOP implementation
        "If vector length <= Literals.blockSize, the root node should be empty",``If vector length <= Literals.blockSize, the root node should be empty``
        "If vector length >  Literals.blockSize, the root node should not be empty",``If vector length >  Literals.blockSize, the root node should not be empty``
        "If vector length >  Literals.blockSize, the tree should not contain any empty nodes",``If vector length >  Literals.blockSize, the tree should not contain any empty nodes``
        "If vector length > (Literals.blockSize * 2), the root node should contain more than one node",``If vector length > (Literals.blockSize * 2), the root node should contain more than one node``  // TODO: Move to "sometimesProperties" list
        "No TreeNode should contain a \"full\" size table. If the size table was full, it should have been turned into a FullNode.",``No TreeNode should contain a "full" size table. If the size table was full, it should have been turned into a FullNode.``
        "All nodes in an RRBVector, except the rightmost spine of the tree, should contain between (m-e) and m children, where e is the allowable flex factor",``All nodes in an RRBVector, except the rightmost spine of the tree, should contain between (m-e) and m children, where e is the allowable flex factor``
        "If the root node is empty, the shift is blockSizeShift, not 0",``If the root node is empty, the shift is blockSizeShift, not 0``
        "The shift of a vector should always be greater than 0",``The shift of a vector should always be greater than 0``
    ]

    type PropResult =
    | Success
    | Failure of string list

    let checkProperty name pred vec =
        if pred vec then Success else Failure [name]

    let combine r1 r2 =
        match r1 with
        | Success -> r2
        | Failure f1 ->
            match r2 with
            | Success -> Failure f1
            | Failure f2 -> Failure (f1 @ f2)

    let checkProperties vec =
        let result = properties |> List.map (fun (name,pred) -> checkProperty name pred vec) |> List.fold combine Success
        match result with
        | Success -> ()
        | Failure errors -> printfn "Vector %A failed the following RRBVector invariants:\n%A" vec errors
        result |> should equal Success

// For various tests, we'll want to generate a list and an index of an item within that list.
// Note that if the list is empty, the index will be 0, which is not a valid index of an
// empty list. So for some tests, we'll want to use arbNonEmptyArrayAndIdx instead.
type ArrayAndIdx = ArrayAndIdx of arr:int[] * idx:int

// TODO: Determine if we can use Arb.from<PositiveInt> here, or Gen.nonEmptyListOf, or something
let genArray = Gen.sized <| fun s -> gen {
    let! arr = Gen.arrayOfLength s (Gen.choose (1,100))
    let! idx = Gen.choose (0, max 0 (Array.length arr - 1))
    return ArrayAndIdx (arr,idx)
}
let genNonEmptyArray = Gen.sized <| fun s -> gen {
    let! arr = Gen.arrayOfLength (min s 1) (Gen.choose (1,100))
    let! idx = Gen.choose (0, max 0 (Array.length arr - 1))
    return ArrayAndIdx (arr,idx)
}
let rec shrink (ArrayAndIdx (arr:int[],idx:int)) = seq {
    if arr.Length = 0 then () else
    let rest = arr |> Array.skip 1
    let i = max 0 (max idx rest.Length - 1)
    yield ArrayAndIdx (rest,i)
    yield! shrink (ArrayAndIdx (rest,i))
}
let arbArrayAndIdx = Arb.fromGenShrink (genArray,shrink)
let arbNonEmptyArrayAndIdx = Arb.fromGenShrink (genNonEmptyArray,shrink)

[<Test>]
let ``Array.copyAndAppend works`` () =
    let check (ArrayAndIdx (arr:int[],_)) =
        let expected = Array.init (arr.Length + 1) (fun i -> if i = Array.length arr then 512 else arr.[i])
        arr |> Array.copyAndAppend 512 |> should equal expected
    Prop.forAll arbArrayAndIdx check |> Check.QuickThrowOnFailure

[<Test>]
let ``Array.copyAndSet works`` () =
    let check (ArrayAndIdx (arr:int[],idx:int)) =
        if arr = [||] then () else
        let expected = Array.copy arr
        expected.[idx] <- 512
        arr |> Array.copyAndSet idx 512 |> should equal expected
    Prop.forAll arbNonEmptyArrayAndIdx check |> Check.QuickThrowOnFailure

[<Test>]
let ``Array.copyAndSetLast works`` () =
    let check (ArrayAndIdx (arr:int[],_)) =
        if arr = [||] then () else
        let expected = Array.copy arr
        expected.[Array.length arr - 1] <- 512
        arr |> Array.copyAndSetLast 512 |> should equal expected
    Prop.forAll arbNonEmptyArrayAndIdx check |> Check.QuickThrowOnFailure

[<Test>]
let ``Array.copyAndInsertAt works`` () =
    let check (ArrayAndIdx (arr:int[],idx:int)) =
        let expected = Array.append (Array.append (Array.take idx arr) [|512|]) (Array.skip idx arr)
        arr |> Array.copyAndInsertAt idx 512 |> should equal expected
    Prop.forAll arbArrayAndIdx check |> Check.QuickThrowOnFailure

[<Test>]
let ``Array.copyAndRemoveAt works`` () =
    let check (ArrayAndIdx (arr:int[],idx:int)) =
        if arr = [||] then () else
        let expected = Array.append (Array.take idx arr) (Array.skip (idx+1) arr)
        arr |> Array.copyAndRemoveAt idx |> should equal expected
    Prop.forAll arbArrayAndIdx check |> Check.QuickThrowOnFailure

[<Test>]
let ``Array.copyAndRemoveFirst works`` () =
    let check (ArrayAndIdx (arr:int[],_)) =
        if arr = [||] then () else
        let expected = Array.skip 1 arr
        arr |> Array.copyAndRemoveFirst |> should equal expected
    Prop.forAll arbArrayAndIdx check |> Check.QuickThrowOnFailure

[<Test>]
let ``Array.copyAndPop works`` () =
    let check (ArrayAndIdx (arr:int[],_)) =
        if arr = [||] then () else
        let expected = Array.take (Array.length arr - 1) arr
        arr |> Array.copyAndPop |> should equal expected
    Prop.forAll arbArrayAndIdx check |> Check.QuickThrowOnFailure

[<Test>]
let ``Array.splitAt works`` () =
    let check (ArrayAndIdx (arr:int[],idx:int)) =
        // if arr = [||] then () else
        let expected = (Array.take idx arr, Array.skip idx arr)
        let actual = Array.splitAt idx arr
        // actual |> should equal expected  // Doesn't work for some reason. Workaround is below.
        fst actual |> should equal (fst expected)
        snd actual |> should equal (snd expected)
    Prop.forAll arbArrayAndIdx check |> Check.QuickThrowOnFailure

let genTwoArrays = Gen.two genArray  // TODO: Since this makes us ignore idx two or three times later, let's try something else next time
let arbTwoArrays = Arb.fromGen genTwoArrays  // No shrink, but that won't matter much
let genThreeArrays = Gen.three genArray
let arbThreeArrays = Arb.fromGen genThreeArrays  // No shrink, but that won't matter much

[<Test>]
let ``Array.append3 works`` () =
    let check (ArrayAndIdx (l,_),ArrayAndIdx (c,_),ArrayAndIdx (e,_)) =
        let expected = Array.append (Array.append l c) e
        Array.append3 l c e |> should equal expected
    Prop.forAll arbThreeArrays check |> Check.QuickThrowOnFailure

[<Test>]
let ``Array.append3' works`` () =
    let check (ArrayAndIdx (l,c),ArrayAndIdx (e,_)) =  // TODO: HACK HACK HACK, but it gives us a c value that's an int. Good enough.
        let expected = Array.append (Array.append l [|c|]) e
        Array.append3' l c e |> should equal expected
    Prop.forAll arbTwoArrays check |> Check.QuickThrowOnFailure

[<Test>]
let ``Empty vector has 0 items`` () =
    let vec = emptyVec
    RRBProperties.checkProperties vec
    length vec |> should equal 0

// [<Test>]
// let ``Malformed vector should fail at least property checks`` () =
//     let badVec = { root = FullNode { entries = [||] }
//                    shift = 2
//                    tail = { items = [|3|] }
//                    tailOffset = 1<globalIdx>
//                    vecLen = 2<globalIdx> }
//     RRBProperties.checkProperties badVec

[<Test>]
let ``Appending 1 item to empty vector should produce vector of length 1`` () =
    let vec = emptyVec |> push 42
    RRBProperties.checkProperties vec
    length vec |> should equal 1

[<Test>]
let ``Appending 2 items should produce vector of length 2`` () =
    let vec = emptyVec |> push 4 |> push 2
    RRBProperties.checkProperties vec
    length vec |> should equal 2

[<Test>]
let ``Appending items should increase vector's length by 1`` () =
    // Don't actually need FsCheck for this particular test
    let runCount = 1156
    let unfolder (vec,n) =
        length vec |> should equal n
        let vec' = vec |> push n
        RRBProperties.checkProperties vec'
        if n >= runCount then None else Some (vec',(vec',n+1))
    let actualRunCount = Seq.unfold unfolder (emptyVec,0) |> Seq.length
    runCount |> should equal actualRunCount

[<Test>]
let ``Can create vector from list`` () =
    let vec = ofList [1;3;5;7;9;11;13;15;17]
    RRBProperties.checkProperties vec
    length vec |> should equal 9

[<Test>]
let ``Indexing into vectors works`` () =
    let property (list:int list) =
        let vec = ofList list
        let idxs = [0 .. List.length list - 1] |> List.map ((*) 1<globalIdx>)
        RRBProperties.checkProperties vec
        List.forall2 (fun item idx -> nth idx vec = item) list idxs
    Check.QuickThrowOnFailure property
    // NOTE: This found errors with vectors of length 25, 37, 57, and 69. NONE of those are tests I would have thought to write myself.
    // But once I looked at them, it was immediately clear that my code had built the wrong data structure for those cases.
    // Thanks to FsCheck, I found these four bugs *immediately* without spending a day or two in head-scratching!

let compareVecToList vec list =
    vec |> toList = list

let compareVecToArray vec arr =
    vec |> toArray = arr

[<Test>]
let ``Popping from vectors works`` () =
    let property (list:int list) =
        let vec = ofList list
        RRBProperties.checkProperties vec
        let folder expected (valid,acc) =
            RRBProperties.checkProperties acc
            let actual = peek acc
            let acc' = pop acc
            (valid && (expected = actual), acc')
        List.foldBack folder list (true,vec) |> fst
    Check.QuickThrowOnFailure property

[<Test>]
let ``Splitting trees produces two parts that add up to the original whole`` () =
    let test (ArrayAndIdx (arr,idx)) =
        let globalIdx = idx * 1<globalIdx>
        let vec = ofArray arr
        let arrL = arr |> Array.take idx
        let arrR = arr |> Array.skip idx
        let l,r = vec |> split globalIdx
        RRBProperties.checkProperties l
        RRBProperties.checkProperties r
        (length l = globalIdx |@ "Left length should = split index") .&.
        (length r = (length vec - length l) |@ "Length of split vectors should equal length of original vector") .&.
        (compareVecToArray l arrL) |@ "Left split list should equal left split vector" .&.
        (compareVecToArray r arrR) |@ "Right split list should equal right split vector" .&.
        (Array.append arrL arrR = toArray vec) |@ "Split lists joined back together should equal original vector"
    Prop.forAll arbArrayAndIdx test |> Check.QuickThrowOnFailure

[<Test>]
let ``Manual split test`` () =
    let test (vec,idx) =
        let globalIdx = idx * 1<globalIdx>
        let l,r = vec |> split globalIdx
        RRBProperties.checkProperties r
        let r' = r |> push 21 |> push 22 |> push 23 |> push 24
        RRBProperties.checkProperties r'
        RRBProperties.checkProperties l
    let vec = [0..20] |> ofList
    test (vec,4)
    let trickyVec =
      {
        root = TreeNode {entries = [|FullNode {entries = [|LeafNode {items = [| 1;  2;  3;  4|];};|]}
                                     FullNode {entries = [|LeafNode {items = [| 8;  9; 10; 11|];};|];}|];
                         sizeTable = [|4<treeIdx>; 8<treeIdx>|];};
        tail = {items = [|12|]}
        tailOffset = 8<globalIdx>
        vecLen = 9<globalIdx>
        shift = 4
      }
    RRBProperties.checkProperties trickyVec
    test (trickyVec,4)
    test (trickyVec,8)

[<Test>]
let ``Iterating over items from an index works`` () =
    let property (ArrayAndIdx (list,idx)) =
        if Array.isEmpty list then true else
        let globalIdx = idx * 1<globalIdx>
        let vec = ofArray list
        let items = TreeIteration.iterItemsFromIdx globalIdx vec
        (items |> Seq.toArray) = (list |> Array.skip idx)
    // Check the previously-failed test first
    Check.One({ Config.QuickThrowOnFailure with Replay = Some (FsCheck.Random.StdGen (882045033,296273890)) }, Prop.forAll arbArrayAndIdx property)
    // Uncomment below once the focused test has succeeded
    // Prop.forAll arbArrayAndIdx property |> Check.QuickThrowOnFailure

[<Test>]
let ``Iterating over items from a specific index works`` () =
    let array =
        [|54; 70; 1; 21; 22; 82; 7; 1; 22; 92; 73; 61; 83; 75; 77; 81; 20; 78; 63; 69;
          38; 72; 44; 50; 19; 53; 59; 31; 65; 34; 40; 12; 46; 15; 21; 93; 94; 63; 19;
          84; 38; 99; 68; 57; 56; 7; 45; 47; 8; 45; 70; 99; 90; 57; 96; 4; 9; 100; 10;
          20; 1; 40; 88; 87; 7; 48; 2; 49; 18; 90; 96; 60; 87; 39; 33; 9; 30; 21|]
    let idx = 70
    if Array.isEmpty array then () else
    let globalIdx = idx * 1<globalIdx>
    let vec = ofArray array
    let items = TreeIteration.iterItemsFromIdx globalIdx vec
    Assert.That(items |> Seq.toArray, Is.EquivalentTo(array |> Array.skip idx))

[<Test>]
let ``Iterating backwards over items from an index works`` () =
    let property (ArrayAndIdx (list,idx)) =
        if Array.isEmpty list then true else
        let globalIdx = idx * 1<globalIdx>
        let vec = ofArray list
        let items = TreeIteration.revIterItemsFromIdx globalIdx vec
        (items |> Seq.toArray) = (list |> Array.truncate (idx + 1) |> Array.rev)
    Prop.forAll arbArrayAndIdx property |> Check.QuickThrowOnFailure

[<Test>]
let ``Iterating over items up to an index works`` () =
    let property (ArrayAndIdx (list,idx)) =
        if Array.isEmpty list then true else
        let globalIdx = idx * 1<globalIdx>
        let vec = ofArray list
        let items = TreeIteration.iterItemsUpToIdx globalIdx vec
        (items |> Seq.toArray) = (list |> Array.truncate (idx+1))
    Prop.forAll arbArrayAndIdx property |> Check.QuickThrowOnFailure

[<Test>]
let ``Iterating backwards over items up to an index works`` () =
    let property (ArrayAndIdx (list,idx)) =
        if Array.isEmpty list then true else
        let globalIdx = idx * 1<globalIdx>
        let vec = ofArray list
        let items = TreeIteration.revIterItemsUpToIdx globalIdx vec
        (items |> Seq.toArray) = (list |> Array.skip (idx) |> Array.rev)
    Prop.forAll arbArrayAndIdx property |> Check.QuickThrowOnFailure
