module FSharpx.Collections.Literals

// Original values
[<Literal>]
let internal blockSizeShift = 5 // TODO: what can we do in 64Bit case?

[<Literal>]
let internal blockSize = 32

[<Literal>]
let internal blockIndexMask = 0x01f

// Values during internal testing
// [<Literal>]
// let internal blockSizeShift = 3

// [<Literal>]
// let internal blockSize = 8

// [<Literal>]
// let internal blockIndexMask = 0x07
