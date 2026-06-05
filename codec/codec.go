// Package codec shows encoding a small message (two uint64s) to a byte slice
// and decoding it back, the core of serializing RPC messages over the network.
// Uses tchajed/marshal, the same library Perennial's distributed proofs use.
package codec

import "github.com/tchajed/marshal"

// Pair is a tiny message: two 64-bit fields.
type Pair struct {
	A uint64
	B uint64
}

// Encode serializes p as A then B, little-endian, into a fresh byte slice.
func Encode(p Pair) []byte {
	var b []byte
	b = marshal.WriteInt(b, p.A)
	b = marshal.WriteInt(b, p.B)
	return b
}

// Decode parses a Pair back out of b (assuming b starts with the encoding).
func Decode(b []byte) Pair {
	a, b2 := marshal.ReadInt(b)
	c, _ := marshal.ReadInt(b2)
	return Pair{A: a, B: c}
}
