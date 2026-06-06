// Package example is a tiny hand-written Go package used to demo goose
// translation (Go -> Rocq) in this Perennial project.
package example

// MaxRetries is a plain constant; goose turns it into a Rocq definition.
const MaxRetries uint64 = 3

// Add returns the sum of two machine integers.
func Add(a uint64, b uint64) uint64 {
	return a + b
}

// Counter is a small mutable struct with a pointer method.
type Counter struct {
	n uint64
}

// Inc bumps the counter by one.
func (c *Counter) Inc() {
	c.n = c.n + 1
}

// Get reads the current value.
func (c *Counter) Get() uint64 {
	return c.n
}

// SumTo computes 0 + 1 + ... + (n-1) using goose's canonical `for cond {}` loop.
func SumTo(n uint64) uint64 {
	var total uint64 = 0
	var i uint64 = 0
	for i < n {
		total = total + i
		i = i + 1
	}
	return total
}

// StoreLoad makes a fresh map, stores v at key k, and reads it back.
// It should always return v — a roundtrip through Go's built-in map, which
// goose models as a Rocq `gmap`.
func StoreLoad(k uint64, v uint64) uint64 {
	m := make(map[uint64]uint64)
	m[k] = v
	return m[k]
}
