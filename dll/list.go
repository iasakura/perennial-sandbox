// Package dll is a doubly-linked list, kept in its own package so its generated
// struct names don't collide with the `example` package identifier.
package dll

// Node is one element of a doubly-linked list.
type Node struct {
	val  uint64
	next *Node
	prev *Node
}

// List is a doubly-linked list tracking head, tail, and size.
type List struct {
	head *Node
	tail *Node
	size uint64
}

// NewList returns an empty list.
func NewList() *List {
	return &List{head: nil, tail: nil, size: 0}
}

// PushBack appends v at the tail.
func (l *List) PushBack(v uint64) {
	n := &Node{val: v, next: nil, prev: l.tail}
	if l.tail == nil {
		l.head = n
	} else {
		l.tail.next = n
	}
	l.tail = n
	l.size = l.size + 1
}

// PushFront prepends v at the head.
func (l *List) PushFront(v uint64) {
	n := &Node{val: v, next: l.head, prev: nil}
	if l.head == nil {
		l.tail = n
	} else {
		l.head.prev = n
	}
	l.head = n
	l.size = l.size + 1
}

// Len returns the number of elements.
func (l *List) Len() uint64 {
	return l.size
}

func (n *Node) findLeastGreaterNode(v uint64) (*Node, *Node) {
	var p *Node
	cur := n
	for cur != nil && cur.val < v {
		p = cur
		cur = cur.next
	}
	return p, cur
}

// n must be not nil
func (n *Node) insertNodeBefore(node *Node) {
	p := n.prev
	n.prev = node;
	if p != nil {
		p.next = node;
	}
}

func (l *List) InsertSorted(v uint64) {
	l.size++
	if l.head == nil {
		l.head = &Node{val: v, next: nil, prev: nil}
		l.tail = l.head
		return
	}
	p, n := l.head.findLeastGreaterNode(v)
	newNode := &Node{val: v, next: n, prev: p}
	if n != nil {
		n.insertNodeBefore(newNode)
	}
	if p == l.tail {
		l.tail = newNode
	}
	if n == l.head {
		l.head = newNode
	}
}