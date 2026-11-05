// Independent tree walk for 2-state 4-symbol machines on a finite start tape.
// Written from the problem statement only. Classifies every node as
// H steps | C start period offset | U (no halt and no Lin recurrence seen).
//
// usage: walk -tape '110[1]011' -limit N -lincap N -out DIR -workers K [-nonorm]
package main

import (
	"bufio"
	"flag"
	"sort"
	"fmt"
	"os"
	"strings"
	"sync"
	"sync/atomic"
)

const undef = 255

type Mach struct {
	w, d, n [8]uint8 // write, move(0=L,1=R), next; index state*4+symbol; w==undef => undefined
}

func emptyMach() Mach {
	var m Mach
	for i := range m.w {
		m.w[i] = undef
	}
	return m
}

func (m *Mach) String() string {
	var b strings.Builder
	for i := 0; i < 8; i++ {
		if i == 4 {
			b.WriteByte('_')
		}
		if m.w[i] == undef {
			b.WriteString("---")
		} else {
			b.WriteByte('0' + m.w[i])
			b.WriteByte("LR"[m.d[i]])
			b.WriteByte('A' + m.n[i])
		}
	}
	return b.String()
}

type Tape struct {
	left, right []uint8 // cells left of head (outermost first) and right of head (innermost first)
	head        uint8
}

func parseTape(s string) Tape {
	i := strings.IndexByte(s, '[')
	j := strings.IndexByte(s, ']')
	if i < 0 || j != i+2 {
		panic("bad tape")
	}
	var t Tape
	for _, c := range s[:i] {
		t.left = append(t.left, uint8(c-'0'))
	}
	t.head = s[i+1] - '0'
	for _, c := range s[j+1:] {
		t.right = append(t.right, uint8(c-'0'))
	}
	return t
}

type Sim struct {
	tape   []uint8
	center int
	snap   []uint8
	t      Tape
	dirty  int // cells within +-dirty of center may be non-zero
}

func newSim(t Tape, limit int64) *Sim {
	r := int(limit) + len(t.left) + len(t.right) + 64
	return &Sim{tape: make([]uint8, 2*r+1), center: r, t: t}
}

func (s *Sim) reset() {
	if s.dirty > 0 {
		lo, hi := s.center-s.dirty, s.center+s.dirty
		if lo < 0 {
			lo = 0
		}
		if hi >= len(s.tape) {
			hi = len(s.tape) - 1
		}
		clear(s.tape[lo : hi+1])
	}
	for i, c := range s.t.left {
		s.tape[s.center-len(s.t.left)+i] = c
	}
	s.tape[s.center] = s.t.head
	for i, c := range s.t.right {
		s.tape[s.center+1+i] = c
	}
	s.dirty = len(s.t.left) + len(s.t.right) + 2
}

type Result struct {
	kind        byte // H C U
	steps       int64
	s, p, off   int64
	haltQ, haltA uint8
}

// classify runs m. Lin recurrence is looked for by snapshotting at t0=0,1,2,4,..
// and comparing against the snapshot up to the next snapshot, while t<=lincap.
func (s *Sim) classify(m *Mach, limit, lincap int64) Result {
	s.reset()
	tp := s.tape
	h := s.center
	q := uint8(0)
	var t int64
	vmin, vmax := s.center-len(s.t.left), s.center+len(s.t.right)

	t0 := int64(0)
	next := int64(32)
	for t < lincap && t < limit {
		// snapshot at t0
		smin, smax := vmin, vmax
		for smin <= smax && tp[smin] == 0 {
			smin++
		}
		for smax >= smin && tp[smax] == 0 {
			smax--
		}
		// keep head cell representable
		n := 0
		if smin <= smax {
			n = smax - smin + 1
		}
		if cap(s.snap) < n {
			s.snap = make([]uint8, n*2)
		}
		snap := s.snap[:n]
		if n > 0 {
			copy(snap, tp[smin:smax+1])
		}
		h0 := h
		q0 := q
		a0 := tp[h]
		lo, hi := h, h
		for t < next && t < limit {
			a := tp[h]
			idx := int(q)*4 + int(a)
			if m.w[idx] == undef {
				s.dirty = max(s.dirty, max(s.center-vmin, vmax-s.center)+2)
				return Result{kind: 'H', steps: t + 1, haltQ: q, haltA: a}
			}
			if h < lo {
				lo = h
			}
			if h > hi {
				hi = h
			}
			tp[h] = m.w[idx]
			if m.d[idx] == 1 {
				h++
			} else {
				h--
			}
			q = m.n[idx]
			t++
			if h < vmin {
				vmin = h
			}
			if h > vmax {
				vmax = h
			}
			if q == q0 && tp[h] == a0 {
				d := h - h0
				ok := true
				if d > 0 && smax > hi && n > 0 {
					ok = false
				}
				if d < 0 && smin < lo && n > 0 {
					ok = false
				}
				if ok {
					for x := lo; x <= hi; x++ {
						var v uint8
						if x >= smin && x <= smax {
							v = snap[x-smin]
						}
						if tp[x+d] != v {
							ok = false
							break
						}
					}
				}
				if ok {
					s.dirty = max(s.dirty, max(s.center-vmin, vmax-s.center)+2)
					return Result{kind: 'C', s: t0, p: t - t0, off: int64(d)}
				}
			}
		}
		t0 = t
		next = t0 * 2
	}
	// raw phase
	tbl := [8]int32{}
	for i := 0; i < 8; i++ {
		if m.w[i] == undef {
			tbl[i] = -1
		} else {
			tbl[i] = int32(m.w[i]) | int32(m.d[i])<<2 | int32(m.n[i])<<3
		}
	}
	c := int32(q)
	rem := limit - t
	done := int64(0)
	hh := h
	for done < rem {
		a := int32(tp[hh])
		e := tbl[c*4+a]
		if e < 0 {
			break
		}
		tp[hh] = uint8(e & 3)
		hh += int(e>>2&1)*2 - 1
		c = e >> 3
		done++
	}
	t += done
	s.dirty = max(s.dirty, max(s.center-vmin, vmax-s.center)+int(done)+2)
	if done < rem {
		a := tp[hh]
		return Result{kind: 'H', steps: t + 1, haltQ: uint8(c), haltA: a}
	}
	return Result{kind: 'U', steps: t}
}


var nnodes atomic.Int64

func tapeMaxOf(t Tape) uint8 {
	x := t.head
	for _, c := range t.left {
		x = max(x, c)
	}
	for _, c := range t.right {
		x = max(x, c)
	}
	return x
}

// canon relabels symbols 2 and 3 if swap is set.
func canon(m *Mach, swap bool) Mach {
	if !swap {
		return *m
	}
	c := *m
	for st := 0; st < 2; st++ {
		c.w[st*4+2], c.w[st*4+3] = m.w[st*4+3], m.w[st*4+2]
		c.d[st*4+2], c.d[st*4+3] = m.d[st*4+3], m.d[st*4+2]
		c.n[st*4+2], c.n[st*4+3] = m.n[st*4+3], m.n[st*4+2]
	}
	for i := 0; i < 8; i++ {
		if c.w[i] == 2 {
			c.w[i] = 3
		} else if c.w[i] == 3 {
			c.w[i] = 2
		}
	}
	return c
}

// Full unnormalised tree on T*: every defined transition may write any of the four symbols.
// Each node's relabelled form must be a node of the normalised tree with the same class and step count;
// that comparison is done afterwards on the output.
func main() {
	tapeS := flag.String("tape", "110[1]011", "")
	limit := flag.Int64("limit", 2000000, "")
	shortLimit := flag.Int64("short", 100000, "limit for nodes whose canonical form is in the -u list")
	lincap := flag.Int64("lincap", 32768, "")
	uPath := flag.String("u", "", "canonical machines not halting at the full limit")
	outP := flag.String("o", "", "")
	workers := flag.Int("workers", 2, "")
	flag.Parse()
	T := parseTape(*tapeS)
	tmax := tapeMaxOf(T)
	if tmax != 1 {
		panic("this tool assumes free symbols 2 and 3")
	}
	uset := map[string]bool{}
	f, err := os.Open(*uPath)
	if err != nil {
		panic(err)
	}
	sc := bufio.NewScanner(f)
	for sc.Scan() {
		uset[strings.Fields(sc.Text())[0]] = true
	}
	f.Close()

	type item struct {
		m    Mach
		swap bool
		used bool // 2 or 3 written already
	}
	var run func(sim *Sim, it item, w *bufio.Writer)
	run = func(sim *Sim, it item, w *bufio.Writer) {
		c := canon(&it.m, it.swap)
		cs := c.String()
		lim := *limit
		if uset[cs] {
			lim = *shortLimit
		}
		r := sim.classify(&it.m, lim, *lincap)
		switch r.kind {
		case 'H':
			fmt.Fprintf(w, "%s H %d\n", cs, r.steps)
		case 'C':
			fmt.Fprintf(w, "%s C\n", cs)
		default:
			fmt.Fprintf(w, "%s U\n", cs)
		}
		nnodes.Add(1)
		if r.kind != 'H' {
			return
		}
		ndef := 0
		for i := 0; i < 8; i++ {
			if it.m.w[i] != undef {
				ndef++
			}
		}
		if ndef >= 7 {
			return
		}
		idx := int(r.haltQ)*4 + int(r.haltA)
		for wr := uint8(0); wr <= 3; wr++ {
			for n := uint8(0); n < 2; n++ {
				for d := uint8(0); d < 2; d++ {
					ch := item{it.m, it.swap, it.used}
					ch.m.w[idx], ch.m.d[idx], ch.m.n[idx] = wr, d, n
					if !it.used && wr >= 2 {
						ch.used = true
						ch.swap = wr == 3
					}
					run(sim, ch, w)
				}
			}
		}
	}
	// frontier
	sim0 := newSim(T, *limit)
	of, err := os.Create(*outP)
	if err != nil {
		panic(err)
	}
	ow := bufio.NewWriterSize(of, 1<<20)
	queue := []item{{m: emptyMach()}}
	for len(queue) < 200 {
		var nq []item
		for _, it := range queue {
			c := canon(&it.m, it.swap)
			r := sim0.classify(&it.m, *limit, *lincap)
			if r.kind == 'H' {
				fmt.Fprintf(ow, "%s H %d\n", c.String(), r.steps)
				idx := int(r.haltQ)*4 + int(r.haltA)
				for wr := uint8(0); wr <= 3; wr++ {
					for n := uint8(0); n < 2; n++ {
						for d := uint8(0); d < 2; d++ {
							ch := item{it.m, it.swap, it.used}
							ch.m.w[idx], ch.m.d[idx], ch.m.n[idx] = wr, d, n
							if !it.used && wr >= 2 {
								ch.used = true
								ch.swap = wr == 3
							}
							nq = append(nq, ch)
						}
					}
				}
			} else if r.kind == 'C' {
				fmt.Fprintf(ow, "%s C\n", c.String())
			} else {
				fmt.Fprintf(ow, "%s U\n", c.String())
			}
		}
		queue = nq
	}
	var mu sync.Mutex
	var idx atomic.Int64
	var wg sync.WaitGroup
	for k := 0; k < *workers; k++ {
		wg.Add(1)
		go func() {
			defer wg.Done()
			sim := newSim(T, *limit)
			var sb strings.Builder
			for {
				i := int(idx.Add(1) - 1)
				if i >= len(queue) {
					return
				}
				sb.Reset()
				bw := bufio.NewWriterSize(&sb, 1<<20)
				run(sim, queue[i], bw)
				bw.Flush()
				mu.Lock()
				ow.WriteString(sb.String())
				mu.Unlock()
				if i%100 == 0 {
					fmt.Fprintln(os.Stderr, i, len(queue), nnodes.Load())
				}
			}
		}()
	}
	wg.Wait()
	ow.Flush()
	of.Close()
	_ = sort.Strings
	fmt.Fprintln(os.Stderr, "finished", nnodes.Load())
}
