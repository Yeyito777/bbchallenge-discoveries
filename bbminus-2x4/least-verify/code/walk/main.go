// Independent tree walk for 2-state 4-symbol machines on a finite start tape.
// Written from the problem statement only. Classifies every node as
// H steps | C start period offset | U (no halt and no Lin recurrence seen).
//
// usage: walk -tape '110[1]011' -limit N -lincap N -out DIR -workers K [-nonorm]
package main

import (
	"bufio"
	"flag"
	"fmt"
	"os"
	"path/filepath"
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

var (
	nonorm   = flag.Bool("nonorm", false, "no symbol normalisation: all four writes at every node")
	nnodes   atomic.Int64
	transMax = 7
)

func children(m *Mach, q, a uint8, tapeMax uint8, fn func(*Mach)) {
	maxs := tapeMax
	ndef := 0
	for i := 0; i < 8; i++ {
		if m.w[i] != undef {
			ndef++
			if m.w[i] > maxs {
				maxs = m.w[i]
			}
		}
	}
	if ndef >= transMax {
		return // the eighth transition would remove the last halting entry
	}
	wmax := maxs + 1
	if wmax > 3 {
		wmax = 3
	}
	if *nonorm {
		wmax = 3
	}
	idx := int(q)*4 + int(a)
	for w := uint8(0); w <= wmax; w++ {
		for n := uint8(0); n < 2; n++ {
			for d := uint8(0); d < 2; d++ {
				c := *m
				c.w[idx], c.d[idx], c.n[idx] = w, d, n
				fn(&c)
			}
		}
	}
}

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

func emit(w *bufio.Writer, m *Mach, r Result) {
	switch r.kind {
	case 'H':
		fmt.Fprintf(w, "%s H %d\n", m.String(), r.steps)
	case 'C':
		fmt.Fprintf(w, "%s C %d %d %d\n", m.String(), r.s, r.p, r.off)
	default:
		fmt.Fprintf(w, "%s U %d\n", m.String(), r.steps)
	}
}

func main() {
	tapeS := flag.String("tape", "110[1]011", "")
	limit := flag.Int64("limit", 4000000, "")
	lincap := flag.Int64("lincap", 32768, "")
	outDir := flag.String("out", "", "")
	workers := flag.Int("workers", 2, "")
	front := flag.Int("frontier", 20000, "")
	flag.Parse()
	T := parseTape(*tapeS)
	tmax := tapeMaxOf(T)
	os.MkdirAll(*outDir, 0o755)

	// Frontier: expand breadth first with a fast classification (lincap, no long raw run),
	// recording nothing here; the frontier nodes and the expanded nodes are emitted to part files.
	sim0 := newSim(T, *limit)
	hdr, err := os.Create(filepath.Join(*outDir, "top.tmp"))
	if err != nil {
		panic(err)
	}
	hw := bufio.NewWriter(hdr)
	queue := []Mach{emptyMach()}
	for len(queue) > 0 && len(queue) < *front {
		var nq []Mach
		for i := range queue {
			m := &queue[i]
			r := sim0.classify(m, *limit, *lincap)
			emit(hw, m, r)
			if r.kind == 'H' {
				children(m, r.haltQ, r.haltA, tmax, func(c *Mach) { nq = append(nq, *c) })
			}
		}
		queue = nq
	}
	hw.Flush()
	hdr.Close()
	os.Rename(filepath.Join(*outDir, "top.tmp"), filepath.Join(*outDir, "top.txt"))
	fmt.Fprintf(os.Stderr, "frontier %d\n", len(queue))

	var wg sync.WaitGroup
	idx := atomic.Int64{}
	var ndone atomic.Int64
	for k := 0; k < *workers; k++ {
		wg.Add(1)
		go func() {
			defer wg.Done()
			sim := newSim(T, *limit)
			for {
				i := int(idx.Add(1) - 1)
				if i >= len(queue) {
					return
				}
				final := filepath.Join(*outDir, fmt.Sprintf("part_%06d.txt", i))
				if _, err := os.Stat(final); err == nil {
					ndone.Add(1)
					continue
				}
				f, err := os.Create(final + ".tmp")
				if err != nil {
					panic(err)
				}
				w := bufio.NewWriterSize(f, 1<<20)
				var rec func(m *Mach)
				rec = func(m *Mach) {
					r := sim.classify(m, *limit, *lincap)
					emit(w, m, r)
					nnodes.Add(1)
					if r.kind == 'H' {
						children(m, r.haltQ, r.haltA, tmax, func(c *Mach) { cc := *c; rec(&cc) })
					}
				}
				rec(&queue[i])
				w.Flush()
				f.Close()
				os.Rename(final+".tmp", final)
				d := ndone.Add(1)
				if d%200 == 0 {
					fmt.Fprintf(os.Stderr, "done %d/%d nodes(this run) %d\n", d, len(queue), nnodes.Load())
				}
			}
		}()
	}
	wg.Wait()
	fmt.Fprintf(os.Stderr, "finished nodes(this run) %d\n", nnodes.Load())
	os.WriteFile(filepath.Join(*outDir, "DONE"), []byte("ok\n"), 0o644)
}
