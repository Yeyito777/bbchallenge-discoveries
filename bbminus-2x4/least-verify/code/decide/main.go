// Independent non-halting decider for machines started on a finite tape.
//
// Each tape side is abstracted by a deterministic automaton read from infinity towards the head.
// A push follows the automaton; a pop goes to every recorded predecessor. Fixpoint over configs
// (left state, control, head cell, right state) and recorded edges. If no reachable abstract config
// has an undefined transition, the machine never halts: every real config maps to a config in the set,
// by induction on the run, because each side's path through the automaton only uses recorded edges.
//
// The fixpoint is then re-checked from its final edge and config sets alone by check().
package main

import (
	"bufio"
	"flag"
	"fmt"
	"os"
	"strconv"
	"strings"
	"sync"
	"sync/atomic"
)

const undef = 255

type Mach struct{ w, d, n [8]uint8 }

func parseM(s string) (m Mach, err error) {
	s = strings.ReplaceAll(s, "_", "")
	if len(s) != 24 {
		return m, fmt.Errorf("bad machine %q", s)
	}
	for i := 0; i < 8; i++ {
		c := s[3*i : 3*i+3]
		if c == "---" {
			m.w[i] = undef
			continue
		}
		m.w[i] = c[0] - '0'
		if c[1] == 'R' {
			m.d[i] = 1
		}
		m.n[i] = c[2] - 'A'
	}
	return m, nil
}

func (m Mach) mirror() Mach {
	for i := range m.d {
		m.d[i] ^= 1
	}
	return m
}

// Family describes the automata.
type Family struct {
	Kind   string // "g": last n cells; "r": run list
	N      int    // g: n
	B      int    // r: block length
	K, M   int    // r: counts 1..K exact, above K modulo M
	D      int    // r: runs kept, 0 = all
	Grid   int    // r: -1 anchored at first nonblank; >=0 absolute grid with this offset
	Par    int    // bitmask of symbols whose count parity is tracked
	CellH  int    // cell history length: symbols previously held by the cell
	CellQ  int    // 1: tag cell with writing state, 2: tag with writing state and direction
	HeadH  int    // head history length (state,symbol) pairs carried in control
	Mirror bool
}

func (f Family) String() string {
	mir := 0
	if f.Mirror {
		mir = 1
	}
	return fmt.Sprintf("%s,%d,%d,%d,%d,%d,%d,%d,%d,%d,%d,%d", f.Kind, f.N, f.B, f.K, f.M, f.D, f.Grid, f.Par, f.CellH, f.CellQ, f.HeadH, mir)
}

func parseF(s string) Family {
	p := strings.Split(s, ",")
	a := func(i int) int { v, _ := strconv.Atoi(p[i]); return v }
	return Family{p[0], a(1), a(2), a(3), a(4), a(5), a(6), a(7), a(8), a(9), a(10), a(11) == 1}
}

type edge struct {
	sym uint8
	to  int32
}
type pred struct {
	prev int32
	sym  uint8
}
type lis struct {
	other int32
	ctl   int32
}
type Side struct {
	ids   map[string]int32
	keys  []string
	next  [][]edge
	preds [][]pred
	lis   [][]lis
}

func newSide() *Side { return &Side{ids: map[string]int32{}} }

func (s *Side) id(k string) int32 {
	if v, ok := s.ids[k]; ok {
		return v
	}
	v := int32(len(s.keys))
	s.ids[k] = v
	s.keys = append(s.keys, k)
	s.next = append(s.next, nil)
	s.preds = append(s.preds, nil)
	s.lis = append(s.lis, nil)
	return v
}

type Cfg struct{ l, r, q int32; e uint8 }

type Eng struct {
	m       Mach
	f       Family
	L, R    *Side
	ext     map[string]uint8
	extName []string
	ctlIDs  map[string]int32
	ctlName []string
	seen    map[Cfg]struct{}
	work    []Cfg
	budget  int
	over    bool
}

func (g *Eng) extOf(sym uint8, tag string) uint8 {
	k := string([]byte{sym}) + tag
	if v, ok := g.ext[k]; ok {
		return v
	}
	if len(g.extName) >= 250 {
		g.over = true
		return 0
	}
	v := uint8(len(g.extName))
	g.ext[k] = v
	g.extName = append(g.extName, k)
	return v
}

func (g *Eng) ctl(q uint8, hist string) int32 {
	k := string([]byte{q}) + hist
	if v, ok := g.ctlIDs[k]; ok {
		return v
	}
	v := int32(len(g.ctlName))
	g.ctlIDs[k] = v
	g.ctlName = append(g.ctlName, k)
	return v
}

// step is the automaton's transition function on state keys.
// Key layout: byte0 parity bits, byte1 grid phase, rest family payload.
func (g *Eng) step(key string, e uint8, right bool) string {
	f := &g.f
	par := key[0]
	sym := g.extName[e][0]
	if f.Par>>sym&1 == 1 {
		par ^= 1 << sym
	}
	if f.Kind == "g" {
		b := make([]byte, 0, len(key))
		b = append(b, par, key[1])
		b = append(b, key[3:]...)
		b = append(b, e)
		return string(b)
	}
	// run list payload: [partial len][partial...] then runs: each [count][block...] innermost last
	phase := int(key[1])
	plen := int(key[2])
	partial := key[3 : 3+plen]
	rest := key[3+plen:]
	if f.Grid < 0 && plen == 0 && len(rest) == 0 && sym == 0 && len(g.extName[e]) == 1 && par == 0 {
		return key // still in the blank tail of an anchored grid
	}
	np := make([]byte, 0, f.B)
	nphase := 0
	if f.Grid >= 0 {
		isBlank := sym == 0 && len(g.extName[e]) == 1
		if plen == 0 && len(rest) == 0 && par == 0 && isBlank {
			// blank tail of an absolute grid: one state per phase, cycling under blank
			return string([]byte{0, byte((phase + 1) % f.B), 0})
		}
		if plen == 0 && len(rest) == 0 {
			// leaving the tail: the block so far is blank cells
			for i := 0; i < phase; i++ {
				np = append(np, 0)
			}
		} else {
			np = append(np, partial...)
		}
		nphase = (phase + 1) % f.B
	} else {
		np = append(np, partial...)
	}
	np = append(np, e)
	if len(np) < f.B {
		b := []byte{par, byte(nphase), byte(len(np))}
		b = append(b, np...)
		b = append(b, rest...)
		return string(b)
	}
	// a block finished; entries in the run list are fixed width (B+1)
	w := f.B + 1
	blk := np
	r := []byte(rest)
	if len(r) >= w && string(r[len(r)-w+1:]) == string(blk) {
		c := int(r[len(r)-w])
		c++
		if c > f.K {
			c = f.K + (c-f.K-1)%f.M + 1
			if f.M == 1 {
				c = f.K
			}
		}
		r[len(r)-w] = byte(c)
	} else {
		r = append(r, 1)
		r = append(r, blk...)
		if f.D > 0 && len(r) > f.D*w {
			r = r[len(r)-f.D*w:]
		}
	}
	b := []byte{par, byte(nphase), 0}
	b = append(b, r...)
	return string(b)
}

func (g *Eng) addEdge(s *Side, from int32, e uint8, right bool) int32 {
	for _, x := range s.next[from] {
		if x.sym == e {
			return x.to
		}
	}
	to := s.id(g.step(s.keys[from], e, right))
	s.next[from] = append(s.next[from], edge{e, to})
	s.preds[to] = append(s.preds[to], pred{from, e})
	for _, li := range s.lis[to] {
		if right {
			g.add(Cfg{li.other, from, li.ctl, e})
		} else {
			g.add(Cfg{from, li.other, li.ctl, e})
		}
	}
	return to
}

func (g *Eng) add(c Cfg) {
	if _, ok := g.seen[c]; ok {
		return
	}
	g.seen[c] = struct{}{}
	g.work = append(g.work, c)
	if len(g.seen) > g.budget || len(g.L.keys)+len(g.R.keys) > g.budget {
		g.over = true
	}
}

func initKey(f Family, right bool, cellsFromHead int) string {
	if f.Kind == "g" {
		b := make([]byte, 3+f.N)
		return string(b)
	}
	return string([]byte{0, 0, 0})
}

type tapeT struct {
	left, right []uint8
	head        uint8
}

func parseTape(s string) tapeT {
	i := strings.IndexByte(s, '[')
	var t tapeT
	for _, c := range s[:i] {
		t.left = append(t.left, uint8(c-'0'))
	}
	t.head = s[i+1] - '0'
	for _, c := range s[i+3:] {
		t.right = append(t.right, uint8(c-'0'))
	}
	return t
}

// run does the fixpoint. Returns true if closed with no reachable undefined transition.
func run(m Mach, T tapeT, f Family, budget int) (*Eng, bool) {
	g := &Eng{m: m, f: f, L: newSide(), R: newSide(), ext: map[string]uint8{}, ctlIDs: map[string]int32{},
		seen: map[Cfg]struct{}{}, budget: budget}
	if f.Mirror {
		g.m = m.mirror()
		l := make([]uint8, 0)
		for i := len(T.right) - 1; i >= 0; i-- {
			l = append(l, T.right[i])
		}
		r := make([]uint8, 0)
		for i := len(T.left) - 1; i >= 0; i-- {
			r = append(r, T.left[i])
		}
		T = tapeT{l, r, T.head}
	}
	blank := g.extOf(0, "")
	var startL, startR int32
	if f.Kind == "r" && f.Grid >= 0 {
		// Absolute grid. Cell x lies at phase (x-Grid) mod B. The left automaton reads x upward,
		// so its phase after reading cell x-1 is (x-Grid) mod B. The right automaton reads x
		// downward, its phase after reading cell x+1 is (Grid-1-x) mod B.
		// Blank tails: one state per phase, cycling under blank.
		mk := func(p int) string { return string([]byte{0, byte(p), 0}) }
		for p := 0; p < f.B; p++ {
			g.L.id(mk(p))
			g.R.id(mk(p))
		}
		md := func(a int) int { return ((a % f.B) + f.B) % f.B }
		// head at x=0; left word's outermost nonblank at x=-len(left); start phase there
		startL = g.L.ids[mk(md(-len(T.left)-f.Grid))]
		startR = g.R.ids[mk(md(f.Grid-1-len(T.right)))]
		// tails: every blank state must lie on the blank cycle, so every one has a predecessor
		for p := 0; p < f.B; p++ {
			if g.addEdge(g.L, g.L.ids[mk(p)], blank, false) != g.L.ids[mk((p+1)%f.B)] ||
				g.addEdge(g.R, g.R.ids[mk(p)], blank, true) != g.R.ids[mk((p+1)%f.B)] {
				panic("blank tail is not a cycle")
			}
		}
	} else {
		startL = g.L.id(initKey(f, false, 0))
		startR = g.R.id(initKey(f, true, 0))
		if g.addEdge(g.L, startL, blank, false) != startL || g.addEdge(g.R, startR, blank, true) != startR {
			panic("blank state has no self loop")
		}
	}
	l, r := startL, startR
	for _, c := range T.left {
		l = g.addEdge(g.L, l, g.extOf(c, ""), false)
	}
	for i := len(T.right) - 1; i >= 0; i-- {
		r = g.addEdge(g.R, r, g.extOf(T.right[i], ""), true)
	}
	g.add(Cfg{l, r, g.ctl(0, ""), g.extOf(T.head, "")})
	for len(g.work) > 0 {
		if g.over {
			return g, false
		}
		c := g.work[len(g.work)-1]
		g.work = g.work[:len(g.work)-1]
		name := g.ctlName[c.q]
		q := name[0]
		en := g.extName[c.e]
		a := en[0]
		idx := int(q)*4 + int(a)
		if g.m.w[idx] == undef {
			return g, false
		}
		w, d, nq := g.m.w[idx], g.m.d[idx], g.m.n[idx]
		tag := ""
		if f.CellH > 0 {
			// new history: old symbol then old history, truncated
			old := []byte{a}
			old = append(old, en[1:]...)
			if len(old) > f.CellH {
				old = old[:f.CellH]
			}
			tag = string(old)
		}
		if f.CellQ == 1 {
			tag += string([]byte{q + 100})
		} else if f.CellQ == 2 {
			tag += string([]byte{q + 100 + 10*d})
		}
		ne := g.extOf(w, tag)
		hist := ""
		if f.HeadH > 0 {
			hh := append([]byte{q<<4 | a}, name[1:]...)
			if len(hh) > f.HeadH {
				hh = hh[:f.HeadH]
			}
			hist = string(hh)
		}
		nc := g.ctl(nq, hist)
		if d == 1 {
			nl := g.addEdge(g.L, c.l, ne, false)
			g.R.lis[c.r] = append(g.R.lis[c.r], lis{nl, nc})
			for _, p := range g.R.preds[c.r] {
				g.add(Cfg{nl, p.prev, nc, p.sym})
			}
		} else {
			nr := g.addEdge(g.R, c.r, ne, true)
			g.L.lis[c.l] = append(g.L.lis[c.l], lis{nr, nc})
			for _, p := range g.L.preds[c.l] {
				g.add(Cfg{p.prev, nr, nc, p.sym})
			}
		}
	}
	return g, !g.over
}

// check verifies the closure from the final sets alone.
func check(g *Eng, T tapeT) string {
	f := g.f
	if f.Mirror {
		l := make([]uint8, 0)
		for i := len(T.right) - 1; i >= 0; i-- {
			l = append(l, T.right[i])
		}
		r := make([]uint8, 0)
		for i := len(T.left) - 1; i >= 0; i-- {
			r = append(r, T.left[i])
		}
		T = tapeT{l, r, T.head}
	}
	nxt := func(s *Side, a int32, e uint8) int32 {
		for _, x := range s.next[a] {
			if x.sym == e {
				return x.to
			}
		}
		return -1
	}
	type pe struct {
		prev int32
		sym  uint8
	}
	predL := make([][]pe, len(g.L.keys))
	predR := make([][]pe, len(g.R.keys))
	for a := range g.L.next {
		for _, x := range g.L.next[a] {
			predL[x.to] = append(predL[x.to], pe{int32(a), x.sym})
		}
	}
	for a := range g.R.next {
		for _, x := range g.R.next[a] {
			predR[x.to] = append(predR[x.to], pe{int32(a), x.sym})
		}
	}
	for c := range g.seen {
		name := g.ctlName[c.q]
		en := g.extName[c.e]
		q, a := name[0], en[0]
		idx := int(q)*4 + int(a)
		if g.m.w[idx] == undef {
			return "halting config in set"
		}
		w, d, nq := g.m.w[idx], g.m.d[idx], g.m.n[idx]
		tag := ""
		if f.CellH > 0 {
			old := []byte{a}
			old = append(old, en[1:]...)
			if len(old) > f.CellH {
				old = old[:f.CellH]
			}
			tag = string(old)
		}
		if f.CellQ == 1 {
			tag += string([]byte{q + 100})
		} else if f.CellQ == 2 {
			tag += string([]byte{q + 100 + 10*d})
		}
		ne, ok := g.ext[string([]byte{w})+tag]
		if !ok {
			return "missing ext"
		}
		hist := ""
		if f.HeadH > 0 {
			hh := append([]byte{q<<4 | a}, name[1:]...)
			if len(hh) > f.HeadH {
				hh = hh[:f.HeadH]
			}
			hist = string(hh)
		}
		nc, ok := g.ctlIDs[string([]byte{nq})+hist]
		if !ok {
			return "missing ctl"
		}
		if d == 1 {
			nl := nxt(g.L, c.l, ne)
			if nl < 0 {
				return "missing L edge"
			}
			for _, x := range predR[c.r] {
				if _, ok := g.seen[Cfg{nl, x.prev, nc, x.sym}]; !ok {
					return "not closed R-move"
				}
			}
		} else {
			nr := nxt(g.R, c.r, ne)
			if nr < 0 {
				return "missing R edge"
			}
			for _, x := range predL[c.l] {
				if _, ok := g.seen[Cfg{x.prev, nr, nc, x.sym}]; !ok {
					return "not closed L-move"
				}
			}
		}
	}
	return ""
}

// dump writes the explicit certificate for the external checker.
// Cells and controls are written in terms of the plain tape symbol plus an opaque ext id.
func dump(w *bufio.Writer, name string, g *Eng) {
	mir := 0
	if g.f.Mirror {
		mir = 1
	}
	fmt.Fprintf(w, "CERT %s %s %d\n", name, g.f, mir)
	for i, n := range g.extName {
		fmt.Fprintf(w, "X %d %d %x\n", i, n[0], n[1:])
	}
	for i, n := range g.ctlName {
		fmt.Fprintf(w, "Q %d %d %x\n", i, n[0], n[1:])
	}
	for a := range g.L.next {
		for _, x := range g.L.next[a] {
			fmt.Fprintf(w, "EL %d %d %d\n", a, x.sym, x.to)
		}
	}
	for a := range g.R.next {
		for _, x := range g.R.next[a] {
			fmt.Fprintf(w, "ER %d %d %d\n", a, x.sym, x.to)
		}
	}
	for c := range g.seen {
		fmt.Fprintf(w, "C %d %d %d %d\n", c.l, c.q, c.e, c.r)
	}
	fmt.Fprintf(w, "END\n")
}

func main() {
	tapeS := flag.String("tape", "110[1]011", "")
	famS := flag.String("fams", "", "file with families, one per line: family budget")
	workers := flag.Int("workers", 2, "")
	dumpP := flag.String("dump", "", "explicit certificate output")
	dumpEvery := flag.Int("dump-every", 0, "dump every Nth decided machine (1 = all)")
	nocheck := flag.Bool("nocheck", false, "")
	flag.Parse()
	T := parseTape(*tapeS)
	type fb struct {
		f Family
		b int
	}
	var fams []fb
	ff, err := os.Open(*famS)
	if err != nil {
		panic(err)
	}
	sc := bufio.NewScanner(ff)
	for sc.Scan() {
		t := strings.Fields(sc.Text())
		if len(t) < 2 || t[0][0] == '#' {
			continue
		}
		b, _ := strconv.Atoi(t[1])
		fams = append(fams, fb{parseF(t[0]), b})
	}
	var names []string
	in := bufio.NewScanner(os.Stdin)
	in.Buffer(make([]byte, 1<<20), 1<<20)
	for in.Scan() {
		t := strings.Fields(in.Text())
		if len(t) > 0 {
			names = append(names, t[0])
		}
	}
	out := bufio.NewWriter(os.Stdout)
	defer out.Flush()
	var mu sync.Mutex
	var dw *bufio.Writer
	if *dumpP != "" {
		df, err := os.Create(*dumpP)
		if err != nil {
			panic(err)
		}
		defer df.Close()
		dw = bufio.NewWriterSize(df, 1<<20)
		defer dw.Flush()
	}
	var idx, ndec, ndone atomic.Int64
	var wg sync.WaitGroup
	for k := 0; k < *workers; k++ {
		wg.Add(1)
		go func() {
			defer wg.Done()
			for {
				i := int(idx.Add(1) - 1)
				if i >= len(names) {
					return
				}
				m, err := parseM(names[i])
				if err != nil {
					panic(err)
				}
				decided := false
				for fi, x := range fams {
					g, ok := run(m, T, x.f, x.b)
					if !ok {
						continue
					}
					msg := ""
					if !*nocheck {
						msg = check(g, T)
					}
					mu.Lock()
					if msg != "" {
						fmt.Fprintf(out, "%s CHECKFAIL %s %s\n", names[i], x.f, msg)
					} else {
						fmt.Fprintf(out, "%s D %d %s %d\n", names[i], fi, x.f, len(g.seen))
						d := ndec.Add(1)
						if dw != nil && *dumpEvery > 0 && d%int64(*dumpEvery) == 0 {
							dump(dw, names[i], g)
						}
					}
					mu.Unlock()
					decided = msg == ""
					break
				}
				if !decided {
					mu.Lock()
					fmt.Fprintf(out, "%s OPEN\n", names[i])
					mu.Unlock()
				}
				if d := ndone.Add(1); d%20000 == 0 {
					fmt.Fprintf(os.Stderr, "%d/%d decided %d\n", d, len(names), ndec.Load())
				}
			}
		}()
	}
	wg.Wait()
	fmt.Fprintf(os.Stderr, "total %d decided %d\n", len(names), ndec.Load())
}
