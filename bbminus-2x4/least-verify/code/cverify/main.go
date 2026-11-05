// Reads "machine C s p d" lines on stdin (ledger parameters). For each: run to step s, snapshot, run p
// more steps, then require the Lin recurrence criterion. Also runs 5 more periods past that and requires
// no undefined transition and the same head displacement per period.
package main

import (
	"bufio"
	"fmt"
	"os"
	"strconv"
	"strings"
)

const undef = 255

func main() {
	left := []int{1, 1, 0}
	right := []int{0, 1, 1}
	head := 1
	const R = 1 << 20
	tape := make([]uint8, 2*R)
	in := bufio.NewScanner(os.Stdin)
	var n, bad, zero, nonzero int64
	for in.Scan() {
		f := strings.Fields(in.Text())
		name := strings.ReplaceAll(f[0], "_", "")
		var w, d, nx [8]int
		for i := 0; i < 8; i++ {
			c := name[3*i : 3*i+3]
			if c == "---" {
				w[i] = undef
				continue
			}
			w[i] = int(c[0] - '0')
			d[i] = -1
			if c[1] == 'R' {
				d[i] = 1
			}
			nx[i] = int(c[2] - 'A')
		}
		s, _ := strconv.Atoi(f[2])
		p, _ := strconv.Atoi(f[3])
		off, _ := strconv.Atoi(f[4])
		maxt := s + 6*p + 8
		clear(tape[R-maxt-8 : R+maxt+8])
		for i, c := range left {
			tape[R-len(left)+i] = uint8(c)
		}
		tape[R] = uint8(head)
		for i, c := range right {
			tape[R+1+i] = uint8(c)
		}
		h, q := R, 0
		fail := ""
		stepOne := func() bool {
			i := q*4 + int(tape[h])
			if w[i] == undef {
				return false
			}
			tape[h] = uint8(w[i])
			h += d[i]
			q = nx[i]
			return true
		}
		for t := 0; t < s; t++ {
			if !stepOne() {
				fail = "halted before start"
				break
			}
		}
		if fail == "" {
			h0, q0 := h, q
			var snap []uint8
			lo0 := R - s - 8
			hi0 := R + s + 8
			snap = append(snap, tape[lo0:hi0+1]...)
			smin, smax := lo0, hi0
			for smin <= hi0 && snap[smin-lo0] == 0 {
				smin++
			}
			for smax >= lo0 && snap[smax-lo0] == 0 {
				smax--
			}
			lo, hi := h, h
			for t := 0; t < p; t++ {
				if h < lo {
					lo = h
				}
				if h > hi {
					hi = h
				}
				if !stepOne() {
					fail = "halted in period"
					break
				}
			}
			if fail == "" {
				if q != q0 {
					fail = "state differs"
				}
				if h-h0 != off {
					fail = "offset differs"
				}
				get := func(x int) uint8 {
					if x < lo0 || x > hi0 {
						return 0
					}
					return snap[x-lo0]
				}
				for x := lo; x <= hi && fail == ""; x++ {
					if tape[x+off] != get(x) {
						fail = "window differs"
					}
				}
				if off > 0 && smin <= smax && smax > hi {
					fail = "nonblank ahead"
				}
				if off < 0 && smin <= smax && smin < lo {
					fail = "nonblank ahead"
				}
				// five more periods by plain running
				for k := 0; k < 5 && fail == ""; k++ {
					hk := h
					for t := 0; t < p; t++ {
						if !stepOne() {
							fail = "halted later"
							break
						}
					}
					if fail == "" && (h-hk != off || q != q0) {
						fail = "later period differs"
					}
				}
			}
		}
		n++
		if off == 0 {
			zero++
		} else {
			nonzero++
		}
		if fail != "" {
			bad++
			fmt.Println("BAD", in.Text(), fail)
		}
		if n%2000000 == 0 {
			fmt.Fprintln(os.Stderr, n, bad)
		}
	}
	fmt.Println("checked", n, "bad", bad, "offset0", zero, "translated", nonzero)
}
