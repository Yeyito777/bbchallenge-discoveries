// Plain long simulation with a growing tape. Lines of machine names on stdin; -steps per machine.
package main

import (
	"bufio"
	"flag"
	"fmt"
	"os"
	"strings"
)

func main() {
	steps := flag.Int64("steps", 10000000000, "")
	flag.Parse()
	in := bufio.NewScanner(os.Stdin)
	for in.Scan() {
		name := strings.Fields(in.Text())[0]
		s := strings.ReplaceAll(name, "_", "")
		var tbl [8]int32
		for i := 0; i < 8; i++ {
			c := s[3*i : 3*i+3]
			if c == "---" {
				tbl[i] = -1
				continue
			}
			d := int32(0)
			if c[1] == 'R' {
				d = 1
			}
			tbl[i] = int32(c[0]-'0') | d<<2 | int32(c[2]-'A')<<3
		}
		tape := make([]uint8, 1<<16)
		c0 := len(tape) / 2
		copy(tape[c0-3:], []uint8{1, 1, 0, 1, 0, 1, 1})
		h := c0
		st := int32(0)
		var n int64
		halted := false
		for n < *steps {
			// run until near an edge
			margin := h
			if len(tape)-1-h < margin {
				margin = len(tape) - 1 - h
			}
			lim := int64(margin - 1)
			if *steps-n < lim {
				lim = *steps - n
			}
			var k int64
			for k = 0; k < lim; k++ {
				e := tbl[st*4+int32(tape[h])]
				if e < 0 {
					halted = true
					break
				}
				tape[h] = uint8(e & 3)
				h += int(e>>2&1)*2 - 1
				st = e >> 3
			}
			n += k
			if halted {
				break
			}
			if margin < 16 {
				nt := make([]uint8, len(tape)*2)
				copy(nt[len(tape)/2:], tape)
				h += len(tape) / 2
				tape = nt
			}
		}
		if halted {
			fmt.Printf("%s HALT %d\n", name, n+1)
		} else {
			lo, hi := 0, len(tape)-1
			for lo < hi && tape[lo] == 0 {
				lo++
			}
			for hi > lo && tape[hi] == 0 {
				hi--
			}
			fmt.Printf("%s no-halt-through %d span %d\n", name, n, hi-lo+1)
		}
	}
}
