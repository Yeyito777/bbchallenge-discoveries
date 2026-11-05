#!/bin/bash
# prove.sh TAPE THRESHOLD DIR: full ledger for a tape: tree, Lin recurrence, CPS, RepWL at growing caps.
# Writes DIR/ledger.txt (records for check) and DIR/holdouts.txt (partial machines still open at the last cap).
T="$1"; TH="$2"; D="$3"; B=${LEASTBIN:-$HOME/least}; mkdir -p "$D"; cd "$D" || exit 1
export ABORT_AT=$TH
GRID1="1,0,0,0 2,0,0,0 3,0,0,0 4,0,0,0 5,0,0,0 6,0,0,0 2,1,1,0 3,1,1,0 2,1,2,0 3,1,2,0 2,3,2,0 3,3,2,0 2,2,4,0 2,1,4,0 3,1,4,0 4,1,1,0 4,3,2,0 7,0,0,0 8,0,0,0"
GRID2="9,0,0,0,200000 10,0,0,0,200000 5,1,1,0,200000 6,1,1,0,200000 4,1,2,0,200000 5,1,2,0,200000 2,2,8,0,200000 3,3,6,0,200000 2,1,8,0,200000 3,1,6,0,200000"
for H in 3 4 5 6 8 10; do for n in 2 3 4 5; do GRID2="$GRID2 $n,1,$H,0,200000"; done; done
RW=""; for L in 1 2 3 4 5 6 7 8 9 10 12; do for T2 in 2 3 4; do for ((K=0;K<L;K++)); do RW="$RW $L,$T2,$K,0,100000,128"; done; done; done
: > ledger.txt; : > stages.log; roots=""
for cap in 3000 200000 $TH; do
  lin=1; [ "$cap" -gt 1000000 ] && lin=0
  if [ -n "$roots" ]; then "$B/tree" "$T" "$cap" led.txt $lin roots.txt > tree_$cap.out; else "$B/tree" "$T" "$cap" led.txt $lin > tree_$cap.out; fi
  rc=$?; if [ $rc = 3 ]; then echo "DEAD: $(grep ABORT tree_$cap.out)" | tee -a stages.log; exit 3; fi
  grep -E '^[HC] ' led.txt >> ledger.txt
  grep '^S ' led.txt | cut -d' ' -f2 > s.txt
  "$B/cps" "$T" "$GRID1 $GRID2" < s.txt > cps.txt 2>> cps.err
  grep '^D ' cps.txt | awk '{print "P",$2,$3,$4,$5,$6}' >> ledger.txt
  grep '^U ' cps.txt | cut -d' ' -f2 > u.txt
  "$B/repwl" "$T" "$RW" < u.txt > rw.txt 2>> rw.err
  grep '^D ' rw.txt | awk '{print "W",$2,$3,$4,$5,$6}' >> ledger.txt
  grep '^U ' rw.txt | cut -d' ' -f2 > roots.txt; roots=1
  echo "cap=$cap tree=[$(head -1 tree_$cap.out | sed 's/.*: //')] survivors=$(wc -l < s.txt) aftercps=$(wc -l < u.txt) afterrepwl=$(wc -l < roots.txt)" | tee -a stages.log
done
cp roots.txt holdouts.txt
grep -E '^ +[0-9]' tree_*.out | sed 's/.*out: *//' | sort -rn | head -12 > top.txt
