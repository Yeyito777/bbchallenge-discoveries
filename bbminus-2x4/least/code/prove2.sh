#!/bin/bash
# prove2.sh TAPE THRESHOLD DIR: as prove.sh, plus run-language and heavy CPS on what remains; declares final holdouts in the ledger.
T="$1"; TH="$2"; D="$3"; B=${LEASTBIN:-$HOME/least}; mkdir -p "$D"; cd "$D" || exit 1
export ABORT_AT=$TH
GRID1="1,0,0,0 2,0,0,0 3,0,0,0 4,0,0,0 5,0,0,0 6,0,0,0 2,1,1,0 3,1,1,0 2,1,2,0 3,1,2,0 2,3,2,0 3,3,2,0 2,2,4,0 2,1,4,0 3,1,4,0 4,1,1,0 4,3,2,0 7,0,0,0 8,0,0,0"
RW=""; for L in 1 2 3 4 6 8 12; do for T2 in 2 3; do for ((K=0;K<L;K++)); do RW="$RW $L,$T2,$K,0,20000,64"; done; done; done
HEAVY="9,0,0,0,300000 10,0,0,0,300000 11,0,0,0,300000 12,0,0,0,300000"; for H in 1 2 3 4 5 6 8 10; do for n in 2 3 4 5 6; do HEAVY="$HEAVY $n,1,$H,0,300000"; done; done; for H in 2 3 4; do for n in 2 3 4; do HEAVY="$HEAVY $n,3,$H,0,300000 $n,2,$H,0,300000"; done; done
RL=""; for Bl in 1 2 3 4; do for ((o=0;o<Bl;o++)); do for K in 1 2 3 4; do for M in 1 2; do RL="$RL $K,$M,$Bl,$o,0,20000"; done; done; done; done
RL="$RL 4,3,4,0,0,20000"
for C in 8 4 2 1 12 9 10 5 6 3; do for K in 1 2 3; do for Bl in 1 2 4; do RL="$RL $K,1,$Bl,-1,$C,20000"; done; done; done
: > ledger.txt; : > stages.log; roots=""
step() { # filter s.txt through deciders; leaves undecided in roots.txt
  "$B/cps" "$T" "$GRID1" < s.txt > cps.txt 2>> cps.err
  grep '^D ' cps.txt | awk '{print "P",$2,$3,$4,$5,$6}' >> ledger.txt
  grep '^U ' cps.txt | cut -d' ' -f2 > u.txt
  "$B/repwl" "$T" "$RW" < u.txt > rw.txt 2>> rw.err
  grep '^D ' rw.txt | awk '{print "W",$2,$3,$4,$5,$6}' >> ledger.txt
  grep '^U ' rw.txt | cut -d' ' -f2 > roots.txt
}
for cap in 3000 200000 $TH; do
  lin=1; [ "$cap" -gt 1000000 ] && lin=0
  if [ -n "$roots" ]; then "$B/tree" "$T" "$cap" led.txt $lin roots.txt > tree_$cap.out; else "$B/tree" "$T" "$cap" led.txt $lin > tree_$cap.out; fi
  rc=$?; if [ $rc = 3 ]; then echo "DEAD: $(grep ABORT tree_$cap.out)" | tee -a stages.log; exit 3; fi
  grep -E '^[HC] ' led.txt >> ledger.txt
  grep '^S ' led.txt | cut -d' ' -f2 > s.txt
  step; roots=1
  echo "cap=$cap tree=[$(head -1 tree_$cap.out | sed 's/.*: //')] survivors=$(wc -l < s.txt) aftercps=$(wc -l < u.txt) afterrepwl=$(wc -l < roots.txt)" | tee -a stages.log
done
rm -f led.txt
"$B/runlang" "$T" "$RL" < roots.txt > rl.txt 2>> rl.err
grep '^D ' rl.txt | awk '{print "L",$2,$3,$4,$5,$6,$7}' >> ledger.txt
grep '^U ' rl.txt | cut -d' ' -f2 > a.txt
"$B/cps" "$T" "$HEAVY" < a.txt > cps2.txt 2>> cps2.err
grep '^D ' cps2.txt | awk '{print "P",$2,$3,$4,$5,$6}' >> ledger.txt
grep '^U ' cps2.txt | cut -d' ' -f2 > holdouts.txt
awk '{print "X",$1,"holdout"}' holdouts.txt >> ledger.txt
echo "runlang left=$(wc -l < a.txt) heavy cps left=$(wc -l < holdouts.txt)" | tee -a stages.log
grep -hE '^ +[0-9]' tree_*.out | sort -rn | head -12 > top.txt
