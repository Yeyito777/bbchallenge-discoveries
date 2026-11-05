#!/bin/bash
# evaluate.sh TAPE: quick verdict on a tape. Prints the summary line. Aborts as soon as a machine halts at or above the threshold.
T="$1"; B=${LEASTBIN:-$HOME/least}; ID=$(echo "$T" | tr '()[]' 'lrab'); D=$B/run/eval/$ID; mkdir -p "$D"; cd "$D" || exit 1
TH=3932964; export ABORT_AT=$TH LEDGER_S_ONLY=1
GRID1="1,0,0,0 2,0,0,0 3,0,0,0 4,0,0,0 5,0,0,0 6,0,0,0 2,1,1,0 3,1,1,0 2,1,2,0 3,1,2,0 2,3,2,0 3,3,2,0 2,2,4,0 2,1,4,0 3,1,4,0 4,1,1,0 4,3,2,0 7,0,0,0 8,0,0,0"
RW=""; for L in 1 2 3 4 6 8 12; do for T2 in 2 3 ; do for ((K=0;K<L;K++)); do RW="$RW $L,$T2,$K,0,20000,64"; done; done; done
log() { echo "$T $*" >> $B/run/eval/summary.txt; }
top=0
# Known long runners first: a seed that halts at or above the threshold ends the evaluation at once.
[ -f $B/seeds.txt ] && { cat $B/seeds.txt > cur_seeds.txt; grep -h -o "halter [0-9]* [^ ]*" $B/run/eval/summary.txt 2>/dev/null | cut -d' ' -f3 | sort -u >> cur_seeds.txt
  r=$(echo "$T" | $B/seedcheck $TH 20000000 cur_seeds.txt); case "$r" in *" DEAD "*) log "DEAD ABORT seed halter $(echo "$r" | cut -d' ' -f3,4) at cap=2e7"; exit 0;; esac; }
stage() { # stage CAP LIN ROOTS(optional)
  local cap=$1 lin=$2 roots=$3
  if [ -n "$roots" ]; then $B/tree "$T" $cap s.txt $lin $roots > t.out; else $B/tree "$T" $cap s.txt $lin > t.out; fi
  rc=$?; if [ $rc = 3 ]; then log "DEAD $(grep ABORT t.out) at cap=$cap"; rm -f s.txt r.txt r2.txt u.txt v.txt s0.txt; exit 0; fi
  [ $rc != 0 ] && { log "ERROR rc=$rc"; exit 1; }
  t=$(grep -E '^ +[0-9]' t.out | sort -rn | head -1 | awk '{print $1}'); [ -n "$t" ] && [ "$t" -gt "$top" ] && top=$t
  head -1 t.out >> tree.log
  cut -d' ' -f2 s.txt > s0.txt
  $B/cps "$T" "$GRID1" < s0.txt > r.txt 2>> cps.log; grep '^U' r.txt | cut -d' ' -f2 > u.txt
  $B/repwl "$T" "$RW" < u.txt > r2.txt 2>> rw.log; grep '^U' r2.txt | cut -d' ' -f2 > v.txt
  echo "stage cap=$cap in=$(wc -l < s0.txt) aftercps=$(wc -l < u.txt) afterrw=$(wc -l < v.txt) top=$top" >> stages.log
  cp v.txt roots.txt
}
stage 3000 1
stage 1000000 1 roots.txt
stage 100000000 0 roots.txt
n=$(wc -l < roots.txt)
[ "$n" != 0 ] && { $B/tree "$T" 1000000000 s.txt 0 roots.txt > t.out; [ $? = 3 ] && { log "DEAD $(grep ABORT t.out) at cap=1e9"; rm -f s.txt; exit 0; }; }
log "ALIVE top=$top left=$n $(head -1 tree.log | sed 's/.*: //') "
