#!/bin/bash
# gridone.sh TAPE TM OUT: try one machine against a large run-language parameter grid, in parallel.
T="$1"; TM="$2"; OUT="$3"; BIN=${LEASTBIN:-$HOME/least}/runlang
: > "$OUT"
{ for lim in 30000 300000 3000000; do
  for C in 0 8 4 2 1 12 10 9 6 5 3; do for B in 1 2 3 4 6; do for K in 1 2 3 4 5 6 8 10; do for M in 1 2 3 4; do
    echo "-1 $K,$M,$B,-1,$C,$lim"
    [ "$C" = 0 ] && for ((o=0;o<B;o++)); do echo "$o $K,$M,$B,$o,0,$lim"; done
  done; done; done; done
done; } | xargs -P ${P:-3} -L 1 bash -c 'r=$(echo "'"$TM"'" | OMP_NUM_THREADS=1 timeout 300 '"$BIN"' "'"$T"'" "$2" 2>/dev/null); case "$r" in D*) echo "$r" >> '"$OUT"';; esac' _
