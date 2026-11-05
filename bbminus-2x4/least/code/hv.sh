# hv.sh TAPE DIR ROOTS: run-language grid, then heavy annotated CPS, on a holdout list. Leaves undecided machines in b.txt.
T="$1"; B=${LEASTBIN:-$HOME/least}; mkdir -p "$2"; cd "$2"; [ "$3" = roots.txt ] || cp "$3" roots.txt
RL=""; for Bl in 1 2 3 4; do for ((o=0;o<Bl;o++)); do for K in 1 2 3 4; do for M in 1 2 3 4; do RL="$RL $K,$M,$Bl,$o,0,20000"; done; done; done; done
for C in 2 4 8 1 3 5 6 9 10 12 14 13 11 7 15; do for K in 1 2 3 4; do for Bl in 1 2 3 4; do RL="$RL $K,1,$Bl,-1,$C,50000"; done; done; done
"$B/runlang" "$T" "$RL" < roots.txt > rl.txt 2> rl.err
grep "^U" rl.txt | cut -d" " -f2 > a.txt
HEAVY="9,0,0,0,300000 10,0,0,0,300000"; for H in 1 2 3 4 5 6 8 10; do for n in 2 3 4 5 6; do HEAVY="$HEAVY $n,1,$H,0,300000"; done; done
"$B/cps" "$T" "$HEAVY" < a.txt > cps.txt 2> cps.err
grep "^U" cps.txt | cut -d" " -f2 > b.txt
