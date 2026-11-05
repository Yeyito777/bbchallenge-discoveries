#!/bin/bash
# Build the proof: tools/build.sh JOBS (run from anywhere; logs to logs/build_<date>.log)
ulimit -s unlimited
cd "$(dirname "$0")/../BBminus2x4"
eval "$(opam env --switch=rocq 2>/dev/null)"
J=${1:-8}
coq_makefile -f _CoqProject -o Makefile.coq > /dev/null
LOG=../logs/build_$(date +%Y%m%d_%H%M%S).log
{ echo "jobs $J start $(date)"; /usr/bin/time -v make -j"$J" -f Makefile.coq TIMED=1; echo "exit $? end $(date)"; } > "$LOG" 2>&1
echo "$LOG"
