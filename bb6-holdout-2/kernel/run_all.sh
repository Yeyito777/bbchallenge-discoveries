#!/bin/bash
# Resumable kernel check of the c273 orbit. Everything lives under K (default: this script's folder): sources, .vo files, logs, markers.
# A job is done only when done/JNNNN.ok exists; it is written after coqc exits 0 and the .vo exists. Rerunning skips done jobs.
#   run_all.sh setup        build BusyCoq, Rules273, Kernel273 (skips what is built)
#   run_all.sh jobs [P] [list]   run every unfinished job (or those in list) with P parallel coqc (default 120)
#   run_all.sh chain        compile Chain.v once every job is done; writes done/CHAIN.ok and logs/Chain.log
set -u
K=${K:-$(cd "$(dirname "$0")" && pwd)}; cd "$K" || exit 1
eval "$(opam env --switch=rocq)"
mkdir -p done logs
QF="-Q . H -Q busycoq BusyCoq"
case "${1:-}" in
setup)
  if [ ! -f done/SETUP.ok ]; then
    (cd busycoq && coq_makefile -Q . BusyCoq -o Makefile.coq $(ls *.v) >/dev/null && make -f Makefile.coq -j8 Individual62.vo >/dev/null 2>&1) || exit 1
    coqc $QF Rules273.v > logs/Rules273.log 2>&1 || exit 1
    coqc $QF Kernel273.v > logs/Kernel273.log 2>&1 || exit 1
    coqc $QF Final273.v > logs/Final273.log 2>&1 || exit 1
    gcc -O2 -march=native -o count273 count273.c || exit 1
    rustc --edition 2021 -C opt-level=3 -C target-cpu=native -o count273r count273.rs || exit 1
    touch done/SETUP.ok
  fi
  echo setup ok;;
jobs)
  # tasks.txt: "K Jnnnn" kernel job, "C Jnnnn" / "R Jnnnn" raw-step counts (C and Rust). Markers: done/Jnnnn.ok, .c.ok, .r.ok
  P=${2:-120}
  [ -f done/SETUP.ok ] || { echo "run setup first"; exit 1; }
  mkdir -p counts
  list=${3:-tasks.txt}
  while read t j; do
    case $t in K) m=done/$j.ok;; C) m=done/$j.c.ok;; R) m=done/$j.r.ok;; esac
    [ -f $m ] || echo "$t $j"
  done < "$list" |
    xargs -P "$P" -L 1 bash -c '
      t=$0; j=$1; start=$(date +%s)
      case $t in
      K) if /usr/bin/time -f "maxrss_kb %M elapsed_s %e" coqc '"$QF"' jobs/$j.v > logs/$j.log 2>&1 && [ -f jobs/$j.vo ]; then
           echo "$j ok $(( $(date +%s) - start ))s $(tail -n1 logs/$j.log)" > done/$j.ok.tmp && mv done/$j.ok.tmp done/$j.ok
         else echo "$(date -u +%FT%TZ) K $j FAILED" >> logs/failures.log; fi;;
      C|R) bin=./count273; [ $t = R ] && bin=./count273r; ext=$(echo $t | tr CR cr)
         set -- $(grep "^$j " counts.txt)
         if [ "$6" = halt ]; then args="$2 $3 $4 $5 halt"; want=""; else args="$2 $3 $4 $5"; want="$6 $7 $8"; fi
         if $bin $args > counts/$j.$ext.tmp 2> counts/$j.$ext.err; then
           got=$(cut -d" " -f1-3 counts/$j.$ext.tmp)
           if [ -z "$want" ] || [ "$got" = "$want" ]; then mv counts/$j.$ext.tmp counts/$j.$ext.txt; touch done/$j.$ext.ok
           else echo "$(date -u +%FT%TZ) $t $j END STATE $got != $want" >> logs/failures.log; fi
         else echo "$(date -u +%FT%TZ) $t $j FAILED" >> logs/failures.log; fi;;
      esac'
  echo "kernel $(ls done | grep -c "^J[0-9]*\.ok$"), C $(ls done | grep -c "\.c\.ok$"), Rust $(ls done | grep -c "\.r\.ok$") of $(wc -l < jobs.txt)";;
chain)
  n=$(ls done | grep -c "^J[0-9]*\.ok$"); t=$(wc -l < jobs.txt)
  [ "$n" -eq "$t" ] || { echo "only $n of $t jobs done"; exit 1; }
  if coqc $QF Chain.v > logs/Chain.log 2>&1 && coqc $QF Halts273.v > logs/Halts273.log 2>&1; then touch done/CHAIN.ok; fi
  cat logs/Chain.log logs/Halts273.log;;
*) echo "usage: run_all.sh setup | jobs [P] [list] | chain"; exit 1;;
esac
