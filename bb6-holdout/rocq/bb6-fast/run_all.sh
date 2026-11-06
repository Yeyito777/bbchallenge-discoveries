#!/bin/bash
# Build the checker and prove `halts tm c0`. Usage: run_all.sh [PARALLEL_JOBS] (default: all cores, one job per core).
# A job needs about 3 GB; lower PARALLEL_JOBS if memory is short. Finished jobs are kept, so the script can be restarted.
set -u
J=${1:-$(nproc)}
cd "$(dirname "$0")"
export OCAMLPARAM='_,O3=1,inline=1000,unbox-closures=1'   # flambda: about 2x; harmless without flambda
ulimit -s unlimited
die() { echo "run_all.sh: $*" >&2; exit 1; }
for c in coqc coq_makefile make ocamlfind; do
  command -v "$c" >/dev/null || die "$c not found in PATH (activate the switch: eval \$(opam env --switch=rocq-fl))"
done
sed -i 's/-native-compiler ondemand/-native-compiler yes/' _CoqProject
coq_makefile -f _CoqProject -o Makefile.coq || die "coq_makefile failed"
[ -f Makefile.coq ] || die "coq_makefile did not write Makefile.coq"
make -j"$J" -f Makefile.coq || die "building theories/ failed"
Q="-native-compiler yes -Q ../base/busycoq BusyCoq -Q ../base/theories BB6 -Q ../theories BF -Q . \"\""
cd proof
eval coqc $Q Cuts.v || die "compiling proof/Cuts.v failed"
run1() { f=$1; [ -f "${f%.v}.vo" ] && exit 0; eval coqc $Q "$f" > "${f%.v}.log" 2>&1 && echo "ok $f $(date +%T)" || { echo "FAILED $f"; exit 1; }; }
export -f run1; export Q
ls J*.v | xargs -P "$J" -n 1 bash -c 'run1 "$0"' || die "a job failed (see proof/J*.log)"
eval coqc $(echo "$Q" | sed 's/-native-compiler yes/-native-compiler no/') Final.v > Final.out 2> Final.err || { cat Final.err >&2; die "compiling proof/Final.v failed"; }
grep -v "^$" Final.out
