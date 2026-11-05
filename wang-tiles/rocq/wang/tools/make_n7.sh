#!/bin/bash
# Regenerate the n = 7 data files of the proof from the certificate wang/certs/n7 (release v1).
#
# usage: tools/make_n7.sh CERTDIR [JOBS] [WORKDIR]
#
# CERTDIR holds n7_D17_sNNN.{tree,tori}.xz and SHA256SUMS (the 64 shards, 195 MB). JOBS is the number
# of parallel processes (default 8). WORKDIR (default ./n7work, about 1 GB, deleted at the end unless
# KEEP=1) holds the intermediate files. Steps:
#   1. check the shards against CERTDIR/SHA256SUMS;
#   2. build tools/c/recut (and tools/c/check4 with CHECK=1) with cc;
#   3. merge the 64 torus tables into one (tools/n7_tori.py);
#   4. recut each shard: walk it as wang/code/check_cert.c does, and write each subtree's tokens with
#      torus ids renumbered and remember marks added (tools/c/recut.c);
#   5. share the 5,519 subtrees out over 72 jobs by node count (tools/n7_assemble.py);
#   6. with CHECK=1, check every job with the C checker for the new format (tools/c/check4.c);
#   7. write the Rocq data files n7/*.v and _CoqProject (tools/n7_to_coq.py);
#   8. compare the generated files with n7/MANIFEST.sha256 when that exists, else write it.
# It needs Python 3, xz and a C compiler, and takes about 70 core-minutes (step 4; step 6 adds 40).
set -e
here=$(cd "$(dirname "$0")/.." && pwd)
certs=$(cd "$1" && pwd)
par=${2:-8}
work=${3:-$here/n7work}
NJOBS=72
mkdir -p "$work"/seg "$work"/logs "$work"/tori "$work"/bin
(cd "$certs" && sha256sum --quiet -c SHA256SUMS)
echo "certificate files match SHA256SUMS"
cc -O2 -o "$work/bin/recut" "$here/tools/c/recut.c"
[ "$CHECK" = 1 ] && cc -O2 -o "$work/bin/check4" "$here/tools/c/check4.c"
python3 "$here/tools/n7_tori.py" "$certs" "$work/tori" > /dev/null
one() {
  s=$1; top=0; [ "$s" = 000 ] && top=1
  t=$(mktemp -d "$work/tmp.XXXXXX")
  xz -dc "$certs/n7_D17_s$s.tori.xz" > "$t/s.tori"; xz -dc "$certs/n7_D17_s$s.tree.xz" > "$t/s.tree"
  "$work/bin/recut" "$t/s" "$work/tori/map_s$s.txt" "$work/seg" $top > "$work/logs/$s.out" 2> "$work/logs/$s.err"
  rm -rf "$t"
  grep -q "^OK" "$work/logs/$s.out" || { echo "recut failed on shard $s"; cat "$work/logs/$s.out"; exit 1; }
}
for i in $(seq -f %03g 0 63); do
  while [ "$(jobs -rp | wc -l)" -ge "$par" ]; do wait -n; done
  one "$i" &
done
wait
[ "$(cat "$work"/logs/*.out | grep -c '^OK')" = 64 ] || { echo "recut failed"; exit 1; }
echo "recut: all 64 shards walked and checked"
grep -h '^SUB' "$work"/logs/*.err | sed 's/^SUB \([0-9]*\) nodes=\([0-9]*\) .*rels=\([0-9]*\)$/\1 \2 \3/' | sort -n > "$work/seg/subs.txt"
awk '{print $1, $2}' "$work/seg/subs.txt" > "$work/seg/sizes.txt"
awk '{print $1, $3}' "$work/seg/subs.txt" > "$work/seg/rels.txt"
python3 "$here/tools/n7_assemble.py" "$work/seg" "$work/seg/prefixes.txt" "$work/tori" "$work/jobs" $NJOBS
if [ "$CHECK" = 1 ]; then
  for j in $(seq 0 $((NJOBS - 1))); do
    while [ "$(jobs -rp | wc -l)" -ge "$par" ]; do wait -n; done
    "$work/bin/check4" "$work/jobs" "$j" > "$work/logs/job_$j.out" &
  done
  wait
  [ "$(cat "$work"/logs/job_*.out | grep -c '^OK')" = $NJOBS ] || { echo "a job fails the C checker"; exit 1; }
  echo "check4: all $NJOBS jobs pass the C checker"
fi
rm -f "$here"/n7/Job7_*.v "$here"/n7/Check7_*.v "$here"/n7/Tori7*.v "$here"/n7/Jobs7.v
PAR=$par python3 "$here/tools/n7_to_coq.py" "$work/jobs" "$here/n7" > /dev/null
# _CoqProject: the files without n = 7, then the n = 7 data and jobs, largest job first
{
  cat "$here/_CoqProject.small"
  echo
  echo "n7/Wang7_Prefixes.v"
  ls "$here"/n7/Tori7_*.v | xargs -n1 basename | sort -V | sed 's|^|n7/|'
  echo "n7/Tori7.v"
  for j in $(sort -k2 -n -r "$work/jobs/jobs.txt" | awk '{printf "%03d\n", $1}'); do
    ls "$here"/n7/Job7_j${j}_*.v | xargs -n1 basename | sort -V | sed 's|^|n7/|'
    echo "n7/Check7_j$j.v"
  done
  echo "n7/Jobs7.v"
  echo
  echo "WangTiles_Theorem7.v"
} > "$here/_CoqProject"
cd "$here/n7"
if [ -f MANIFEST.sha256 ]; then
  sha256sum --quiet -c MANIFEST.sha256 && echo "generated files match n7/MANIFEST.sha256"
else
  sha256sum Wang7_Prefixes.v Tori7*.v Job7_*.v Check7_*.v Jobs7.v ../_CoqProject > MANIFEST.sha256
  echo "wrote n7/MANIFEST.sha256"
fi
[ "$KEEP" = 1 ] || rm -rf "$work"
