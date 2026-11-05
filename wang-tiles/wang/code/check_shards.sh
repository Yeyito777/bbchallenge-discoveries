#!/bin/bash
# usage: check_shards.sh CHECK_CERT_BIN DIR NAME SHARDS [PARALLEL] [RESULTDIR]
# Checks DIR/NAME_sNNN.tree(.xz) + .tori(.xz) for every shard and prints one line per shard, then a total.
# The claim for NAME holds only if all SHARDS pass and no shard reports a holdout, which the checker
# would reject as a complete fill with no torus.  With RESULTDIR, each shard's line is kept there, and a
# shard that already passed is not checked again, so the run can be stopped and resumed.
bin=$1; dir=$2; name=$3; shards=$4; par=${5:-1}; res=$6
tmp=$(mktemp -d); trap 'rm -rf "$tmp"' EXIT
[ -n "$res" ] && mkdir -p "$res"
one() {
  s=$(printf "%03d" "$1"); p="$dir/${name}_s$s"; q="$tmp/${name}_s$s"
  if [ -n "$res" ] && grep -q ' OK ' "$res/$s.txt" 2>/dev/null; then cat "$res/$s.txt"; return; fi
  if [ -f "$p.tori.xz" ]; then xz -dc "$p.tori.xz" > "$q.tori"; else cp "$p.tori" "$q.tori"; fi
  if [ -f "$p.tree.xz" ]; then r=$(xz -dc "$p.tree.xz" | "$bin" "$q" - | head -1); else cp "$p.tree" "$q.tree"; r=$("$bin" "$q" | head -1); rm -f "$q.tree"; fi
  rm -f "$q.tori"
  echo "$s $r"
  [ -n "$res" ] && echo "$s $r" > "$res/$s.txt"
}
for i in $(seq 0 $((shards - 1))); do
  while [ "$(jobs -rp | wc -l)" -ge "$par" ]; do wait -n; done
  one "$i" &
done | tee "$tmp/out"
wait
ok=$(grep -c ' OK ' "$tmp/out")
echo "shards passing: $ok of $shards"
python3 - "$tmp/out" "$shards" <<'PY'
import re, sys
nodes = leaves = closed = 0
seen, lists = set(), set()
for line in open(sys.argv[1]):
    m = re.search(r"nodes=(\d+) leaves=(\d+) closed=(\d+) tori=\d+ shard=(\d+)/(\d+) reset=(\d+) subtrees=(\d+) digest=(\w+)", line)
    if m:
        nodes += int(m[1]); leaves += int(m[2]); closed += int(m[3])
        seen.add(int(m[4]))
        lists.add((m[5], m[6], m[7], m[8]))
w = int(sys.argv[2])
cover = seen == set(range(w)) and len(lists) == 1 and int(next(iter(lists))[0]) == w
print(f"total nodes={nodes} leaves={leaves} closed={closed}")
print(f"shard ids 0..{w - 1} all present and all shards agree on (shards, reset, subtrees, digest) = {sorted(lists)}: {cover}")
sys.exit(0 if cover else 1)
PY
[ $? = 0 ] && [ "$ok" = "$shards" ] && echo "ALL SHARDS PASS: the claim holds"
