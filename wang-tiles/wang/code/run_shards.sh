#!/bin/bash
# usage: run_shards.sh BIN N D OUTDIR RESET SHARDS GATE PARALLEL FIRST LAST
# Runs wt_lazy for shards FIRST..LAST, at most PARALLEL at once.  A shard that finished is skipped.
bin=$1; n=$2; d=$3; out=$4; reset=$5; shards=$6; gate=$7; par=$8; first=$9; last=${10}
mkdir -p "$out"
run_one() {
  s=$1; p=$(printf "%s/n%s_D%s_s%03d" "$out" "$n" "$d" "$s")
  [ -f "$p.done" ] && return 0
  "$bin" "$n" "$d" ringsym 12 "$p" "$p.hold" "$reset" "$shards" "$s" "$gate" > "$p.out" 2> "$p.log" && touch "$p.done"
}
for s in $(seq "$first" "$last"); do
  while [ "$(jobs -rp | wc -l)" -ge "$par" ]; do wait -n; done
  run_one "$s" &
done
wait
