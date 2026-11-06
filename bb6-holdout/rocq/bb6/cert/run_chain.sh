#!/bin/bash
# Run the whole chain with the extracted checker: run_chain.sh WORKERS OUTDIR CHECK_BINARY CHUNKS
# The chunks are dealt out evenly, one list per worker, and each worker appends one line per chunk to OUTDIR/res_k.tsv.
# Stop it any time and start it again with the same WORKERS: finished chunks are skipped.
W=$1; OUT=$2; BIN=$(realpath "$3"); CH=$(realpath "$4")
mkdir -p "$OUT/lists"; cd "$OUT" || exit 1
rm -f lists/rest_*.tsv
awk -v W="$W" '{ print > ("lists/rest_" ((NR-1)%W) ".tsv") }' "$CH"
for ((k = 0; k < W; k++)); do
  [ -s "lists/rest_$k.tsv" ] && "$BIN" chunks "lists/rest_$k.tsv" 1 0 "res_$k.tsv" >> "res_$k.tsv" 2>> "err_$k.log" &
done
wait
