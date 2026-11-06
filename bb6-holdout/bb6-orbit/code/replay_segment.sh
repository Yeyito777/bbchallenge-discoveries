#!/bin/bash
# Rerun one segment of the traversal and compare with its stored result. usage: replay_segment.sh ID  (run from code/, with ./seg built)
set -e; L=../certs/seglist.txt; R=../certs/segments; read -r id a0 b a1 y < <(awk -v i="$1" '$1==i' $L); o=$(mktemp -u); ./seg "$a0" "$b" "$a1" "$y" "$o"
python3 - "$o" "$R/seg_$id.txt" <<'PY'
import sys,re
def k(f):
    T=open(f).read().split('\n'); m=re.search(r'end (\d+ \d+) .* apps (\d+) phases',T[0]); return m[1],m[2],T[1],[re.sub(r' phases \d+ sweeps \d+$','',x) for x in T[2:] if x.startswith(('scale','halt'))]
a,b=k(sys.argv[1]),k(sys.argv[2]); print('identical' if a==b else 'DIFFERENT'); sys.exit(a!=b)
PY
rm -f "$o"
