#!/bin/bash
# usage: check_proofs.sh TOOLDIR CHAMPIONDIR
# Re-checks each stored UNSAT proof with drat-trim and with the verified checker cake_lpr, and the
# CNF and tiling against the tile list.  TOOLDIR holds drat/drat-trim and cake/cake_lpr built from source.
tools=$1; dir=$2; here=$(cd "$(dirname "$0")" && pwd); bad=0
for tiles in "$dir"/*.tiles; do
  name=$(basename "$tiles" .tiles); d=$(echo "$name" | sed -E 's/.*_d([0-9]+).*/\1/'); e=$((d + 1))
  python3 "$here/champion_cert.py" check "$tiles" "$d" "$dir" || bad=1
  cnf="$dir/$name.d$e.cnf"
  a=$("$tools/drat/drat-trim" "$cnf" "$dir/$name.d$e.drat" 2>&1 | grep -aoE 's VERIFIED( UNSAT)?' | tail -1)
  b=$("$tools/cake/cake_lpr" "$cnf" "$dir/$name.d$e.lrat" 2>&1 | grep -aoE 's VERIFIED( UNSAT)?' | tail -1)
  echo "$name: drat-trim: $a; cake_lpr: $b"
  [ "$a" = "s VERIFIED" ] || bad=1
  [ "$b" = "s VERIFIED UNSAT" ] || bad=1
done
[ $bad = 0 ] && echo "ALL PROOFS OK" || { echo "SOME CHECK FAILED"; exit 1; }
