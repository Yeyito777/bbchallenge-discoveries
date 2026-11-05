#!/bin/bash
# usage: cascade.sh input "spec1" "spec2" ... ; prints remaining machines to stdout
T=$(dirname $0)/dec/tryd
in=$1; shift
cp $in /tmp/casc.$$
for spec in "$@"; do
  timeout 3000 $T $spec < /tmp/casc.$$ > /tmp/casc2.$$ 2> >(grep -v ^HALT >&2)
  mv /tmp/casc2.$$ /tmp/casc.$$
done
cat /tmp/casc.$$; rm -f /tmp/casc.$$
