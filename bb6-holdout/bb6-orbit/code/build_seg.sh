#!/bin/bash
# Profile-guided build of seg for this machine. train.txt holds one real stretch of the orbit: a0 B a1 Y.
set -e; d=$(mktemp -d); read A B A1 Y < train.txt; CC=${CC:-gcc}; M=${MARCH:--march=native}; X=${EXTRA:-}
$CC -O3 $M $X -fprofile-generate -fprofile-update=single -fprofile-dir=$d -I. -w -o seg_pg seg.c
./seg_pg $A $B $A1 $Y $d/o.txt
$CC -O3 $M $X -fprofile-use -fprofile-dir=$d -fprofile-correction -Wno-missing-profile -Wno-coverage-mismatch -I. -w -o seg seg.c; rm -rf seg_pg $d; echo built
