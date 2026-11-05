#!/bin/bash
export PATH=$HOME/.opam/rocq/bin:$PATH
cd $(dirname $0)
/usr/bin/time -v coqc -Q ../../BBminus2x4 BBminus2x4 T1.v > T1.log 2>&1
