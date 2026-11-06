#!/usr/bin/env python3
"""mkchunks output -> chunks.tsv: the last chunk runs to the halt form instead of to an endpoint. usage: finalize_chunks.py IN > OUT"""
import sys
L=open(sys.argv[1]).read().split('\n')[:-1]
x=L[-1].split(); x[4]='H'; x[5]='0'; L[-1]=' '.join(x)
print('\n'.join(L))
