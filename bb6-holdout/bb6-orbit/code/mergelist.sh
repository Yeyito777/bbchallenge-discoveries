#!/bin/bash
# For each grid X (stdin) compute a merged reset state close after X. Output: X a0 B phases start
while read X; do r=$(timeout 25 ./cftp near $X 4096 400000); echo "$X $r"; done
