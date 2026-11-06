#!/bin/bash
while read X; do r=$(timeout 100 ./cftp near $X 4096 3000000); echo "$X $r"; done
