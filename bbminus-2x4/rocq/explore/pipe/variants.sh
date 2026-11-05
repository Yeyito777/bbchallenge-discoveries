#!/bin/bash
ulimit -s unlimited
cd $(dirname $0)
TAIL="rwl:2:3:320:400,lru:2:2:1000,ng1:2:2:2:3000,ng1:2:3:3:1600,ng1:4:2:2:600,ng1:4:3:3:1600,ng1:6:2:2:3200,ng1:6:3:3:3200,ng1:8:3:3:1600,lru:3:3:20000,rwl:4:2:320:2000,rwl:6:2:320:2000,ng2:4:4:20000,halt:1845977"
./pmain /tmp/v0.unk 1 "loop:107,ng2:1:1:400,ng2:2:2:800,ng2:3:3:400,ng2:4:4:800,loop:4100,$TAIL" > v0.txt
./pmain /tmp/v1.unk 1 "loop:30,loop:107,ng2:1:1:400,ng2:2:2:800,ng2:3:3:400,ng2:4:4:800,loop:4100,$TAIL" > v1.txt
./pmain /tmp/v2.unk 1 "loop:107,loop:1000,ng2:1:1:400,ng2:2:2:800,ng2:3:3:400,ng2:4:4:800,loop:4100,$TAIL" > v2.txt
./pmain /tmp/v3.unk 1 "loop:50,ng2:1:1:400,loop:300,ng2:2:2:800,ng2:3:3:400,ng2:4:4:800,loop:4100,$TAIL" > v3.txt
