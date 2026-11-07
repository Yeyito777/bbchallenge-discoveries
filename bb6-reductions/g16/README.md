# 16 BB(6) holdouts, one question

**This settles none of the 16 machines.** It proves that they all halt or don't for the same reason.

For each of the 16 machines below, Rocq proves from the raw transition table that the machine halts from blank if and only if some stack of one explicit orbit has a top event with P + 2 = 2^k:

```coq
Theorem g16_NN : halts (TM_from_str "M") c0 <-> exists n, hit (orbit n).
```

The orbit, the map and `hit` are in `rocq/theories/Spec.v` and mention no machine. So an answer about that one sequence settles all 16 at once.

- **Proved, with no axioms:** both directions for all 16, and the exact map (until such a stack, each machine passes through the tape of every stack, in order). `Print Assumptions` on all 33 theorems prints `Closed under the global context` (`rocq/logs/build_clean_j1.log`).
- **Checked in the kernel:** the first 30,000 stacks have no such event (`no_hit_below`).
- **Not proved:** whether such a stack exists. A C run (`analysis/lm.c`) reached 2×10^10 map steps and P = 1.09×10^10 with no hit. A rough model gives about 2×10^-10 expected hits from there.
- **Build:** `cd rocq && make`. It takes 27 minutes on one core, about 10.5 minutes with `make -j3`, and needs Rocq 8.20.1 only.

The 16 machines (`analysis/g16_members.txt`):

```
1RB0LB_1LC1RD_0LE1LA_0RB1RD_---0LF_1RA1LF
1RB---_0LC1LB_1RC1LD_1LA0RE_1LB0RF_0LD1RF
1RB0LC_1LC0RE_0LA1LD_1LA1LD_---0RF_1LA1RF
1RB0LD_1LC1RD_0LE1LA_0RB1RD_---0LF_1RA1LF
1RB0LE_0RC1RB_1LC1RD_0RF0LA_0RD1LE_1LA---
1RB0LE_0RC1RB_1LC1RD_1RF0LA_0RD1LE_1LB---
1RB0LE_0RC1RB_1LC1RD_1RF0LA_0RD1LE_1RB---
1RB0LE_1RC---_1RD1RC_1LA0RA_0RB0LF_1RD1LF
1RB0LF_1LC0RD_1LA1LC_---0RE_1LA1RE_0LA1LC
1RB0LF_1LC0RD_1LA1LC_---0RE_1LA1RE_1LB1LC
1RB---_0RC1RB_1LC1RD_1RA0LE_1RB0LF_0RD1LF
1RB1LA_1LC0RC_1RE0LD_0RE0LA_1RF---_1RB1RF
1RB1RA_1LC0RC_1RE0LD_0RE0LF_1RA---_1RB1LF
1RB1RC_1LA0LE_1RD1RC_1LB0RA_---0LF_1RD1LF
1RB1RC_1LC0LE_1RD1RC_1LB0RA_---0LF_1RD1LF
1RB1RC_1RC0LE_1RD1RC_1LB0RA_---0LF_1RD1LF
```

Files: `rocq/` is the proof (`ROCQ.md` says what is and isn't proved), and `analysis/` is the map, the raw-machine checks and the orbit run (`REPORT.md`).

## Credits

aducharme noticed that two of these machines behave identically despite very different tables. mxdys listed five of them and asked whether they all follow the same rules (#bb6, Apr 11 2026). This answers that question for 16 machines. busycoq is by Maja Kądziołka, via ccz181078's BB6 branch (MIT, licence files kept in `rocq/busycoq/`).
