#!/usr/bin/env python3
"""Generate the proof files for `halts_in tm c0 n_steps`: XCuts.v, one XJnnnn.v per job, XJHalt.v, XFinalProof.v.
usage: gen_xfinal.py CHUNKS_TSV ALLRES OUTDIR CHUNKS_PER_JOB [HALTS_TIMES TARGET_SECONDS]
With HALTS_TIMES (lines "Jnnnn seconds ..." from the halts run, jobs of CHUNKS_PER_JOB chunks), each such stretch is cut into
ceil(seconds / TARGET_SECONDS) jobs of equal chunk count, so long stretches become several short jobs.
Cut points and per-job counts and costs come from earlier runs and are untrusted: a wrong one only makes a job fail."""
import sys, os
tsv, allres, out, per = sys.argv[1], sys.argv[2], sys.argv[3], int(sys.argv[4])
A_HALT = 1083197534374707740536733690
P63 = 2**63; PM = 2**315
rows = [l.split() for l in open(tsv) if l.strip()]
assert rows[-1][4] == 'H' and rows[0][2:4] == ['6', '1']
for x, y in zip(rows, rows[1:]):
    assert x[4:6] == y[2:4]
res = {}
for l in open(allres):
    p = l.split()
    if len(p) >= 4 and p[1] == 'OK':
        res[p[0]] = (int(p[2]), int(p[3]))
    elif len(p) >= 5 and p[1] == 'HALT':
        assert int(p[2]) == A_HALT
        res[p[0]] = (int(p[3]), int(p[4]))

def w(x):
    x = int(x); assert 0 <= x < 2**117
    return f"(mkW {x // P63}%uint63 {x % P63}%uint63)"
def v(c):
    c %= PM
    return "(mkV " + " ".join(f"{(c >> (63 * i)) & (P63 - 1)}%uint63" for i in range(5)) + ")"

body = rows[:-1]
blocks = [body[i:i + per] for i in range(0, len(body), per)]
jobs = blocks
if len(sys.argv) > 6:
    secs = {}
    for l in open(sys.argv[5]):
        p = l.split()
        if p and p[0].startswith('J') and p[0][1:].isdigit():
            secs[int(p[0][1:])] = float(p[1])
    target = float(sys.argv[6])
    jobs = []
    for i, bl in enumerate(blocks):
        k = max(1, -(-int(secs.get(i, target)) // int(target)))
        step = -(-len(bl) // k)
        jobs += [bl[j:j + step] for j in range(0, len(bl), step)]
os.makedirs(out, exist_ok=True)
with open(f"{out}/XCuts.v", "w") as f:
    f.write("From Coq Require Import Uint63.\nFrom BB6 Require Import Num Vec.\n\n")
    tot_n = tot_c = 0
    for i, jb in enumerate(jobs):
        n = sum(res[r[0]][0] for r in jb); c = sum(res[r[0]][1] for r in jb)
        tot_n += n; tot_c += c
        f.write(f"Definition z{i} : int := {jb[0][2]}%uint63.\nDefinition b{i} : W := {w(jb[0][3])}.\n")
        f.write(f"Definition n{i} : W := {w(n)}.\nDefinition v{i} : V := {v(c)}.\n")
    h = rows[-1]; nh, ch = res[h[0]]
    tot_n += nh; tot_c += ch
    k = len(jobs)
    f.write(f"Definition z{k} : int := {h[2]}%uint63.\nDefinition b{k} : W := {w(h[3])}.\n")
    f.write(f"Definition nh : W := {w(nh)}.\nDefinition vh : V := {v(ch)}.\n")
    f.write(f"Definition a_halt : W := {w(A_HALT)}.\nDefinition y_end : W := {w(2**100)}.\n")
print("total apps", tot_n, "cost mod 2^315", tot_c % PM)
assert tot_n == 674564771793355691986675473, "total apps differ from n_apps"
assert (tot_c - 38693417180063871717059872803770979643885910167836334283316455175709787324184634) % PM == 0, "total cost differs from R_total"
print("totals match Statement.v")
k = len(jobs)
for i in range(k):
    with open(f"{out}/XJ{i:04d}.v", "w") as f:
        f.write(f"""From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z{i} XCuts.b{i} XCuts.z{i+1} XCuts.b{i+1} XCuts.n{i} XCuts.v{i} = true.
Proof. native_cast_no_check (eq_refl true). Qed.
""")
with open(f"{out}/XJHalt.v", "w") as f:
    f.write(f"""From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_halt_at XCuts.z{k} XCuts.b{k} XCuts.y_end XCuts.a_halt XCuts.nh XCuts.vh = true.
Proof. native_cast_no_check (eq_refl true). Qed.
""")
with open(f"{out}/XFinalProof.v", "w") as f:
    f.write("""(** [halts_in tm c0 n_steps] for the holdout 1RB0LF_1RC1RA_0RD0RB_1LE---_0LA1LE_1RD1LA, n_steps as in Statement.v. *)
From Coq Require Import ZArith.
From Coq Require Uint63.
From BusyCoq Require Import Individual62.
From BB6 Require Import Rules Map Num Vec Statement.
From BF Require HTop XTop.
From BF Require Import XFinal.
Require XCuts XJHalt.
""")
    for i in range(k):
        f.write(f"Require XJ{i:04d}.\n")
    f.write("Local Open Scope Z_scope.\n\n")
    def job(i):
        return f"(XTop.xrun_seg_sound XCuts.z{i} XCuts.b{i} XCuts.z{i+1} XCuts.b{i+1} XCuts.n{i} XCuts.v{i} eq_refl XJ{i:04d}.seg)"
    f.write(f"Definition k0 := {job(0)}.\n")
    for i in range(1, k):
        f.write(f"Definition k{i} := XR_trans _ _ _ _ _ _ _ _ _ _ k{i-1} {job(i)}.\n")
    f.write(f"""Definition korbit := XR_trans _ _ _ _ _ _ _ _ _ _ k{k-1}
  (XTop.xrun_halt_at_sound XCuts.z{k} XCuts.b{k} XCuts.y_end XCuts.a_halt XCuts.nh XCuts.vh eq_refl XJHalt.seg).

Lemma orbit_n : {' + '.join(['Num.val XCuts.n'+str(i) for i in range(k)]+['Num.val XCuts.nh'])} = n_apps.
Proof. vm_compute. reflexivity. Qed.

Theorem bb6_holdout_steps : halts_in tm c0 n_steps.
Proof.
  refine (steps_of_orbit _ _ _ orbit_n _); [exact korbit|vm_compute; reflexivity].
Qed.

Print Assumptions bb6_holdout_steps.
""")
print(k, "jobs + 1 halt job")
