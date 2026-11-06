# Can the orbit be certified with far fewer checks?

Short answer: not with anything found here. The structure is real and is written down below, but the certificate stays
near 10^12 facts, not thousands. The estimate comes from one measured stretch at scale 87 and a scaling argument. It does
not rule out a cleverer proof.

## What the orbit is doing

Write p = a+6 and S = a+b. On a D letter p doubles. On u or v, p becomes 2p - S plus a small constant. So p/S follows the
doubling map, and a sweep from (a0,B) is long division: its letters are the bits of (a0+6)/B, with small perturbations.
b flips parity on each D and is even after u or v. So a sweep continues through odd-length runs of D and ends at the
first even run. That is a prefix code over the quotient's bits.

Taking the bits two at a time after the first run: two of the four patterns stop and two continue, each with a quarter
of the width. So the set of starts B with a long tail is Cantor-like:

- tail depth t has exactly 2^(t/2) cylinders, each of width about 2^(log2 B - t);
- sweeps move B by about 600 to 900, so every cylinder wider than that is visited, down to t about log2 B - 9;
- that gives about sqrt(B) phases per bracket, which is the 1.35x growth per doubling (exactly sqrt 2 per doubling of B).

The depth counts in one stretch double exactly: 1, 3, 5, 10, 20, 40, 80, 160, 321, 642 ... The phase order is a binary
tree, Block(t) = stop(t), Block(t+2), stop'(t), Block(t+2), with the T of a stop dropping by about 4 per level.

## Why that does not give a short proof

**Skipping a block needs its exact exit, and the exit depends on the fine structure.** At the leaves, 68.6% of phases
have T = 1. Each of those samples a cylinder narrower than the step, with a D that depends on deep bits. A jump over a
block would need a lemma giving the exit residue as a function of the entry. Measured on 8M phases at scale 87
(`blocks_result.txt`), normalising D by its value at the block head:

| Tail depth | Blocks | Mean phases per block | Distinct shapes | Most repeats of one shape |
|---|---|---|---|---|
| 58 | 2,437 | 3,280 | 2,435 | 2 |
| 66 | 38,991 | 203 | 24,823 | 49 |
| 70 | 155,965 | 49 | 32,892 | 913 |
| 74 | 623,861 | 11 | 20,277 | 5,913 |
| 76 | 1,247,722 | 4.4 | 4,216 | 110,472 |

Blocks with thousands of phases almost never repeat. Small ones repeat, but a dictionary of small blocks would save
about a factor of 5 here: at depth 70, 8M phases become 156k block uses plus 33k shapes of 49 phases each. Each template
would also need its own proved lemma with slack conditions.

**The phase sequence has no short description that I could find.** xz on (D,T) reaches 0.45 bits per phase on 16M phases,
growing as about n^0.7 (`lzgrow.txt`). Extrapolated to 5.4e12 phases that is several GB, and those bytes are not a proof
either. This is a measure of the sequence, not a bound on its complexity.

**The history-free argument, which is how the cut points were found, does not become a proof.** Orbits merge: start every
reset state in a window and they coalesce, which is what `cftp.c` does. Merging would skip everything before a window if
every earlier orbit had to land in the window. That needs a bound on sweep increments for all earlier B, and no such
bound exists: the reset state (22, 84*2^k - 3k - 22) enters the sink family A(4n+2, 8n+22) right after its doublings, so
it has an infinite tail, and there is one at every scale. Excluding those states and their preimages means walking the
tree of all cylinders down to width 1, about 2^(t/2) nodes with t about log2 B. That is more nodes than the orbit has
phases, by roughly 2^4.5 at the same scale. Any proof has to show that the actual orbit avoids them, and I found no way
to do that without following it.

A related fact showed up: changing a chunk's start by 1 still lands exactly on the chunk's end (`cert/neg.tsv`, third
line). So a wrong jump can heal before the next cut point. Link checks alone are weak evidence, which is why the checker
proves every jump.

## Certificate sizes

| Form | Size | Checks |
|---|---|---|
| Replay the map, no jumps | 6.7e26 applications | not feasible |
| One-level jumps (the existing traversal and this checker) | 712 cut points, or 307k for quick chunks | 5.37e12 phases |
| Block templates (estimate from the table) | a dictionary of 10^7 to 10^9 lemmas | about 1e12 |
| Thousands of checks | nothing found | |
