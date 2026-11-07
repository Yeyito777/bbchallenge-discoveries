From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z672 XCuts.b672 XCuts.z673 XCuts.b673 XCuts.n672 XCuts.v672 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
