From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z696 XCuts.b696 XCuts.z697 XCuts.b697 XCuts.n696 XCuts.v696 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
