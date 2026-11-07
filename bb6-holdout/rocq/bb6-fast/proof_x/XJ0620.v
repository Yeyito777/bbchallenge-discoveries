From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z620 XCuts.b620 XCuts.z621 XCuts.b621 XCuts.n620 XCuts.v620 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
