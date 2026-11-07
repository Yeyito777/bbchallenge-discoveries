From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z621 XCuts.b621 XCuts.z622 XCuts.b622 XCuts.n621 XCuts.v621 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
