From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z595 XCuts.b595 XCuts.z596 XCuts.b596 XCuts.n595 XCuts.v595 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
