From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z660 XCuts.b660 XCuts.z661 XCuts.b661 XCuts.n660 XCuts.v660 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
