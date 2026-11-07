From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z661 XCuts.b661 XCuts.z662 XCuts.b662 XCuts.n661 XCuts.v661 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
