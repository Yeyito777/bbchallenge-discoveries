From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z662 XCuts.b662 XCuts.z663 XCuts.b663 XCuts.n662 XCuts.v662 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
