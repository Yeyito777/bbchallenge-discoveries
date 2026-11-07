From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z243 XCuts.b243 XCuts.z244 XCuts.b244 XCuts.n243 XCuts.v243 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
