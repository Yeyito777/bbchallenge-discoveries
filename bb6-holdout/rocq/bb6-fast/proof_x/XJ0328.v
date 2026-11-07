From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z328 XCuts.b328 XCuts.z329 XCuts.b329 XCuts.n328 XCuts.v328 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
