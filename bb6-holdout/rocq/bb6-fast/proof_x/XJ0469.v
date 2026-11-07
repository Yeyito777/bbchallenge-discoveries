From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z469 XCuts.b469 XCuts.z470 XCuts.b470 XCuts.n469 XCuts.v469 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
