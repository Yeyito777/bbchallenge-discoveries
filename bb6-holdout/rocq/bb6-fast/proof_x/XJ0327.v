From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z327 XCuts.b327 XCuts.z328 XCuts.b328 XCuts.n327 XCuts.v327 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
