From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z326 XCuts.b326 XCuts.z327 XCuts.b327 XCuts.n326 XCuts.v326 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
