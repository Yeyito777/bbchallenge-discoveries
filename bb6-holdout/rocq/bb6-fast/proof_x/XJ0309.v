From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z309 XCuts.b309 XCuts.z310 XCuts.b310 XCuts.n309 XCuts.v309 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
