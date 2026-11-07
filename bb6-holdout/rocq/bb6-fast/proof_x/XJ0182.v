From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z182 XCuts.b182 XCuts.z183 XCuts.b183 XCuts.n182 XCuts.v182 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
