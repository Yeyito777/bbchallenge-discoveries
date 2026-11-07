From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z186 XCuts.b186 XCuts.z187 XCuts.b187 XCuts.n186 XCuts.v186 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
