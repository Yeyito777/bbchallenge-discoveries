From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z228 XCuts.b228 XCuts.z229 XCuts.b229 XCuts.n228 XCuts.v228 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
