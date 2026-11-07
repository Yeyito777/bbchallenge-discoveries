From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z229 XCuts.b229 XCuts.z230 XCuts.b230 XCuts.n229 XCuts.v229 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
