From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z183 XCuts.b183 XCuts.z184 XCuts.b184 XCuts.n183 XCuts.v183 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
