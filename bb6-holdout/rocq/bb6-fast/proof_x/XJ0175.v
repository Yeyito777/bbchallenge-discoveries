From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z175 XCuts.b175 XCuts.z176 XCuts.b176 XCuts.n175 XCuts.v175 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
