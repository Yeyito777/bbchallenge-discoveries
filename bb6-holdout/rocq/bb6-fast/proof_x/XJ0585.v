From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z585 XCuts.b585 XCuts.z586 XCuts.b586 XCuts.n585 XCuts.v585 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
