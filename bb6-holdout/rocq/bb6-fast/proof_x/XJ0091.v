From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z91 XCuts.b91 XCuts.z92 XCuts.b92 XCuts.n91 XCuts.v91 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
