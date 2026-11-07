From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z165 XCuts.b165 XCuts.z166 XCuts.b166 XCuts.n165 XCuts.v165 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
