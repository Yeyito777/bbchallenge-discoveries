From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z158 XCuts.b158 XCuts.z159 XCuts.b159 XCuts.n158 XCuts.v158 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
