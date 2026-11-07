From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z257 XCuts.b257 XCuts.z258 XCuts.b258 XCuts.n257 XCuts.v257 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
