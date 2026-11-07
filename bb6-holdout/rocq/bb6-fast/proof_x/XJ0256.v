From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z256 XCuts.b256 XCuts.z257 XCuts.b257 XCuts.n256 XCuts.v256 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
