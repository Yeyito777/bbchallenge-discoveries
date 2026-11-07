From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z361 XCuts.b361 XCuts.z362 XCuts.b362 XCuts.n361 XCuts.v361 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
