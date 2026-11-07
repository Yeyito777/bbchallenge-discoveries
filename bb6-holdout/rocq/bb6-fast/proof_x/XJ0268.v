From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z268 XCuts.b268 XCuts.z269 XCuts.b269 XCuts.n268 XCuts.v268 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
