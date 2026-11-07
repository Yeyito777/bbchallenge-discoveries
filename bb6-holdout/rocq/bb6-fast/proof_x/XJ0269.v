From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z269 XCuts.b269 XCuts.z270 XCuts.b270 XCuts.n269 XCuts.v269 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
