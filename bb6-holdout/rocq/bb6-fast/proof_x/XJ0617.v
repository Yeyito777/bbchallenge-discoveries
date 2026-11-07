From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z617 XCuts.b617 XCuts.z618 XCuts.b618 XCuts.n617 XCuts.v617 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
