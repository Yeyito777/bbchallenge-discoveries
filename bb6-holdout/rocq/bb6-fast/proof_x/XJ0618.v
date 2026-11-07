From Coq Require Import Uint63.
From BF Require Import HTop XTop.
Require XCuts.
Lemma seg : xrun_seg XCuts.z618 XCuts.b618 XCuts.z619 XCuts.b619 XCuts.n618 XCuts.v618 = true.
Proof. native_cast_no_check (eq_refl true). Qed.
