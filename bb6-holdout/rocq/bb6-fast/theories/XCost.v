(** Cost polynomials for block lemmas: exact integers in five limbs. *)
From Coq Require Import ZArith Lia Uint63 List Bool.
From BB6 Require Import Num.
From BF Require Import Ints.
Local Notation phi := Uint63.to_Z.

Definition M31 : int := 2147483647.
Local Open Scope uint63_scope.

(** ** Signed five-limb numbers: limbs 0..3 canonical, limb 4 two's complement and small. *)
Record P5 := mk5 { q0:int; q1:int; q2:int; q3:int; q4:int }.
Definition OFF : int := 2305843009213693952.
Definition OFFC : int := 1073741824.
Definition nrm (x0 x1 x2 x3 x4 : int) : P5 :=
  let c0 := x0 + OFF in
  let c1 := x1 + OFF + ((c0 >> 31) - OFFC) in
  let c2 := x2 + OFF + ((c1 >> 31) - OFFC) in
  let c3 := x3 + OFF + ((c2 >> 31) - OFFC) in
  mk5 (c0 land M31) (c1 land M31) (c2 land M31) (c3 land M31) (x4 + ((c3 >> 31) - OFFC)).
Definition ok5 (x : P5) : bool := (q4 x + 1073741824) <? 2147483648.
Definition zero5 : P5 := mk5 0 0 0 0 0.
Definition addk (z : P5) (k : int) (x : P5) : P5 :=
  nrm (q0 z + k * q0 x) (q1 z + k * q1 x) (q2 z + k * q2 x) (q3 z + k * q3 x) (q4 z + k * q4 x).
Definition subk (z : P5) (k : int) (x : P5) : P5 :=
  nrm (q0 z - k * q0 x) (q1 z - k * q1 x) (q2 z - k * q2 x) (q3 z - k * q3 x) (q4 z - k * q4 x).
Definition add5 (z x : P5) : P5 := nrm (q0 z + q0 x) (q1 z + q1 x) (q2 z + q2 x) (q3 z + q3 x) (q4 z + q4 x).
(** a nonnegative int below 2^62 *)
Definition pnat (k : int) : P5 := mk5 (k land M31) ((k >> 31) land M31) (k >> 62) 0 0.

Record Poly := mkP { pA:P5; pB:P5; pC:P5; pD:P5; pE:P5; pF:P5; pG:P5; pH:P5; pI:P5; pJ:P5 }.
Definition poly0 : Poly := mkP zero5 zero5 zero5 zero5 zero5 zero5 zero5 zero5 zero5 zero5.
Definition pok (p : Poly) : bool :=
  let (a,b,c,d,e,f,g,h,i,j) := p in
  ok5 a && ok5 b && ok5 c && ok5 d && ok5 e && ok5 f && ok5 g && ok5 h && ok5 i && ok5 j.
Definition padd (p r : Poly) : Poly :=
  let (a,b,c,d,e,f,g,h,i,j) := p in let (a',b',c',d',e',f',g',h',i',j') := r in
  mkP (add5 a a') (add5 b b') (add5 c c') (add5 d d') (add5 e e') (add5 f f') (add5 g g') (add5 h h') (add5 i i') (add5 j j').
Definition digitUD (p : Poly) : Poly :=
  let (A,B,C,D,E,F,G,H,I,J) := p in
  mkP
   (nrm (16 * q0 A) (16 * q1 A) (16 * q2 A) (16 * q3 A) (16 * q4 A))
   (nrm (4 * q0 B - 8 * q0 A) (4 * q1 B - 8 * q1 A) (4 * q2 B - 8 * q2 A) (4 * q3 B - 8 * q3 A) (4 * q4 B - 8 * q4 A))
   (nrm (16 * q0 C) (16 * q1 C) (16 * q2 C) (16 * q3 C) (16 * q4 C))
   (nrm (q0 A + q0 D - q0 B) (q1 A + q1 D - q1 B) (q2 A + q2 D - q2 B) (q3 A + q3 D - q3 B) (q4 A + q4 D - q4 B))
   (nrm (4 * q0 E - 4 * q0 C) (4 * q1 E - 4 * q1 C) (4 * q2 E - 4 * q2 C) (4 * q3 E - 4 * q3 C) (4 * q4 E - 4 * q4 C))
   (nrm (16 * q0 F) (16 * q1 F) (16 * q2 F) (16 * q3 F) (16 * q4 F))
   (nrm (40 * q0 B + 4 * q0 G - 144 * q0 A - 4 * q0 C) (40 * q1 B + 4 * q1 G - 144 * q1 A - 4 * q1 C) (40 * q2 B + 4 * q2 G - 144 * q2 A - 4 * q2 C) (40 * q3 B + 4 * q3 G - 144 * q3 A - 4 * q3 C) (40 * q4 B + 4 * q4 G - 144 * q4 A - 4 * q4 C))
   (nrm (36 * q0 A + q0 C + 20 * q0 D + q0 H - 28 * q0 B - q0 E - q0 G) (36 * q1 A + q1 C + 20 * q1 D + q1 H - 28 * q1 B - q1 E - q1 G) (36 * q2 A + q2 C + 20 * q2 D + q2 H - 28 * q2 B - q2 E - q2 G) (36 * q3 A + q3 C + 20 * q3 D + q3 H - 28 * q3 B - q3 E - q3 G) (36 * q4 A + q4 C + 20 * q4 D + q4 H - 28 * q4 B - q4 E - q4 G))
   (nrm (40 * q0 E + 4 * q0 I - 72 * q0 C - 8 * q0 F) (40 * q1 E + 4 * q1 I - 72 * q1 C - 8 * q1 F) (40 * q2 E + 4 * q2 I - 72 * q2 C - 8 * q2 F) (40 * q3 E + 4 * q3 I - 72 * q3 C - 8 * q3 F) (40 * q4 E + 4 * q4 I - 72 * q4 C - 8 * q4 F))
   (nrm (324 * q0 A + 18 * q0 C + 100 * q0 D + q0 F + 10 * q0 H + q0 J - 180 * q0 B - 10 * q0 E - 18 * q0 G - q0 I) (324 * q1 A + 18 * q1 C + 100 * q1 D + q1 F + 10 * q1 H + q1 J - 180 * q1 B - 10 * q1 E - 18 * q1 G - q1 I) (324 * q2 A + 18 * q2 C + 100 * q2 D + q2 F + 10 * q2 H + q2 J - 180 * q2 B - 10 * q2 E - 18 * q2 G - q2 I) (324 * q3 A + 18 * q3 C + 100 * q3 D + q3 F + 10 * q3 H + q3 J - 180 * q3 B - 10 * q3 E - 18 * q3 G - q3 I) (324 * q4 A + 18 * q4 C + 100 * q4 D + q4 F + 10 * q4 H + q4 J - 180 * q4 B - 10 * q4 E - 18 * q4 G - q4 I))
  .
Definition digitVD (p : Poly) : Poly :=
  let (A,B,C,D,E,F,G,H,I,J) := p in
  mkP
   (nrm (16 * q0 A) (16 * q1 A) (16 * q2 A) (16 * q3 A) (16 * q4 A))
   (nrm (4 * q0 B - 8 * q0 A) (4 * q1 B - 8 * q1 A) (4 * q2 B - 8 * q2 A) (4 * q3 B - 8 * q3 A) (4 * q4 B - 8 * q4 A))
   (nrm (16 * q0 C) (16 * q1 C) (16 * q2 C) (16 * q3 C) (16 * q4 C))
   (nrm (q0 A + q0 D - q0 B) (q1 A + q1 D - q1 B) (q2 A + q2 D - q2 B) (q3 A + q3 D - q3 B) (q4 A + q4 D - q4 B))
   (nrm (4 * q0 E - 4 * q0 C) (4 * q1 E - 4 * q1 C) (4 * q2 E - 4 * q2 C) (4 * q3 E - 4 * q3 C) (4 * q4 E - 4 * q4 C))
   (nrm (16 * q0 F) (16 * q1 F) (16 * q2 F) (16 * q3 F) (16 * q4 F))
   (nrm (56 * q0 B + 4 * q0 G - 240 * q0 A - 4 * q0 C) (56 * q1 B + 4 * q1 G - 240 * q1 A - 4 * q1 C) (56 * q2 B + 4 * q2 G - 240 * q2 A - 4 * q2 C) (56 * q3 B + 4 * q3 G - 240 * q3 A - 4 * q3 C) (56 * q4 B + 4 * q4 G - 240 * q4 A - 4 * q4 C))
   (nrm (60 * q0 A + q0 C + 28 * q0 D + q0 H - 44 * q0 B - q0 E - q0 G) (60 * q1 A + q1 C + 28 * q1 D + q1 H - 44 * q1 B - q1 E - q1 G) (60 * q2 A + q2 C + 28 * q2 D + q2 H - 44 * q2 B - q2 E - q2 G) (60 * q3 A + q3 C + 28 * q3 D + q3 H - 44 * q3 B - q3 E - q3 G) (60 * q4 A + q4 C + 28 * q4 D + q4 H - 44 * q4 B - q4 E - q4 G))
   (nrm (56 * q0 E + 4 * q0 I - 120 * q0 C - 8 * q0 F) (56 * q1 E + 4 * q1 I - 120 * q1 C - 8 * q1 F) (56 * q2 E + 4 * q2 I - 120 * q2 C - 8 * q2 F) (56 * q3 E + 4 * q3 I - 120 * q3 C - 8 * q3 F) (56 * q4 E + 4 * q4 I - 120 * q4 C - 8 * q4 F))
   (nrm (900 * q0 A + 30 * q0 C + 196 * q0 D + q0 F + 14 * q0 H + q0 J - 420 * q0 B - 14 * q0 E - 30 * q0 G - q0 I) (900 * q1 A + 30 * q1 C + 196 * q1 D + q1 F + 14 * q1 H + q1 J - 420 * q1 B - 14 * q1 E - 30 * q1 G - q1 I) (900 * q2 A + 30 * q2 C + 196 * q2 D + q2 F + 14 * q2 H + q2 J - 420 * q2 B - 14 * q2 E - 30 * q2 G - q2 I) (900 * q3 A + 30 * q3 C + 196 * q3 D + q3 F + 14 * q3 H + q3 J - 420 * q3 B - 14 * q3 E - 30 * q3 G - q3 I) (900 * q4 A + 30 * q4 C + 196 * q4 D + q4 F + 14 * q4 H + q4 J - 420 * q4 B - 14 * q4 E - 30 * q4 G - q4 I))
  .
Definition digitDD (p : Poly) : Poly :=
  let (A,B,C,D,E,F,G,H,I,J) := p in
  mkP
   (nrm (16 * q0 A) (16 * q1 A) (16 * q2 A) (16 * q3 A) (16 * q4 A))
   (nrm (4 * q0 B - 24 * q0 A) (4 * q1 B - 24 * q1 A) (4 * q2 B - 24 * q2 A) (4 * q3 B - 24 * q3 A) (4 * q4 B - 24 * q4 A))
   (nrm (16 * q0 C) (16 * q1 C) (16 * q2 C) (16 * q3 C) (16 * q4 C))
   (nrm (9 * q0 A + q0 D - 3 * q0 B) (9 * q1 A + q1 D - 3 * q1 B) (9 * q2 A + q2 D - 3 * q2 B) (9 * q3 A + q3 D - 3 * q3 B) (9 * q4 A + q4 D - 3 * q4 B))
   (nrm (4 * q0 E - 12 * q0 C) (4 * q1 E - 12 * q1 C) (4 * q2 E - 12 * q2 C) (4 * q3 E - 12 * q3 C) (4 * q4 E - 12 * q4 C))
   (nrm (16 * q0 F) (16 * q1 F) (16 * q2 F) (16 * q3 F) (16 * q4 F))
   (nrm (24 * q0 B + 4 * q0 G - 96 * q0 A - 12 * q0 C) (24 * q1 B + 4 * q1 G - 96 * q1 A - 12 * q1 C) (24 * q2 B + 4 * q2 G - 96 * q2 A - 12 * q2 C) (24 * q3 B + 4 * q3 G - 96 * q3 A - 12 * q3 C) (24 * q4 B + 4 * q4 G - 96 * q4 A - 12 * q4 C))
   (nrm (72 * q0 A + 9 * q0 C + 12 * q0 D + q0 H - 30 * q0 B - 3 * q0 E - 3 * q0 G) (72 * q1 A + 9 * q1 C + 12 * q1 D + q1 H - 30 * q1 B - 3 * q1 E - 3 * q1 G) (72 * q2 A + 9 * q2 C + 12 * q2 D + q2 H - 30 * q2 B - 3 * q2 E - 3 * q2 G) (72 * q3 A + 9 * q3 C + 12 * q3 D + q3 H - 30 * q3 B - 3 * q3 E - 3 * q3 G) (72 * q4 A + 9 * q4 C + 12 * q4 D + q4 H - 30 * q4 B - 3 * q4 E - 3 * q4 G))
   (nrm (24 * q0 E + 4 * q0 I - 48 * q0 C - 24 * q0 F) (24 * q1 E + 4 * q1 I - 48 * q1 C - 24 * q1 F) (24 * q2 E + 4 * q2 I - 48 * q2 C - 24 * q2 F) (24 * q3 E + 4 * q3 I - 48 * q3 C - 24 * q3 F) (24 * q4 E + 4 * q4 I - 48 * q4 C - 24 * q4 F))
   (nrm (144 * q0 A + 36 * q0 C + 36 * q0 D + 9 * q0 F + 6 * q0 H + q0 J - 72 * q0 B - 18 * q0 E - 12 * q0 G - 3 * q0 I) (144 * q1 A + 36 * q1 C + 36 * q1 D + 9 * q1 F + 6 * q1 H + q1 J - 72 * q1 B - 18 * q1 E - 12 * q1 G - 3 * q1 I) (144 * q2 A + 36 * q2 C + 36 * q2 D + 9 * q2 F + 6 * q2 H + q2 J - 72 * q2 B - 18 * q2 E - 12 * q2 G - 3 * q2 I) (144 * q3 A + 36 * q3 C + 36 * q3 D + 9 * q3 F + 6 * q3 H + q3 J - 72 * q3 B - 18 * q3 E - 12 * q3 G - 3 * q3 I) (144 * q4 A + 36 * q4 C + 36 * q4 D + 9 * q4 F + 6 * q4 H + q4 J - 72 * q4 B - 18 * q4 E - 12 * q4 G - 3 * q4 I))
  .

Definition shift (y : int) (p : Poly) : option Poly :=
  let (A,B,C,D,E,F,G,H,I,J) := p in
  let yA := addk C y A in
  let yB := addk (add5 E G) y B in
  let yD := addk H y D in
  if ok5 yA && ok5 yB && ok5 yD then
    Some (mkP A B (addk yA y A) D (addk E y B) (addk F y yA) (addk G y B) (addk yD y D) (addk I y yB) (addk J y yD))
  else None.

(** z + k1*x + k2*y, one normalisation *)
Definition add2k (z : P5) (k1 : int) (x : P5) (k2 : int) (y : P5) : P5 :=
  nrm (q0 z + k1 * q0 x + k2 * q0 y) (q1 z + k1 * q1 x + k2 * q1 y) (q2 z + k1 * q2 x + k2 * q2 y) (q3 z + k1 * q3 x + k2 * q3 y) (q4 z + k1 * q4 x + k2 * q4 y).
Definition add1s1 (z : P5) (k1 : int) (x : P5) (k2 : int) (y : P5) : P5 :=
  nrm (q0 z + k1 * q0 x - k2 * q0 y) (q1 z + k1 * q1 x - k2 * q1 y) (q2 z + k1 * q2 x - k2 * q2 y) (q3 z + k1 * q3 x - k2 * q3 y) (q4 z + k1 * q4 x - k2 * q4 y).
Definition sub2k (z : P5) (k1 : int) (x : P5) (k2 : int) (y : P5) : P5 :=
  nrm (q0 z - k1 * q0 x - k2 * q0 y) (q1 z - k1 * q1 x - k2 * q1 y) (q2 z - k1 * q2 x - k2 * q2 y) (q3 z - k1 * q3 x - k2 * q3 y) (q4 z - k1 * q4 x - k2 * q4 y).
(** letters DD: 90 X - 90 Z - 144 summed over visits *)
Definition pairDD (p : Poly) (n m1 : int) (m2 : P5) : Poly :=
  let (A,B,C,D,E,F,G,H,I,J) := p in
  let pn := pnat n in let pm := pnat m1 in
  mkP A B C D E F (addk G 90 pn) (subk H 90 pn) (addk I 90 pm) (sub2k J 90 pm 144 pn).
(** letters uD or vD: 4 X Z + kx X - kz Z - k0 *)
Definition pairUV (kx kz k0 : int) (p : Poly) (n m1 : int) (m2 : P5) : Poly :=
  let (A,B,C,D,E,F,G,H,I,J) := p in
  let pn := pnat n in let pm := pnat m1 in
  mkP A (addk B 4 pn) C D (addk E 4 pm) F (add2k G 4 pm kx pn) (subk H kz pn) (add2k I 4 m2 kx pm) (sub2k J kz pm k0 pn).
(** a stop after one letter: 32 X^2 - xz X Z + zz Z^2 - kx X + kz Z + k0 *)
Definition stopQ (xz zz kx kz k0 : int) (p : Poly) (n m1 : int) (m2 : P5) : Poly :=
  let (A,B,C,D,E,F,G,H,I,J) := p in
  let pn := pnat n in let pm := pnat m1 in
  mkP (addk A 32 pn) (subk B xz pn) (addk C 64 pm) (addk D zz pn) (subk E xz pm) (addk F 32 m2)
      (sub2k G xz pm kx pn) (add2k H (2 * zz) pm kz pn) (sub2k I xz m2 kx pm)
      (add2k (add1s1 J zz m2 0 pn) kz pm k0 pn).

(** ** Lemmas of the band *)

Local Close Scope uint63_scope.
Local Open Scope Z_scope.

(** ** Meaning *)
Notation PA := 2147483648%Z.
Notation PB := 4611686018427387904%Z.
Notation PC := 9903520314283042199192993792%Z.
Notation PD := 21267647932558653966460912964485513216%Z.
Notation L61 := 2305843008139952128%Z.   (* 2^61 - 2^30 *)
Notation H61 := 2305843009213693952%Z.   (* 2^61 *)

Definition val5 (x : P5) : Z := phi (q0 x) + phi (q1 x) * PA + phi (q2 x) * PB + phi (q3 x) * PC + sg (q4 x) * PD.
Definition good5 (m : Z) (x : P5) : Prop :=
  phi (q0 x) < PA /\ phi (q1 x) < PA /\ phi (q2 x) < PA /\ phi (q3 x) < PA /\ Z.abs (sg (q4 x)) <= m.

Lemma cg_sg h : cg h (sg h).
Proof.
  unfold cg, sg. destruct (phi h <? P62) eqn:E; [reflexivity|].
  replace (phi h - P63) with (phi h + (-1) * P63) by ring. rewrite Z.mod_add by lia. reflexivity.
Qed.

Lemma step31 (c : int) (Y : Z) : cg c (Y + H61) -> - H61 <= Y -> Y + H61 < P63 ->
  phi (c land M31)%uint63 = Y mod PA /\ cg ((c >> 31) - OFFC)%uint63 (Y / PA).
Proof.
  intros H L U. assert (Ec : phi c = Y + H61) by (apply phi_of_cg; [exact H|lia]). split.
  - unfold M31. rewrite phi_land_31, Ec. replace (Y + H61) with (Y + 1073741824 * PA) by lia. rewrite Z.mod_add by lia. reflexivity.
  - replace (Y / PA) with ((Y + 1073741824 * PA) / PA - 1073741824) by (rewrite Z.div_add by lia; ring).
    apply cg_sub.
    + unfold cg. rewrite phi_lsr_31, Ec. replace (Y + 1073741824 * PA) with (Y + H61) by lia. reflexivity.
    + reflexivity.
Qed.

Lemma dv31 (Y : Z) : - H61 <= Y <= 5000000000000000000 ->
  - 1073741824 <= Y / PA <= 2328306437 /\ Y = PA * (Y / PA) + Y mod PA /\ 0 <= Y mod PA < PA.
Proof. intros H. Z.div_mod_to_equations. lia. Qed.

Theorem nrm_spec x0 x1 x2 x3 x4 X0 X1 X2 X3 X4 m :
  cg x0 X0 -> cg x1 X1 -> cg x2 X2 -> cg x3 X3 -> cg x4 X4 ->
  - H61 <= X0 <= 4611686018427387904 -> - L61 <= X1 <= 4611686018427387904 -> - L61 <= X2 <= 4611686018427387904 -> - L61 <= X3 <= 4611686018427387904 ->
  Z.abs X4 <= m -> m <= H61 ->
  good5 (m + 4294967296) (nrm x0 x1 x2 x3 x4) /\ val5 (nrm x0 x1 x2 x3 x4) = X0 + X1 * PA + X2 * PB + X3 * PC + X4 * PD.
Proof.
  intros C0 C1 C2 C3 C4 B0 B1 B2 B3 B4 Bm. unfold nrm. cbv zeta.
  assert (F0 : cg (x0 + OFF)%uint63 (X0 + H61)) by (apply cg_add; [exact C0|reflexivity]).
  destruct (step31 _ X0 F0 ltac:(lia) ltac:(lia)) as [L0 D0]. destruct (dv31 X0 ltac:(lia)) as (E0a & E0b & E0c).
  set (d0 := X0 / PA) in *. set (r0 := X0 mod PA) in *. clearbody d0 r0.
  assert (F1 : cg (x1 + OFF + ((x0 + OFF) >> 31 - OFFC))%uint63 ((X1 + d0) + H61)).
  { replace (X1 + d0 + H61) with (X1 + H61 + d0) by ring. apply cg_add; [apply cg_add; [exact C1|reflexivity]|exact D0]. }
  destruct (step31 _ (X1 + d0) F1 ltac:(lia) ltac:(lia)) as [L1 D1]. destruct (dv31 (X1 + d0) ltac:(lia)) as (E1a & E1b & E1c).
  set (d1 := (X1 + d0) / PA) in *. set (r1 := (X1 + d0) mod PA) in *. clearbody d1 r1.
  assert (F2 : cg (x2 + OFF + ((x1 + OFF + ((x0 + OFF) >> 31 - OFFC)) >> 31 - OFFC))%uint63 ((X2 + d1) + H61)).
  { replace (X2 + d1 + H61) with (X2 + H61 + d1) by ring. apply cg_add; [apply cg_add; [exact C2|reflexivity]|exact D1]. }
  destruct (step31 _ (X2 + d1) F2 ltac:(lia) ltac:(lia)) as [L2 D2]. destruct (dv31 (X2 + d1) ltac:(lia)) as (E2a & E2b & E2c).
  set (d2 := (X2 + d1) / PA) in *. set (r2 := (X2 + d1) mod PA) in *. clearbody d2 r2.
  assert (F3 : cg (x3 + OFF + ((x2 + OFF + ((x1 + OFF + ((x0 + OFF) >> 31 - OFFC)) >> 31 - OFFC)) >> 31 - OFFC))%uint63 ((X3 + d2) + H61)).
  { replace (X3 + d2 + H61) with (X3 + H61 + d2) by ring. apply cg_add; [apply cg_add; [exact C3|reflexivity]|exact D2]. }
  destruct (step31 _ (X3 + d2) F3 ltac:(lia) ltac:(lia)) as [L3 D3]. destruct (dv31 (X3 + d2) ltac:(lia)) as (E3a & E3b & E3c).
  set (d3 := (X3 + d2) / PA) in *. set (r3 := (X3 + d2) mod PA) in *. clearbody d3 r3.
  assert (S4 : sg (x4 + ((x3 + OFF + ((x2 + OFF + ((x1 + OFF + ((x0 + OFF) >> 31 - OFFC)) >> 31 - OFFC)) >> 31 - OFFC)) >> 31 - OFFC))%uint63 = X4 + d3).
  { apply sg_of; [lia|]. change (phi (x4 + ((x3 + OFF + ((x2 + OFF + ((x1 + OFF + ((x0 + OFF) >> 31 - OFFC)) >> 31 - OFFC)) >> 31 - OFFC)) >> 31 - OFFC))%uint63 =
       (X4 + d3) mod P63). pose proof (cg_add _ _ _ _ C4 D3) as X. unfold cg in X.
    rewrite Z.mod_small in X by (apply phi_bd63). exact X. }
  unfold good5, val5. cbn [q0 q1 q2 q3 q4]. rewrite L0, L1, L2, L3, S4. split.
  - repeat split; try lia.
  - lia.
Qed.

(** Reading an int expression as an integer, to feed [nrm_spec]. *)
Ltac zof t :=
  lazymatch t with
  | (?a + ?b)%uint63 => let x := zof a in let y := zof b in constr:((x + y)%Z)
  | (?a - ?b)%uint63 => let x := zof a in let y := zof b in constr:((x - y)%Z)
  | (?a * ?b)%uint63 => let x := zof a in let y := zof b in constr:((x * y)%Z)
  | q4 ?x => constr:(sg (q4 x))
  | q0 ?x => constr:(phi (q0 x))
  | q1 ?x => constr:(phi (q1 x))
  | q2 ?x => constr:(phi (q2 x))
  | q3 ?x => constr:(phi (q3 x))
  | _ => let v := eval cbv in (phi t) in v
  end.
Ltac cgz :=
  repeat first
    [ apply cg_add | apply cg_sub | apply cg_mul | apply cg_sg | apply cg_refl | (unfold cg; reflexivity) ].

Lemma bd_good m x : good5 m x -> 0 <= phi (q0 x) < PA /\ 0 <= phi (q1 x) < PA /\ 0 <= phi (q2 x) < PA /\ 0 <= phi (q3 x) < PA /\ - m <= sg (q4 x) <= m.
Proof.
  intros (H0 & H1 & H2 & H3 & H4). pose proof (phi_bd63 (q0 x)). pose proof (phi_bd63 (q1 x)). pose proof (phi_bd63 (q2 x)). pose proof (phi_bd63 (q3 x)). lia.
Qed.
Lemma good_mono m1 m2 x : m1 <= m2 -> good5 m1 x -> good5 m2 x.
Proof. intros H (H0 & H1 & H2 & H3 & H4). unfold good5. repeat split; try assumption. lia. Qed.

Lemma addk_spec z k x m1 m2 : good5 m1 z -> good5 m2 x -> phi k < 1073741824 -> 0 <= m2 -> m1 + phi k * m2 <= H61 ->
  good5 (m1 + phi k * m2 + 4294967296) (addk z k x) /\ val5 (addk z k x) = val5 z + phi k * val5 x.
Proof.
  intros Gz Gx Hk M0 Hm. destruct (bd_good _ _ Gz) as (Z0 & Z1 & Z2 & Z3 & Z4). destruct (bd_good _ _ Gx) as (X0 & X1 & X2 & X3 & X4).
  pose proof (phi_bd63 k) as Bk.
  assert (Pk : forall v, 0 <= v < PA -> 0 <= phi k * v <= 1073741823 * 2147483647) by (intros v Hv; split; [apply Z.mul_nonneg_nonneg; lia|apply Z.mul_le_mono_nonneg; lia]).
  pose proof (Pk _ X0) as P0. pose proof (Pk _ X1) as P1. pose proof (Pk _ X2) as P2. pose proof (Pk _ X3) as P3.
  assert (P4 : Z.abs (sg (q4 z) + phi k * sg (q4 x)) <= m1 + phi k * m2).
  { assert (A : phi k * - m2 <= phi k * sg (q4 x)) by (apply Z.mul_le_mono_nonneg_l; lia).
    assert (B : phi k * sg (q4 x) <= phi k * m2) by (apply Z.mul_le_mono_nonneg_l; lia). lia. }
  destruct (nrm_spec (q0 z + k * q0 x) (q1 z + k * q1 x) (q2 z + k * q2 x) (q3 z + k * q3 x) (q4 z + k * q4 x)
     (phi (q0 z) + phi k * phi (q0 x)) (phi (q1 z) + phi k * phi (q1 x)) (phi (q2 z) + phi k * phi (q2 x)) (phi (q3 z) + phi k * phi (q3 x)) (sg (q4 z) + phi k * sg (q4 x)) (m1 + phi k * m2))
    as [G V]; try (cgz; fail); try lia.
  split; [exact G|]. unfold addk. rewrite V. unfold val5. ring.
Qed.
Lemma subk_spec z k x m1 m2 : good5 m1 z -> good5 m2 x -> phi k < 1073741824 -> 0 <= m2 -> m1 + phi k * m2 <= H61 ->
  good5 (m1 + phi k * m2 + 4294967296) (subk z k x) /\ val5 (subk z k x) = val5 z - phi k * val5 x.
Proof.
  intros Gz Gx Hk M0 Hm. destruct (bd_good _ _ Gz) as (Z0 & Z1 & Z2 & Z3 & Z4). destruct (bd_good _ _ Gx) as (X0 & X1 & X2 & X3 & X4).
  pose proof (phi_bd63 k) as Bk.
  assert (Pk : forall v, 0 <= v < PA -> 0 <= phi k * v <= 1073741823 * 2147483647) by (intros v Hv; split; [apply Z.mul_nonneg_nonneg; lia|apply Z.mul_le_mono_nonneg; lia]).
  pose proof (Pk _ X0) as P0. pose proof (Pk _ X1) as P1. pose proof (Pk _ X2) as P2. pose proof (Pk _ X3) as P3.
  assert (P4 : Z.abs (sg (q4 z) - phi k * sg (q4 x)) <= m1 + phi k * m2).
  { assert (A : phi k * - m2 <= phi k * sg (q4 x)) by (apply Z.mul_le_mono_nonneg_l; lia).
    assert (B : phi k * sg (q4 x) <= phi k * m2) by (apply Z.mul_le_mono_nonneg_l; lia). lia. }
  destruct (nrm_spec (q0 z - k * q0 x) (q1 z - k * q1 x) (q2 z - k * q2 x) (q3 z - k * q3 x) (q4 z - k * q4 x)
     (phi (q0 z) - phi k * phi (q0 x)) (phi (q1 z) - phi k * phi (q1 x)) (phi (q2 z) - phi k * phi (q2 x)) (phi (q3 z) - phi k * phi (q3 x)) (sg (q4 z) - phi k * sg (q4 x)) (m1 + phi k * m2))
    as [G V]; try (cgz; fail); try lia.
  split; [exact G|]. unfold subk. rewrite V. unfold val5. ring.
Qed.
Lemma add5_spec z x m1 m2 : good5 m1 z -> good5 m2 x -> m1 + m2 <= H61 ->
  good5 (m1 + m2 + 4294967296) (add5 z x) /\ val5 (add5 z x) = val5 z + val5 x.
Proof.
  intros Gz Gx Hm. destruct (bd_good _ _ Gz) as (Z0 & Z1 & Z2 & Z3 & Z4). destruct (bd_good _ _ Gx) as (X0 & X1 & X2 & X3 & X4).
  destruct (nrm_spec (q0 z + q0 x) (q1 z + q1 x) (q2 z + q2 x) (q3 z + q3 x) (q4 z + q4 x)
     (phi (q0 z) + phi (q0 x)) (phi (q1 z) + phi (q1 x)) (phi (q2 z) + phi (q2 x)) (phi (q3 z) + phi (q3 x)) (sg (q4 z) + sg (q4 x)) (m1 + m2))
    as [G V]; try (cgz; fail); try lia.
  split; [exact G|]. unfold add5. rewrite V. unfold val5. ring.
Qed.
Lemma pnat_spec k : good5 0 (pnat k) /\ val5 (pnat k) = phi k.
Proof.
  unfold good5, val5, pnat. cbn [q0 q1 q2 q3 q4]. unfold M31. rewrite !phi_land_31.
  pose proof (phi_bd63 k) as Bk.
  assert (E2 : phi (k >> 62)%uint63 = phi k / PB) by (rewrite lsr_spec; reflexivity).
  assert (E1 : phi (k >> 31)%uint63 = phi k / PA) by (rewrite lsr_spec; reflexivity).
  rewrite E1, E2. change (phi 0%uint63) with 0. change (sg 0%uint63) with 0.
  generalize (phi k) Bk. intros v Bv. clear - Bv.
  assert (Dd : v / PB = v / PA / PA) by (rewrite Z.div_div by lia; reflexivity).
  set (u := v / PA). assert (Eu : v = PA * u + v mod PA /\ 0 <= v mod PA < PA) by (unfold u; Z.div_mod_to_equations; lia).
  assert (Bu : 0 <= u < 4294967296) by (unfold u; Z.div_mod_to_equations; lia).
  rewrite Dd. clear Dd. fold u. clearbody u.
  assert (Ev : u = PA * (u / PA) + u mod PA /\ 0 <= u mod PA < PA /\ 0 <= u / PA < PA) by (clear - Bu; Z.div_mod_to_equations; lia).
  set (r0 := v mod PA) in *. set (r1 := u mod PA) in *. set (q := u / PA) in *. clearbody r0 r1 q. unfold good5.
  split; [repeat split; lia|lia].
Qed.
Lemma zero5_spec : good5 0 zero5 /\ val5 zero5 = 0.
Proof. split; [repeat split; vm_compute; try reflexivity; discriminate|reflexivity]. Qed.

(** ** Polynomials in (b, S, g) *)
Definition pval (p : Poly) (b S g : Z) : Z :=
  val5 (pA p) * (b * b) + val5 (pB p) * (b * S) + val5 (pC p) * (b * g) + val5 (pD p) * (S * S) + val5 (pE p) * (S * g) + val5 (pF p) * (g * g)
  + val5 (pG p) * b + val5 (pH p) * S + val5 (pI p) * g + val5 (pJ p).
Definition pgood (m : Z) (p : Poly) : Prop :=
  good5 m (pA p) /\ good5 m (pB p) /\ good5 m (pC p) /\ good5 m (pD p) /\ good5 m (pE p) /\ good5 m (pF p) /\ good5 m (pG p) /\ good5 m (pH p) /\ good5 m (pI p) /\ good5 m (pJ p).

Lemma ok5_good x m : good5 m x -> ok5 x = true -> good5 1073741824 x.
Proof.
  intros (H0 & H1 & H2 & H3 & _) H. unfold ok5 in H. apply ltb_true in H.
  pose proof (cg_add _ _ _ _ (cg_sg (q4 x)) (cg_refl 1073741824%uint63)) as C.
  change (phi 1073741824%uint63) with 1073741824 in C. change (phi 2147483648%uint63) with 2147483648 in H.
  pose proof (sg_bd (q4 x)) as Bs. pose proof (phi_bd63 (q4 x + 1073741824)%uint63) as Bp.
  unfold cg in C. rewrite Z.mod_small in C by exact Bp.
  assert (A : Z.abs (sg (q4 x)) <= 1073741824).
  { (* the sum is below 2^31 and congruent to s + 2^30, so s is in range *)
    set (u := phi (q4 x + 1073741824)%uint63) in *. set (s := sg (q4 x)) in *. clearbody u s.
    assert (E : (s + 1073741824) mod P63 = s + 1073741824 \/ (s + 1073741824) mod P63 = s + 1073741824 + P63).
    { destruct (Z.le_gt_cases 0 (s + 1073741824)) as [L|L].
      - left. apply Z.mod_small. lia.
      - right. replace (s + 1073741824) with ((s + 1073741824 + P63) + (-1) * P63) at 1 by ring. rewrite Z.mod_add by lia. apply Z.mod_small. lia. }
    destruct E as [E|E]; lia. }
  unfold good5. repeat split; assumption.
Qed.

Lemma pok_good p m : pgood m p -> pok p = true -> pgood 1073741824 p.
Proof.
  destruct p as [a b c d e f g h i j]. intros (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10) H. cbn [pok] in H. unfold pok in H.
  repeat (apply andb_prop in H; destruct H as [H ?]).
  cbn [pA pB pC pD pE pF pG pH pI pJ] in *.
  refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _))))))))); cbn [pA pB pC pD pE pF pG pH pI pJ]; eapply ok5_good; eassumption.
Qed.

(** A linear combination of limbs, normalised once. *)
Ltac nrm_at m :=
  lazymatch goal with
  | |- context [nrm ?x0 ?x1 ?x2 ?x3 ?x4] =>
    let X0 := zof x0 in let X1 := zof x1 in let X2 := zof x2 in let X3 := zof x3 in let X4 := zof x4 in
    let G := fresh "G" in let V := fresh "V" in
    destruct (nrm_spec x0 x1 x2 x3 x4 X0 X1 X2 X3 X4 m) as [G V]; [cgz..| lia | lia | lia | lia | lia | lia | ]
  end.

Ltac unpack5 :=
  repeat match goal with
  | H : good5 _ _ |- _ =>
    let a := fresh "B5" in let b := fresh "B5" in let c := fresh "B5" in let d := fresh "B5" in let e := fresh "B5" in
    destruct (bd_good _ _ H) as (a & b & c & d & e); clear H
  end.

Ltac nrm_good m :=
  lazymatch goal with
  | |- good5 _ (nrm ?x0 ?x1 ?x2 ?x3 ?x4) =>
    let X0 := zof x0 in let X1 := zof x1 in let X2 := zof x2 in let X3 := zof x3 in let X4 := zof x4 in
    let G := fresh "G" in let V := fresh "V" in
    destruct (nrm_spec x0 x1 x2 x3 x4 X0 X1 X2 X3 X4 m) as [G V];
    [cgz..| lia | lia | lia | lia | lia | lia | eapply good_mono; [|exact G]; lia ]
  end.
Ltac nrm_vals :=
  repeat lazymatch goal with
  | |- context [val5 (nrm ?x0 ?x1 ?x2 ?x3 ?x4)] =>
    let X0 := zof x0 in let X1 := zof x1 in let X2 := zof x2 in let X3 := zof x3 in let X4 := zof x4 in
    let G := fresh "G" in let V := fresh "V" in
    destruct (nrm_spec x0 x1 x2 x3 x4 X0 X1 X2 X3 X4 2199023255552) as [G V];
    [cgz..| lia | lia | lia | lia | lia | lia | rewrite V; clear G V ]
  end.

Ltac split10 := refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _))))))))).

Definition GD : Z := 2203318222848.   (* 2^41 + 2^32 *)
Lemma digitUD_spec p b S g : pgood 1073741824 p ->
  pgood GD (digitUD p) /\ pval (digitUD p) b S g = pval p (4 * b - S - 18) (S + 10) (4 * g - 1).
Proof.
  destruct p as [Ap Bp Cp Dp Ep Fp Gp Hp Ip Jp]. intros (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10).
  cbn [pA pB pC pD pE pF pG pH pI pJ] in *. unfold digitUD. cbv beta iota zeta. unpack5. unfold GD, pgood, pval. cbn [pA pB pC pD pE pF pG pH pI pJ]. split.
  - split10; nrm_good 2199023255552.
  - nrm_vals. unfold val5. ring.
Qed.
Lemma digitVD_spec p b S g : pgood 1073741824 p ->
  pgood GD (digitVD p) /\ pval (digitVD p) b S g = pval p (4 * b - S - 30) (S + 14) (4 * g - 1).
Proof.
  destruct p as [Ap Bp Cp Dp Ep Fp Gp Hp Ip Jp]. intros (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10).
  cbn [pA pB pC pD pE pF pG pH pI pJ] in *. unfold digitVD. cbv beta iota zeta. unpack5. unfold GD, pgood, pval. cbn [pA pB pC pD pE pF pG pH pI pJ]. split.
  - split10; nrm_good 2199023255552.
  - nrm_vals. unfold val5. ring.
Qed.
Lemma digitDD_spec p b S g : pgood 1073741824 p ->
  pgood GD (digitDD p) /\ pval (digitDD p) b S g = pval p (4 * b - 3 * S - 12) (S + 6) (4 * g - 3).
Proof.
  destruct p as [Ap Bp Cp Dp Ep Fp Gp Hp Ip Jp]. intros (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10).
  cbn [pA pB pC pD pE pF pG pH pI pJ] in *. unfold digitDD. cbv beta iota zeta. unpack5. unfold GD, pgood, pval. cbn [pA pB pC pD pE pF pG pH pI pJ]. split.
  - split10; nrm_good 2199023255552.
  - nrm_vals. unfold val5. ring.
Qed.

Lemma padd_spec p r b S g m1 m2 : pgood m1 p -> pgood m2 r -> m1 + m2 <= H61 ->
  pgood (m1 + m2 + 4294967296) (padd p r) /\ pval (padd p r) b S g = pval p b S g + pval r b S g.
Proof.
  destruct p as [Ap Bp Cp Dp Ep Fp Gp Hp Ip Jp]. destruct r as [Ar Br Cr Dr Er Fr Gr Hr Ir Jr].
  intros (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10) (K1 & K2 & K3 & K4 & K5 & K6 & K7 & K8 & K9 & K10) Hm.
  cbn [pA pB pC pD pE pF pG pH pI pJ] in *. unfold padd, pgood, pval. cbn [pA pB pC pD pE pF pG pH pI pJ].
  destruct (add5_spec _ _ _ _ G1 K1 Hm) as [a1 a2]. destruct (add5_spec _ _ _ _ G2 K2 Hm) as [b1 b2]. destruct (add5_spec _ _ _ _ G3 K3 Hm) as [c1 c2]. destruct (add5_spec _ _ _ _ G4 K4 Hm) as [d1 d2].
  destruct (add5_spec _ _ _ _ G5 K5 Hm) as [e1 e2]. destruct (add5_spec _ _ _ _ G6 K6 Hm) as [f1 f2]. destruct (add5_spec _ _ _ _ G7 K7 Hm) as [g1 g2]. destruct (add5_spec _ _ _ _ G8 K8 Hm) as [h1 h2].
  destruct (add5_spec _ _ _ _ G9 K9 Hm) as [i1 i2]. destruct (add5_spec _ _ _ _ G10 K10 Hm) as [j1 j2].
  split; [split10; assumption|]. rewrite a2, b2, c2, d2, e2, f2, g2, h2, i2, j2. ring.
Qed.

Lemma shift_spec y p s b S g : pgood 1073741824 p -> phi y < 1073741824 -> shift y p = Some s ->
  pgood H61 s /\ pval s b S g = pval p (b + g * phi y) (S + phi y) g.
Proof.
  destruct p as [Ap Bp Cp Dp Ep Fp Gp Hp Ip Jp]. intros (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10) Hy H.
  cbn [pA pB pC pD pE pF pG pH pI pJ] in *. unfold shift in H. cbv zeta in H.
  pose proof (phi_bd63 y) as By.
  assert (Ky : 0 <= phi y * 1073741824 <= 1152921504606846976) by (split; [apply Z.mul_nonneg_nonneg|]; lia).
  destruct (addk_spec Cp y Ap _ _ G3 G1 Hy ltac:(lia) ltac:(lia)) as [Ya Va].
  destruct (add5_spec Ep Gp _ _ G5 G7 ltac:(lia)) as [Yeg Veg].
  destruct (addk_spec _ y Bp _ _ Yeg G2 Hy ltac:(lia) ltac:(lia)) as [Yb Vb].
  destruct (addk_spec Hp y Dp _ _ G8 G4 Hy ltac:(lia) ltac:(lia)) as [Yd Vd].
  destruct (ok5 (addk Cp y Ap) && ok5 (addk (add5 Ep Gp) y Bp) && ok5 (addk Hp y Dp)) eqn:C; [|discriminate].
  injection H as <-. apply andb_prop in C. destruct C as [C O3]. apply andb_prop in C. destruct C as [O1 O2].
  pose proof (ok5_good _ _ Ya O1) as Ya'. pose proof (ok5_good _ _ Yb O2) as Yb'. pose proof (ok5_good _ _ Yd O3) as Yd'.
  set (yA := addk Cp y Ap) in *. set (yB := addk (add5 Ep Gp) y Bp) in *. set (yD := addk Hp y Dp) in *. clearbody yA yB yD.
  assert (Gm : forall z x, good5 1073741824 z -> good5 1073741824 x ->
     good5 H61 (addk z y x) /\ val5 (addk z y x) = val5 z + phi y * val5 x).
  { intros z x Gz Gx. destruct (addk_spec z y x _ _ Gz Gx Hy ltac:(lia) ltac:(lia)) as [U V]. split; [|exact V]. eapply good_mono; [|exact U]. lia. }
  destruct (Gm _ _ Ya' G1) as [a1 a2]. destruct (Gm _ _ G5 G2) as [b1 b2]. destruct (Gm _ _ G6 Ya') as [c1 c2]. destruct (Gm _ _ G7 G2) as [d1 d2].
  destruct (Gm _ _ Yd' G4) as [e1 e2]. destruct (Gm _ _ G9 Yb') as [f1 f2]. destruct (Gm _ _ G10 Yd') as [h1 h2].
  unfold pgood, pval. cbn [pA pB pC pD pE pF pG pH pI pJ]. split.
  - assert (Ml : forall x, good5 1073741824 x -> good5 H61 x) by (intros x; apply good_mono; lia).
    split10; first [assumption | apply Ml; assumption].
  - rewrite a2, b2, c2, d2, e2, f2, h2, Va, Vb, Veg, Vd. ring.
Qed.

Lemma add2k_spec z k1 x k2 y mz mx my : good5 mz z -> good5 mx x -> good5 my y -> phi k1 < 16384 -> phi k2 < 16384 -> 0 <= mx -> 0 <= my ->
  mz + phi k1 * mx + phi k2 * my <= H61 ->
  good5 (mz + phi k1 * mx + phi k2 * my + 4294967296) (add2k z k1 x k2 y) /\ val5 (add2k z k1 x k2 y) = val5 z + phi k1 * val5 x + phi k2 * val5 y.
Proof.
  intros Gz Gx Gy H1 H2 M1 M2 Hm. unfold add2k. destruct (bd_good _ _ Gz) as (Z0 & Z1 & Z2 & Z3 & Z4). destruct (bd_good _ _ Gx) as (X0 & X1 & X2 & X3 & X4). destruct (bd_good _ _ Gy) as (Y0 & Y1 & Y2 & Y3 & Y4).
  pose proof (phi_bd63 k1) as B1. pose proof (phi_bd63 k2) as B2.
  assert (P : forall k v, 0 <= phi k < 16384 -> 0 <= v < PA -> 0 <= phi k * v <= 16384 * PA) by (intros k v K V; split; [apply Z.mul_nonneg_nonneg; lia|apply Z.mul_le_mono_nonneg; lia]).
  assert (A1 : Z.abs (phi k1 * sg (q4 x)) <= phi k1 * mx).
  { rewrite Z.abs_mul, Z.abs_eq by lia. apply Z.mul_le_mono_nonneg_l; lia. }
  assert (A2 : Z.abs (phi k2 * sg (q4 y)) <= phi k2 * my).
  { rewrite Z.abs_mul, Z.abs_eq by lia. apply Z.mul_le_mono_nonneg_l; lia. }
  pose proof (P k1 _ ltac:(lia) X0). pose proof (P k1 _ ltac:(lia) X1). pose proof (P k1 _ ltac:(lia) X2). pose proof (P k1 _ ltac:(lia) X3).
  pose proof (P k2 _ ltac:(lia) Y0). pose proof (P k2 _ ltac:(lia) Y1). pose proof (P k2 _ ltac:(lia) Y2). pose proof (P k2 _ ltac:(lia) Y3).
  destruct (nrm_spec (q0 z + k1 * q0 x + k2 * q0 y) (q1 z + k1 * q1 x + k2 * q1 y) (q2 z + k1 * q2 x + k2 * q2 y) (q3 z + k1 * q3 x + k2 * q3 y) (q4 z + k1 * q4 x + k2 * q4 y)
     (phi (q0 z) + phi k1 * phi (q0 x) + phi k2 * phi (q0 y)) (phi (q1 z) + phi k1 * phi (q1 x) + phi k2 * phi (q1 y)) (phi (q2 z) + phi k1 * phi (q2 x) + phi k2 * phi (q2 y)) (phi (q3 z) + phi k1 * phi (q3 x) + phi k2 * phi (q3 y))
     (sg (q4 z) + phi k1 * sg (q4 x) + phi k2 * sg (q4 y)) (mz + phi k1 * mx + phi k2 * my)) as [G V]; try (cgz; fail); try lia.
  split; [exact G|]. rewrite V. unfold val5. ring.
Qed.
Lemma sub2k_spec z k1 x k2 y mz mx my : good5 mz z -> good5 mx x -> good5 my y -> phi k1 < 16384 -> phi k2 < 16384 -> 0 <= mx -> 0 <= my ->
  mz + phi k1 * mx + phi k2 * my <= H61 ->
  good5 (mz + phi k1 * mx + phi k2 * my + 4294967296) (sub2k z k1 x k2 y) /\ val5 (sub2k z k1 x k2 y) = val5 z - phi k1 * val5 x - phi k2 * val5 y.
Proof.
  intros Gz Gx Gy H1 H2 M1 M2 Hm. unfold sub2k. destruct (bd_good _ _ Gz) as (Z0 & Z1 & Z2 & Z3 & Z4). destruct (bd_good _ _ Gx) as (X0 & X1 & X2 & X3 & X4). destruct (bd_good _ _ Gy) as (Y0 & Y1 & Y2 & Y3 & Y4).
  pose proof (phi_bd63 k1) as B1. pose proof (phi_bd63 k2) as B2.
  assert (P : forall k v, 0 <= phi k < 16384 -> 0 <= v < PA -> 0 <= phi k * v <= 16384 * PA) by (intros k v K V; split; [apply Z.mul_nonneg_nonneg; lia|apply Z.mul_le_mono_nonneg; lia]).
  assert (A1 : Z.abs (phi k1 * sg (q4 x)) <= phi k1 * mx).
  { rewrite Z.abs_mul, Z.abs_eq by lia. apply Z.mul_le_mono_nonneg_l; lia. }
  assert (A2 : Z.abs (phi k2 * sg (q4 y)) <= phi k2 * my).
  { rewrite Z.abs_mul, Z.abs_eq by lia. apply Z.mul_le_mono_nonneg_l; lia. }
  pose proof (P k1 _ ltac:(lia) X0). pose proof (P k1 _ ltac:(lia) X1). pose proof (P k1 _ ltac:(lia) X2). pose proof (P k1 _ ltac:(lia) X3).
  pose proof (P k2 _ ltac:(lia) Y0). pose proof (P k2 _ ltac:(lia) Y1). pose proof (P k2 _ ltac:(lia) Y2). pose proof (P k2 _ ltac:(lia) Y3).
  destruct (nrm_spec (q0 z - k1 * q0 x - k2 * q0 y) (q1 z - k1 * q1 x - k2 * q1 y) (q2 z - k1 * q2 x - k2 * q2 y) (q3 z - k1 * q3 x - k2 * q3 y) (q4 z - k1 * q4 x - k2 * q4 y)
     (phi (q0 z) - phi k1 * phi (q0 x) - phi k2 * phi (q0 y)) (phi (q1 z) - phi k1 * phi (q1 x) - phi k2 * phi (q1 y)) (phi (q2 z) - phi k1 * phi (q2 x) - phi k2 * phi (q2 y)) (phi (q3 z) - phi k1 * phi (q3 x) - phi k2 * phi (q3 y))
     (sg (q4 z) - phi k1 * sg (q4 x) - phi k2 * sg (q4 y)) (mz + phi k1 * mx + phi k2 * my)) as [G V]; try (cgz; fail); try lia.
  split; [exact G|]. rewrite V. unfold val5. ring.
Qed.

(** ** Costs summed over visits with moments n, m1, m2 of the offsets *)
Definition GW : Z := 70368744177664.  (* 2^46 *)

Lemma add1s1_spec z k1 x k2 y mz mx my : good5 mz z -> good5 mx x -> good5 my y -> phi k1 < 16384 -> phi k2 < 16384 -> 0 <= mx -> 0 <= my ->
  mz + phi k1 * mx + phi k2 * my <= H61 ->
  good5 (mz + phi k1 * mx + phi k2 * my + 4294967296) (add1s1 z k1 x k2 y) /\ val5 (add1s1 z k1 x k2 y) = val5 z + phi k1 * val5 x - phi k2 * val5 y.
Proof.
  intros Gz Gx Gy H1 H2 M1 M2 Hm. unfold add1s1. destruct (bd_good _ _ Gz) as (Z0 & Z1 & Z2 & Z3 & Z4). destruct (bd_good _ _ Gx) as (X0 & X1 & X2 & X3 & X4). destruct (bd_good _ _ Gy) as (Y0 & Y1 & Y2 & Y3 & Y4).
  pose proof (phi_bd63 k1) as B1. pose proof (phi_bd63 k2) as B2.
  assert (P : forall k v, 0 <= phi k < 16384 -> 0 <= v < PA -> 0 <= phi k * v <= 16384 * PA) by (intros k v K V; split; [apply Z.mul_nonneg_nonneg; lia|apply Z.mul_le_mono_nonneg; lia]).
  assert (A1 : Z.abs (phi k1 * sg (q4 x)) <= phi k1 * mx).
  { rewrite Z.abs_mul, Z.abs_eq by lia. apply Z.mul_le_mono_nonneg_l; lia. }
  assert (A2 : Z.abs (phi k2 * sg (q4 y)) <= phi k2 * my).
  { rewrite Z.abs_mul, Z.abs_eq by lia. apply Z.mul_le_mono_nonneg_l; lia. }
  pose proof (P k1 _ ltac:(lia) X0). pose proof (P k1 _ ltac:(lia) X1). pose proof (P k1 _ ltac:(lia) X2). pose proof (P k1 _ ltac:(lia) X3).
  pose proof (P k2 _ ltac:(lia) Y0). pose proof (P k2 _ ltac:(lia) Y1). pose proof (P k2 _ ltac:(lia) Y2). pose proof (P k2 _ ltac:(lia) Y3).
  destruct (nrm_spec (q0 z + k1 * q0 x - k2 * q0 y) (q1 z + k1 * q1 x - k2 * q1 y) (q2 z + k1 * q2 x - k2 * q2 y) (q3 z + k1 * q3 x - k2 * q3 y) (q4 z + k1 * q4 x - k2 * q4 y)
     (phi (q0 z) + phi k1 * phi (q0 x) - phi k2 * phi (q0 y)) (phi (q1 z) + phi k1 * phi (q1 x) - phi k2 * phi (q1 y)) (phi (q2 z) + phi k1 * phi (q2 x) - phi k2 * phi (q2 y)) (phi (q3 z) + phi k1 * phi (q3 x) - phi k2 * phi (q3 y))
     (sg (q4 z) + phi k1 * sg (q4 x) - phi k2 * sg (q4 y)) (mz + phi k1 * mx + phi k2 * my)) as [G V]; try (cgz; fail); try lia.
  split; [exact G|]. rewrite V. unfold val5. ring.
Qed.

Section Sums.
Variables (m : Z) (n1 m1w : int) (m2 : P5) (b S g : Z).
Hypotheses (Hm : 0 <= m <= 576460752303423488) (Gm2 : good5 1073741824 m2).
Let Pn := pnat_spec n1.
Let Pm := pnat_spec m1w.

Local Ltac fin_good :=
  unfold GW; lazymatch goal with
  | H : good5 ?u ?x |- good5 ?v ?x => apply (good_mono u v x); [|exact H]
  | _ => idtac
  end.

Lemma pairDD_spec q : pgood m q ->
  pgood (m + GW) (pairDD q n1 m1w m2) /\
  pval (pairDD q n1 m1w m2) b S g = pval q b S g + phi n1 * (90 * b - 90 * S - 144) + phi m1w * (90 * g - 90).
Proof.
  destruct q as [Ap Bp Cp Dp Ep Fp Gp Hp Ip Jp]. intros (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10).
  cbn [pA pB pC pD pE pF pG pH pI pJ] in *. unfold pairDD. cbv beta iota zeta. destruct Pn as [Gn Vn]. destruct Pm as [Gp1 Vm].
  assert (Mg : forall x, good5 m x -> good5 (m + GW) x) by (intros x; apply good_mono; unfold GW; lia).
  change (phi 90%uint63) with 90 in *.
  destruct (addk_spec Gp 90 (pnat n1) _ _ G7 Gn ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(change (phi 90%uint63) with 90; lia)) as [a1 a2].
  destruct (subk_spec Hp 90 (pnat n1) _ _ G8 Gn ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(change (phi 90%uint63) with 90; lia)) as [b1 b2].
  destruct (addk_spec Ip 90 (pnat m1w) _ _ G9 Gp1 ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(change (phi 90%uint63) with 90; lia)) as [c1 c2].
  destruct (sub2k_spec Jp 90 (pnat m1w) 144 (pnat n1) _ _ _ G10 Gp1 Gn ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(lia) ltac:(change (phi 90%uint63) with 90; change (phi 144%uint63) with 144; lia)) as [d1 d2].
  change (phi 90%uint63) with 90 in *. change (phi 144%uint63) with 144 in *.
  unfold pgood, pval. cbn [pA pB pC pD pE pF pG pH pI pJ]. split.
  - refine (conj (Mg _ G1) (conj (Mg _ G2) (conj (Mg _ G3) (conj (Mg _ G4) (conj (Mg _ G5) (conj (Mg _ G6) (conj _ (conj _ (conj _ _))))))))); fin_good; unfold GW; lia.
  - rewrite a2, b2, c2, d2, Vn, Vm. ring.
Qed.

Lemma pairUV_spec kx kz k0 q : pgood m q -> phi kx < 16384 -> phi kz < 16384 -> phi k0 < 16384 ->
  pgood (m + GW) (pairUV kx kz k0 q n1 m1w m2) /\
  pval (pairUV kx kz k0 q n1 m1w m2) b S g = pval q b S g
    + 4 * (phi n1 * (b * S) + phi m1w * (b + g * S) + val5 m2 * g)
    + phi kx * (phi n1 * b + phi m1w * g) - phi kz * (phi n1 * S + phi m1w) - phi k0 * phi n1.
Proof.
  destruct q as [Ap Bp Cp Dp Ep Fp Gp Hp Ip Jp]. intros (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10) Kx Kz K0.
  cbn [pA pB pC pD pE pF pG pH pI pJ] in *. unfold pairUV. cbv beta iota zeta. destruct Pn as [Gn Vn]. destruct Pm as [Gp1 Vm].
  assert (Mg : forall x, good5 m x -> good5 (m + GW) x) by (intros x; apply good_mono; unfold GW; lia).
  pose proof (phi_bd63 kx) as Bx. pose proof (phi_bd63 kz) as Bz. pose proof (phi_bd63 k0) as B0.
  change (phi 4%uint63) with 4 in *.
  destruct (addk_spec Bp 4 (pnat n1) _ _ G2 Gn ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(change (phi 4%uint63) with 4; lia)) as [a1 a2].
  destruct (addk_spec Ep 4 (pnat m1w) _ _ G5 Gp1 ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(change (phi 4%uint63) with 4; lia)) as [b1 b2].
  destruct (add2k_spec Gp 4 (pnat m1w) kx (pnat n1) _ _ _ G7 Gp1 Gn ltac:(vm_compute; reflexivity) Kx ltac:(lia) ltac:(lia) ltac:(change (phi 4%uint63) with 4; lia)) as [c1 c2].
  destruct (subk_spec Hp kz (pnat n1) _ _ G8 Gn ltac:(lia) ltac:(lia) ltac:(lia)) as [d1 d2].
  assert (K4 : 0 <= phi kx * 0 <= 0) by lia.
  destruct (add2k_spec Ip 4 m2 kx (pnat m1w) m 1073741824 0 G9 Gm2 Gp1 ltac:(vm_compute; reflexivity) Kx ltac:(lia) ltac:(lia) ltac:(change (phi 4%uint63) with 4; lia)) as [e1 e2].
  destruct (sub2k_spec Jp kz (pnat m1w) k0 (pnat n1) _ _ _ G10 Gp1 Gn Kz K0 ltac:(lia) ltac:(lia) ltac:(lia)) as [f1 f2].
  change (phi 4%uint63) with 4 in *.
  unfold pgood, pval. cbn [pA pB pC pD pE pF pG pH pI pJ]. split.
  - refine (conj (Mg _ G1) (conj _ (conj (Mg _ G3) (conj (Mg _ G4) (conj _ (conj (Mg _ G6) (conj _ (conj _ (conj _ _))))))))); fin_good; unfold GW; lia.
  - rewrite a2, b2, c2, d2, e2, f2, Vn, Vm. ring.
Qed.

Lemma stopQ_spec xz zz kx kz k0 p : pgood m p -> phi xz < 4096 -> phi zz < 4096 -> phi kx < 16384 -> phi kz < 16384 -> phi k0 < 16384 ->
  pgood (m + GW) (stopQ xz zz kx kz k0 p n1 m1w m2) /\
  pval (stopQ xz zz kx kz k0 p n1 m1w m2) b S g = pval p b S g
    + 32 * (phi n1 * (b * b) + 2 * phi m1w * (b * g) + val5 m2 * (g * g))
    - phi xz * (phi n1 * (b * S) + phi m1w * (b + g * S) + val5 m2 * g)
    + phi zz * (phi n1 * (S * S) + 2 * phi m1w * S + val5 m2)
    - phi kx * (phi n1 * b + phi m1w * g) + phi kz * (phi n1 * S + phi m1w) + phi k0 * phi n1.
Proof.
  destruct p as [Ap Bp Cp Dp Ep Fp Gp Hp Ip Jp]. intros (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10) Xz Zz Kx Kz K0.
  cbn [pA pB pC pD pE pF pG pH pI pJ] in *. unfold stopQ. cbv beta iota zeta. destruct Pn as [Gn Vn]. destruct Pm as [Gp1 Vm].
  pose proof (phi_bd63 xz) as Bxz. pose proof (phi_bd63 zz) as Bzz. pose proof (phi_bd63 kx) as Bx. pose proof (phi_bd63 kz) as Bz. pose proof (phi_bd63 k0) as B0.
  assert (Ez : phi (2 * zz)%uint63 = 2 * phi zz) by (apply phi_of_cg; [apply cg_mul; [reflexivity|apply cg_refl]|lia]).
  destruct (addk_spec Ap 32 (pnat n1) _ _ G1 Gn ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(change (phi 32%uint63) with 32; lia)) as [a1 a2].
  destruct (subk_spec Bp xz (pnat n1) _ _ G2 Gn ltac:(lia) ltac:(lia) ltac:(lia)) as [b1 b2].
  destruct (addk_spec Cp 64 (pnat m1w) _ _ G3 Gp1 ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(change (phi 64%uint63) with 64; lia)) as [c1 c2].
  destruct (addk_spec Dp zz (pnat n1) _ _ G4 Gn ltac:(lia) ltac:(lia) ltac:(lia)) as [d1 d2].
  destruct (subk_spec Ep xz (pnat m1w) _ _ G5 Gp1 ltac:(lia) ltac:(lia) ltac:(lia)) as [e1 e2].
  assert (Kk : forall k : int, 0 <= phi k <= 16384 -> 0 <= phi k * 1073741824 <= 17592186044416) by (intros k Hk; lia).
  destruct (addk_spec Fp 32 m2 _ _ G6 Gm2 ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(change (phi 32%uint63) with 32; lia)) as [f1 f2].
  destruct (sub2k_spec Gp xz (pnat m1w) kx (pnat n1) _ _ _ G7 Gp1 Gn ltac:(lia) Kx ltac:(lia) ltac:(lia) ltac:(lia)) as [g1 g2].
  destruct (add2k_spec Hp (2 * zz) (pnat m1w) kz (pnat n1) _ _ _ G8 Gp1 Gn ltac:(rewrite Ez; lia) Kz ltac:(lia) ltac:(lia) ltac:(rewrite Ez; lia)) as [h1 h2].
  destruct (sub2k_spec Ip xz m2 kx (pnat m1w) m 1073741824 0 G9 Gm2 Gp1 ltac:(lia) Kx ltac:(lia) ltac:(lia) ltac:(lia)) as [i1 i2].
  destruct (add1s1_spec Jp zz m2 0 (pnat n1) m 1073741824 0 G10 Gm2 Gn ltac:(lia) ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(lia) ltac:(change (phi 0%uint63) with 0; lia)) as [j1 j2].
  destruct (add2k_spec _ kz (pnat m1w) k0 (pnat n1) _ _ _ j1 Gp1 Gn Kz K0 ltac:(lia) ltac:(lia) ltac:(change (phi 0%uint63) with 0; lia)) as [k1 k2].
  change (phi 32%uint63) with 32 in *. change (phi 64%uint63) with 64 in *. change (phi 0%uint63) with 0 in *.
  unfold pgood, pval. cbn [pA pB pC pD pE pF pG pH pI pJ]. split.
  - refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _))))))))); fin_good; unfold GW; try rewrite Ez; lia.
  - rewrite a2, b2, c2, d2, e2, f2, g2, h2, i2, k2, j2, Vn, Vm, Ez. ring.
Qed.
End Sums.
