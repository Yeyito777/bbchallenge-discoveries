(**
  This file contains the statement of "BB^-(2,4) <= 1,845,977 < 3,932,964 <= BB(2,4)" and the definitions it needs.
  Everything up to `End TM.` is Coq-BB5's `BB2x4_Statement.v` (MIT, mxdys), unchanged.
  New here: the start tape `110[1]011` (`StartTape`, `StartES`) and the two statements at the end.
*)

Require Import ZArith.

(** 2-state Turing machines *)
Inductive St:Set :=
| St0
| St1.

(** 4-symbol Turing machines *)
Inductive Σ:Set :=
| Σ0
| Σ1
| Σ2
| Σ3.

(** Equality on states *)
Definition St_eqb(s1 s2:St) :=
match s1,s2 with
| St0,St0 | St1,St1 => true
| _,_ => false
end.

(** Equality on alphabet symbols *)
Definition Σ_eqb(i1 i2:Σ) :=
match i1,i2 with
| Σ0,Σ0 | Σ1,Σ1 | Σ2,Σ2 | Σ3,Σ3 => true
| _,_ => false
end.

(** Left/Right move direction *)
Inductive Dir:Set :=
| Dneg
| Dpos.

(** Mapping Left to -1 and Right to 1 *)
Definition Dir_to_Z(x:Dir) :=
match x with
| Dneg => Zneg 1
| Dpos => Zpos 1
end.

Section TM.

(** Σ is the Turing machine's alphabet and Σ0 the zero symbol *)
Hypothesis Σ:Set.
Hypothesis Σ0:Σ.

(** Turing machine transition: `nxt` next state, `dir` head move direction, `out` written symbol *)
Record Trans:Set := {
  nxt: St;
  dir: Dir;
  out: Σ;
}.

(** Turing machine partial transition function: the function returns the transition for a given state and read symbol.
Undefined transitions are encoded with None. *)
Definition TM:Set := St->Σ->option Trans.

(** Turing machine Execution State (ES), also known as "configuration" encodes the current state and tape content.
The tape content is represented as a function from integers to symbols, where 0 corresponds to the current head position.
*)
Definition ExecState:Set := St*(Z->Σ).

(** Initial configuration: state 0 and all-0 tape *)
Definition InitES:ExecState := (St0,fun _=>Σ0).

(** Tape content update *)
Definition upd(t:(Z->Σ))(o:Σ) :=
  fun x:Z => if Z.eqb x Z0 then o else t x.

(** Head position update, implemented by translating the tape content function *)
Definition mov(t:(Z->Σ))(d:Dir) :=
  fun x:Z => t ((x+(Dir_to_Z d))%Z).

(** Turing machine step: returns the next configuration or None if the machine has halted *)
Definition step(tm:TM)(st:ExecState): option ExecState :=
  let (s,t):=st in
  let read_symbol := t Z0 in
  match tm s read_symbol with
  | None => None
  | Some tr =>
    let (s',d,o):=tr in
    Some (s',mov (upd t o) d)
  end.

(** `Steps tm n st1 st2` holds if configuration `st2` is reached from `st1` after `n` Turing machine steps. *)
Inductive Steps: TM->nat->ExecState->ExecState->Prop :=
| steps_O tm st:
  Steps tm O st st
| steps_S tm n st st0 st1:
  Steps tm n st st0 ->
  step tm st0 = Some st1 ->
  Steps tm (S n) st st1.

(** `HaltsAtPlusOne tm n st` holds if Turing machine `tm` halts at configuration `st` after `n` steps.

  Note: Coq-BB5 'HaltsAt' definition (see TM.v) is off by one compared to Radò's definition which is why we have to use 'HaltsAtPlusOne'
        here in order to prove BB(5) = 47176870 and not BB(5) = 47176869.
*)
Inductive HaltsAtPlusOne(tm:TM): nat->ExecState->Prop :=
| HaltsAtPlusOne_intro n st:
  (exists st', Steps tm n st st' /\ step tm st' = None) ->
  HaltsAtPlusOne tm (S n) st.

End TM.

(** The start configuration of this proof: state A (St0) on the tape `110[1]011`.
  Cells -3..3 hold 1 1 0 1 0 1 1, the head is on cell 0 (which holds 1), every other cell holds 0. *)
Definition StartTape (x:Z) : Σ :=
  match x with
  | (-3)%Z | (-2)%Z | 0%Z | 2%Z | 3%Z => Σ1
  | _ => Σ0
  end.

Definition StartES : ExecState Σ := (St0, StartTape).

(** BB_init(2,4,110[1]011): the longest halting run from `StartES`. *)
Definition BBinit2x4_StartTape := 1845977%N.

(** The step count of the BB(2,4) champion from the blank tape (Coq-BB5 proves BB(2,4) equals it). *)
Definition BB2x4 := 3932964%N.

(** Main theorem statement. Steps are counted as in Coq-BB5's BB(2,4) statement: the step that reaches the
  undefined transition counts (`HaltsAtPlusOne`).

  - Upper bound (hard): every 2-state 4-symbol machine that halts from `StartES` halts within 1,845,977 steps.
  - Lower bound (easy): some machine halts from `StartES` after exactly 1,845,977 steps.
*)
Definition BBinit2x4_StartTape_statement :=
  (forall tm n0, HaltsAtPlusOne Σ tm n0 StartES -> n0 <= N.to_nat BBinit2x4_StartTape) /\
  (exists tm, HaltsAtPlusOne Σ tm (N.to_nat BBinit2x4_StartTape) StartES).

(** Corollary: BB^-(2,4) < BB(2,4).
  BB^-(n,m) is the least, over start tapes T (state A, head at cell 0), of the longest halting run from T.
  There is a tape on which every halting machine stops within 1,845,977 steps, so BB^-(2,4) <= 1,845,977;
  some machine takes 3,932,964 steps from the blank tape, so 3,932,964 <= BB(2,4).
*)
Definition BBminus2x4_lt_BB2x4_statement :=
  exists t : Z -> Σ,
    (forall tm n0, HaltsAtPlusOne Σ tm n0 (St0, t) -> n0 <= N.to_nat BBinit2x4_StartTape) /\
    (exists tm, HaltsAtPlusOne Σ tm (N.to_nat BB2x4) (InitES Σ Σ0)) /\
    (BBinit2x4_StartTape < BB2x4)%N.
