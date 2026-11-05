(** Per-machine parameters (new; modelled on Coq-BB5's `BB5_Deciders_Hardcoded.v`).

  A table maps a machine to the decider and parameters that decide it, or to a closed automaton
  certificate. Soundness does not depend on the table: every entry is run through a decider that is proved
  sound for every machine, so a wrong entry can only fail to decide. *)

Require Import List.
Require Import NArith.

From BBminus2x4 Require Import BBminus2x4_Statement.
From BBminus2x4 Require Import TM.
From BBminus2x4 Require Import Deciders_Common.
From BBminus2x4 Require Import Decider_NGramCPS.
From BBminus2x4 Require Import Decider_RepWL.
From BBminus2x4 Require Import Verifier_ClosedAut.

(** Parameters are binary numbers (`N`): a unary `nat` literal such as 100000 would make the files huge terms. *)
Inductive TableEntry :=
| TE_NG2(len_l len_r gas:N)
| TE_NG1(len_h len_l len_r gas:N)
| TE_LRU(len_l len_r gas:N)
| TE_RWL(len min_cnt maxt gas:N).

Definition getDecider(e:TableEntry):HaltDecider :=
  match e with
  | TE_NG2 l r g => NGramCPS_decider_impl2 (N.to_nat l) (N.to_nat r) (N.to_nat g)
  | TE_NG1 h l r g => NGramCPS_decider_impl1 (N.to_nat h) (N.to_nat l) (N.to_nat r) (N.to_nat g)
  | TE_LRU l r g => NGramCPS_LRU_decider (N.to_nat l) (N.to_nat r) (N.to_nat g)
  | TE_RWL len m t g => RepWL_ES_decider (N.to_nat len) (N.to_nat m) (N.to_nat t) (N.to_nat g)
  end.

Lemma getDecider_spec e BB:
  HaltDecider_WF BB (getDecider e).
Proof.
  destruct e; cbn.
  - apply NGramCPS_decider_impl2_spec.
  - apply NGramCPS_decider_impl1_spec.
  - apply NGramCPS_LRU_decider_spec.
  - apply RepWL_ES_decider_spec.
Qed.

(** Machines are looked up by their 8 transitions, stored as plain data. *)
Definition TM_key := list (option (Trans Σ)).

Definition tm_key(tm:TM Σ):TM_key :=
  tm St0 Σ0 :: tm St0 Σ1 :: tm St0 Σ2 :: tm St0 Σ3 ::
  tm St1 Σ0 :: tm St1 Σ1 :: tm St1 Σ2 :: tm St1 Σ3 :: nil.

Fixpoint key_eqb(k1 k2:TM_key):bool :=
  match k1,k2 with
  | nil,nil => true
  | a::t,b::u => if option_eqb Trans_eqb a b then key_eqb t u else false
  | _,_ => false
  end.

Fixpoint find_entry{T}(k:TM_key)(ls:list (TM_key*T)):option T :=
  match ls with
  | nil => None
  | (k',e)::t => if key_eqb k k' then Some e else find_entry k t
  end.

Definition table_decider(ps:list (TM_key*TableEntry))(cs:list (TM_key*AutCert)):HaltDecider :=
  fun tm =>
  let k := tm_key tm in
  match find_entry k ps with
  | Some e => getDecider e tm
  | None =>
    match find_entry k cs with
    | Some c => closed_aut_decider c tm
    | None => Result_Unknown
    end
  end.

Lemma table_decider_spec ps cs BB:
  HaltDecider_WF BB (table_decider ps cs).
Proof.
  intro tm.
  unfold table_decider.
  destruct (find_entry (tm_key tm) ps) as [e|].
  - apply getDecider_spec.
  - destruct (find_entry (tm_key tm) cs) as [c|].
    + apply closed_aut_decider_spec.
    + trivial.
Qed.
