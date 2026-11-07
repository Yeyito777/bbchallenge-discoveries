(** The list map of the 16-machine group, with no reference to any Turing machine.
    A state is a stack of run lengths, rightmost run first. *)
From Coq Require Import List Arith.
Import ListNotations.

(** The first-run stage of a top event: while P is even, [P/2+1] goes on the stack and P becomes [P/2-1].
    When P is odd it splits into the two new leftmost runs. The fuel is P, which is always enough. *)
Fixpoint top (fuel P : nat) : list nat :=
  match fuel with
  | 0 => []
  | S f => if Nat.even P then (P / 2 + 1) :: top f (P / 2 - 1)
           else [(P + 1) / 2 + 3; (P + 1) / 2]
  end.

(** The carry moving left through the stack. *)
Fixpoint carry (r : nat) (rest : list nat) : list nat :=
  match rest with
  | [] => []
  | a :: t =>
    if Nat.even r then
      (r / 2 + 2) :: match t with
                     | [] => top (a + r / 2) (a + r / 2)
                     | _ :: _ => carry (a + r / 2 - 2) t
                     end
    else ((r + 9) / 2) :: (a + (r + 3) / 2) :: t
  end.

(** One step of the map. *)
Definition step (s : list nat) : list nat :=
  match s with
  | [] => []
  | x :: t => carry (x + 2) t
  end.

(** The value P if this step of the map is a top event. *)
Fixpoint carryP (r : nat) (rest : list nat) : option nat :=
  match rest with
  | [] => None
  | a :: t =>
    if Nat.even r then
      match t with
      | [] => Some (a + r / 2)
      | _ :: _ => carryP (a + r / 2 - 2) t
      end
    else None
  end.

Definition topP (s : list nat) : option nat :=
  match s with
  | [] => None
  | x :: t => carryP (x + 2) t
  end.

(** The orbit of every machine in the group. *)
Definition s0 : list nat := [9; 10].
Definition orbit (n : nat) : list nat := Nat.iter n step s0.

(** A top event with P + 2 a power of 2. *)
Definition pw (P : nat) : Prop := exists k, P + 2 = 2 ^ k.
Definition hit (s : list nat) : Prop := exists P, topP s = Some P /\ pw P.
