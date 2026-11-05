(** * BB_WT: the Busy Beaver function for Wang tiles, stated in Rocq.

    Definition (bbchallenge wiki, page "Wang Tiles", and the BB_WT forum thread):
    "Define the score of a set of Wang tiles as the largest d such that it can tile a d×d square,
     or 0 if there is no largest d. Then BB_WT(n) = the maximum score over all n-tile sets."
    Colours are unlimited, there is no seed tile or other constraint, and tiles may not be
    rotated or reflected. Tiles are written [TOP,RIGHT,BOTTOM,LEFT] as on the wiki. *)

From Coq Require Import List Arith ZArith.
Import ListNotations.

(** A Wang tile: four colours, given in the wiki's order [TOP,RIGHT,BOTTOM,LEFT]. Colours are
    natural numbers, so there is no limit on how many colours a set may use. *)
Record tile := mk_tile { top : nat; right : nat; bottom : nat; left : nat }.

(** [T] tiles the d×d square: every cell (i, j), row i from the top and column j from the
    left, gets a tile of [T], and touching edges have equal colours. *)
Definition tiles_square (T : list tile) (d : nat) : Prop :=
  exists f : nat -> nat -> tile,
    (forall i j, i < d -> j < d -> In (f i j) T) /\
    (forall i j, i < d -> S j < d -> right (f i j) = left (f i (S j))) /\
    (forall i j, S i < d -> j < d -> bottom (f i j) = top (f (S i) j)).

(** [T] tiles the whole plane. *)
Definition tiles_plane (T : list tile) : Prop :=
  exists f : Z -> Z -> tile,
    (forall i j, In (f i j) T) /\
    (forall i j, right (f i j) = left (f i (j + 1)%Z)) /\
    (forall i j, bottom (f i j) = top (f (i + 1)%Z j)).

(** d is the largest size of square that [T] tiles. *)
Definition largest_square (T : list tile) (d : nat) : Prop :=
  tiles_square T d /\ forall e, tiles_square T e -> e <= d.

(** The score: the largest d such that [T] tiles a d×d square, or 0 if there is no largest d. *)
Definition score (T : list tile) (s : nat) : Prop :=
  largest_square T s \/ (s = 0 /\ ~ exists d, largest_square T d).

(** An n-tile set: n distinct tiles. *)
Definition tile_set (T : list tile) (n : nat) : Prop := length T = n /\ NoDup T.

(** BB_WT(n) = v: some n-tile set has score v, and no n-tile set has a larger score. *)
Definition BB_WT_is (n v : nat) : Prop :=
  (exists T, tile_set T n /\ score T v) /\
  (forall T s, tile_set T n -> score T s -> s <= v).

(** BB_WT(n) >= v: some n-tile set has score at least v. *)
Definition BB_WT_at_least (n v : nat) : Prop :=
  exists T s, tile_set T n /\ score T s /\ v <= s.

(** The results proved in WangTiles_Theorem.v. *)
Definition BB_WT_5_statement := BB_WT_is 5 6.
Definition BB_WT_6_statement := BB_WT_is 6 8.
Definition BB_WT_7_statement := BB_WT_is 7 16.
Definition BB_WT_7_lower_statement := BB_WT_at_least 7 16.
Definition BB_WT_8_lower_statement := BB_WT_at_least 8 17.

(** The certificate theorems behind the upper bounds. *)
Definition plane_5_statement := forall T, length T = 5 -> tiles_square T 7 -> tiles_plane T.
Definition plane_6_statement := forall T, length T = 6 -> tiles_square T 9 -> tiles_plane T.
Definition plane_7_statement := forall T, length T = 7 -> tiles_square T 17 -> tiles_plane T.
