
(** val negb : bool -> bool **)

let negb = function
| true -> false
| false -> true

(** val fst : ('a1 * 'a2) -> 'a1 **)

let fst = function
| (x, _) -> x

(** val snd : ('a1 * 'a2) -> 'a2 **)

let snd = function
| (_, y) -> y

(** val length : 'a1 list -> int **)

let rec length = function
| [] -> 0
| _ :: l' -> Stdlib.Int.succ (length l')

(** val app : 'a1 list -> 'a1 list -> 'a1 list **)

let rec app l2 m1 =
  match l2 with
  | [] -> m1
  | a :: l3 -> a :: (app l3 m1)

type comparison =
| Eq
| Lt
| Gt

(** val compOpp : comparison -> comparison **)

let compOpp = function
| Eq -> Eq
| Lt -> Gt
| Gt -> Lt

module Coq__1 = struct
 (** val add : int -> int -> int **)

 let rec add = (+)
end
include Coq__1

type positive =
| XI of positive
| XO of positive
| XH

type z =
| Z0
| Zpos of positive
| Zneg of positive

module Nat =
 struct
  (** val pred : int -> int **)

  let pred n =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> n)
      (fun u -> u)
      n

  (** val ltb : int -> int -> bool **)

  let ltb n m1 =
    (<=) (Stdlib.Int.succ n) m1
 end

module Pos =
 struct
  (** val succ : positive -> positive **)

  let rec succ = function
  | XI p -> XO (succ p)
  | XO p -> XI p
  | XH -> XO XH

  (** val add : positive -> positive -> positive **)

  let rec add x y =
    match x with
    | XI p ->
      (match y with
       | XI q -> XO (add_carry p q)
       | XO q -> XI (add p q)
       | XH -> XO (succ p))
    | XO p ->
      (match y with
       | XI q -> XI (add p q)
       | XO q -> XO (add p q)
       | XH -> XI p)
    | XH -> (match y with
             | XI q -> XO (succ q)
             | XO q -> XI q
             | XH -> XO XH)

  (** val add_carry : positive -> positive -> positive **)

  and add_carry x y =
    match x with
    | XI p ->
      (match y with
       | XI q -> XI (add_carry p q)
       | XO q -> XO (add_carry p q)
       | XH -> XI (succ p))
    | XO p ->
      (match y with
       | XI q -> XO (add_carry p q)
       | XO q -> XI (add p q)
       | XH -> XO (succ p))
    | XH ->
      (match y with
       | XI q -> XI (succ q)
       | XO q -> XO (succ q)
       | XH -> XI XH)

  (** val pred_double : positive -> positive **)

  let rec pred_double = function
  | XI p -> XI (XO p)
  | XO p -> XI (pred_double p)
  | XH -> XH

  (** val mul : positive -> positive -> positive **)

  let rec mul x y =
    match x with
    | XI p -> add y (XO (mul p y))
    | XO p -> XO (mul p y)
    | XH -> y

  (** val compare_cont : comparison -> positive -> positive -> comparison **)

  let rec compare_cont r2 x y =
    match x with
    | XI p ->
      (match y with
       | XI q -> compare_cont r2 p q
       | XO q -> compare_cont Gt p q
       | XH -> Gt)
    | XO p ->
      (match y with
       | XI q -> compare_cont Lt p q
       | XO q -> compare_cont r2 p q
       | XH -> Gt)
    | XH -> (match y with
             | XH -> r2
             | _ -> Lt)

  (** val compare : positive -> positive -> comparison **)

  let compare =
    compare_cont Eq

  (** val eqb : positive -> positive -> bool **)

  let rec eqb p q =
    match p with
    | XI p0 -> (match q with
                | XI q0 -> eqb p0 q0
                | _ -> false)
    | XO p0 -> (match q with
                | XO q0 -> eqb p0 q0
                | _ -> false)
    | XH -> (match q with
             | XH -> true
             | _ -> false)

  (** val iter_op : ('a1 -> 'a1 -> 'a1) -> positive -> 'a1 -> 'a1 **)

  let rec iter_op op p a =
    match p with
    | XI p0 -> op a (iter_op op p0 (op a a))
    | XO p0 -> iter_op op p0 (op a a)
    | XH -> a

  (** val to_nat : positive -> int **)

  let to_nat x =
    iter_op Coq__1.add x (Stdlib.Int.succ 0)

  (** val of_succ_nat : int -> positive **)

  let rec of_succ_nat n =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> XH)
      (fun x -> succ (of_succ_nat x))
      n
 end

module Z =
 struct
  (** val double : z -> z **)

  let double = function
  | Z0 -> Z0
  | Zpos p -> Zpos (XO p)
  | Zneg p -> Zneg (XO p)

  (** val succ_double : z -> z **)

  let succ_double = function
  | Z0 -> Zpos XH
  | Zpos p -> Zpos (XI p)
  | Zneg p -> Zneg (Pos.pred_double p)

  (** val pred_double : z -> z **)

  let pred_double = function
  | Z0 -> Zneg XH
  | Zpos p -> Zpos (Pos.pred_double p)
  | Zneg p -> Zneg (XI p)

  (** val pos_sub : positive -> positive -> z **)

  let rec pos_sub x y =
    match x with
    | XI p ->
      (match y with
       | XI q -> double (pos_sub p q)
       | XO q -> succ_double (pos_sub p q)
       | XH -> Zpos (XO p))
    | XO p ->
      (match y with
       | XI q -> pred_double (pos_sub p q)
       | XO q -> double (pos_sub p q)
       | XH -> Zpos (Pos.pred_double p))
    | XH ->
      (match y with
       | XI q -> Zneg (XO q)
       | XO q -> Zneg (Pos.pred_double q)
       | XH -> Z0)

  (** val add : z -> z -> z **)

  let add x y =
    match x with
    | Z0 -> y
    | Zpos x' ->
      (match y with
       | Z0 -> x
       | Zpos y' -> Zpos (Pos.add x' y')
       | Zneg y' -> pos_sub x' y')
    | Zneg x' ->
      (match y with
       | Z0 -> x
       | Zpos y' -> pos_sub y' x'
       | Zneg y' -> Zneg (Pos.add x' y'))

  (** val opp : z -> z **)

  let opp = function
  | Z0 -> Z0
  | Zpos x0 -> Zneg x0
  | Zneg x0 -> Zpos x0

  (** val sub : z -> z -> z **)

  let sub m1 n =
    add m1 (opp n)

  (** val mul : z -> z -> z **)

  let mul x y =
    match x with
    | Z0 -> Z0
    | Zpos x' ->
      (match y with
       | Z0 -> Z0
       | Zpos y' -> Zpos (Pos.mul x' y')
       | Zneg y' -> Zneg (Pos.mul x' y'))
    | Zneg x' ->
      (match y with
       | Z0 -> Z0
       | Zpos y' -> Zneg (Pos.mul x' y')
       | Zneg y' -> Zpos (Pos.mul x' y'))

  (** val compare : z -> z -> comparison **)

  let compare x y =
    match x with
    | Z0 -> (match y with
             | Z0 -> Eq
             | Zpos _ -> Lt
             | Zneg _ -> Gt)
    | Zpos x' -> (match y with
                  | Zpos y' -> Pos.compare x' y'
                  | _ -> Gt)
    | Zneg x' ->
      (match y with
       | Zneg y' -> compOpp (Pos.compare x' y')
       | _ -> Lt)

  (** val ltb : z -> z -> bool **)

  let ltb x y =
    match compare x y with
    | Lt -> true
    | _ -> false

  (** val eqb : z -> z -> bool **)

  let eqb x y =
    match x with
    | Z0 -> (match y with
             | Z0 -> true
             | _ -> false)
    | Zpos p -> (match y with
                 | Zpos q -> Pos.eqb p q
                 | _ -> false)
    | Zneg p -> (match y with
                 | Zneg q -> Pos.eqb p q
                 | _ -> false)

  (** val of_nat : int -> z **)

  let of_nat n =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> Z0)
      (fun n0 -> Zpos (Pos.of_succ_nat n0))
      n
 end

(** val nth : int -> 'a1 list -> 'a1 -> 'a1 **)

let rec nth n l2 default =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> match l2 with
              | [] -> default
              | x :: _ -> x)
    (fun m1 -> match l2 with
               | [] -> default
               | _ :: t0 -> nth m1 t0 default)
    n

(** val map : ('a1 -> 'a2) -> 'a1 list -> 'a2 list **)

let rec map f = function
| [] -> []
| a :: t0 -> (f a) :: (map f t0)

(** val fold_left : ('a1 -> 'a2 -> 'a1) -> 'a2 list -> 'a1 -> 'a1 **)

let rec fold_left f l2 a0 =
  match l2 with
  | [] -> a0
  | b :: t0 -> fold_left f t0 (f a0 b)

(** val forallb : ('a1 -> bool) -> 'a1 list -> bool **)

let rec forallb f = function
| [] -> true
| a :: l3 -> (&&) (f a) (forallb f l3)

(** val filter : ('a1 -> bool) -> 'a1 list -> 'a1 list **)

let rec filter f = function
| [] -> []
| x :: l3 -> if f x then x :: (filter f l3) else filter f l3

(** val firstn : int -> 'a1 list -> 'a1 list **)

let rec firstn n l2 =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> [])
    (fun n0 -> match l2 with
               | [] -> []
               | a :: l3 -> a :: (firstn n0 l3))
    n

(** val skipn : int -> 'a1 list -> 'a1 list **)

let rec skipn n l2 =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> l2)
    (fun n0 -> match l2 with
               | [] -> []
               | _ :: l3 -> skipn n0 l3)
    n

(** val seq : int -> int -> int list **)

let rec seq start len =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> [])
    (fun len0 -> start :: (seq (Stdlib.Int.succ start) len0))
    len

(** val repeat : 'a1 -> int -> 'a1 list **)

let rec repeat x n =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> [])
    (fun k -> x :: (repeat x k))
    n

type st =
| St0
| St1

type _UU03a3_ =
| Coq__UU03a3_0
| Coq__UU03a3_1
| Coq__UU03a3_2
| Coq__UU03a3_3

(** val st_eqb : st -> st -> bool **)

let st_eqb s2 s3 =
  match s2 with
  | St0 -> (match s3 with
            | St0 -> true
            | St1 -> false)
  | St1 -> (match s3 with
            | St0 -> false
            | St1 -> true)

(** val _UU03a3__eqb : _UU03a3_ -> _UU03a3_ -> bool **)

let _UU03a3__eqb i1 i2 =
  match i1 with
  | Coq__UU03a3_0 -> (match i2 with
                      | Coq__UU03a3_0 -> true
                      | _ -> false)
  | Coq__UU03a3_1 -> (match i2 with
                      | Coq__UU03a3_1 -> true
                      | _ -> false)
  | Coq__UU03a3_2 -> (match i2 with
                      | Coq__UU03a3_2 -> true
                      | _ -> false)
  | Coq__UU03a3_3 -> (match i2 with
                      | Coq__UU03a3_3 -> true
                      | _ -> false)

type dir =
| Dneg
| Dpos

(** val dir_to_Z : dir -> z **)

let dir_to_Z = function
| Dneg -> Zneg XH
| Dpos -> Zpos XH

type 'x trans = { nxt : st; dir0 : dir; out : 'x }

type 'x tM = st -> 'x -> 'x trans option

(** val append : positive -> positive -> positive **)

let rec append i j =
  match i with
  | XI ii -> XI (append ii j)
  | XO ii -> XO (append ii j)
  | XH -> j

module PositiveMap =
 struct
  type key = positive

  type 'a tree =
  | Leaf
  | Node of 'a tree * 'a option * 'a tree

  type 'a t = 'a tree

  (** val empty : 'a1 t **)

  let empty =
    Leaf

  (** val find : key -> 'a1 t -> 'a1 option **)

  let rec find i = function
  | Leaf -> None
  | Node (l2, o, r2) ->
    (match i with
     | XI ii -> find ii r2
     | XO ii -> find ii l2
     | XH -> o)

  (** val add : key -> 'a1 -> 'a1 t -> 'a1 t **)

  let rec add i v = function
  | Leaf ->
    (match i with
     | XI ii -> Node (Leaf, None, (add ii v Leaf))
     | XO ii -> Node ((add ii v Leaf), None, Leaf)
     | XH -> Node (Leaf, (Some v), Leaf))
  | Node (l2, o, r2) ->
    (match i with
     | XI ii -> Node (l2, o, (add ii v r2))
     | XO ii -> Node ((add ii v l2), o, r2)
     | XH -> Node (l2, (Some v), r2))
 end

(** val dir_rev : dir -> dir **)

let dir_rev = function
| Dneg -> Dpos
| Dpos -> Dneg

type 't setOfEncodings = 't list * unit PositiveMap.tree

(** val set_ins :
    ('a1 -> positive) -> 'a1 setOfEncodings -> 'a1 -> 'a1
    setOfEncodings * bool **)

let set_ins enc s2 x =
  let enc0 = enc x in
  (match PositiveMap.find enc0 (snd s2) with
   | Some _ -> (s2, true)
   | None -> (((x :: (fst s2)), (PositiveMap.add enc0 () (snd s2))), false))

(** val dir_eqb : dir -> dir -> bool **)

let dir_eqb d1 d2 =
  match d1 with
  | Dneg -> (match d2 with
             | Dneg -> true
             | Dpos -> false)
  | Dpos -> (match d2 with
             | Dneg -> false
             | Dpos -> true)

(** val positive_len : positive -> int **)

let rec positive_len = function
| XI x0 -> Stdlib.Int.succ (positive_len x0)
| XO x0 -> Stdlib.Int.succ (positive_len x0)
| XH -> 0

(** val enc_v1 : positive -> positive **)

let rec enc_v1 = function
| XI x0 -> XI (XI (enc_v1 x0))
| XO x0 -> XI (XO (enc_v1 x0))
| XH -> XH

(** val enc_pair : (positive * positive) -> positive **)

let enc_pair = function
| (x1, x2) ->
  append (enc_v1 (Pos.of_succ_nat (positive_len x1))) (XO (append x1 x2))

(** val enc_list : positive list -> positive **)

let rec enc_list = function
| [] -> XH
| h :: t0 -> enc_pair (h, (enc_list t0))

(** val st_enc : st -> positive **)

let st_enc = function
| St0 -> XH
| St1 -> XO XH

(** val _UU03a3__enc : _UU03a3_ -> positive **)

let _UU03a3__enc = function
| Coq__UU03a3_0 -> XH
| Coq__UU03a3_1 -> XO XH
| Coq__UU03a3_2 -> XI XH
| Coq__UU03a3_3 -> XO (XO XH)

(** val list_UU03a3__enc : _UU03a3_ list -> positive **)

let rec list_UU03a3__enc = function
| [] -> XH
| _UU03c3_ :: t0 ->
  (match _UU03c3_ with
   | Coq__UU03a3_0 -> XO (XO (list_UU03a3__enc t0))
   | Coq__UU03a3_1 -> XI (XO (list_UU03a3__enc t0))
   | Coq__UU03a3_2 -> XO (XI (list_UU03a3__enc t0))
   | Coq__UU03a3_3 -> XI (XI (list_UU03a3__enc t0)))

(** val listT_enc : ('a1 -> positive) -> 'a1 list -> positive **)

let listT_enc f x =
  enc_list (map f x)

(** val listSt_UU03a3__enc : (st * _UU03a3_) list -> positive **)

let rec listSt_UU03a3__enc = function
| [] -> XH
| p :: t0 ->
  let (s2, _UU03c3_) = p in
  (match s2 with
   | St0 ->
     (match _UU03c3_ with
      | Coq__UU03a3_0 -> XO (XO (XO (listSt_UU03a3__enc t0)))
      | Coq__UU03a3_1 -> XO (XO (XI (listSt_UU03a3__enc t0)))
      | Coq__UU03a3_2 -> XO (XI (XO (listSt_UU03a3__enc t0)))
      | Coq__UU03a3_3 -> XO (XI (XI (listSt_UU03a3__enc t0))))
   | St1 ->
     (match _UU03c3_ with
      | Coq__UU03a3_0 -> XI (XO (XO (listSt_UU03a3__enc t0)))
      | Coq__UU03a3_1 -> XI (XO (XI (listSt_UU03a3__enc t0)))
      | Coq__UU03a3_2 -> XI (XI (XO (listSt_UU03a3__enc t0)))
      | Coq__UU03a3_3 -> XI (XI (XI (listSt_UU03a3__enc t0)))))

(** val dir_enc : dir -> positive **)

let dir_enc = function
| Dneg -> XH
| Dpos -> XI XH

(** val bool_enc : bool -> positive **)

let bool_enc = function
| true -> XI XH
| false -> XH

(** val pop_back : 'a1 -> 'a1 list -> 'a1 list **)

let rec pop_back x = function
| [] -> []
| h :: t0 -> x :: (pop_back h t0)

(** val pop_back' : 'a1 -> 'a1 list -> 'a1 list * 'a1 **)

let rec pop_back' x = function
| [] -> ([], x)
| h :: t0 -> let (a, b) = pop_back' h t0 in ((x :: a), b)

(** val tapeOfLists : 'a1 -> 'a1 list -> 'a1 list -> 'a1 -> z -> 'a1 **)

let tapeOfLists _UU03a3_0 l2 r2 m1 = function
| Z0 -> m1
| Zpos x0 -> nth (Pos.to_nat x0) (m1 :: r2) _UU03a3_0
| Zneg x0 -> nth (Pos.to_nat x0) (m1 :: l2) _UU03a3_0

(** val start_l : _UU03a3_ list **)

let start_l =
  Coq__UU03a3_0 :: (Coq__UU03a3_1 :: (Coq__UU03a3_1 :: []))

(** val start_r : _UU03a3_ list **)

let start_r =
  Coq__UU03a3_0 :: (Coq__UU03a3_1 :: (Coq__UU03a3_1 :: []))

(** val start_m : _UU03a3_ **)

let start_m =
  Coq__UU03a3_1

(** val st_UU03a3__neb : (st * _UU03a3_) -> (st * _UU03a3_) -> bool **)

let st_UU03a3__neb x1 x2 =
  let (s2, i1) = x1 in
  let (s3, i2) = x2 in
  if st_eqb s2 s3 then negb (_UU03a3__eqb i1 i2) else true

type _UU03a3__history = _UU03a3_ * (st * _UU03a3_) list

(** val _UU03a3__history_0 : _UU03a3__history **)

let _UU03a3__history_0 =
  (Coq__UU03a3_0, [])

(** val tM_history : int -> _UU03a3_ tM -> _UU03a3__history tM **)

let tM_history n tm s2 = function
| (i0, i1) ->
  (match tm s2 i0 with
   | Some tr ->
     let { nxt = s'; dir0 = d; out = o0 } = tr in
     Some { nxt = s'; dir0 = d; out = (o0, (firstn n ((s2, i0) :: i1))) }
   | None -> None)

(** val tM_history_LRU : _UU03a3_ tM -> _UU03a3__history tM **)

let tM_history_LRU tm s2 = function
| (i0, i1) ->
  (match tm s2 i0 with
   | Some tr ->
     let { nxt = s'; dir0 = d; out = o0 } = tr in
     Some { nxt = s'; dir0 = d; out = (o0, ((s2,
     i0) :: (filter (st_UU03a3__neb (s2, i0)) i1))) }
   | None -> None)

type haltDecideResult =
| Result_Halt of st * _UU03a3_
| Result_NonHalt
| Result_Unknown

type haltDecider = _UU03a3_ tM -> haltDecideResult

(** val _UU03a3__history_enc : _UU03a3__history -> positive **)

let _UU03a3__history_enc = function
| (x0, x1) ->
  (match x0 with
   | Coq__UU03a3_0 -> XO (XO (listSt_UU03a3__enc x1))
   | Coq__UU03a3_1 -> XO (XI (listSt_UU03a3__enc x1))
   | Coq__UU03a3_2 -> XI (XO (listSt_UU03a3__enc x1))
   | Coq__UU03a3_3 -> XI (XI (listSt_UU03a3__enc x1)))

type 'x midWord = { l : 'x list; r : 'x list; m : 'x; s : st }

(** val midWord_enc :
    ('a1 -> positive) -> ('a1 list -> positive) -> 'a1 midWord -> positive **)

let midWord_enc _UU03a3__enc0 list_UU03a3__enc0 mw =
  let { l = l2; r = r2; m = m1; s = s2 } = mw in
  enc_list
    ((st_enc s2) :: ((_UU03a3__enc0 m1) :: ((list_UU03a3__enc0 l2) :: (
    (list_UU03a3__enc0 r2) :: []))))

type 'x xset_impl = 'x setOfEncodings PositiveMap.tree

type 'x mset_impl = 'x midWord setOfEncodings

type 'x aES_impl = { lset' : 'x xset_impl; rset' : 'x xset_impl;
                     mset' : 'x mset_impl }

(** val xset_as_list :
    ('a1 list -> positive) -> 'a1 xset_impl -> 'a1 list -> 'a1 list **)

let xset_as_list list_UU03a3__enc0 xs x1 =
  match PositiveMap.find (list_UU03a3__enc0 x1) xs with
  | Some v -> fst v
  | None -> []

(** val xset_ins0 :
    ('a1 -> positive) -> ('a1 list -> positive) -> 'a1 xset_impl -> 'a1
    setOfEncodings -> 'a1 list -> 'a1 -> 'a1 xset_impl * bool **)

let xset_ins0 _UU03a3__enc0 list_UU03a3__enc0 xs v x1 x2 =
  let (v', flag) = set_ins _UU03a3__enc0 v x2 in
  ((PositiveMap.add (list_UU03a3__enc0 x1) v' xs), flag)

(** val xset_ins :
    ('a1 -> positive) -> ('a1 list -> positive) -> 'a1 xset_impl -> 'a1 list
    -> 'a1 xset_impl * bool **)

let xset_ins _UU03a3__enc0 list_UU03a3__enc0 xs = function
| [] -> (xs, false)
| h :: t0 ->
  let (x1, x2) = pop_back' h t0 in
  (match PositiveMap.find (list_UU03a3__enc0 x1) xs with
   | Some v -> xset_ins0 _UU03a3__enc0 list_UU03a3__enc0 xs v x1 x2
   | None ->
     xset_ins0 _UU03a3__enc0 list_UU03a3__enc0 xs ([], PositiveMap.empty) x1
       x2)

(** val mset_ins0 :
    ('a1 -> positive) -> ('a1 list -> positive) -> 'a1 mset_impl -> 'a1
    midWord -> 'a1 mset_impl * bool **)

let mset_ins0 _UU03a3__enc0 list_UU03a3__enc0 ms mw =
  set_ins (midWord_enc _UU03a3__enc0 list_UU03a3__enc0) ms mw

(** val mset_ins :
    ('a1 -> positive) -> ('a1 list -> positive) -> 'a1 midWord list -> 'a1
    mset_impl -> bool -> ('a1 -> 'a1 midWord) -> 'a1 list -> ('a1 midWord
    list * 'a1 mset_impl) * bool **)

let rec mset_ins _UU03a3__enc0 list_UU03a3__enc0 q ms flag f = function
| [] -> ((q, ms), flag)
| h :: t0 ->
  let (ms', flag') = mset_ins0 _UU03a3__enc0 list_UU03a3__enc0 ms (f h) in
  let q' = if flag' then q else (f h) :: q in
  mset_ins _UU03a3__enc0 list_UU03a3__enc0 q' ms' ((&&) flag flag') f t0

(** val update_AES_MidWord :
    ('a1 -> positive) -> ('a1 list -> positive) -> 'a1 tM -> 'a1 midWord list
    -> 'a1 midWord -> 'a1 aES_impl -> ('a1 midWord list * 'a1 aES_impl) * bool **)

let update_AES_MidWord _UU03a3__enc0 list_UU03a3__enc0 tm q mw sI =
  let { l = l2; r = r2; m = m1; s = s2 } = mw in
  let { lset' = ls; rset' = rs; mset' = ms } = sI in
  (match l2 with
   | [] -> ((q, sI), false)
   | hl :: l3 ->
     (match r2 with
      | [] -> ((q, sI), false)
      | hr :: r3 ->
        (match tm s2 m1 with
         | Some tr ->
           let { nxt = s3; dir0 = d; out = o } = tr in
           (match d with
            | Dneg ->
              let (rs', flag1) =
                xset_ins _UU03a3__enc0 list_UU03a3__enc0 rs r2
              in
              let (p, flag2) =
                mset_ins _UU03a3__enc0 list_UU03a3__enc0 q ms true (fun x ->
                  { l = (app l3 (x :: [])); r = (o :: (pop_back hr r3)); m =
                  hl; s = s3 }) (xset_as_list list_UU03a3__enc0 ls l3)
              in
              let (q', ms') = p in
              ((q', { lset' = ls; rset' = rs'; mset' = ms' }),
              ((&&) flag1 flag2))
            | Dpos ->
              let (ls', flag1) =
                xset_ins _UU03a3__enc0 list_UU03a3__enc0 ls l2
              in
              let (p, flag2) =
                mset_ins _UU03a3__enc0 list_UU03a3__enc0 q ms true (fun x ->
                  { l = (o :: (pop_back hl l3)); r = (app r3 (x :: [])); m =
                  hr; s = s3 }) (xset_as_list list_UU03a3__enc0 rs r3)
              in
              let (q', ms') = p in
              ((q', { lset' = ls'; rset' = rs; mset' = ms' }),
              ((&&) flag1 flag2)))
         | None -> ((q, sI), false))))

(** val update_AES :
    ('a1 -> positive) -> ('a1 list -> positive) -> 'a1 tM -> 'a1 midWord list
    -> 'a1 aES_impl -> bool -> int -> ('a1 aES_impl * bool) * int **)

let rec update_AES _UU03a3__enc0 list_UU03a3__enc0 tm ms sI flag n =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> ((sI, false), 0))
    (fun n0 ->
    match ms with
    | [] -> ((sI, flag), n0)
    | mw :: ms0 ->
      let (s', flag') =
        update_AES_MidWord _UU03a3__enc0 list_UU03a3__enc0 tm ms0 mw sI
      in
      let (q', sI') = s' in
      update_AES _UU03a3__enc0 list_UU03a3__enc0 tm q' sI' ((&&) flag flag')
        n0)
    n

(** val tape_seg : (z -> 'a1) -> z -> dir -> int -> 'a1 list **)

let rec tape_seg t0 x d n =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> [])
    (fun n0 -> (t0 x) :: (tape_seg t0 (Z.add x (dir_to_Z d)) d n0))
    n

(** val init_tape : 'a1 -> 'a1 list -> 'a1 list -> 'a1 -> z -> 'a1 **)

let init_tape =
  tapeOfLists

(** val init_segs :
    'a1 -> 'a1 list -> 'a1 list -> 'a1 -> dir -> int -> int -> 'a1 list list **)

let init_segs _UU03a3_0 init_l init_r init_m d len k =
  map (fun n ->
    tape_seg (init_tape _UU03a3_0 init_l init_r init_m)
      (Z.mul (Z.of_nat n) (dir_to_Z d)) d len)
    (seq (Stdlib.Int.succ (Stdlib.Int.succ 0)) (Stdlib.Int.succ k))

(** val init_lsegs :
    int -> 'a1 -> 'a1 list -> 'a1 list -> 'a1 -> 'a1 list list **)

let init_lsegs len_l _UU03a3_0 init_l init_r init_m =
  init_segs _UU03a3_0 init_l init_r init_m Dneg len_l (length init_l)

(** val init_rsegs :
    int -> 'a1 -> 'a1 list -> 'a1 list -> 'a1 -> 'a1 list list **)

let init_rsegs len_r _UU03a3_0 init_l init_r init_m =
  init_segs _UU03a3_0 init_l init_r init_m Dpos len_r (length init_r)

(** val init_mw :
    int -> int -> 'a1 -> 'a1 list -> 'a1 list -> 'a1 -> 'a1 midWord **)

let init_mw len_l len_r _UU03a3_0 init_l init_r init_m =
  { l =
    (tape_seg (init_tape _UU03a3_0 init_l init_r init_m) (Zneg XH) Dneg len_l);
    r =
    (tape_seg (init_tape _UU03a3_0 init_l init_r init_m) (Zpos XH) Dpos len_r);
    m = init_m; s = St0 }

(** val xset_ins_list :
    ('a1 -> positive) -> ('a1 list -> positive) -> 'a1 xset_impl -> 'a1 list
    list -> 'a1 xset_impl **)

let xset_ins_list _UU03a3__enc0 list_UU03a3__enc0 xs ls =
  fold_left (fun xs0 x ->
    fst (xset_ins _UU03a3__enc0 list_UU03a3__enc0 xs0 x)) ls xs

(** val check_InitES_InAES :
    int -> int -> ('a1 -> positive) -> ('a1 list -> positive) -> 'a1 -> 'a1
    list -> 'a1 list -> 'a1 -> 'a1 aES_impl -> bool **)

let check_InitES_InAES len_l len_r _UU03a3__enc0 list_UU03a3__enc0 _UU03a3_0 init_l init_r init_m s2 =
  let { lset' = ls; rset' = rs; mset' = ms } = s2 in
  (&&)
    ((&&)
      (snd
        (mset_ins0 _UU03a3__enc0 list_UU03a3__enc0 ms
          (init_mw len_l len_r _UU03a3_0 init_l init_r init_m)))
      (forallb (fun x -> snd (xset_ins _UU03a3__enc0 list_UU03a3__enc0 ls x))
        (init_lsegs len_l _UU03a3_0 init_l init_r init_m)))
    (forallb (fun x -> snd (xset_ins _UU03a3__enc0 list_UU03a3__enc0 rs x))
      (init_rsegs len_r _UU03a3_0 init_l init_r init_m))

(** val nGramCPS_decider_0 :
    int -> int -> ('a1 -> positive) -> ('a1 list -> positive) -> 'a1 -> 'a1
    list -> 'a1 list -> 'a1 -> int -> int -> 'a1 tM -> 'a1 aES_impl -> bool **)

let rec nGramCPS_decider_0 len_l len_r _UU03a3__enc0 list_UU03a3__enc0 _UU03a3_0 init_l init_r init_m m1 n tm s2 =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> false)
    (fun m2 ->
    let (p, n0) =
      update_AES _UU03a3__enc0 list_UU03a3__enc0 tm (fst s2.mset') s2 true n
    in
    let (s', flag) = p in
    if flag
    then check_InitES_InAES len_l len_r _UU03a3__enc0 list_UU03a3__enc0
           _UU03a3_0 init_l init_r init_m s'
    else nGramCPS_decider_0 len_l len_r _UU03a3__enc0 list_UU03a3__enc0
           _UU03a3_0 init_l init_r init_m m2 n0 tm s')
    m1

(** val nGramCPS_decider :
    int -> int -> ('a1 -> positive) -> ('a1 list -> positive) -> 'a1 -> 'a1
    list -> 'a1 list -> 'a1 -> int -> 'a1 tM -> bool **)

let nGramCPS_decider len_l len_r _UU03a3__enc0 list_UU03a3__enc0 _UU03a3_0 init_l init_r init_m m1 tm =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> false)
    (fun _ ->
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> false)
      (fun _ ->
      nGramCPS_decider_0 len_l len_r _UU03a3__enc0 list_UU03a3__enc0
        _UU03a3_0 init_l init_r init_m m1 m1 tm { lset' =
        (xset_ins_list _UU03a3__enc0 list_UU03a3__enc0 PositiveMap.empty
          (init_lsegs len_l _UU03a3_0 init_l init_r init_m)); rset' =
        (xset_ins_list _UU03a3__enc0 list_UU03a3__enc0 PositiveMap.empty
          (init_rsegs len_r _UU03a3_0 init_l init_r init_m)); mset' =
        (fst
          (mset_ins0 _UU03a3__enc0 list_UU03a3__enc0 ([], PositiveMap.empty)
            (init_mw len_l len_r _UU03a3_0 init_l init_r init_m))) })
      len_r)
    len_l

(** val _UU03a3__history_lift : _UU03a3_ -> _UU03a3__history **)

let _UU03a3__history_lift x =
  (x, [])

(** val nGramCPS_decider_impl1_0 :
    int -> int -> int -> int -> _UU03a3_ tM -> bool **)

let nGramCPS_decider_impl1_0 len_h len_l len_r m1 tm =
  nGramCPS_decider len_l len_r _UU03a3__history_enc
    (listT_enc _UU03a3__history_enc) _UU03a3__history_0
    (map _UU03a3__history_lift start_l) (map _UU03a3__history_lift start_r)
    (_UU03a3__history_lift start_m) m1 (tM_history len_h tm)

(** val nGramCPS_decider_impl2_0 :
    int -> int -> int -> _UU03a3_ tM -> bool **)

let nGramCPS_decider_impl2_0 len_l len_r m1 tm =
  nGramCPS_decider len_l len_r _UU03a3__enc list_UU03a3__enc Coq__UU03a3_0
    start_l start_r start_m m1 tm

(** val nGramCPS_LRU_decider_0 : int -> int -> int -> _UU03a3_ tM -> bool **)

let nGramCPS_LRU_decider_0 len_l len_r m1 tm =
  nGramCPS_decider len_l len_r _UU03a3__history_enc
    (listT_enc _UU03a3__history_enc) _UU03a3__history_0
    (map _UU03a3__history_lift start_l) (map _UU03a3__history_lift start_r)
    (_UU03a3__history_lift start_m) m1 (tM_history_LRU tm)

(** val nGramCPS_decider_impl1 : int -> int -> int -> int -> haltDecider **)

let nGramCPS_decider_impl1 len_h len_l len_r m1 tm =
  if nGramCPS_decider_impl1_0 len_h len_l len_r m1 tm
  then Result_NonHalt
  else Result_Unknown

(** val nGramCPS_decider_impl2 : int -> int -> int -> haltDecider **)

let nGramCPS_decider_impl2 len_l len_r m1 tm =
  if nGramCPS_decider_impl2_0 len_l len_r m1 tm
  then Result_NonHalt
  else Result_Unknown

(** val nGramCPS_LRU_decider : int -> int -> int -> haltDecider **)

let nGramCPS_LRU_decider len_l len_r m1 tm =
  if nGramCPS_LRU_decider_0 len_l len_r m1 tm
  then Result_NonHalt
  else Result_Unknown

type listES = { l0 : _UU03a3_ list; r0 : _UU03a3_ list; m0 : _UU03a3_; s0 : st }

(** val listES_step' : _UU03a3_ trans -> listES -> listES **)

let listES_step' tr x =
  let { l0 = l2; r0 = r2; m0 = _; s0 = _ } = x in
  let { nxt = s2; dir0 = d; out = o } = tr in
  (match d with
   | Dneg ->
     (match l2 with
      | [] -> { l0 = []; r0 = (o :: r2); m0 = Coq__UU03a3_0; s0 = s2 }
      | m1 :: l3 -> { l0 = l3; r0 = (o :: r2); m0 = m1; s0 = s2 })
   | Dpos ->
     (match r2 with
      | [] -> { l0 = (o :: l2); r0 = []; m0 = Coq__UU03a3_0; s0 = s2 }
      | m1 :: r3 -> { l0 = (o :: l2); r0 = r3; m0 = m1; s0 = s2 }))

(** val startListES : listES **)

let startListES =
  { l0 = start_l; r0 = start_r; m0 = start_m; s0 = St0 }

(** val verify_loop1 :
    (listES * z) -> (listES * z) -> (listES * z) list -> (listES * z) list ->
    int -> z -> bool **)

let rec verify_loop1 h0 h1 ls0 ls1 n dpos =
  let (es0, d0) = h0 in
  let (es1, d1) = h1 in
  if st_eqb es0.s0 es1.s0
  then if _UU03a3__eqb es0.m0 es1.m0
       then if (fun fO fS n -> if n=0 then fO () else fS (n-1))
                 (fun _ ->
                 match dpos with
                 | Z0 -> Z.eqb d1 d0
                 | Zpos _ ->
                   (match es1.r0 with
                    | [] -> Z.ltb d1 d0
                    | _ :: _ -> false)
                 | Zneg _ ->
                   (match es1.l0 with
                    | [] -> Z.ltb d0 d1
                    | _ :: _ -> false))
                 (fun _ -> false)
                 n
            then true
            else (match ls0 with
                  | [] -> false
                  | h0' :: ls0' ->
                    (match ls1 with
                     | [] -> false
                     | h1' :: ls1' ->
                       verify_loop1 h0' h1' ls0' ls1' (Nat.pred n) dpos))
       else false
  else false

(** val find_loop1 :
    (listES * z) -> (listES * z) -> (listES * z) -> (listES * z) list ->
    (listES * z) list -> (listES * z) list -> int -> bool **)

let rec find_loop1 h0 h1 h2 ls0 ls1 ls2 n =
  if let (es0, d0) = h0 in
     let (es1, d1) = h1 in
     if st_eqb es0.s0 es1.s0
     then let (es2, _) = h2 in
          if st_eqb es0.s0 es2.s0
          then if _UU03a3__eqb es0.m0 es1.m0
               then if _UU03a3__eqb es0.m0 es2.m0
                    then verify_loop1 h0 h1 ls0 ls1 (Stdlib.Int.succ n)
                           (Z.sub d0 d1)
                    else false
               else false
          else false
     else false
  then true
  else (match ls2 with
        | [] -> false
        | _ :: l2 ->
          (match l2 with
           | [] -> false
           | h2' :: ls2' ->
             (match ls1 with
              | [] -> false
              | h1' :: ls1' ->
                find_loop1 h0 h1' h2' ls0 ls1' ls2' (Stdlib.Int.succ n))))

(** val find_loop1_0 :
    (listES * z) -> (listES * z) -> (listES * z) list -> bool **)

let find_loop1_0 h0 h1 ls = match ls with
| [] -> false
| h2 :: ls' -> find_loop1 h0 h1 h2 (h1 :: ls) ls ls' 0

(** val loop1_decider0 :
    _UU03a3_ tM -> int -> listES -> z -> (listES * z) list -> haltDecideResult **)

let rec loop1_decider0 tm n es d ls =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> Result_Unknown)
    (fun n0 ->
    match tm es.s0 es.m0 with
    | Some tr ->
      let es' = listES_step' tr es in
      let d' = Z.add d (dir_to_Z tr.dir0) in
      let ls' = (es, d) :: ls in
      ((fun fO fS n -> if n=0 then fO () else fS (n-1))
         (fun _ ->
         if find_loop1_0 (es', d') (es, d) ls
         then Result_NonHalt
         else loop1_decider0 tm n0 es' d' ls')
         (fun _ -> loop1_decider0 tm n0 es' d' ls')
         n0)
    | None -> Result_Halt (es.s0, es.m0))
    n

(** val loop1_decider : int -> _UU03a3_ tM -> haltDecideResult **)

let loop1_decider n tm =
  loop1_decider0 tm n startListES Z0 []

type word = _UU03a3_ list

type repeatWord = { w : word; min_cnt : int; is_const : bool }

type repeatWordList_ES = { l1 : repeatWord list; r1 : repeatWord list;
                           s1 : st; sgn : dir }

(** val all0 : word -> bool **)

let rec all0 = function
| [] -> true
| _UU03c3_ :: t0 ->
  (match _UU03c3_ with
   | Coq__UU03a3_0 -> all0 t0
   | _ -> false)

(** val word_eqb : word -> word -> bool **)

let rec word_eqb x1 x2 =
  match x1 with
  | [] -> (match x2 with
           | [] -> true
           | _ :: _ -> false)
  | h1 :: t1 ->
    (match x2 with
     | [] -> false
     | h2 :: t2 -> if _UU03a3__eqb h1 h2 then word_eqb t1 t2 else false)

(** val chunk_words : int -> int -> _UU03a3_ list -> word list **)

let rec chunk_words len fuel x =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> [])
    (fun f ->
    match x with
    | [] -> []
    | _ :: _ ->
      (firstn len (app x (repeat Coq__UU03a3_0 len))) :: (chunk_words len f
                                                           (skipn len x)))
    fuel

(** val const_word : word -> repeatWord **)

let const_word w0 =
  { w = w0; min_cnt = (Stdlib.Int.succ 0); is_const = true }

(** val repWL_StartES : int -> repeatWordList_ES **)

let repWL_StartES len =
  { l1 = (map const_word (chunk_words len (length start_l) start_l)); r1 =
    (map const_word
      (chunk_words len (Stdlib.Int.succ (length start_r))
        (start_m :: start_r))); s1 = St0; sgn = Dpos }

(** val pop :
    int -> repeatWord list -> (word * repeatWord list list) option **)

let pop len wl = match wl with
| [] -> Some ((repeat Coq__UU03a3_0 len), ([] :: []))
| v :: wl0 ->
  ((fun fO fS n -> if n=0 then fO () else fS (n-1))
     (fun _ -> None)
     (fun n0 -> Some (v.w,
     (((fun fO fS n -> if n=0 then fO () else fS (n-1))
         (fun _ -> wl0)
         (fun _ -> { w = v.w; min_cnt = n0; is_const = true } :: wl0)
         n0) :: (if v.is_const then [] else wl :: []))))
     v.min_cnt)

(** val push : int -> repeatWord list -> word -> repeatWord list **)

let push min_nonconst_len wl w0 =
  match wl with
  | [] ->
    if all0 w0
    then []
    else { w = w0; min_cnt = (Stdlib.Int.succ 0); is_const = true } :: wl
  | v0 :: wl0 ->
    if word_eqb v0.w w0
    then let cnt = Stdlib.Int.succ v0.min_cnt in
         (if Nat.ltb cnt min_nonconst_len
          then { w = w0; min_cnt = cnt; is_const = v0.is_const }
          else { w = w0; min_cnt = min_nonconst_len; is_const = false }) :: wl0
    else { w = w0; min_cnt = (Stdlib.Int.succ 0); is_const = true } :: wl

(** val wordUpdate_step0 :
    _UU03a3_ tM -> listES -> (listES * dir option) option **)

let wordUpdate_step0 tm x =
  let { l0 = l2; r0 = r2; m0 = m1; s0 = s2 } = x in
  (match tm s2 m1 with
   | Some tr ->
     let { nxt = s3; dir0 = d; out = o } = tr in
     Some
     (match d with
      | Dneg ->
        (match l2 with
         | [] -> ({ l0 = []; r0 = r2; m0 = o; s0 = s3 }, (Some Dneg))
         | m2 :: l3 -> ({ l0 = l3; r0 = (o :: r2); m0 = m2; s0 = s3 }, None))
      | Dpos ->
        (match r2 with
         | [] -> ({ l0 = l2; r0 = []; m0 = o; s0 = s3 }, (Some Dpos))
         | m2 :: r3 -> ({ l0 = (o :: l2); r0 = r3; m0 = m2; s0 = s3 }, None)))
   | None -> None)

(** val wordUpdate_steps :
    _UU03a3_ tM -> listES -> int -> (listES * dir) option **)

let rec wordUpdate_steps tm x n =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> None)
    (fun n0 ->
    match wordUpdate_step0 tm x with
    | Some p ->
      let (x0, o) = p in
      (match o with
       | Some d -> Some (x0, d)
       | None -> wordUpdate_steps tm x0 n0)
    | None -> None)
    n

(** val wordUpdate :
    int -> _UU03a3_ tM -> st -> word -> dir -> ((st * word) * bool) option **)

let wordUpdate wordUpdate_MAXT tm s2 w0 sgn0 =
  match w0 with
  | [] -> None
  | m1 :: w1 ->
    (match match sgn0 with
           | Dneg ->
             wordUpdate_steps tm { l0 = w1; r0 = []; m0 = m1; s0 = s2 }
               wordUpdate_MAXT
           | Dpos ->
             wordUpdate_steps tm { l0 = []; r0 = w1; m0 = m1; s0 = s2 }
               wordUpdate_MAXT with
     | Some p ->
       let (l2, d) = p in
       let { l0 = l3; r0 = r2; m0 = m2; s0 = s3 } = l2 in
       (match d with
        | Dneg -> Some ((s3, (m2 :: r2)), (negb (dir_eqb sgn0 d)))
        | Dpos -> Some ((s3, (m2 :: l3)), (negb (dir_eqb sgn0 d))))
     | None -> None)

(** val repWL_step00 :
    int -> int -> _UU03a3_ tM -> repeatWordList_ES -> word -> repeatWord list
    -> repeatWordList_ES option **)

let repWL_step00 min_nonconst_len wordUpdate_MAXT tm x w0 r2 =
  let { l1 = l2; r1 = _; s1 = s2; sgn = sgn0 } = x in
  (match wordUpdate wordUpdate_MAXT tm s2 w0 sgn0 with
   | Some p ->
     let (p0, is_back) = p in
     let (s3, w1) = p0 in
     if is_back
     then Some { l1 = (push min_nonconst_len r2 w1); r1 = l2; s1 = s3; sgn =
            (dir_rev sgn0) }
     else Some { l1 = (push min_nonconst_len l2 w1); r1 = r2; s1 = s3; sgn =
            sgn0 }
   | None -> None)

(** val repWL_step0 :
    int -> int -> _UU03a3_ tM -> repeatWordList_ES -> word -> repeatWord list
    list -> repeatWordList_ES list option **)

let rec repWL_step0 min_nonconst_len wordUpdate_MAXT tm x w0 = function
| [] -> Some []
| r2 :: ls0 ->
  (match repWL_step00 min_nonconst_len wordUpdate_MAXT tm x w0 r2 with
   | Some x1 ->
     (match repWL_step0 min_nonconst_len wordUpdate_MAXT tm x w0 ls0 with
      | Some ret -> Some (x1 :: ret)
      | None -> None)
   | None -> None)

(** val repWL_step :
    int -> int -> int -> _UU03a3_ tM -> repeatWordList_ES ->
    repeatWordList_ES list option **)

let repWL_step len min_nonconst_len wordUpdate_MAXT tm x =
  let { l1 = _; r1 = r2; s1 = _; sgn = _ } = x in
  (match pop len r2 with
   | Some p ->
     let (w0, ls) = p in
     repWL_step0 min_nonconst_len wordUpdate_MAXT tm x w0 ls
   | None -> None)

(** val repeatWord_enc : repeatWord -> positive **)

let repeatWord_enc x =
  let { w = w0; min_cnt = mc; is_const = isc } = x in
  enc_list
    ((list_UU03a3__enc w0) :: ((Pos.of_succ_nat mc) :: ((bool_enc isc) :: [])))

(** val list_enc : ('a1 -> positive) -> 'a1 list -> positive **)

let list_enc t_enc ls =
  enc_list (map t_enc ls)

(** val repWL_ES_enc : repeatWordList_ES -> positive **)

let repWL_ES_enc x =
  let { l1 = l2; r1 = r2; s1 = s2; sgn = sgn0 } = x in
  enc_list
    ((dir_enc sgn0) :: ((st_enc s2) :: ((list_enc repeatWord_enc l2) :: (
    (list_enc repeatWord_enc r2) :: []))))

(** val ins_all :
    ('a1 -> positive) -> 'a1 list -> unit PositiveMap.tree -> 'a1 list -> 'a1
    list * unit PositiveMap.tree **)

let rec ins_all t_enc q st0 = function
| [] -> (q, st0)
| h :: ls0 ->
  let (q', st') = fst (set_ins t_enc (q, st0) h) in ins_all t_enc q' st' ls0

(** val t_close_set_searcher :
    ('a1 -> positive) -> (_UU03a3_ tM -> 'a1 -> 'a1 list option) -> _UU03a3_
    tM -> int -> 'a1 list -> unit PositiveMap.tree -> ('a1 list * unit
    PositiveMap.tree) option **)

let rec t_close_set_searcher t_enc t_step tm n q st0 =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> Some (q, st0))
    (fun n0 ->
    match q with
    | [] -> Some (q, st0)
    | x :: q0 ->
      (match t_step tm x with
       | Some ls ->
         let (q', st') = ins_all t_enc q0 st0 ls in
         t_close_set_searcher t_enc t_step tm n0 q' st'
       | None -> None))
    n

(** val t_decider0 :
    ('a1 -> positive) -> 'a1 -> (_UU03a3_ tM -> 'a1 -> 'a1 list option) ->
    int -> _UU03a3_ tM -> bool **)

let t_decider0 t_enc t_InitES t_step n tm =
  let (q0, st0) = fst (set_ins t_enc ([], PositiveMap.empty) t_InitES) in
  (match t_close_set_searcher t_enc t_step tm n q0 st0 with
   | Some p ->
     let (l2, q2') = p in
     (match l2 with
      | [] ->
        (match PositiveMap.find (t_enc t_InitES) q2' with
         | Some _ -> true
         | None -> false)
      | _ :: _ -> false)
   | None -> false)

(** val t_decider :
    ('a1 -> positive) -> 'a1 -> (_UU03a3_ tM -> 'a1 -> 'a1 list option) ->
    int -> haltDecider **)

let t_decider t_enc t_InitES t_step n tm =
  if t_decider0 t_enc t_InitES t_step n tm
  then Result_NonHalt
  else Result_Unknown

(** val repWL_ES_decider : int -> int -> int -> int -> haltDecider **)

let repWL_ES_decider len min_nonconst_len wordUpdate_MAXT n =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ _ -> Result_Unknown)
    (fun _ ->
    t_decider repWL_ES_enc (repWL_StartES len)
      (repWL_step len min_nonconst_len wordUpdate_MAXT) n)
    len

(** val halt_decider0 : _UU03a3_ tM -> int -> listES -> haltDecideResult **)

let rec halt_decider0 tm n es =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> Result_Unknown)
    (fun n0 ->
    match tm es.s0 es.m0 with
    | Some tr -> halt_decider0 tm n0 (listES_step' tr es)
    | None -> Result_Halt (es.s0, es.m0))
    n

(** val halt_decider : int -> _UU03a3_ tM -> haltDecideResult **)

let halt_decider n tm =
  halt_decider0 tm n startListES
