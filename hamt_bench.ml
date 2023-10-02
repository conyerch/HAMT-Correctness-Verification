
type bool =
| True
| False

type nat =
| O
| S of nat

type 'a option =
| Some of 'a
| None

type ('a, 'b) prod =
| Pair of 'a * 'b

type 'a list =
| Nil
| Cons of 'a * 'a list

type comparison =
| Eq
| Lt
| Gt

(** val compOpp : comparison -> comparison **)

let compOpp = function
| Eq -> Eq
| Lt -> Gt
| Gt -> Lt

type positive =
| XI of positive
| XO of positive
| XH

type n =
| N0
| Npos of positive

type z =
| Z0
| Zpos of positive
| Zneg of positive

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

  (** val pred_N : positive -> n **)

  let pred_N = function
  | XI p -> Npos (XO p)
  | XO p -> Npos (pred_double p)
  | XH -> N0

  (** val mul : positive -> positive -> positive **)

  let rec mul x y =
    match x with
    | XI p -> add y (XO (mul p y))
    | XO p -> XO (mul p y)
    | XH -> y

  (** val iter : ('a1 -> 'a1) -> 'a1 -> positive -> 'a1 **)

  let rec iter f x = function
  | XI n' -> f (iter f (iter f x n') n')
  | XO n' -> iter f (iter f x n') n'
  | XH -> f x

  (** val div2 : positive -> positive **)

  let div2 = function
  | XI p0 -> p0
  | XO p0 -> p0
  | XH -> XH

  (** val div2_up : positive -> positive **)

  let div2_up = function
  | XI p0 -> succ p0
  | XO p0 -> p0
  | XH -> XH

  (** val compare_cont : comparison -> positive -> positive -> comparison **)

  let rec compare_cont r x y =
    match x with
    | XI p ->
      (match y with
       | XI q -> compare_cont r p q
       | XO q -> compare_cont Gt p q
       | XH -> Gt)
    | XO p ->
      (match y with
       | XI q -> compare_cont Lt p q
       | XO q -> compare_cont r p q
       | XH -> Gt)
    | XH -> (match y with
             | XH -> r
             | _ -> Lt)

  (** val compare : positive -> positive -> comparison **)

  let compare =
    compare_cont Eq

  (** val coq_Nsucc_double : n -> n **)

  let coq_Nsucc_double = function
  | N0 -> Npos XH
  | Npos p -> Npos (XI p)

  (** val coq_Ndouble : n -> n **)

  let coq_Ndouble = function
  | N0 -> N0
  | Npos p -> Npos (XO p)

  (** val coq_lor : positive -> positive -> positive **)

  let rec coq_lor p q =
    match p with
    | XI p0 ->
      (match q with
       | XI q0 -> XI (coq_lor p0 q0)
       | XO q0 -> XI (coq_lor p0 q0)
       | XH -> p)
    | XO p0 ->
      (match q with
       | XI q0 -> XI (coq_lor p0 q0)
       | XO q0 -> XO (coq_lor p0 q0)
       | XH -> XI p0)
    | XH -> (match q with
             | XO q0 -> XI q0
             | _ -> q)

  (** val coq_land : positive -> positive -> n **)

  let rec coq_land p q =
    match p with
    | XI p0 ->
      (match q with
       | XI q0 -> coq_Nsucc_double (coq_land p0 q0)
       | XO q0 -> coq_Ndouble (coq_land p0 q0)
       | XH -> Npos XH)
    | XO p0 ->
      (match q with
       | XI q0 -> coq_Ndouble (coq_land p0 q0)
       | XO q0 -> coq_Ndouble (coq_land p0 q0)
       | XH -> N0)
    | XH -> (match q with
             | XO _ -> N0
             | _ -> Npos XH)

  (** val ldiff : positive -> positive -> n **)

  let rec ldiff p q =
    match p with
    | XI p0 ->
      (match q with
       | XI q0 -> coq_Ndouble (ldiff p0 q0)
       | XO q0 -> coq_Nsucc_double (ldiff p0 q0)
       | XH -> Npos (XO p0))
    | XO p0 ->
      (match q with
       | XI q0 -> coq_Ndouble (ldiff p0 q0)
       | XO q0 -> coq_Ndouble (ldiff p0 q0)
       | XH -> Npos p)
    | XH -> (match q with
             | XO _ -> Npos XH
             | _ -> N0)

  (** val of_succ_nat : nat -> positive **)

  let rec of_succ_nat = function
  | O -> XH
  | S x -> succ (of_succ_nat x)
 end

module N =
 struct
  (** val succ_pos : n -> positive **)

  let succ_pos = function
  | N0 -> XH
  | Npos p -> Pos.succ p

  (** val coq_lor : n -> n -> n **)

  let coq_lor n0 m =
    match n0 with
    | N0 -> m
    | Npos p -> (match m with
                 | N0 -> n0
                 | Npos q -> Npos (Pos.coq_lor p q))

  (** val coq_land : n -> n -> n **)

  let coq_land n0 m =
    match n0 with
    | N0 -> N0
    | Npos p -> (match m with
                 | N0 -> N0
                 | Npos q -> Pos.coq_land p q)

  (** val ldiff : n -> n -> n **)

  let ldiff n0 m =
    match n0 with
    | N0 -> N0
    | Npos p -> (match m with
                 | N0 -> n0
                 | Npos q -> Pos.ldiff p q)
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

  (** val of_nat : nat -> z **)

  let of_nat = function
  | O -> Z0
  | S n1 -> Zpos (Pos.of_succ_nat n1)

  (** val of_N : n -> z **)

  let of_N = function
  | N0 -> Z0
  | Npos p -> Zpos p

  (** val div2 : z -> z **)

  let div2 = function
  | Z0 -> Z0
  | Zpos p -> (match p with
               | XH -> Z0
               | _ -> Zpos (Pos.div2 p))
  | Zneg p -> Zneg (Pos.div2_up p)

  (** val shiftl : z -> z -> z **)

  let shiftl a = function
  | Z0 -> a
  | Zpos p -> Pos.iter (mul (Zpos (XO XH))) a p
  | Zneg p -> Pos.iter div2 a p

  (** val shiftr : z -> z -> z **)

  let shiftr a n0 =
    shiftl a (opp n0)

  (** val coq_lor : z -> z -> z **)

  let coq_lor a b =
    match a with
    | Z0 -> b
    | Zpos a0 ->
      (match b with
       | Z0 -> a
       | Zpos b0 -> Zpos (Pos.coq_lor a0 b0)
       | Zneg b0 -> Zneg (N.succ_pos (N.ldiff (Pos.pred_N b0) (Npos a0))))
    | Zneg a0 ->
      (match b with
       | Z0 -> a
       | Zpos b0 -> Zneg (N.succ_pos (N.ldiff (Pos.pred_N a0) (Npos b0)))
       | Zneg b0 ->
         Zneg (N.succ_pos (N.coq_land (Pos.pred_N a0) (Pos.pred_N b0))))

  (** val coq_land : z -> z -> z **)

  let coq_land a b =
    match a with
    | Z0 -> Z0
    | Zpos a0 ->
      (match b with
       | Z0 -> Z0
       | Zpos b0 -> of_N (Pos.coq_land a0 b0)
       | Zneg b0 -> of_N (N.ldiff (Npos a0) (Pos.pred_N b0)))
    | Zneg a0 ->
      (match b with
       | Z0 -> Z0
       | Zpos b0 -> of_N (N.ldiff (Npos b0) (Pos.pred_N a0))
       | Zneg b0 ->
         Zneg (N.succ_pos (N.coq_lor (Pos.pred_N a0) (Pos.pred_N b0))))
 end

(** val zeq_bool : z -> z -> bool **)

let zeq_bool x y =
  match Z.compare x y with
  | Eq -> True
  | _ -> False

type int (* AXIOM TO BE REALIZED *)

(** val lsl0 : int -> int -> int **)

let lsl0 =
  failwith "AXIOM TO BE REALIZED"

(** val lsr0 : int -> int -> int **)

let lsr0 =
  failwith "AXIOM TO BE REALIZED"

(** val land0 : int -> int -> int **)

let land0 =
  failwith "AXIOM TO BE REALIZED"

(** val lor0 : int -> int -> int **)

let lor0 =
  failwith "AXIOM TO BE REALIZED"

(** val sub : int -> int -> int **)

let sub =
  failwith "AXIOM TO BE REALIZED"

(** val eqb : int -> int -> bool **)

let eqb =
  failwith "AXIOM TO BE REALIZED"

(** val size : nat **)

let size =
  S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

(** val is_zero : int -> bool **)

let is_zero i =
  eqb i (Uint63.of_int (0))

(** val is_even : int -> bool **)

let is_even i =
  is_zero (land0 i (Uint63.of_int (1)))

(** val opp0 : int -> int **)

let opp0 i =
  sub (Uint63.of_int (0)) i

(** val to_Z_rec : nat -> int -> z **)

let rec to_Z_rec n0 i =
  match n0 with
  | O -> Z0
  | S n1 ->
    (match is_even i with
     | True -> Z.double (to_Z_rec n1 (lsr0 i (Uint63.of_int (1))))
     | False -> Z.succ_double (to_Z_rec n1 (lsr0 i (Uint63.of_int (1)))))

(** val to_Z : int -> z **)

let to_Z =
  to_Z_rec size

(** val of_pos_rec : nat -> positive -> int **)

let rec of_pos_rec n0 p =
  match n0 with
  | O -> (Uint63.of_int (0))
  | S n1 ->
    (match p with
     | XI p0 ->
       lor0 (lsl0 (of_pos_rec n1 p0) (Uint63.of_int (1))) (Uint63.of_int (1))
     | XO p0 -> lsl0 (of_pos_rec n1 p0) (Uint63.of_int (1))
     | XH -> (Uint63.of_int (1)))

(** val of_pos : positive -> int **)

let of_pos =
  of_pos_rec size

(** val of_Z : z -> int **)

let of_Z = function
| Z0 -> (Uint63.of_int (0))
| Zpos p -> of_pos p
| Zneg p -> opp0 (of_pos p)

type 'x array (* AXIOM TO BE REALIZED *)

(** val make : int -> 'a1 -> 'a1 array **)

let make =
  failwith "AXIOM TO BE REALIZED"

(** val get : 'a1 array -> int -> 'a1 **)

let get =
  failwith "AXIOM TO BE REALIZED"

(** val set : 'a1 array -> int -> 'a1 -> 'a1 array **)

let set =
  failwith "AXIOM TO BE REALIZED"

type 'a hAMT =
| Empty
| HashMapEntry of z * key * 'a
| ArrayNode of z * 'a hAMT array
| CollisionNode of z * (key, 'a) prod list

(** val empty_HAMT : 'a1 hAMT **)

let empty_HAMT =
  Empty

(** val hasher2 : nat -> z **)

let hasher2 key0 =
  let int_initial = Z.of_nat key0 in
  let hash = Z.mul fMV_prime fMV_offset in
  let hash0 =
    Z.coq_lor hash
      (Z.coq_land int_initial (Zpos (XI (XI (XI (XI (XI (XI (XI XH)))))))))
  in
  let hash1 = Z.mul fMV_prime hash0 in
  let hash2 =
    Z.coq_lor hash1
      (Z.coq_land int_initial (Zpos (XO (XO (XO (XO (XO (XO (XO (XO (XI (XI
        (XI (XI (XI (XI (XI XH)))))))))))))))))
  in
  let hash3 = Z.mul fMV_prime hash2 in
  let hash4 =
    Z.coq_lor hash3
      (Z.coq_land int_initial (Zpos (XO (XO (XO (XO (XO (XO (XO (XO (XO (XO
        (XO (XO (XO (XO (XO (XO (XI (XI (XI (XI (XI (XI (XI
        XH)))))))))))))))))))))))))
  in
  let hash5 = Z.mul fMV_prime hash4 in
  let hash6 =
    Z.coq_lor hash5
      (Z.coq_land int_initial (Zpos (XO (XO (XO (XO (XO (XO (XO (XO (XO (XO
        (XO (XO (XO (XO (XO (XO (XO (XO (XO (XO (XO (XO (XO (XO (XI (XI (XI
        (XI (XI (XI (XI XH)))))))))))))))))))))))))))))))))
  in
  let hash7 = Z.mul fMV_prime hash6 in
  let hash8 =
    Z.coq_lor hash7
      (Z.coq_land int_initial (Zpos (XO (XO (XO (XO (XO (XO (XO (XO (XO (XO
        (XO (XO (XO (XO (XO (XO (XO (XO (XO (XO (XO (XO (XO (XO (XO (XO (XO
        (XO (XO (XO (XO (XO (XI (XI (XI (XI (XI (XI (XI
        XH)))))))))))))))))))))))))))))))))))))))))
  in
  let hash9 = Z.mul fMV_prime hash8 in
  let hash10 =
    Z.coq_lor hash9
      (Z.coq_land int_initial (Zpos (XO (XO (XO (XO (XO (XO (XO (XO (XO (XO
        (XO (XO (XO (XO (XO (XO (XO (XO (XO (XO (XO (XO (XO (XO (XO (XO (XO
        (XO (XO (XO (XO (XO (XO (XO (XO (XO (XO (XO (XO (XO (XI (XI (XI (XI
        (XI (XI (XI XH)))))))))))))))))))))))))))))))))))))))))))))))))
  in
  let hash11 = Z.mul fMV_prime hash10 in
  let hash12 =
    Z.coq_lor hash11
      (Z.coq_land int_initial (Zpos (XO (XO (XO (XO (XO (XO (XO (XO (XO (XO
        (XO (XO (XO (XO (XO (XO (XO (XO (XO (XO (XO (XO (XO (XO (XO (XO (XO
        (XO (XO (XO (XO (XO (XO (XO (XO (XO (XO (XO (XO (XO (XO (XO (XO (XO
        (XO (XO (XO (XO (XI (XI (XI (XI (XI (XI (XI
        XH)))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  in
  let hash13 = Z.mul fMV_prime hash12 in
  Z.coq_lor hash13
    (Z.coq_land int_initial (Zpos (XO (XO (XO (XO (XO (XO (XO (XO (XO (XO (XO
      (XO (XO (XO (XO (XO (XO (XO (XO (XO (XO (XO (XO (XO (XO (XO (XO (XO (XO
      (XO (XO (XO (XO (XO (XO (XO (XO (XO (XO (XO (XO (XO (XO (XO (XO (XO (XO
      (XO (XO (XO (XO (XO (XO (XO (XO (XO (XI (XI (XI (XI (XI (XI (XI
      XH)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

(** val findv : (key, 'a1) prod list -> key -> 'a1 option **)

let rec findv hmes k1 =
  match hmes with
  | Nil -> None
  | Cons (p, t) ->
    let Pair (k, v) = p in
    (match eqb0 k k1 with
     | True -> Some v
     | False -> findv t k1)

(** val find : 'a1 hAMT -> key -> 'a1 option **)

let rec find hamt k =
  match hamt with
  | Empty -> None
  | HashMapEntry (_, k1, val0) ->
    (match eqb0 k k1 with
     | True -> Some val0
     | False -> None)
  | ArrayNode (shift0, map) ->
    find (get map (of_Z (Z.coq_land (Z.shiftr (hasher2 k) shift0) mask))) k
  | CollisionNode (_, hmes) -> findv hmes k

(** val remove_ass : key -> (key, 'a1) prod list -> (key, 'a1) prod list **)

let rec remove_ass k = function
| Nil -> Nil
| Cons (p, tl) ->
  let Pair (k1, v) = p in
  (match eqb0 k k1 with
   | True -> remove_ass k tl
   | False -> Cons ((Pair (k1, v)), (remove_ass k tl)))

(** val remove : 'a1 hAMT -> key -> 'a1 hAMT **)

let rec remove hamt k =
  match hamt with
  | ArrayNode (shifter, map) ->
    let index = of_Z (Z.coq_land (Z.shiftr (hasher2 k) shifter) mask) in
    let newVal = remove (get map index) k in
    ArrayNode (shift, (set map index newVal))
  | CollisionNode (hash, hmes) ->
    let newl = remove_ass k hmes in
    (match newl with
     | Nil -> Empty
     | Cons (_, _) -> CollisionNode (hash, newl))
  | _ -> Empty

(** val add0 : 'a1 hAMT -> key -> 'a1 -> z -> 'a1 hAMT **)

let rec add0 hamt k val0 shifter =
  match hamt with
  | Empty -> HashMapEntry ((hasher2 k), k, val0)
  | HashMapEntry (hash1, key0, val1) ->
    let index1 = of_Z (Z.coq_land (Z.shiftr (hasher2 key0) shifter) mask) in
    let index2 = of_Z (Z.coq_land (Z.shiftr (hasher2 k) shifter) mask) in
    let newArr = make (Uint63.of_int (32)) empty_HAMT in
    (match zeq_bool (to_Z index1) (to_Z index2) with
     | True ->
       ArrayNode ((Z.add shifter shift),
         (set newArr index1 (CollisionNode (hash1, (Cons ((Pair (key0,
           val1)), (Cons ((Pair (k, val0)), Nil))))))))
     | False ->
       let newArr2 = set newArr index2 (HashMapEntry ((hasher2 k), k, val0))
       in
       ArrayNode ((Z.add shifter shift), newArr2))
  | ArrayNode (shift1, map) ->
    let index = of_Z (Z.coq_land (Z.shiftr (hasher2 k) shift1) mask) in
    let newVal = add0 (get map index) k val0 (Z.add shifter shift) in
    ArrayNode (shift1, (set map index newVal))
  | CollisionNode (hash, hmes) ->
    CollisionNode (hash, (Cons ((Pair (k, val0)), hmes)))




