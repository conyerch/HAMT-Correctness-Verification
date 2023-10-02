
type nat =
| O
| S of nat

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
    | XH ->
      (match y with
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
    | Npos p ->
      (match m with
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

  (** val of_nat : nat -> z **)

  let of_nat = function
  | O -> Z0
  | S n1 -> Zpos (Pos.of_succ_nat n1)

  (** val of_N : n -> z **)

  let of_N = function
  | N0 -> Z0
  | Npos p -> Zpos p

  (** val coq_lor : z -> z -> z **)

  let coq_lor a b =
    match a with
    | Z0 -> b
    | Zpos a0 ->
      (match b with
       | Z0 -> a
       | Zpos b0 -> Zpos (Pos.coq_lor a0 b0)
       | Zneg b0 ->
         Zneg (N.succ_pos (N.ldiff (Pos.pred_N b0) (Npos a0))))
    | Zneg a0 ->
      (match b with
       | Z0 -> a
       | Zpos b0 ->
         Zneg (N.succ_pos (N.ldiff (Pos.pred_N a0) (Npos b0)))
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

(** val hasher2 : nat -> z **)

let hasher2 key =
  let int_initial = Z.of_nat key in
  let hash = Z.mul fMV_prime fMV_offset in
  let hash0 =
    Z.coq_lor hash
      (Z.coq_land int_initial (Zpos (XI (XI (XI (XI (XI (XI (XI
        XH)))))))))
  in
  let hash1 = Z.mul fMV_prime hash0 in
  let hash2 =
    Z.coq_lor hash1
      (Z.coq_land int_initial (Zpos (XO (XO (XO (XO (XO (XO (XO (XO
        (XI (XI (XI (XI (XI (XI (XI XH)))))))))))))))))
  in
  let hash3 = Z.mul fMV_prime hash2 in
  let hash4 =
    Z.coq_lor hash3
      (Z.coq_land int_initial (Zpos (XO (XO (XO (XO (XO (XO (XO (XO
        (XO (XO (XO (XO (XO (XO (XO (XO (XI (XI (XI (XI (XI (XI (XI
        XH)))))))))))))))))))))))))
  in
  let hash5 = Z.mul fMV_prime hash4 in
  let hash6 =
    Z.coq_lor hash5
      (Z.coq_land int_initial (Zpos (XO (XO (XO (XO (XO (XO (XO (XO
        (XO (XO (XO (XO (XO (XO (XO (XO (XO (XO (XO (XO (XO (XO (XO
        (XO (XI (XI (XI (XI (XI (XI (XI
        XH)))))))))))))))))))))))))))))))))
  in
  let hash7 = Z.mul fMV_prime hash6 in
  let hash8 =
    Z.coq_lor hash7
      (Z.coq_land int_initial (Zpos (XO (XO (XO (XO (XO (XO (XO (XO
        (XO (XO (XO (XO (XO (XO (XO (XO (XO (XO (XO (XO (XO (XO (XO
        (XO (XO (XO (XO (XO (XO (XO (XO (XO (XI (XI (XI (XI (XI (XI
        (XI XH)))))))))))))))))))))))))))))))))))))))))
  in
  let hash9 = Z.mul fMV_prime hash8 in
  let hash10 =
    Z.coq_lor hash9
      (Z.coq_land int_initial (Zpos (XO (XO (XO (XO (XO (XO (XO (XO
        (XO (XO (XO (XO (XO (XO (XO (XO (XO (XO (XO (XO (XO (XO (XO
        (XO (XO (XO (XO (XO (XO (XO (XO (XO (XO (XO (XO (XO (XO (XO
        (XO (XO (XI (XI (XI (XI (XI (XI (XI
        XH)))))))))))))))))))))))))))))))))))))))))))))))))
  in
  let hash11 = Z.mul fMV_prime hash10 in
  let hash12 =
    Z.coq_lor hash11
      (Z.coq_land int_initial (Zpos (XO (XO (XO (XO (XO (XO (XO (XO
        (XO (XO (XO (XO (XO (XO (XO (XO (XO (XO (XO (XO (XO (XO (XO
        (XO (XO (XO (XO (XO (XO (XO (XO (XO (XO (XO (XO (XO (XO (XO
        (XO (XO (XO (XO (XO (XO (XO (XO (XO (XO (XI (XI (XI (XI (XI
        (XI (XI
        XH)))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  in
  let hash13 = Z.mul fMV_prime hash12 in
  Z.coq_lor hash13
    (Z.coq_land int_initial (Zpos (XO (XO (XO (XO (XO (XO (XO (XO (XO
      (XO (XO (XO (XO (XO (XO (XO (XO (XO (XO (XO (XO (XO (XO (XO (XO
      (XO (XO (XO (XO (XO (XO (XO (XO (XO (XO (XO (XO (XO (XO (XO (XO
      (XO (XO (XO (XO (XO (XO (XO (XO (XO (XO (XO (XO (XO (XO (XO (XI
      (XI (XI (XI (XI (XI (XI
      XH)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
