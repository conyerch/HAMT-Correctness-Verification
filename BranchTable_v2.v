(* From Coq Require Import Strings.String.  (* for manual grading *) *)
From Coq Require Export Bool.Bool.
(* From Coq Require Export Arith.Arith. *)
(* From Coq Require Export Arith.EqNat. *)
(* From Coq Require Export Lia. *)
From Coq Require Export Lists.List.
Export ListNotations.
(* From Coq Require Export Permutation. *)

(* From Coq Require Import String.  (* for manual grading *) *)
(*From VFA Require Import Perm. *)
(* From VFA Require Import Maps. *)
(* From VFA Require Import SearchTree. *)

(* From VFA Require Import LibTactics. *)

Class Eq A :=
  {
    eqb: A -> A -> bool
  }.
Notation "x =? y" := (eqb x y) (at level 70).

Class EqDec A {H:Eq A} :=
  {
    eqb_reflect : forall (k1 k2 : A), reflect (k1=k2) (eqb k1 k2);
  }.

Proposition eqb_eq `{EqDec} : forall x y, x =? y = true <-> x = y .
Proof.
  split; destruct (eqb_reflect x y); auto; discriminate.
Qed.

Proposition eqb_neq `{EqDec} : forall x y, x <> y <-> (x =? y) = false.
Proof.
  split; destruct(eqb_reflect x y); auto; intros; exfalso; auto; discriminate.
Qed.

#[export] Instance eqNat : Eq nat :=
  {
    eqb := Nat.eqb
  }.

#[export] Instance eqDecNat : EqDec nat.
Proof.
  constructor. intros. generalize dependent k1. induction k2.
  - destruct k1; constructor; auto.
  - induction k1.
    + constructor. auto.
    + simpl. specialize (IHk2 k1).
      destruct (k1=?k2) eqn:E; simpl in *; rewrite E in *;
        constructor; inversion IHk2; auto.
Qed.

#[export] Instance eqProd {A B : Type} `{Eq A} `{Eq B} : Eq (prod A B) :=
  {
    eqb x y := match x, y with
               | (x1,x2), (y1,y2) => (x1 =? y1) && (x2 =? y2)
               end
  }.

#[export] Instance eqDecProd {A B : Type} `{EqDec A} `{EqDec B} : EqDec (prod A B).
Proof.
  constructor. intros [x1 x2] [y1 y2]. simpl.
  destruct (x1 =? y1) eqn:E1, (x2 =? y2) eqn:E2; constructor.
  - apply eqb_eq in E1,E2. subst. auto.
  - apply eqb_neq in E2. intro Heq. inversion Heq. auto.
  - apply eqb_neq in E1. intro Heq. inversion Heq. auto.
  - apply eqb_neq in E1,E2. intro Heq. inversion Heq. auto.
Qed.

(* Class ValType V := *)
(*   { *)
(*     default : V *)
(*   }. *)

(* #[export] Instance valTypeNatZero : ValType nat := *)
(*   { default := 0 }. *)

Class Table (key V:Type) (default:V) `{EqDec key} :=
  {
    table : Type;
    empty : table;
    get : key -> table -> V;
    set : key -> V -> table -> table;
  }.

Class AlgebraicTable (key V:Type) (default:V) `{Table key V} :=
  {
    get_empty_default : forall (k : key), get k empty = default;
    get_set_same : forall (k : key) (v : V) (t : table),
      get k (set k v t) = v;
    get_set_other : forall (k k' : key) (v : V) (t : table),
      k <> k' -> get k' (set k v t) = get k' t
  }.

#[export] Instance FunTable (key V :Type) (default:V) `{EqDec key} :
  Table key V default :=
  {
    empty _ := default;
    get k t := t k;
    set k v t := fun k' => if k =? k' then v else t k'
  }.

#[export] Instance FunTableAlgebraic (key V:Type) (default:V) `{EqDec key} :
  @AlgebraicTable key V default _ _ _ (FunTable key V default).
Proof.
  constructor; auto; intros; simpl.
  - destruct (eqb_eq k k) as [_ Heq]. rewrite Heq; auto.
  - destruct (eqb_neq k k') as [Hneq _]. rewrite Hneq; auto.
Qed.

#[export] Instance BranchTable (key1 key2 V : Type) (default:V)
  `{HT2 : Table key2 V default} `{HT1 : Table key1 HT2.(table) HT2.(empty)}
  : Table (prod key1 key2) V default :=
  {
    table := HT1.(table);
    empty :=  HT1.(empty);
    get k t := match k with
               | (k1,k2) => get k2 (get k1 t)
               end;
    set k v t := match k with
                 | (k1,k2) => set k1 (set k2 v (get k1 t)) t
                 end
  }.

#[export] Instance BranchTableAlgebraic (key1 key2 V : Type) (default:V)
  `{HT2 : Table key2 V default} `{HT1 : Table key1 HT2.(table) HT2.(empty)}
  `{HAT2 : AlgebraicTable key2 V default}
  `{HAT1 : AlgebraicTable key1 HT2.(table) HT2.(empty)} :
  @AlgebraicTable (prod key1 key2) V default _ _ _ (BranchTable key1 key2 V default).
Proof.
  constructor; intros; destruct k as [k1 k2]; auto.
  - simpl.
    destruct (eqb_eq k1 k1) as [_ Heq1]. rewrite Heq1; auto.
    destruct (eqb_eq k2 k2) as [_ Heq2]. rewrite Heq2; auto.
  - destruct k' as [k1' k2']. simpl.
    destruct (eqb_reflect k1 k1') as [?|?],
        (eqb_reflect k2 k2') as [?|?]; subst; auto.
    + exfalso. auto.
Qed.

Class HAMT (key1 key2 V:Type) (default:V) `{EqDec key1} `{EqDec key2}
`{HT2 : Table key2 V default} `{HT1 : Table key1 HT2.(table) HT2.(empty)} :=
  {
    hamt : Type;
    emptyH : hamt;
    getH : key2 -> list key1 -> hamt -> V;
    setH : key2 -> list key1 -> V -> hamt -> hamt;
  }.

Class ModularHAMT (key1 key2 V:Type) (default:V) `{HAMT key1 key2 V} :=
  {
    get_empty_default_HAMT : forall (k1 : list key1) (k2 : key2), getH k2 k1 emptyH = default;
    get_set_same_HAMT : forall (k1 : list key1) (k2 : key2) (v : V) (h : hamt),
      getH k2 k1 (setH k2 k1 v h) = v;
    get_set_other_HAMT : forall (k k' : key2) (k1 k2 : list key1) (v : V) (h : hamt),
      k <> k' /\ k1 <> k2 -> getH k' k2 (setH k k1 v h) = getH k' k2 h
  }.


  (* what is the stopping condition for set *)
  (* do we need to store how many vals in each HT1? *)

#[export] Instance NestedHamt (key1 key2 V:Type) (default:V) `{EqDec key1} `{EqDec key2}
`{HT2 : Table key2 V default} `{HT1 : Table key1 HT2.(table) HT2.(empty)} :
  HAMT key1 key2 V default :=
  {

    hamt := (* inductive type of either HT1, HT2, or association list, haven't figured
            out how to properly set this type *)

    emptyH := HT2.(empty) (* instantiated to just be an empty HT2*)

    getH k2 k1 h := match h with 
                        | HT2 => get k2 h
                        | HT1 => 
                            match k1 with
                            | head :: t => getH k2 t (get head h)
                            end
                        | _ => default (* case for assoication list, need to update with
                                        find function for lists *)
                        end;

    setH k2 k1 v h := (* implement setH by iterating through list of 
                          key2 and applying gets to HT2 *)
                        (* need to modify HT2 to give back HT2 and HT1? *)
  }.


