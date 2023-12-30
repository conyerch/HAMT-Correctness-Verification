(* From Coq Require Import Strings.String.  (* for manual grading *) *)
From Coq Require Export Bool.Bool.
(* From Coq Require Export Arith.Arith. *)
(* From Coq Require Export Arith.EqNat. *)
(* From Coq Require Export Lia. *)
(* From Coq Require Export Lists.List. *)
(* Export ListNotations. *)
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

Class AlgebraicTable {key V:Type} {default:V} `(HT:Table key V default) :=
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
  AlgebraicTable (FunTable key V default).
Proof.
  constructor; auto; intros; simpl.
  - destruct (eqb_eq k k) as [_ Heq]. rewrite Heq; auto.
  - destruct (eqb_neq k k') as [Hneq _]. rewrite Hneq; auto.
Qed.

#[export] Instance BranchTable {key1 key2 V : Type} {default:V}
  `(HT2 : Table key2 V default) `(HT1 : Table key1 HT2.(table) HT2.(empty))
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

#[export] Instance BranchTableAlgebraic {key1 key2 V : Type} {default:V}
  `(HT2 : Table key2 V default) `(HT1 : Table key1 HT2.(table) HT2.(empty))
  `{HAT2 : @AlgebraicTable key2 V default _ _ HT2}
  `{HAT1 : @AlgebraicTable key1 HT2.(table) HT2.(empty) _ _ HT1} :
  @AlgebraicTable (prod key1 key2) V default _ _ (BranchTable HT2 HT1).
Proof.
  constructor; intros; destruct k as [k1 k2]; simpl.
  - rewrite HAT1.(get_empty_default), HAT2.(get_empty_default). auto.
  - rewrite HAT1.(get_set_same), HAT2.(get_set_same). auto.
  - destruct k' as [k1' k2'].
    destruct (eqb_reflect k1 k1') as [?|?]; subst.
    + rewrite HAT1.(get_set_same).
      destruct (eqb_reflect k2 k2') as [?|?]; subst.
      * exfalso. auto.
      * rewrite HAT2.(get_set_other); auto.
    + rewrite HAT1.(get_set_other); auto.
Qed.

Definition natnatboolBranchTable := (BranchTable (FunTable nat bool false) (FunTable nat _ _)).
Definition natnatboolBranchTableAlgebraic : AlgebraicTable natnatboolBranchTable := BranchTableAlgebraic _ _.

Definition FunBranchTable (key1:Type) `{EqDec key1} {key2 V:Type} {default:V}
  `(HT2 : Table key2 V default) := (BranchTable HT2 (FunTable _ _ _)).

Definition FunBranchTableAlgebraic {key1 key2 V: Type} {default:V} `{EqDec key1}
  `(HT2 : Table key2 V default) `{HAT2 : @AlgebraicTable key2 V default _ _ HT2} :
  AlgebraicTable (FunBranchTable key1 HT2) := BranchTableAlgebraic _ _.

Example natnatboolBranchTable' := FunBranchTable nat (FunTable nat bool false).
Example natnatnatboolBranchTable' := FunBranchTable nat (FunBranchTable nat (FunTable nat bool false)).
Example natnatnatnatboolBranchTable' := FunBranchTable nat (FunBranchTable nat (FunBranchTable nat (FunTable nat bool false))).
Example natnatnatnatnatboolBranchTable' := FunBranchTable nat (FunBranchTable nat (FunBranchTable nat (FunBranchTable nat (FunTable nat bool false)))).

Compute natnatboolBranchTable'.(get) (1,3) (natnatboolBranchTable'.(set) (1,2) true natnatboolBranchTable'.(empty)).
