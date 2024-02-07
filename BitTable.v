(* From Coq Require Import Strings.String.  (* for manual grading *) *)
From Coq Require Export Bool.Bool.
From Coq Require Export Arith.Arith. 
(* From Coq Require Export Arith.EqNat. *)
(* From Coq Require Export Lia. *)
From Coq Require Export Lists.List. 
Export ListNotations. 
(* From Coq Require Export Permutation. *)
(*From Coq Require Export Vectors.Vector.*)
(*Import VectorNotations.*)


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

#[export] Instance eqBool : Eq bool :=
  {
    eqb := Bool.eqb
  }.

#[export] Instance eqDecBool : EqDec bool.
Proof.
  constructor. intros. destruct k1, k2; constructor; try discriminate; auto.
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
  - 
    apply (eqb_eq x1 y1) in E1. apply (eqb_eq x2 y2) in E2.
    subst. auto.
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
    (*all : table -> list (key * V)*)
  }.

Class AlgebraicTable {key V:Type} {default:V} `(HT:Table key V default) :=
  {
    get_empty_default : forall (k : key), get k empty = default;
    get_set_same : forall (k : key) (v : V) (t : table),
      get k (set k v t) = v;
    get_set_other : forall (k k' : key) (v : V) (t : table),
      k <> k' -> get k' (set k v t) = get k' t;
    (*all_set_same : forall (k : key) (v : V) (t : table),
      In (k, v) (all (set k v t)) = True*)
  }.

Definition const_list {V : Type} (v : V) (n : nat) : list V :=
  repeat v n.
  
Fixpoint bitCount (i: nat) (bitmap: list bool) : nat :=
    match i with 
    |0 => 0
    |S i' => 
      match bitmap with 
      |Coq.Lists.List.nil => 0
      |Coq.Lists.List.cons hd tl => 
        match hd with 
        |true => 1 + bitCount i' tl
        |false => bitCount i' tl
        end
      end
    end.

  
Record HAMTRecord (V : Type) (def: V) (HT : Table nat V def) : Type :=
    {
      bitmap : list bool;
      map : HT.(table);
    }.

Fixpoint replace (l : list bool) (n : nat) := 
  match l with 
  |[] => []
  |b :: t => 
    match n with 
    |0 => true :: t
    |S n' => b :: replace t n'
    end
  end.

Fixpoint atIndex (n: nat) (el : list bool) : bool := 
    match n with 
    |0 => 
      match el with 
      |b :: t => b
      |_ => false
      end
    |S n' => atIndex n' (tl el)
    end.

Fixpoint setTable (V: Type) (def: V) (v: V) (HT: Table nat V def) (t: table) 
(t2: table) (p: nat) (n : nat) : table := 
  match n with 
  |0 => HT.(set) p v t2
  |S n' => 
    let v1 := (HT.(get) n' t) in 
    match (n' <? p) with 
    |true => setTable V def v HT t (HT.(set) n' v1 t2) p n'
    |false => setTable V def v HT t (HT.(set) (S n') v1 t2) p n'
    end
  end. 
  
#[export] Instance BitTable (B V:Type) (n: nat) (default:V) (f : B -> nat)
  (HT: Table nat V default) `{EqDec nat} `{EqDec B} (H: forall (b:B), f b < n) 
  : Table B V default :=
  {
    table := HAMTRecord V default HT; 
    empty := 
      {|
        bitmap := const_list false n;
        map := HT.(empty);
      |}; 
    get k t :=
      let k' := bitCount (f k) t.(bitmap V default HT) in 
      get k' t.(map V default HT);
    set k v t := 
      let key := f k in 
      let k' := bitCount key t.(bitmap V default HT) in 
      match (atIndex key t.(bitmap V default HT)) with 
      |true =>
        let new_map :=  HT.(set) k' v t.(map V default HT) in 
        {|
        bitmap := t.(bitmap V default HT);
        map := new_map;
        |}
      |false => 
        let new_map := setTable V default v HT t.(map V default HT) HT.(empty) k' (bitCount n t.(bitmap V default HT)) in 
        let new_map' := HT.(set) k' v new_map in 
        let new_bitmap := replace t.(bitmap V default HT) key in 
      {|
        bitmap := new_bitmap;
        map := new_map';
      |}
      end;
    (*all t := HT.(all) t.(map V default HT)*)
  }.

Lemma bitC_same : forall (n: nat) (b: list bool), 
bitCount n  (replace b n) = bitCount n b.
Proof.
  intros. generalize dependent n.
  induction b as [|hd tl IH]; intros [|i'].  
  - simpl. reflexivity.
  - simpl. reflexivity. 
  - simpl. reflexivity.
  - simpl. destruct hd. rewrite -> IH. reflexivity. apply IH.
  Qed.   

#[export] Instance BitTableAlgebraic (B: Type) {V : Type} {default:V} (n: nat)
  (HT: Table nat V default) (f : B -> nat) `{EqDec B} (H1: forall (b:B), f b < n) 
  `{HAT : @AlgebraicTable nat V default _ _ HT} :
  AlgebraicTable (BitTable B V n default f HT H1).
Proof.
  constructor; auto; intros; simpl.
  - apply get_empty_default.
  - destruct (atIndex (f k) (bitmap V default HT t)) eqn:H2.
    * simpl. apply get_set_same.
    * simpl. rewrite -> bitC_same. apply get_set_same.
  - destruct (atIndex (f k) (bitmap V default HT t)) eqn:H3.
    * simpl. apply get_set_other. assert (f k <> f k'). admit.
    admit.
    * simpl. rewrite -> bitC_same. apply get_set_other.   
  
  
  assert (forall (l p: nat), bitCount l (const_list false p) = 0).
    * intros. unfold const_list. induction (repeat false). unfold repeat. induction p. 
    unfold bitCount. simpl. destruct l. auto. auto. 
    unfold bitCount. destruct l. reflexivity. fold bitCount. apply IHp.  simpl. 
    induction n0. reflexivity.
    destruct (const' p). reflexivity.  