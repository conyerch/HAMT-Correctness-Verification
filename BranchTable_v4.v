(* From Coq Require Import Strings.String.  (* for manual grading *) *)
From Coq Require Export Bool.Bool.
(* From Coq Require Export Arith.Arith. *)
(* From Coq Require Export Arith.EqNat. *)
(* From Coq Require Export Lia. *)
(* From Coq Require Export Lists.List. *)
(* Export ListNotations. *)
(* From Coq Require Export Permutation. *)
From Coq Require Export Vectors.Vector.
Import VectorNotations.

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
  - destruct (eqb_eq k k) as [_ Heq]. rewrite Heq;auto.
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
  `(HT2 : Table key2 V default) := (BranchTable HT2 (FunTable key1 _ _)).

Definition FunBranchTableAlgebraic {key1 key2 V: Type} {default:V} `{EqDec key1}
  `(HT2 : Table key2 V default) `{HAT2 : @AlgebraicTable key2 V default _ _ HT2} :
  AlgebraicTable (FunBranchTable key1 HT2) := BranchTableAlgebraic _ _.

Example natnatboolBranchTable' := FunBranchTable nat (FunTable nat bool false).
Example natnatnatboolBranchTable' := FunBranchTable nat (FunBranchTable nat (FunTable nat bool false)).
Example natnatnatnatboolBranchTable' := FunBranchTable nat (FunBranchTable nat (FunBranchTable nat (FunTable nat bool false))).
Example natnatnatnatnatboolBranchTable' := FunBranchTable nat (FunBranchTable nat (FunBranchTable nat (FunBranchTable nat (FunTable nat bool false)))).

(*Compute natnatboolBranchTable'.(get) (1,3) (natnatboolBranchTable'.(set) (1,2) true natnatboolBranchTable'.(empty)).*)

#[export] Instance eqVector {A:Type} `{HEq:Eq A} {n} : Eq (t A n)
  := { eqb := Vector.eqb A HEq.(eqb) }.

#[export] Instance eqDecVector {A:Type} `{Heq:Eq A} `{HeqDec:EqDec A} {n} : EqDec (t A n).
Proof.
  constructor. intros k1 k2.
  destruct (k1 =? k2) eqn:Heqn; constructor.
  - apply (Vector.eqb_eq _ _ eqb_eq _). auto.
  - simpl in Heqn. intro Hc.
    rewrite<-(Vector.eqb_eq _ _ eqb_eq _) in Hc.
    rewrite Hc in Heqn. discriminate.
Qed.

Example tboolnatboolBranchTable (n:nat) := FunBranchTable (t bool n) (FunTable nat bool false).

#[export] Instance PrecomposeTable {key1 key2 V : Type} {default:V}
  `{EqDec key1} `{EqDec key2}
  (f:key1->key2) (HT:Table key2 V default)
  : Table key1 V default :=
  {
    table := HT.(table);
    empty := HT.(empty);
    get k t := HT.(get) (f k) t;
    set k v t := HT.(set) (f k) v t
  }.

#[export] Instance PrecomposeTableAlgebraic
  {key1 key2 V : Type} {default:V} `{EqDec key2} `{EqDec key1}
  (f:key1->key2) (Hf: forall k1 k2, f k1 = f k2 -> k1=k2)
  `(HT : Table key2 V default) {HAT: AlgebraicTable HT}
  : AlgebraicTable (PrecomposeTable f HT).
Proof.
  constructor.
  - intros. apply HAT.(get_empty_default).
  - intros. apply HAT.(get_set_same).
  - intros ? ? ? ? Hne. apply HAT.(get_set_other).
    intro. apply Hne. apply Hf. auto.
Qed.

Fixpoint VectorBranchTable (n:nat) (key V : Type) (default:V) `{EqDec key}
                         (HT:forall (V:Type) (default:V), Table key V default)
  : Table (t key (S n)) V default :=
  match n with
  | 0 => PrecomposeTable (fun k:t key 1 => hd k) (HT V default)
  | S n' => PrecomposeTable (fun k:t key (S (S n')) => (hd k, tl k))
              (BranchTable (VectorBranchTable n' key V default HT) (HT _ _))
  end.

#[export] Instance VectorBranchTable' (n:nat) (key V : Type) (default:V) `{EqDec key}
                         (HT:forall (V:Type) (default:V), Table key V default)
  : Table (t key (S n)) V default := VectorBranchTable n key V default HT.

#[export] Instance VectorBranchTableAlgebraic (n:nat) {key V : Type} {default:V} `{Hdec:EqDec key}
  (HT:forall (V:Type) (default:V), Table key V default)
  {HAT:forall (V:Type) (default:V), AlgebraicTable (HT V default)} : AlgebraicTable (VectorBranchTable n key V default HT).
Proof. Admitted. (*
  induction n.
  - simpl. apply PrecomposeTableAlgebraic; auto.
    intros ? ? Heq.
    rewrite eta. rewrite eta at 1.
    rewrite (nil_spec (tl k1)). rewrite (nil_spec (tl k2)).
    rewrite Heq. auto.
  - constructor.
    + intros. simpl. rewrite (HAT _ _).(get_empty_default).
      apply IHn.(get_empty_default).
    + intros. simpl. rewrite (HAT _ _).(get_set_same).
      apply IHn.(get_set_same).
    + intros ? ? ? ? Heq. simpl.
      destruct (Hdec.(eqb_reflect) (hd k) (hd k')).
      * rewrite e. rewrite (HAT _ _).(get_set_same).
        apply IHn.(get_set_other).
        intro Hc. apply Heq. rewrite eta. rewrite eta at 1.
        rewrite e. rewrite Hc. auto.
      * rewrite (HAT _ _).(get_set_other); auto.
Qed.*)

Example myvectorbranch := VectorBranchTable 2 nat bool false (fun V default=>FunTable _ V default).

(*Compute myvectorbranch.(set) [3;2;3] true (myvectorbranch.(set) [1;2;3] true myvectorbranch.(empty)).

Compute myvectorbranch.(set) [3;2;2] true (myvectorbranch.(set) [3;2;3] true (myvectorbranch.(set) [1;2;3] true myvectorbranch.(empty))).

Compute myvectorbranch.(get) [1;2;3] (myvectorbranch.(set) [1;2;3] true myvectorbranch.(empty)).
*)

Definition HashBranchTable {key V B:Type} {n:nat} {default:V}
  `{EqDec key} `{EqDec B}
  (hash_f:key -> t B (S n))
  (HT1:forall (V:Type) (default:V), Table B V default)
  (HT2:Table key V default) : Table key V default :=
  PrecomposeTable (fun k:key => (hash_f k,k))
    (BranchTable HT2 (VectorBranchTable n B _ _ HT1)).

Definition HashBranchTableAlgebraic {key V n B} {default:V}
  (hash_f:key -> t B (S n))
  `{EqDec key} `{EqDec B}
  (HT1:forall (V:Type) (default:V), Table B V default)
  (HT2:Table key V default)
  {HAT1:forall (V:Type) (default:V), AlgebraicTable (HT1 V default)}
  {HAT2:AlgebraicTable HT2}
  : AlgebraicTable (HashBranchTable hash_f HT1 HT2).
Proof.
  apply PrecomposeTableAlgebraic.
  - intros ? ? Hk. inversion Hk. auto.
  - apply BranchTableAlgebraic. auto.
    apply VectorBranchTableAlgebraic. auto.
Qed.

Record MyRecord (key V : Type) (n: nat) : Type :=
  {
    bitmap : t bool n;
    array : t (list (key * V)) n;
  }.

Definition createEmptyRecord (key V : Type) (n:nat) : MyRecord key V n :=
    {|
      bitmap := const false n;
      array := const (Coq.Lists.List.nil) n;
    |}.

Definition upd_nth {A key : Type} {n : nat} (k : key) (f : key -> nat) (H: forall k, f k < n) (x : A) (v : t A n) : t A n :=
      replace v (Fin.of_nat_lt (H k)) x.

Fixpoint AssociationGet {key V: Type} (k: key) (t: list(key * V)) (default: V) `{EqDec key} : V :=
    match t with 
      |Coq.Lists.List.nil => default
      |Coq.Lists.List.cons (k', v) t' => 
        if k =? k' then v else AssociationGet k t' default
      end.  

Require Import Fin.

Definition nat_to_fin (n : nat) (H : 0 < n) : Fin.t n :=
  Fin.of_nat_lt H.

Inductive BST {key V : Type} (n: nat) (f: key -> nat) (H : forall k : key, f k < n) : MyRecord key V n -> Prop :=
  | BST_E : BST n f H (createEmptyRecord key V n)
  | BST_T : forall (t : MyRecord key V n),
      (forall k : key, (bitmap key V n t)[@of_nat_lt (H k)] = false ->
                       (array key V n t)[@of_nat_lt (H k)] = Datatypes.nil) -> 
      BST n f H t.

#[export] Instance HAMTTable (key V:Type) (n: nat) (f: key -> nat) (default:V) 
`{EqDec key} (Hvalid1: forall k, f k < n) : Table key V default :=
  {
    table := MyRecord key V n; 
    empty := createEmptyRecord key V n;
    get k t :=
      let k' := f k in  
      let fin_k' := Fin.of_nat_lt (Hvalid1 k) in
      match Vector.nth_order t.(bitmap key V n) (Hvalid1 k) with
      | true => AssociationGet k (Vector.nth_order t.(array key V n) (Hvalid1 k)) default
      | _ => default
      end;
    set k v t := 
      let fin_k' := Fin.of_nat_lt (Hvalid1 k) in
      let new_bitmap := upd_nth k f Hvalid1 true t.(bitmap key V n) in 
      let new_array := upd_nth k f Hvalid1 (Coq.Lists.List.cons (k, v) (nth t.(array key V n) fin_k')) t.(array key V n)
    in
    {|
      bitmap := new_bitmap;
      array := new_array;
    |};
  }. 

From Coq Require Export Vectors.Vector.
Import VectorNotations.
From Coq Require Export Arith.PeanoNat.
From Coq Require Export Logic.ProofIrrelevance.

Lemma const_false : forall (key: Type) (k: key) (n : nat) (f: key -> nat) (H : forall k, f k < n), 
(const false n)[@of_nat_lt (H k)] = false.
Proof. 
intros. apply const_nth.
Qed.  

Lemma upd_nth' : forall (key V : Type) (f: key -> nat) (k: key) (n: nat) 
(v : t V n) (x: V) (H2: forall l : key, f l < n),
(upd_nth k f H2 x v)[@of_nat_lt (H2 k)] = x.
Proof.
intros. unfold upd_nth. apply nth_order_replace_eq.
Qed.

Lemma nat_to_fin_eq : forall (n m p : nat) (Hn : n < p) (Hm : m < p),
  n = m -> Fin.of_nat_lt Hn = Fin.of_nat_lt Hm.
Proof.
  intros n m p Hn Hm Heq.
  subst m.
  f_equal.
  apply proof_irrelevance.
Qed.

Lemma upd_AG : forall {key V: Type} (k k1: key) (x: V) (t: list(key * V)) (default: V) `{EqDec key},
  k <> k1 -> AssociationGet k (Coq.Lists.List.cons (k1, x) t) default = AssociationGet k t default.
Proof. intros. simpl. inversion H0. destruct (eqb_reflect0 k k1). contradiction. reflexivity.
  Qed.
  
Lemma upd_nth_neq : forall (key V: Type) (f : key -> nat) (n: nat) (t: MyRecord key V n) (k k': key) (H: forall k : key, f k < n ) `{EqDec key} `{Eq key}, 
f k <> f k' -> nth_order (upd_nth k f H true (bitmap key V n t)) (H k') = nth_order (bitmap key V n t) (H k').
Proof. intros. unfold upd_nth. rewrite -> nth_order_replace_neq. reflexivity. auto. 
Qed.  

Lemma upd_nth_neq_H : forall (key V: Type) (f : key -> nat) (k k': key) (v: V) (n: nat) 
(t: MyRecord key V n) (k k': key) (H: forall k : key, f k < n ) `{EqDec key} `{Eq key}, 
  f k <> f k' -> nth_order (upd_nth k f H ((k, v) :: (array key V n t)[@of_nat_lt (H k)])%list
 (array key V n t)) (H k') = nth_order (array key V n t) (H k').
  Proof.
  intros.  unfold upd_nth. rewrite -> nth_order_replace_neq. reflexivity. auto.
Qed.

Lemma bitmap_false_implies_list_empty : 
  forall (key V : Type) (n : nat) (t : MyRecord key V n) (f : key -> nat)
  (k : key) (H: forall k : key, f k < n ),
  BST n f H t ->
  (bitmap key V n t)[@of_nat_lt (H k)] = false ->
  (array key V n t)[@of_nat_lt (H k)] = Coq.Lists.List.nil.
    Proof.
    intros. induction H0.
    - simpl. apply const_nth.
    - apply H0 in H1. apply H1.    
  Qed.  

#[export] Instance FunHAMTTableAlgebraic (key V:Type) (n: nat) 
(default:V) (f: key -> nat) (H: forall l : key, f l < n)
(Hvalid1: forall k, f k < n) `{EqDec key} :
  AlgebraicTable (HAMTTable key V n f default H).
Proof.
  constructor.
  - intros. unfold get, empty, HAMTTable, createEmptyRecord. 
    simpl. unfold nth_order. rewrite -> const_false. auto.
  - intros. unfold get, set, HAMTTable. simpl. unfold nth_order. rewrite -> upd_nth'.
    simpl.
    rewrite -> upd_nth'.
    simpl. inversion H1. destruct (eqb_reflect0 k k). auto. destruct n0. reflexivity.
  - intros. unfold get, set, HAMTTable. simpl. 
    destruct (Nat.eq_dec (f k) (f k')) as [Heq_nat | Hneq_nat]. 
    assert (of_nat_lt (H k) = of_nat_lt (H k')). 
    { simpl. apply nat_to_fin_eq. apply Heq_nat. } unfold nth_order.
    rewrite -> H3. symmetry in H3. rewrite -> H3. 
    rewrite -> upd_nth'. rewrite -> upd_nth'. 
    destruct ((bitmap key V n t)[@of_nat_lt (H k)]) eqn:myb.
  * simpl. inversion H1. specialize (eqb_reflect0 k' k) as H_neq. 
    destruct H_neq as [H_eq | H_false]. symmetry in H_eq. contradiction. reflexivity.
  * rewrite -> bitmap_false_implies_list_empty. simpl. 
    inversion H1. specialize (eqb_reflect0 k' k) as H_neq. 
    destruct H_neq as [H_eq | H_false]. symmetry in H_eq.
    ** contradiction.
    ** reflexivity. 
    ** admit. 
    ** apply myb.      
  * rewrite -> upd_nth_neq with (H0 := H0). 
    rewrite -> upd_nth_neq_H with (H0 := H0). reflexivity.
    repeat auto. auto. auto. auto. auto. auto. auto. auto.
Admitted.

Definition HashBranchTable' {key V B:Type} {n:nat} {default:V}
  `{EqDec key} `{EqDec B}
  (hash_f:key -> t B (S n))
  (hash_f2: key -> nat)
  (H: forall k, hash_f2 k < n)
  (HT1:forall (V:Type) (default:V), Table B V default)
   : Table key V default :=
  PrecomposeTable (fun k:key => (hash_f k, k))
    (BranchTable (HAMTTable key V n hash_f2 default H) (VectorBranchTable n B _ _ HT1)).


Definition HashBranchTableAlgebraic' {key V n B} {default:V}
  (hash_f:key -> t B (S n))
  (hash_f2: key -> nat)
  (H: forall k, hash_f2 k < n)
  `{EqDec key} `{EqDec B}
  (HT1:forall (V:Type) (default:V), Table B V default)
  {HAT1:forall (V:Type) (default:V), AlgebraicTable (HT1 V default)}
  : @AlgebraicTable key V default _ _ (HashBranchTable' hash_f hash_f2 H HT1).
Proof.
  apply PrecomposeTableAlgebraic.
  - intros ? ? Hk. inversion Hk. auto.
  - apply BranchTableAlgebraic. 
    * apply FunHAMTTableAlgebraic. apply H.
    * apply VectorBranchTableAlgebraic. apply HAT1.
Qed.

    
  

