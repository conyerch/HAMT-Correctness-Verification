(* From Coq Require Import Strings.String.  (* for manual grading *) *)
From Coq Require Export Bool.Bool.
From Coq Require Export Arith.Arith. 
(* From Coq Require Export Arith.EqNat. *)
(* From Coq Require Export Lia. *)
(*From Coq Require Export Lists.List. *)
(*Export ListNotations.*)
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
  `(HT2 : Table key2 V default) := (BranchTable HT2 (FunTable key1 _ _)).

Definition FunBranchTableAlgebraic {key1 key2 V: Type} {default:V} `{EqDec key1}
  `(HT2 : Table key2 V default) `{HAT2 : @AlgebraicTable key2 V default _ _ HT2} :
  AlgebraicTable (FunBranchTable key1 HT2) := BranchTableAlgebraic _ _.

Example natnatboolBranchTable' := FunBranchTable nat (FunTable nat bool false).
Example natnatnatboolBranchTable' := FunBranchTable nat (FunBranchTable nat (FunTable nat bool false)).
Example natnatnatnatboolBranchTable' := FunBranchTable nat (FunBranchTable nat (FunBranchTable nat (FunTable nat bool false))).
Example natnatnatnatnatboolBranchTable' := FunBranchTable nat (FunBranchTable nat (FunBranchTable nat (FunBranchTable nat (FunTable nat bool false)))).

Compute natnatboolBranchTable'.(get) (1,3) (natnatboolBranchTable'.(set) (1,2) true natnatboolBranchTable'.(empty)).

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

Lemma nil_spec {A} (v : t A 0) : v = [].
Proof. Admitted. 

#[export] Instance VectorBranchTable' (n:nat) (key V : Type) (default:V) `{EqDec key}
                         (HT:forall (V:Type) (default:V), Table key V default)
  : Table (t key (S n)) V default := VectorBranchTable n key V default HT.

#[export] Instance VectorBranchTableAlgebraic (n:nat) {key V : Type} {default:V} `{Hdec:EqDec key}
  (HT:forall (V:Type) (default:V), Table key V default)
  {HAT:forall (V:Type) (default:V), AlgebraicTable (HT V default)} : AlgebraicTable (VectorBranchTable n key V default HT).
Proof.
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
Qed.

Example myvectorbranch := VectorBranchTable 2 nat bool false (fun V default=>FunTable _ V default).

Compute myvectorbranch.(set) [3;2;3] true (myvectorbranch.(set) [1;2;3] true myvectorbranch.(empty)).

Compute myvectorbranch.(set) [3;2;2] true (myvectorbranch.(set) [3;2;3] true (myvectorbranch.(set) [1;2;3] true myvectorbranch.(empty))).

Compute myvectorbranch.(get) [1;2;3] (myvectorbranch.(set) [1;2;3] true myvectorbranch.(empty)).

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



(* Bit Table Implementation *)


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

Definition const_list {V : Type} (v : V) (n : nat) : list V :=
  repeat v n.

Fixpoint atIndex (n: nat) (el : list bool) : bool := 
    match n with 
    |0 => 
      match el with 
      |b :: t => b
      |_ => false
      end
    |S n' => atIndex n' (tl el)
    end.

Fixpoint atIndexV {V: Type} (n: nat) (def: V) (el : list V) : V := 
  match n with 
  |0 => 
    match el with 
    |v :: t => v
    |_ => def
    end
  |S n' => atIndexV n' def (tl el)
  end.

Fixpoint replace (l : list bool) (n : nat) := 
  match l with 
  |[] => 
    match n with 
    |0 => [true] 
    |_ => []
    end
  |b :: t => 
    match n with 
    |0 => true :: t
    |S n' => b :: replace t n'
    end
  end.

Fixpoint insert' {V: Type} (b1 : bool) (l : list V) (n: nat) (v: V) := 
  match l with 
  |[] => [v]
  |b :: t => 
    match n with 
    |0 => 
      match b1 with 
      |false => v :: b :: t
      |true => v :: t
      end
    |S n' => b :: insert' b1 t n' v 
    end
  end.
    

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

Definition key := nat.

Class ShiftTable (V: Type) (default: V) `{EqDec nat} := 
  {
    table' : Type;
    empty' : table';
    get' : key -> table' -> V;
    insert : bool -> key -> V -> table' -> table'
  }.

Class AlgebraicShiftTable {V:Type} {default:V} `(HT:ShiftTable V default) :=
    {
      get_empty_default' : forall (k : nat), get' k empty' = default;
      get_insert_same : forall (b: bool) (k : nat) (v : V) (t : table'),
        get' k (insert b k v t) = v;
      insertion_same : forall (k k': nat) (v : V) (t : table'),
        k <> k' -> get' k (insert true k' v t) = get' k t;
      insertion_same_lt : forall (k k': nat) (v : V) (t : table'), 
        k' <=? k = false -> get' k (insert false k' v t) = get' k t;
      insertion_same_gt : forall (k k': nat) (v : V) (t : table'), 
        k' <=? k = true -> get' (S k) (insert false k' v t) = get' k t;
    }.

#[export] Instance HamtTable {V : Type} (default : V) 
 `{EqDec nat} : ShiftTable V default :=
  {
    table' := list V;
    empty' := [];
    get' k t := nth k t default;
    insert b k v t := insert' b t k v;
  }.

Axiom key_within_bounds : forall {V: Type} (default: V) `{EqDec nat} (k: key) (t: (HamtTable default).(table')), k > length t -> False.

Require Import Lia.

#[export] Instance ShiftListAlgebraic {V: Type} (def: V) `{EqDec nat}:
  AlgebraicShiftTable (HamtTable def).
Proof.
  constructor; auto; intros; simpl.
  - induction k. simpl. reflexivity. simpl. reflexivity.
  - generalize dependent t. induction k. destruct t. simpl. 
    reflexivity. simpl. destruct b. simpl. reflexivity. simpl. reflexivity. 
    simpl. destruct t eqn: H1.
    assert (False). apply key_within_bounds with (default := def) 
    (H := eqNat) (H0 := eqDecNat) (k := (S k)) (t := t). 
    rewrite H1. simpl. lia. contradiction.
    simpl. apply IHk. 
  - generalize dependent k. generalize dependent k'. 
    induction t; intros k' k Hk'.
    * destruct k'. simpl. destruct k. contradiction. destruct k.
      reflexivity. reflexivity. assert (False). 
      apply key_within_bounds with (default := def) (H := eqNat)
      (H0 := eqDecNat) (k := S k') (t := []). simpl. lia. contradiction.
    * simpl. destruct k'. simpl. destruct k. contradiction. reflexivity.
      destruct k. simpl. reflexivity.
      simpl. apply IHt. lia. 
  - apply Nat.leb_gt in H1. generalize dependent k. 
    generalize dependent k'. induction t; intros k' k Hk'.
    * assert (k' > 0). lia. assert (False). 
      apply key_within_bounds with (default := def) (H := eqNat)
      (H0 := eqDecNat) (k := k') (t := []). simpl. lia. contradiction.
    * simpl. destruct k'. simpl. lia. 
      destruct k. simpl. reflexivity. apply IHt. lia.
  - revert k k' H1. induction t as [| b t' IH]; intros k k' Hk'.
    * simpl. destruct k'; reflexivity.
    * simpl in *. destruct k'; simpl.
      + destruct k; reflexivity.
      + destruct k; simpl.
        ++ simpl. discriminate. 
        ++ apply IH. apply Hk'.
Qed.

Class Bitmap (n: nat) (def: nat) `{EqDec nat} := 
  {
    table'' : Type;
    empty'' : table'';
    get'' : key -> table'' -> bool;
    set'' : key -> table'' -> table'';
    count'' : key -> table'' -> nat
  }.

Class AlgebraicBitmap (n: nat) (d: nat) `(HT:Bitmap n d) :=
  {
    get_empty_default'' : forall (k : nat), get'' k empty'' = false;
    get_set_same'' : forall (k : nat) (t : table''),
      get'' k (set'' k t) = true;
    get_set_other'' : forall (k k': nat) (t : table''), 
      k <> k' -> get'' k (set'' k' t) = get'' k t;
    count_lt : forall (k k': nat) (t : table''), 
      k <=? k' = true -> count'' k (set'' k' t) = count'' k t;
    count_gt : forall (k k': nat) (t : table''), 
      k' <? k = true -> get'' k' t = false -> 
      count'' k (set'' k' t) = S(count'' k t);
    count_less : forall (k k': nat) (t : table''), 
      k <? k' = true -> count'' k t <= count'' k' t;
    count_ne : forall (k k': nat) (t : table''), 
      k > k' -> get'' k' t = true -> count'' k t > count'' k' t
  }.

Require Import Fin.
From Coq Require Export Vectors.Vector.
Import VectorNotations.

Fixpoint count_true (n: nat) (v : t bool n) (k: key) (H: forall k : key, k < n) : nat :=
  match k with 
  |0 => 0
  |S k' => if v[@of_nat_lt (H (k'))] then 1 + count_true n v k' H else count_true n v k' H 
  end. 

#[export] Instance BitmapList (n : nat) (H: forall k : key, k < n)
 `{EqDec nat} : Bitmap n 0 :=
  {
    table'' := t bool n;
    empty'' := const false n;
    get'' k t := t[@of_nat_lt (H k)];
    set'' k t := replace t (of_nat_lt (H k)) true;
    count'' k t := count_true n t k H
  }.

Lemma nat_equality_decidable : forall n m : nat, n = m \/ n <> m.
Proof.
  intros n m.
  destruct (Nat.eq_dec n m) as [H | H].
  - left. apply H.
  - right. apply H.
Qed.

Lemma replace_same : forall (n: nat) (t: t bool n) (k k': key) (H: forall k : key, k < n),
  k <= k' -> count_true n 
  (replace t (of_nat_lt (H k')) true) k H = count_true n t k H.
  Proof.
    intros. induction k. simpl. reflexivity.
    simpl. assert ((replace t (of_nat_lt (H k')) true)[@
    of_nat_lt (H k)] = t[@of_nat_lt (H k)]). 
    apply nth_order_replace_neq. lia.
    rewrite H1. assert (k <= k'). lia. apply IHk in H2. 
    rewrite H2. reflexivity.
  Qed.  

Lemma replace_bitC_same : forall (n: nat) (t: t bool n) (k: key) (H: forall k : key, k < n),
  count_true n (replace t (of_nat_lt (H k)) true)
  k H = (count_true n t k H).
Proof. 
  intros n t k H.
  induction k as [|k' IHk'].
  - (* Base case: k = 0 *)
    simpl. reflexivity.
  - unfold count_true. assert ((replace t (of_nat_lt (H (S k'))) true)[@
    of_nat_lt (H k')] = t[@
    of_nat_lt (H k')]). apply nth_order_replace_neq. lia. rewrite H0. 
    fold count_true. assert (count_true n
    (replace t (of_nat_lt (H (S k'))) true) k' H = count_true n
    (replace t (of_nat_lt (H (k'))) true) k' H). 
    induction k'. simpl. reflexivity. rewrite replace_same. 
    rewrite replace_same.
    reflexivity. lia. lia.
    rewrite H1. rewrite IHk'. reflexivity.
Qed.

Lemma lt_implies : forall k k', (k <? S k') = true -> k = k' \/ (k <? k') = true.
Proof.
  intros k k'. intros H.
  apply Nat.ltb_lt in H. (* Convert (k <? S k') = true to k < S k' in terms of < *)
  destruct (Nat.eqb k k') eqn:Heq.
  - left. apply Nat.eqb_eq in Heq. assumption.
  - right. apply Nat.ltb_lt. apply Nat.eqb_neq in Heq.
    lia.
Qed.

Lemma count_gte : forall (k k' : key) (n: nat) (H: forall k : key, k < n)
(t: t bool n), k < k' -> t[@of_nat_lt (H k)] = true -> count_true n t k' H > count_true n t k H.
  Proof.
  intros. generalize dependent k. induction k'. 
  * simpl. intros. lia.
  * intros. simpl. assert (k = k' \/ k <? k' = true). apply lt_implies.
  apply Nat.leb_le. lia. destruct H2.
    + rewrite <- H2. rewrite H1. lia.
    + apply Nat.leb_le in H2. assert (k < k'). lia. apply IHk' in H3.
     destruct (t[@of_nat_lt (H k')]). lia. apply H3. apply H1.
Qed.          

#[export] Instance BitmapListAlgebraic (n: nat) (H: forall k : key, k < n) `{EqDec key} :
  AlgebraicBitmap n 0 (BitmapList n H).
Proof.
  constructor; auto; intros; simpl. 
  - apply const_nth. 
  - apply nth_order_replace_eq.
  - apply nth_order_replace_neq. apply H2.
  - induction k. destruct k'.
    * simpl. reflexivity. 
    * unfold count_true. reflexivity.
    * assert (k <=? k' = true). apply Nat.leb_le. 
      assert (H_lt: S k <= k'). apply Nat.ltb_lt. apply H2. lia. simpl. 
      assert ((replace t (of_nat_lt (H k')) true)[@of_nat_lt (H k)] 
      = t[@of_nat_lt (H k)]). apply nth_order_replace_neq. 
      assert (H_lt: S k <= k'). apply Nat.ltb_lt. apply H2. lia.
      rewrite H4. apply IHk in H3. rewrite H3. reflexivity.
  - induction k. destruct k'. discriminate. discriminate. 
    assert (k = k' \/ k <> k'). apply nat_equality_decidable. destruct H4.
  * rewrite H4. simpl. 
    assert ((replace t (of_nat_lt (H k')) true)[@of_nat_lt (H k')] = true).
    apply nth_order_replace_eq. rewrite H5. simpl in H3. rewrite H3.
    simpl. assert (count_true n
    (replace t (of_nat_lt (H k')) true) k' H = count_true n t k' H).
    apply replace_bitC_same. rewrite H6.
    reflexivity.  
    (* replacing at index doesn't change bitCount case*) 
  * simpl. assert ((replace t (of_nat_lt (H k')) true)[@of_nat_lt (H k)] =
    t[@of_nat_lt (H k)]). apply nth_order_replace_neq. apply H4. rewrite H5.
    assert (k' <? k = true). apply Nat.ltb_lt. assert (k' < S k).
    apply Nat.ltb_lt. apply H2. lia. apply IHk in H6. rewrite H6.
    destruct (t[@of_nat_lt (H k)]). reflexivity. reflexivity.
  - generalize dependent k. induction k' as [|k' IHk'].
    * simpl. intros. discriminate.
    * intros. simpl. destruct (t[@of_nat_lt (H k')]).
      assert (k = k' \/ k <? k' = true). 
      apply lt_implies. apply H2.
      destruct H3. rewrite H3. lia. apply IHk' in H3. lia.    
      assert (k = k' \/ k <? k' = true). apply lt_implies. apply H2.
      destruct H3. rewrite H3. lia. apply IHk' in H3. lia.
  - generalize dependent k. generalize dependent k'. induction k' as [|k' IHk'].
    * simpl. induction k. intros. lia. intros. destruct k.
    simpl. simpl in H3. rewrite H3. trivial. assert (S k > 0). lia.
    apply IHk in H4. unfold count_true.
    destruct (t[@of_nat_lt (H (S k))]). fold count_true. lia. fold count_true.
     simpl in H4. apply H4.
    * intros. destruct k. lia. apply count_gte. lia. apply H3.       
Qed.

Record HAMTRecord (V : Type) (n: nat) (def: V) `(HT : ShiftTable V def) (HT1: Bitmap n 0): Type :=
    {
      bitmap : HT1.(table'');
      map : HT.(table');
    }.
    
Theorem ne_implies : forall n m : nat, n <> m -> n < m \/ n > m.
    Proof.
      intros n m Hneq.
      destruct (lt_eq_lt_dec n m) as [[Hlt | Heq] | Hgt].
      - left. assumption.
      - contradiction.
      - right. assumption.
Qed.

#[export] Instance BitTable (B V:Type) (n: nat) (default: V) (f : B -> nat)
  `(HT: ShiftTable V default) `{EqDec B} (H: forall (b:B), f b < n) 
  (H2: forall (k k' : B), k <> k' -> f k <> f k')
  (HT1: Bitmap n 0) :  Table B V default :=
  {
    table := HAMTRecord V n default HT HT1; 
    empty := 
      {|
        bitmap := HT1.(empty'');
        map := HT.(empty');
      |}; 
    get k t :=
      match get'' (f k) t.(bitmap V n default HT HT1) with 
      |false => default
      |_ => 
        let k' := count'' (f k) t.(bitmap V n default HT HT1) in 
        get' k' t.(map V n default HT HT1)
        end;
    set k v t := 
      let k' := count'' (f k) t.(bitmap V n default HT HT1) in 
      match (get'' (f k) t.(bitmap V n default HT HT1)) with 
      |true =>
        let new_map :=  insert true k' v t.(map V n default HT HT1) in 
        {|
        bitmap := t.(bitmap V n default HT HT1);
        map := new_map;
        |}
      |_ => 
        let new_map := insert false k' v t.(map V n default HT HT1) in
        let new_bitmap := set'' (f k) t.(bitmap V n default HT HT1) in 
      {|
        bitmap := new_bitmap;
        map := new_map;
      |}
      end;
  }.

#[export] Instance BitTableAlgebraic (B: Type) {V : Type} {default:V} (n: nat)
  `(HT: ShiftTable V default) (f : B -> nat) `{EqDec B} (HF: forall (b:B), f b < n) 
  (HH: forall (k k' : B), k <> k' -> f k <> f k')
  `{HAT: @AlgebraicShiftTable V default _ _ HT} 
  (HT1: Bitmap n 0) `{HAT1: @AlgebraicBitmap n 0 _ _ _ } :
  AlgebraicTable (BitTable B V n default f HT HF HH HT1).
Proof.
  constructor; auto; intros; simpl.
  - rewrite get_empty_default''. reflexivity.  
  - destruct (get'' (f k) (bitmap V n default HT HT1 t)) eqn:H6.
    * simpl. rewrite -> H6. apply get_insert_same.
    * simpl. rewrite get_set_same''. assert ((count'' (f k)
      (set'' (f k) (bitmap V n default HT HT1 t))) = 
      count'' (f k) (bitmap V n default HT HT1 t)).
      apply count_lt. apply Nat.leb_le. trivial.  
      rewrite H3. apply get_insert_same.
  - assert (f k <> f k'). apply HH. apply H3. 
    destruct (get'' (f k) (bitmap V n default HT HT1 t)) eqn:H8.
    * simpl. destruct (get'' (f k') (bitmap V n default HT HT1 t)) eqn:H9.
    (* is both are set already, counts do not change, and get/set is same*)
      ** rewrite insertion_same. reflexivity. 
        assert (f k < f k' \/ f k > f k'). 
        apply ne_implies. apply H4. destruct H5.
        assert (count'' (f k') (bitmap V n default HT HT1 t) >
        count'' (f k) (bitmap V n default HT HT1 t)). apply count_ne. lia.
        apply H8. lia. 
        assert (count'' (f k') (bitmap V n default HT HT1 t) <
        count'' (f k) (bitmap V n default HT HT1 t)). apply count_ne. lia.
        apply H9. lia.
      ** reflexivity.
    * simpl. destruct (get'' (f k') (bitmap V n default HT HT1 t)) eqn:H9.
      ** simpl. rewrite get_set_other''. rewrite H9. assert (f k < f k' \/ f k > f k'). 
      apply ne_implies. apply H4. destruct H5. rewrite count_gt. 
      apply insertion_same_gt. apply Nat.leb_le. apply count_less.
      apply Nat.ltb_lt. apply H5. apply Nat.ltb_lt. apply H5. apply H8.
      rewrite count_lt. apply insertion_same_lt. 
      assert (count'' (f k') (bitmap V n default HT HT1 t) <
      count'' (f k) (bitmap V n default HT HT1 t)). apply count_ne. lia.
      apply H9. apply Nat.leb_gt. lia. 
      (* show that when get is true for the samller, the larger count is 
      always greater *) apply Nat.leb_le. lia. lia.  
      ** rewrite get_set_other''. rewrite H9. reflexivity. lia. 
Qed.

Check BitTable. 
(* Drop in BitTable to bottom layer of HAMT Table to get full HAMT representation *)

Definition HashBranchTable' {key V B:Type} {n:nat} {default:V}
  `{EqDec key} `{EqDec B}
  (f : B -> nat) `(HT: ShiftTable V default) (HF: forall (b:B), f b < n) 
  (HH: forall (k k' : B), k <> k' -> f k <> f k') (HT3: Bitmap n 0)
  (hash_f:key -> t B (S n))
  (HT1:forall (V:Type) (default:V), Table B V default)
  (HT2:Table key V default) : Table key V default :=
  PrecomposeTable (fun k:key => (hash_f k, k))
    (BranchTable  HT2
    (VectorBranchTable n B _ _ (BitTable B V n default f HT HF HH HT3))).
