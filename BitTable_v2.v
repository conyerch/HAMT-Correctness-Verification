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

Fixpoint insert' {V: Type} (l : list V) (n: nat) (v: V) := 
  match l with 
  |[] => [v]
  |b :: t => 
    match n with 
    |0 => v :: b :: t
    |S n' => b :: insert' t n' v 
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
      k <> k' -> get k' (set k v t) = get k' t;
  }.
  
Definition key := nat.

Class ShiftTable (V: Type) (default: V) `{EqDec nat} := 
  {
    table' : Type;
    empty' : table';
    get' : key -> table' -> V;
    insert : key -> V -> table' -> table'
  }.

Class AlgebraicShiftTable {V:Type} {default:V} `(HT:ShiftTable V default) :=
    {
      get_empty_default' : forall (k : nat), get' k empty' = default;
      get_insert_same : forall (k : nat) (v : V) (t : table'),
        get' k (insert k v t) = v;
      insertion_same_lt : forall (k k': nat) (v : V) (t : table'), 
      k' <=? k = false -> get' k (insert k' v t) = get' k t;
      insertion_same_gt : forall (k k': nat) (v : V) (t : table'), 
        k' <=? k = true -> get' (S k) (insert k' v t) = get' k t;
    }.

#[export] Instance HamtTable {V : Type} (default : V) 
 `{EqDec nat} : ShiftTable V default :=
  {
    table' := list V;
    empty' := [];
    get' k t := nth k t default;
    insert k v t := insert' t k v;
  }.

Axiom key_within_bounds : forall {V: Type} (default: V) `{EqDec nat} (k: key) (t: (HamtTable default).(table')), k > length t -> False.

Require Import Lia.

#[export] Instance ShiftListAlgebraic {V: Type} (def: V) `{EqDec nat}:
  AlgebraicShiftTable (HamtTable def).
Proof.
  constructor; auto; intros; simpl.
  - induction k. simpl. reflexivity. simpl. reflexivity.
  - generalize dependent t. induction k. destruct t. simpl. 
    reflexivity. simpl. reflexivity.
    simpl. destruct t eqn: H1.
    assert (False). apply key_within_bounds with (default := def) 
    (H := eqNat) (H0 := eqDecNat) (k := (S k)) (t := t). 
    rewrite H1. simpl. lia. contradiction.
    simpl. apply IHk. 
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

#[export] Instance BitTable (B V:Type) (n: nat) (default:V) (f : B -> nat)
  `(HT: ShiftTable V default) `{EqDec B} (H: forall (b:B), f b < n) 
  (H2: forall (k k' : B), k <> k' -> f k <> f k')
  (HT1: Bitmap n 0) : Table B V default :=
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
        let new_map :=  insert k' v t.(map V n default HT HT1) in 
        {|
        bitmap := t.(bitmap V n default HT HT1);
        map := new_map;
        |}
      |_ => 
        let new_map := insert k' v t.(map V n default HT HT1) in
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
      ** assert (f k < f k' \/ f k > f k'). apply ne_implies. 
        apply H4. destruct H5. apply insertion_same_lt. admit. 
        apply insertion_same_lt. admit.
      ** reflexivity.
    * simpl. destruct (get'' (f k') (bitmap V n default HT HT1 t)) eqn:H9.
      ** simpl. rewrite get_set_other''. rewrite H9. assert (f k < f k' \/ f k > f k'). 
      apply ne_implies. apply H4. destruct H5. rewrite count_gt. 
      apply insertion_same_gt. apply Nat.leb_le. apply count_less.
      apply Nat.ltb_lt. apply H5. apply Nat.ltb_lt. apply H5. apply H8.
      rewrite count_lt. apply insertion_same_lt.
      (* show that when get is true for the samller, the larger count is 
      always greater *) admit. apply Nat.leb_le. lia. lia.  
      ** rewrite get_set_other''. rewrite H9. reflexivity. lia. 
Admitted. 
  
  