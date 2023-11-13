Require Import Coq.Arith.EqNat.
Require Import Lia.
Require Import Coq.Strings.String.
Require Import List.
Import ListNotations.

Module Type Table.

Parameter table : Type.

Definition key := nat.

Parameter V : Type.

Parameter default : V.

Parameter empty : table.

Parameter get : key -> table -> V.

Parameter set : key -> V -> table -> table.

Axiom get_empty_default : forall (k : key),
      get k empty = default.
  Axiom get_set_same : forall (k : key) (v : V) (t : table),
      get k (set k v t) = v.
  Axiom get_set_other : forall (k k' : key) (v : V) (t : table),
      k <> k' -> get k' (set k v t) = get k' t.
End Table.

Definition key := nat. 
Definition total_map (A : Type) : Type := nat -> A.
Definition partial_map (A : Type) := total_map (option A).

Definition t_update {A : Type}
           (m : total_map A) (x : nat) (v : A) : total_map A :=
  fun x' => if beq_nat x x' then v else m x'.

Definition update {A : Type}
           (m : partial_map A) (x : nat) (v : A) : partial_map A :=
  t_update m x (Some v).

Definition find {V : Type} (d : V) (k : key) (m : partial_map V) : V :=
  match m k with
  | Some v => v
  | None => d
  end.

  Definition map_bound {V : Type} (k : key) (m : partial_map V) : bool :=
  match m k with
  | Some _ => true
  | None => false
  end.

Definition map_update {V : Type}
           (k : key) (v : V) (m : partial_map V) : partial_map V :=
  update m k v.
Definition t_empty {A : Type} (v : A) : total_map A :=
    (fun _ => v).
Definition empty {A : Type} : partial_map A :=
  t_empty None.
Definition map_find {V : Type} := @find V.
Definition empty_map {V : Type} := @empty V.
  Fixpoint map_of_list {V : Type} (el : list (key * V)) : partial_map V :=
    match el with
    | [] => empty
    | (k, v) :: el' => update (map_of_list el') k v
    end.

From Coq Require Import Arith.

Module Type ExtendedTableAbs.
    Parameter table : Type.
    Definition key := nat.
    Definition hashKeys := nat.
    Parameter V : Type.
    Parameter default : V.
    Parameter keyNumber : nat.
    Parameter hash : key -> list hashKeys. 
    Parameter empty : table.
    Parameter get : key -> table -> V.
    Parameter set : key -> V -> table -> table.
    Parameter bound : key -> table -> bool.
    Parameter elements : table -> list (key * V).
    Parameter Abs : table -> partial_map V.
    Parameter rep_ok : table -> Prop.
  
  Axiom empty_ok :
    rep_ok empty.
  Axiom set_ok : forall (k : key) (v : V) (t : table),
    rep_ok t -> rep_ok (set k v t).
  Axiom empty_relate :
    Abs empty = empty_map.
  Axiom bound_relate : forall (t : table) (k : key),
    rep_ok t ->
    map_bound k (Abs t) = bound k t.
  Axiom lookup_relate : forall (t : table) (k : key),
    rep_ok t ->
    map_find default k (Abs t) = get k t.
  Axiom insert_relate : forall (t : table) (k : key) (v : V),
    rep_ok t ->
    map_update k v (Abs t) = Abs (set k v t).
  Axiom elements_relate : forall (t : table),
    rep_ok t ->
    Abs t = map_of_list (elements t).
  
  End ExtendedTableAbs.
  
  Module Type ExtendedValType.
    Parameter V : Type.
    Parameter default : V.
    Parameter hash : nat -> list nat. 
    Parameter keyNum : nat.
  End ExtendedValType.
  
  Inductive HAMT (V : Type) : Type :=
    | Empty 
    | HashMapEntry (hash : list nat) (k : key) (val : V)
    | ListNode (map : list (key * HAMT V))
    | CollisionNode (hmes : list (key * V)).
  
  Module ExtendedTableHash (VT : ExtendedValType) <: ExtendedTableAbs.
  
    Definition V := VT.V.
    Definition default := VT.default.
    Definition keyNumber := VT.keyNum.
    Definition hash := VT.hash. 
    Definition table := HAMT V.
    Definition key := nat. 
    Definition hashKeys := nat. 
    Definition empty: table := 
      Empty V. 
  
    (*Fixpoint indexHelper (subHash : list nat) (steps : nat) := 
      match steps with 
      |0 => 0
      |S n => (nth steps subHash 0) + indexHelper subHash n 
      end. 
  
    Definition getIndex (hash : list nat) := 
      indexHelper hash mask.
    
    Fixpoint dropBitsH (hash : list nat) (s : nat) := 
      match hash with 
      |[] => []
      |h :: t => match s with 
        |0 => t
        |S n => dropBitsH t n
        end
      end. 

    Definition dropBits (hash : list nat) := dropBitsH hash mask. *)

    Fixpoint inList (l : list (hashKeys * HAMT V)) (k : hashKeys) := 
      match l with 
      | [] => false
      | (k1, v) :: l1 => 
        if (k1 =? k) then true else inList l1 k
      end.
    
    (*Fixpoint replace (l : list (key * HAMT V)) (k : key) (v : HAMT V) := 
        match l with 
        |[] => []
        |(k1, v1) :: l1 => 
            if (k =? k1) then ((k, v) :: l1) else (k1, v1) :: replace l1 k v
            end.
    
    *)
    Fixpoint find (l : list (hashKeys * HAMT V)) (k : hashKeys)  := 
        match l with 
            |[] => empty 
            |(k1, v) :: l1 => 
                if (k =? k1) then v else find l1 k 
            end.

Unset Guard Checking.

    Program Fixpoint setH (h: list hashKeys) (k : key) (v : V) (t : table) {struct t} : table := 
        match t with 
      |HashMapEntry _ hash k1 v1  => 
        match h with 
        |[] => CollisionNode V ((k, v) :: (k1, v1) :: [])
        |_ => setH hash k1 v1 (setH h k v (ListNode V []))
        end
      | ListNode _  map => 
        match h with
        |[] => empty
        |k :: t => 
        if (inList map k) then 
        ListNode V ((k, (setH t k v (find map k))) :: map) else 
        ListNode V ((k, HashMapEntry V h k v) :: map)
        end
      | CollisionNode _ hmes  => 
        (* call helper function *)
        CollisionNode V ((k, v) :: hmes)
      | Empty _ => 
          HashMapEntry V h k v
      end.
Set Guard Checking. 

    Definition set (k : key) (v : V) (t : table) : table := 
        let h := hash k in 
        setH h k v t. 

    Fixpoint findv (hmes : list (key * V)) (k1 : nat) :=
        match hmes with 
        |[] => default
        |(k, v) :: t => 
          if (k =? k1) then v else findv t k1
        end.
  
Unset Guard Checking.
    Program Fixpoint get (k : key) (t : table) {struct t} : V :=
      match t with 
      |HashMapEntry _ hash k1 val  => 
        if (k =? k1) then val else default
      | ListNode _ map => 
        get k (find map k)
      | CollisionNode _ hmes => 
        (* call helper function *)
        findv hmes k
      | Empty _  => 
        default
      end.
Set Guard Checking.

      Fixpoint mapAL (l:list (hashKeys * HAMT V)) : list (HAMT V) :=
        match l with
          | nil => nil
          | cons (k, v) t => v :: mapAL t
        end.
      
      Fixpoint appList (l: list (list (key * V))) : list (key * V) := 
        match l with
          | nil => nil
          | cons l1 l2 => app l1 (appList l2)
        end.
      

Unset Guard Checking.
      Program Fixpoint elements (t : table) {struct t} : list (key * V) := 
        match t with 
        |HashMapEntry _ hash k1 val  => 
          (k1, val) :: []
        | ListNode _ map => 
          appList (List.map elements (mapAL map))
        | CollisionNode _ hmes => 
          hmes
        | Empty _ => 
          []
          end. 

Set Guard Checking.

    Fixpoint bIn (k : key) (l : list (key * V)) : bool := 
      match l with 
      |[] => false
      |(k1, v) :: t => if (beq_nat k k1) then true else bIn k t
      end. 

    Definition bound (k : key) (t : table) : bool :=
     bIn k (elements t).

    Definition Abs (t : table) : partial_map V := 
      map_of_list (elements t).

    (*Fixpoint noneEq (l : list (key * HAMT V)) : Prop := 
      match l with 
        |[] => True
        |(k, v) :: t => if inList t k then False else noneEq t
        end.*)

    Definition rep_ok (t : table) : Prop := 
      match t with 
      |HashMapEntry _ hash k1 val  => 
        True
      | ListNode _ map => 
        True
      | CollisionNode _ hmes => 
        True
      | Empty _ => 
        True 
        end.
  
  (*Theorem noneEq_comm : forall (l: list (key * HAMT V)) (k : key) (h : HAMT V),
    noneEq ((k, h) :: l) -> noneEq l.
    Proof. 
    intros. Admitted.     

  Theorem noneEq_assoc : forall (l: list (key * HAMT V)) (k : key) (k2: key) (h : HAMT V) (h2 : HAMT V),
    noneEq ((k, h) :: l) -> k <> k2 -> noneEq ((k, h) :: replace l k2 h2).
    Proof. 
    intros. induction l.
    - simpl. trivial.
    - unfold replace. destruct a. destruct (k2 =? k0) eqn : h1.
    * simpl. simpl in H. Admitted.   

  Theorem nonEq_replace : forall (l: list (key * HAMT V)) (k : key) (h : HAMT V),
    noneEq l -> noneEq (replace l k h).
    Proof.
    intros. simpl. induction l. 
    * simpl. trivial.
    * assert (noneEq l). destruct a. apply noneEq_comm with (k :=k0) (h:=h0) in H. apply H.
    destruct a. unfold replace. destruct (k =? k0) eqn: h1.    
    assert (k = k0). admit. rewrite -> H1. simpl. simpl in H. apply H.
    fold replace. simpl. simpl in H. apply IHl in H0. simpl in H0.  Admitted.      *)
      

  Theorem empty_ok : rep_ok empty.
    Proof.
      intros. simpl. trivial.
      Qed. 

  Theorem set_ok : forall (k : key) (v : V) (t : table),
        rep_ok t -> rep_ok (set k v t).
    Proof.
      intros. simpl. unfold set. simpl. induction t. simpl. trivial. 
      - simpl. destruct (hash k).
        * simpl. trivial.
        * simpl. destruct (hash0).
          ** trivial.   
          ** destruct (n =? n0) eqn: h1.
          *** simpl. trivial.
          *** simpl. trivial.
      - simpl. destruct (hash k).
        * trivial.
        * destruct (inList map n) eqn: h1.
          ** simpl. trivial.
          ** simpl. trivial.
      - simpl. trivial.
    Qed.                             
    
  Theorem empty_relate :
      Abs (empty) = empty_map.
    Proof.
      intros. unfold Abs. simpl. trivial.
      Qed.

    Theorem eqb_true : forall (n m : nat),
      n =? m = true -> n = m.
    Proof.
      intros n. induction n.
      - intros [] eq. reflexivity. discriminate.
      - intros [] eq.
        + discriminate.
        + apply f_equal. apply IHn. apply eq.
    Qed.

    Theorem beq_nat_sym : forall (n m : nat),
    beq_nat n m = beq_nat m n.
     Proof.
        intro n.
        induction n as [| n']. 
        intro m. destruct m as [| m']. 
        reflexivity.
        reflexivity. 
        intro m. destruct m as [| m'].
        reflexivity.
        simpl. apply IHn'. 
    Qed.

    Lemma eqNat_refl : forall (n m : nat) (b : bool),
      (n =? m) = b -> (m =? n) = b.
      Proof.
      intros m n b H. destruct b.
      - trivial. rewrite -> eqb_true with (n:=m) (m:=n).
        * symmetry. apply beq_nat_refl.
        * apply H.
      - rewrite -> beq_nat_sym. apply H. 
    Qed.
     
    Lemma rep_comm : forall (a : key * HAMT V) (m : list (key * HAMT V)),
    rep_ok (ListNode V (a :: m)) -> rep_ok (ListNode V m).
    Proof. Admitted. 

    Lemma rep_comm2 : forall (a : key) (v : V) (m : list (key * V)),
    rep_ok (CollisionNode V ((a, v) :: m)) -> rep_ok (CollisionNode V m).
    Proof. Admitted. 

    Lemma map_comm : forall (a k : key) (v : V) (m : list (key * V)),
      map_bound k (map_of_list ((a, v) :: m)) = bIn k ((a, v) :: m) -> 
      map_bound k (map_of_list m) = bIn k m. Proof. Admitted. 

  Theorem bound_relate : forall (t : table) (k : key),
      rep_ok t ->
      map_bound k (Abs t) = bound k t.
  Proof. intros. induction t.
  - simpl. unfold Abs. unfold elements. simpl. unfold bound. simpl. unfold map_bound. simpl. reflexivity.
  - unfold Abs. unfold elements. simpl. unfold update. unfold t_update. unfold bound. 
    unfold elements. unfold bIn. unfold map_bound. destruct (k0 =? k) eqn :h1.
    * trivial. rewrite -> eqNat_refl with (b:= true). trivial. apply h1.
    * simpl. rewrite -> eqNat_refl with (b:= false). reflexivity. apply h1.
  - unfold Abs. unfold bound. destruct ((elements (ListNode V map))).
    * simpl. unfold bound. simpl. unfold map_bound. simpl. reflexivity.
    * induction l. 
      ** simpl. unfold map_bound. unfold update. unfold t_update. destruct p. destruct (k =? k0) eqn: h1.
        *** rewrite -> eqNat_refl with (b := true). reflexivity. apply h1.
        *** rewrite -> eqNat_refl with (b := false). simpl. reflexivity. apply h1.
      ** simpl. destruct p. unfold map_bound. destruct a. unfold update. unfold t_update.
      destruct (k0 =? k) eqn :h1. 
        *** rewrite -> eqNat_refl with (b := true). reflexivity. apply h1.
        *** assert ((k =? k0) = false). rewrite -> eqNat_refl with (b := false). reflexivity. apply h1.
        rewrite -> H0. destruct (k1 =? k) eqn :h2. rewrite -> eqNat_refl with (b := true).
        reflexivity. apply h2. rewrite -> eqNat_refl with (b := false). apply map_comm in IHl.
        unfold map_bound in IHl. apply IHl. apply h2.              
  - unfold Abs. unfold map_of_list. unfold elements. unfold bound. unfold elements. unfold bIn.
    unfold update. unfold t_update. unfold map_bound. induction hmes.
    * simpl. reflexivity.
    * destruct a. destruct (k =? k0) eqn : h1. rewrite -> eqNat_refl with (b := true). trivial. apply h1.
    rewrite -> eqNat_refl with (b:= false). apply rep_comm2 in H. apply IHhmes in H. apply H. apply h1.
  Qed.     

  Theorem lookup_relate : forall (t : table) (k : key),
      rep_ok t ->
      map_find default k (Abs t) = get k t.
  Proof.
  intros. simpl. unfold map_find. unfold Abs. induction t.
   - simpl. unfold ADT_HAMT2.find. simpl. reflexivity.
   - unfold elements. unfold ADT_HAMT2.find. unfold get. simpl. unfold update. unfold t_update. destruct (k =? k0) eqn: h1.
   * rewrite -> eqNat_refl with (b:= true). reflexivity. apply h1.
   * rewrite -> eqNat_refl with (b:= false). simpl. reflexivity. apply h1.
   - admit.
   - simpl. unfold ADT_HAMT2.find. unfold map_of_list. unfold update. unfold t_update.
   unfold findv. induction hmes.
   * simpl. reflexivity.
   * destruct a. apply rep_comm2 in H. apply IHhmes in H. destruct (k =? k0) eqn : h1.                
     rewrite -> eqNat_refl with (b:= true). reflexivity. apply h1. rewrite -> eqNat_refl with (b:= false).
     apply H. apply h1.
  Admitted.

  Theorem insert_relate : forall (t : table) (k : key) (v : V),
  rep_ok t -> map_update k v (Abs t) = Abs (set k v t).
  Proof. intros. induction t.
  - simpl. unfold Abs. simpl. unfold update. unfold t_update. unfold map_update. simpl. unfold update. unfold t_update. reflexivity.
  - simpl. unfold Abs. unfold elements. unfold map_of_list. unfold update. unfold t_update. unfold map_update. unfold update. unfold t_update.       unfold set. unfold setH.                  
    