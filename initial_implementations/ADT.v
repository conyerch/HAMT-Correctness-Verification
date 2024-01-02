Require Import Coq.Arith.EqNat.
Require Import Lia.
Require Import Coq.Strings.String.
Require Import List.
Import ListNotations.
Check [1].

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

Module Type ValType.
  Parameter V : Type.
  Parameter default : V.
End ValType.

Module FunTable (VT : ValType) <: Table.
  Definition V := VT.V.
  Definition default := VT.default.
  Definition key := nat.

  Definition table := key -> V.
  Definition empty : table :=
    fun _ => default.
  Definition get (k : key) (t : table) : V :=
    t k.
  Definition set (k : key) (v : V) (t : table) : table :=
    fun k' => if beq_nat k k' then v else t k'.

  Theorem get_empty_default: forall (k : key),
      get k empty = default.
      Proof.
      intros. simpl. unfold get. unfold empty. reflexivity.
    Qed.

  Theorem get_set_same: forall (k : key) (v : V) (t : table),
      get k (set k v t) = v.
  Proof. intros. unfold get, set. simpl. destruct (PeanoNat.Nat.eqb k k) eqn:H.
     reflexivity. Admitted. 
  Theorem get_set_other: forall (k k' : key) (v : V) (t : table),
      k <> k' -> get k' (set k v t) = get k' t.
  Proof. intros. unfold get, set. destruct (PeanoNat.Nat.eqb k k') eqn:H1.
   Admitted. 
End FunTable.

Module StringVal.
  Definition V := string.
  Definition default := ""%string.
End StringVal.
Module FunTableExamples.
  Module StringFunTable := FunTable StringVal.
  Import StringFunTable.
  Open Scope string_scope.
  Example ex1 : get 0 empty = "".
  Proof. reflexivity. Qed.
  Example ex2 : get 0 (set 0 "A" empty) = "A".
  Proof. reflexivity. Qed.
  Example ex3 : get 1 (set 0 "A" empty) = "".
  Proof. reflexivity. Qed.
End FunTableExamples.

Module ListsTable (VT : ValType) <: Table.
  Definition V := VT.V.
  Definition default := VT.default.
  Definition key := nat.
  Definition table := list (key * V).
  Definition empty : table :=  nil.
  Fixpoint get (k : key) (t : table) : V :=
    match t with 
    |nil => default
    |(x, y) :: t2 => 
        match (beq_nat x k) with
        |true => y
        |false => get k t2
        end
        end. 
  Definition set (k : key) (v : V) (t : table) : table := 
    (k, v) :: t.
  Theorem get_empty_default: forall (k : key),
      get k empty = default.
  Proof.
    intros. simpl. reflexivity.
    Qed.   
  Theorem get_set_same: forall (k : key) (v : V) (t : table),
      get k (set k v t) = v.
  Proof.
    intros. simpl. Admitted.    
  Theorem get_set_other: forall (k k' : key) (v : V) (t : table),
      k <> k' -> get k' (set k v t) = get k' t.
  Proof.
    (* FILL IN HERE *) Admitted.
End ListsTable.

Module StringListsTableExamples.
  Module StringListsTable := ListsTable StringVal.
  Import StringListsTable.
  Open Scope string_scope.
  Example ex1 : get 0 empty = "".
  Proof.
    intros. simpl. trivial. Qed.  
  Example ex2 : get 0 (set 0 "A" empty) = "A".
  Proof.
    (* FILL IN HERE *) Admitted.
  Example ex3 : get 1 (set 0 "A" empty) = "".
  Proof.
    (* FILL IN HERE *) Admitted.
End StringListsTableExamples.


Inductive tree (V : Type) : Type :=
| E
| T (l : tree V) (k : nat) (v : V) (r : tree V).
Arguments E {V}.
Arguments T {V}.

Definition ex_tree : tree string :=
  (T (T E 2 "two" E) 4 "four" (T E 5 "five" E))%string.

Definition empty_tree {V : Type} : tree V :=
  E.

Fixpoint bound {V : Type} (x : nat) (t : tree V) :=
  match t with
  | E => false
  | T l y v r => if Nat.leb x y then bound x l
                else if Nat.leb y x then bound x r
                     else true
  end.

  Fixpoint lookup {V : Type} (d : V) (x : nat) (t : tree V) : V :=
  match t with
  | E => d
  | T l y v r => if Nat.leb x y then lookup d x l
                else if Nat.leb y x then lookup d x r
                     else v
  end.

  Fixpoint insert {V : Type} (x : nat) (v : V) (t : tree V) : tree V :=
  match t with
  | E => T E x v E
  | T l y v' r => if Nat.leb x y then T (insert x v l) y v' r
                 else if Nat.leb y x then T l y v' (insert x v r)
                      else T l x v r
  end.

Module Type ETable_first_attempt.

Include Table.
  Parameter bound : key -> table -> bool.
  Parameter elements : table -> list (key * V).
  Axiom elements_complete : forall (k : key) (v : V) (t : table),
      bound k t = true ->
      get k t = v ->
      In (k, v) (elements t).
  Axiom elements_correct : forall (k : key) (v : V) (t : table),
      In (k, v) (elements t) ->
      bound k t = true /\ get k t = v.
End ETable_first_attempt.


Module TreeTable (VT : ValType) <: Table.
  Definition V := VT.V.
  Definition default := VT.default.
  Definition key := nat.
  Definition table := tree V.
  Definition empty : table :=
    @empty_tree V.
  Definition get (k : key) (t: table) : V :=
    lookup default k t.
  Definition set (k : key) (v : V) (t : table) : table :=
    insert k v t.
Theorem get_empty_default: forall (k : key),
      get k empty = default.
  Proof. Admitted.
Theorem get_set_same: forall (k : key) (v : V) (t : table),
      get k (set k v t) = v.
  Proof. Admitted.

  Theorem get_set_other: forall (k k' : key) (v : V) (t : table),
      k <> k' -> get k' (set k v t) = get k' t.
  Proof. Admitted. 

End TreeTable.

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

Module Type ETableAbs.
  Parameter table : Type.
  Definition key := nat.
  Parameter V : Type.
  Parameter default : V.
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
End ETableAbs.

Module ETableAssoc (VT : ValType) <: ETableAbs.

  Definition V := VT.V.
  Definition default := VT.default.
  Definition table := list (key * V).
  Definition key := nat. 
  Definition empty : table := 
    [].
  Fixpoint get (k : key) (t : table) : V :=
    match t with 
    |nil => default
    |(x, y) :: t2 => 
        match (beq_nat x k) with
        |true => y
        |false => get k t2
        end
        end. 
  Definition set (k : key) (v : V) (t : table) : table := 
    (k, v) :: t.

  Fixpoint bound (k : key) (t : table) : bool :=
    match t with 
    |[] => false
    |(k', v) :: t' => 
        if beq_nat k k' then true else bound k t'
      end. 
  Definition elements (t : table) : list (key * V) := t.

  Require Export Bool. 
  
  Definition Abs (t : table) : partial_map V :=
    map_of_list (elements t).

  Definition rep_ok (t : table) : Prop := 
    match t with 
    |[] => True
    |x :: t' => True 
    end.
    
  Theorem empty_ok : rep_ok empty.
    Proof.
      intros. simpl. trivial.
      Qed. 
  Theorem set_ok : forall (k : key) (v : V) (t : table),
        rep_ok t -> rep_ok (set k v t).
    Proof.
      intros. simpl. trivial.
      Qed.
      
  Theorem empty_relate :
      Abs empty = empty_map.
    Proof.
      intros. unfold Abs. simpl. trivial.
      Qed.
      
  Lemma rep_comm : forall (t : table) (k : key) (v : V),
      rep_ok ((k, v) :: t) -> rep_ok t.
    Proof. unfold rep_ok. intros. simpl. trivial. induction t.
    * trivial.
    * trivial.
    Qed.          

  Theorem bound_relate : forall (t : table) (k : key),
      rep_ok t ->
      map_bound k (Abs t) = bound k t.
  Proof.
    intros. simpl. induction t.
    - simpl. trivial.
    - destruct a. simpl. destruct (PeanoNat.Nat.eqb k k0) eqn :h1.
      * unfold Abs. unfold elements. unfold map_of_list. unfold update. simpl.
      unfold t_update. simpl. unfold map_bound. assert (PeanoNat.Nat.eqb k0 k = true). admit. rewrite -> H0.
      reflexivity. 
      * apply rep_comm in H. apply IHt in H. unfold Abs. unfold elements. unfold map_of_list.
      unfold update. unfold t_update. simpl. unfold map_bound. assert (PeanoNat.Nat.eqb k0 k = false). admit.
      rewrite -> H0. unfold map_bound in H. unfold Abs in H. unfold elements in H. unfold map_of_list in H. unfold update in H. unfold t_update in H. apply H.
  Admitted.
  
  Theorem lookup_relate : forall (t : table) (k : key),
      rep_ok t ->
      map_find default k (Abs t) = get k t.
  Proof.
    intros. unfold Abs. unfold elements. unfold map_of_list. unfold update. unfold t_update. induction t.
    - simpl. trivial. 
    - destruct a. unfold map_find. unfold find. destruct (PeanoNat.Nat.eqb k0 k) eqn:h.
    * unfold get. rewrite -> h. reflexivity.
    * apply rep_comm in H. apply IHt in H. unfold map_find in H. unfold find in H. unfold get.
    rewrite -> h. unfold get in H. apply H.
    Qed.     
      
  Theorem insert_relate : forall (t : table) (k : key) (v : V),
      rep_ok t ->
      map_update k v (Abs t) = Abs (set k v t).
  Proof.
    intros. induction t.
    * simpl. trivial.
    * unfold Abs. unfold elements. unfold set. unfold map_update. unfold update. unfold t_update.
    unfold map_of_list. unfold update. unfold t_update. reflexivity.
    Qed.              
  Theorem elements_relate : forall (t : table),
      rep_ok t ->
      Abs t = map_of_list (elements t).
  Proof.
    intros. unfold elements. unfold Abs. unfold elements. reflexivity.
  Qed.      
End ETableAssoc.


(* Extended Table Definition for HAMT*)
From Coq Require Import Arith.

Module Type ExtendedTableAbs.
  Parameter table : Type.
  Definition key := nat.
  Parameter V : Type.
  Parameter default : V.
  Parameter bitSize : nat.
  Parameter mask : nat.
  Parameter hash : key -> list nat. 
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
  Parameter bitSize : nat.
  Parameter maskSize : nat.
End ExtendedValType.

Inductive HAMT (V : Type) : Type :=
  | Empty (shift : nat)
  | HashMapEntry (shift : nat) (k : key) (val : V)
  | ArrayNode (shift : nat) (map : list (HAMT V))
  | CollisionNode (shift : nat) (hmes : list (key * V)).

Module ExtendedTableHash (VT : ExtendedValType) <: ExtendedTableAbs.

  Definition V := VT.V.
  Definition default := VT.default.
  Definition bitSize := VT.bitSize.
  Definition mask := VT.maskSize. 
  Definition hash := VT.hash. 
  Definition table := HAMT V.
  Definition key := nat. 
  Definition empty  (shift : nat): table := 
    Empty V shift.

  Definition maxDepth : nat := bitSize / mask.
  Definition nodeSize : nat := mask + 1.

  Fixpoint indexHelper (subHash : list nat) (steps : nat) (base : nat) := 
    match steps with 
    |0 => 0
    |S n => (nth (base + steps) subHash 0) + indexHelper subHash n base
    end. 

  Definition getIndex (shift : nat) (hash : list nat) := 
    indexHelper hash mask (shift * mask).

  (*Fixpoint replace (l : list (HAMT V))  (i : nat) (v : (HAMT V)) := 
      match l with 
      | [] => []
      | a :: l1 => match i with 
                   |    0 => v :: l1 
                   | S i1 => a :: replace l1 i1 v 
                   end 
      end.*)
    
  Fixpoint findv (hmes : list (nat * V)) (k1 : nat) :=
      match hmes with 
      |[] => default
      |(k, v) :: t => 
        if (k =? k1) then v else findv t k1
      end.

Unset Guard Checking.

  Program Fixpoint get (k : key) (t : table) {struct t} : V :=
    match t with 
    |HashMapEntry _ shift k1 val  => 
      if (k =? k1) then val else default
    | ArrayNode _ shift map => 
      get k (nth (getIndex shift (hash k)) map (empty shift))
    | CollisionNode _ shift hmes => 
      (* call helper function *)
      findv hmes k
    | Empty _ shift => 
      default
    end.

  Program Fixpoint set (k : key) (v : V) (t : table) {struct t} : table := 
    match t with 
    |HashMapEntry _ shift k1 val  => 
      if (shift =? maxDepth) then CollisionNode V shift ((k, v) :: (k1, val) :: []) else
      set k1 val (set k v (ArrayNode V (shift + 1) []))
    | ArrayNode _ shift map => 
      set k v (nth (getIndex shift (hash k)) map (empty shift)) 
    | CollisionNode _ shift hmes => 
      (* call helper function *)
      CollisionNode V shift ((k, v) :: hmes)
    | Empty _ shift => 
        HashMapEntry V shift k v
    end.

Set Guard Checking.

  Fixpoint bound (k : key) (t : table) : bool :=
    match ((get k t) =? default) with 
    |True => false
    |False => true
    end. 

  Definition elements (t : table) : list (key * V) := 
    Admitted. 
  Definition Abs (t : table) : partial_map V :=
    Admitted. 
  Definition rep_ok (t : table) : Prop := 
    Admitted. 
