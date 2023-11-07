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
    | Empty 
    | HashMapEntry (hash : list nat) (k : key) (val : V)
    | ArrayNode (map : list (key * HAMT V))
    | CollisionNode (hmes : list (key * V)).
  
  Module ExtendedTableHash (VT : ExtendedValType) <: ExtendedTableAbs.
  
    Definition V := VT.V.
    Definition default := VT.default.
    Definition bitSize := VT.bitSize.
    Definition mask := VT.maskSize. 
    Definition hash := VT.hash. 
    Definition table := HAMT V.
    Definition key := nat. 
    Definition empty: table := 
      Empty V. 

    Definition minSize : nat := mask + mask.
  
    Fixpoint indexHelper (subHash : list nat) (steps : nat) := 
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

    Definition dropBits (hash : list nat) := dropBitsH hash mask. 

    Fixpoint inList (l : list (key * HAMT V)) (k : key) := 
      match l with 
      | [] => false
      | (k1, v) :: l1 => 
        if (k1 =? k) then true else inList l1 k
      end.
    
    Fixpoint replace (l : list (key * HAMT V)) (k : key) (v : HAMT V) := 
        match l with 
        |[] => []
        |(k1, v1) :: l1 => 
            if (k =? k1) then ((k, v) :: l1) else (k1, v1) :: replace l1 k v
            end.
    
    Fixpoint find (l : list (key * HAMT V)) (k : key)  := 
        match l with 
            |[] => empty 
            |(k1, v) :: l1 => 
                if (k =? k1) then v else find l1 k 
            end.

Unset Guard Checking.

    Program Fixpoint setH (h: list nat) (k : key) (v : V) (t : table) {struct t} : table := 
        match t with 
      |HashMapEntry _  hash k1 v1  => 
        let hash1 := dropBits hash in 
        let h := dropBits h in 
        setH hash k1 v1 (setH h k v (ArrayNode V []))
      | ArrayNode _  map => 
        let minKey := getIndex h in 
        if (inList map minKey) then 
        ArrayNode V (replace map minKey (setH h k v (find map k))) else 
        ArrayNode V ((minKey, HashMapEntry V h k v) :: map)
      | CollisionNode _ hmes => 
        (* call helper function *)
        CollisionNode V  ((k, v) :: hmes)
      | Empty _  => 
          HashMapEntry V h k v
      end.
Set Guard Checking. 

    Definition set (k : key) (v : V) (t : table) : table := 
        let h := hash k in 
        setH h k v t. 

    Fixpoint findv (hmes : list (nat * V)) (k1 : nat) :=
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
      | ArrayNode _ map => 
        get k (find map k)
      | CollisionNode _ hmes => 
        (* call helper function *)
        findv hmes k
      | Empty _  => 
        default
      end.
Set Guard Checking.

      Fixpoint mapAL (l:list (key * HAMT V)) : list (HAMT V) :=
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
      | ArrayNode _ map => 
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

    Fixpoint allEq (l : list (key * V)) (shift : nat) (test : nat): Prop := 
      match l with 
        |[] => True
        |(k, v) :: t => if ((getIndex (hash k)) =? test) then allEq t shift test else False
        end.

    Definition rep_ok (t : table) : Prop := 
      match t with 
      |HashMapEntry _ hash k1 val  => 
        True
      | ArrayNode _ map => 
        NoDup map  (* check all keys are not equal right place and each sub HAMT is a HAMT*)
      | CollisionNode _ hmes => 
        match hmes with 
        |[] => True
        |(k, v) :: t => True
        end
      | Empty _ => 
        True 
        end.
  
  Theorem empty_ok : rep_ok empty.
    Proof.
      intros. simpl. trivial.
      Qed. 
  Theorem set_ok : forall (k : key) (v : V) (t : table),
        rep_ok t -> rep_ok (set k v t).
    Proof.
      intros. simpl. induction t.
      - simpl. trivial.
      - unfold set. simpl. destruct (getIndex (dropBits (hash k)) =? getIndex hash0) eqn: h1.
        * destruct (getIndex hash0 =? getIndex (dropBits (hash k))) eqn: h2.
            ** simpl. destruct (k0 =? getIndex (dropBits (hash k))) eqn: h3.
                *** admit.
                *** admit.
            ** simpl. admit.
        * simpl. admit.
    - unfold set. simpl.
        destruct (inList map (getIndex (hash k))) eqn : h1.
        * simpl. admit.
        * simpl. admit.
    - simpl. trivial.
    Admitted.                        
      
 
  Theorem empty_relate :
      Abs (empty) = empty_map.
    Proof.
      intros. unfold Abs. simpl. trivial.
      Qed.
    