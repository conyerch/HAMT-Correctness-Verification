(* Notation *)

Notation "( x , y )" := (pair x y).
Notation "X * Y" := (prod X Y) : type_scope.
Infix "::" := cons (at level 60, right associativity) : list_scope.
Notation "x :: l" := (cons x l)
                     (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..).
Definition mylist := 1 :: (2 :: (3 :: nil)).

(* Imports *)

Require Coq.extraction.Extraction.
Extraction Language OCaml.

From Coq Require Import Arith.Arith.
From Coq Require Import Init.Nat.
From Coq Require Import Arith.EqNat.
Require Import ZArith.
From Coq Require Import Array.PArray.
From Coq Require Import Uint63.
From Coq Require Import ZArith.Znat.

(* Definitions *)

Fixpoint eqb (n m : nat) : bool :=
  match n with
  | O => match m with
         | O => true
         | S m' => false
         end
  | S n' => match m with
            | O => false
            | S m' => eqb n' m'
            end
  end.

Definition key := nat.
Definition shift :Z := 5. 
Definition mask :Z := 31.
Definition FMV_prime : Z := 1099511628211.
Definition FMV_offset : Z := 14695981039346656037.

(* HAMT Module *)

Module HAMT.

Inductive HAMT (A : Type) : Type :=
  | Empty
  | HashMapEntry (hash : Z) (k : key) (val : A)
  | ArrayNode (shift : Z) (map : array (HAMT A))
  | CollisionNode (hash : Z) (hmes : list (key * A)).
  
Definition empty_HAMT (A:Type) : HAMT A :=
    Empty A.

Definition hasher2 (key : nat) : Z := 
        let hash := FMV_offset in
        let int_initial := Z.of_nat key in 
        let hash := Z.mul FMV_prime hash in 
        let hash := Z.lor hash (Z.land int_initial 255) in
        let hash := Z.mul FMV_prime hash in 
        let hash := Z.lor hash (Z.land int_initial 65280) in
        let hash := Z.mul FMV_prime hash in 
        let hash := Z.lor hash (Z.land int_initial 16711680) in
        let hash := Z.mul FMV_prime hash in 
        let hash := Z.lor hash (Z.land int_initial 4278190080) in
        let hash := Z.mul FMV_prime hash in 
        let hash := Z.lor hash (Z.land int_initial 1095216660480) in
        let hash := Z.mul FMV_prime hash in 
        let hash := Z.lor hash (Z.land int_initial 280375465082880) in
        let hash := Z.mul FMV_prime hash in 
        let hash := Z.lor hash (Z.land int_initial 71776119061217280) in
        let hash := Z.mul FMV_prime hash in 
        let hash := Z.lor hash (Z.land int_initial 18374686479671623680) in
        hash. 
    
Fixpoint findv (A : Type) (hmes : list (key * A)) (k1 : key) :=
  match hmes with 
  |[] => None
  |(k, v) :: t => 
    if (eqb k k1) then Some v else findv A t k1
  end.

Fixpoint find (A : Type) (hamt : HAMT A) (k : key) : option A :=
  match hamt with 
  |HashMapEntry _ hash k1 val  => 
      if eqb k k1 then Some val else None
  | ArrayNode _ shift map => 
      find A (get map (of_Z(Z.land (Z.shiftr (hasher2 k) shift) mask))) k
  | CollisionNode _ hash hmes => 
      findv A hmes k
  | Empty _ => 
      None
  end.

Fixpoint remove_ass (A : Type) (k : key) (l : list (key * A)) : list (key * A) :=
    match l with
    | nil => nil
    | (k1, v) :: tl => if (eqb k k1) then remove_ass A k tl else (k1, v) :: (remove_ass A k tl)
    end.
       
Fixpoint remove (A : Type) (hamt : HAMT A) (k : key) : HAMT A :=
   match hamt with 
   | ArrayNode _ shifter map => 
     let index := (of_Z(Z.land (Z.shiftr (hasher2 k) shifter) mask)) in 
     let newArr := copy map in 
     let newVal := remove A (get map index) k in 
     ArrayNode A shift (set map index newVal)
   | Empty _ => 
       Empty A
   | CollisionNode _ hash hmes => 
       let newl := (remove_ass A k hmes) in 
       match newl with 
       |[] => Empty A
       |_ :: _ => CollisionNode A hash newl
       end
   | HashMapEntry _ hash1 key val1 => 
       Empty A
   end.

Fixpoint add (A : Type) (hamt : HAMT A) (k : key) (val : A) (shifter : Z) : HAMT A :=
    match hamt with 
    | ArrayNode _ shift1 map => 
      let index := (of_Z(Z.land (Z.shiftr (hasher2 k) shift1) mask)) in
      let newArr := copy map in 
      let newVal := add A (get map index) k val (shifter + shift) in 
      ArrayNode A shift1 (set map index newVal)
    | Empty _ => 
      HashMapEntry A (hasher2 k) k val
    | CollisionNode _ hash hmes => 
      CollisionNode A hash ((k, val) :: hmes)
    | HashMapEntry _ hash1 key val1 => 
      let index1 := (of_Z(Z.land (Z.shiftr (hasher2 key) shifter) mask)) in 
      let index2 := (of_Z(Z.land (Z.shiftr (hasher2 k) shifter) mask)) in
      let newArr := make 32 (empty_HAMT A) in 
      if (Zeq_bool (to_Z(index1)) (to_Z(index2))) then 
      (ArrayNode A (shifter + shift) (set newArr index1 ((CollisionNode A hash1 ((key, val1) :: (k, val)::[]))))) else
        let newArr1 := set newArr index1 (HashMapEntry A hash1 key val1) in 
        let newArr2 := set newArr index2 (HashMapEntry A (hasher2 k) k val) in
        ArrayNode A (shifter + shift) newArr2 
    end.

(* Correctness Axioms to Prove *)

Axiom get_empty_default : forall (k : key) (A: Type),
      find A (empty_HAMT A) k = None.
      
Axiom get_set_same : forall (A: Type) (k : key) (v : A) (hamt : HAMT A),
      find A (add A hamt k v 0) k = Some v.
       
Axiom get_set_other : forall (A: Type) (k k' : key) (v : A) (hamt : HAMT A),
     not (eq k k') -> find A (add A hamt k v 0) k' = find A hamt k'.

(* Correctness Proof Theorems *)

Theorem get_empty_default1: forall (A: Type) (k : key),
      find A (empty_HAMT A) k = None. 
  Proof.
  intros. unfold find. simpl. reflexivity.
Qed.

Theorem get_set_same': forall (A: Type) (k : key) (v : A) (hamt : HAMT A),
      find A (add A hamt k v 0) k = Some v.
   Proof. Admitted.
   
Theorem get_set_other' : forall (A: Type) (k k' : key) (v : A) (hamt : HAMT A),
not (eq k k') -> find A (add A hamt k v 0) k' = find A hamt k'.
    Proof. Admitted.
    
(* Efficiency Proofs (Next Phase of Work)*)


  
  




