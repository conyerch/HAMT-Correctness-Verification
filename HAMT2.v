(* HAMT Implementation using Coq native 63 bit int instead of Z's*)

(* Notation *)
(* These are just declaring to Coq common notation I will be using throughout the project *)

Notation "( x , y )" := (pair x y).
Notation "X * Y" := (prod X Y) : type_scope.
Infix "::" := cons (at level 60, right associativity) : list_scope.
Notation "x :: l" := (cons x l)
                     (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..).
Definition mylist := 1 :: (2 :: (3 :: nil)).

(* Imports *)
(* Common modules I will be using throughout the implementation *)

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

(* Function that takes two natural numbers and returns a boolean describing their equality *)
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

(* keys are defined as nats in this implementation *)
Definition key := int.
(* shift value used for indexing into the arrays using bits of the hash *)
Definition shift : int := 5. 
(* mask out everything but the first 5 bits *)
Definition mask : int := 31.
(* Following two numbers are used for the hashing function, taken from the Fowler–Noll–Vo 32 bit hash function *)
Definition FMV_prime : int := 16777619.
Definition FMV_offset : int := 2166136261.

(* HAMT Module *)

Module HAMT.

(* Inductively define HAMT as an empty node, a hashmap entry which hols a key val pair, collision node if 
two keys hash to the same integer, and array node that holds more HAMT's *)
(* Takes a type that is the type of the value *)
Inductive HAMT (A : Type) : Type :=
  | Empty
  | HashMapEntry (hash : int) (k : key) (val : A)
  | ArrayNode (shift : int) (map : array (HAMT A))
  | CollisionNode (hash : int) (hmes : list (key * A)).
  
(* Function that takes a value type and returns an Empty HAMT of that type *)
Definition empty_HAMT (A:Type) : HAMT A :=
    Empty A.

(* hash function that copies the Fowler-Noll-Vo hash function *)
Definition hasher2 (key : int) : int := 
        let hash := FMV_offset in
        let int_initial := key in 
        let hash := Uint63.mul FMV_prime hash in 
        let hash := Uint63.lxor hash (Uint63.land int_initial 255) in
        let hash := Uint63.mul FMV_prime hash in 
        let hash := Uint63.lxor hash (Uint63.land int_initial 65280) in
        let hash := Uint63.mul FMV_prime hash in 
        let hash := Uint63.lxor hash (Uint63.land int_initial 16711680) in
        let hash := Uint63.mul FMV_prime hash in 
        let hash := Uint63.lxor hash (Uint63.land int_initial 4278190080) in
        hash. 

(* iterates through list of key value pairs and returns an option, used as a helper function for find *)
Fixpoint findv (A : Type) (hmes : list (key * A)) (k1 : key) :=
  match hmes with 
  |[] => None
  |(k, v) :: t => 
    if (Uint63.eqb k k1) then Some v else findv A t k1
  end.

(* Funnction that takes a type, hamt, key, and returns the value associated with that key if it is in the HAMT *)
Fixpoint find (A : Type) (hamt : HAMT A) (k : key) : option A :=
  match hamt with 
  |HashMapEntry _ hash k1 val  => 
      if Uint63.eqb k k1 then Some val else None
  | ArrayNode _ shift map => 
      (* if the HAMT is an array node, need to use the hashed key to index into the array, at the correct depth *)
      find A (get map (Uint63.land (lsr (hasher2 k) shift) mask)) k
  | CollisionNode _ hash hmes => 
      (* call helper function *)
      findv A hmes k
  | Empty _ => 
      None
  end.

(* helper function for the remove function, iterates through collisionNode list and removes key val pair *)
Fixpoint remove_ass (A : Type) (k : key) (l : list (key * A)) : list (key * A) :=
    match l with
    | nil => nil
    | (k1, v) :: tl => if (Uint63.eqb k k1) then remove_ass A k tl else (k1, v) :: (remove_ass A k tl)
    end.
    
(* Function that takes a hamt and removes a key val pair, returning an empty HAMT in place of the hash map entry *)
Fixpoint remove (A : Type) (hamt : HAMT A) (k : key) : HAMT A :=
   match hamt with 
   (* if the hamt is an ArrayNode, we need to index into the array using the hashed key and recursively call remove *)
   | ArrayNode _ shifter map => 
     let index := (Uint63.land (lsr (hasher2 k) shifter) mask) in 
     let newArr := copy map in 
     let newVal := remove A (get map index) k in 
     ArrayNode A shift (set map index newVal)
   | Empty _ => 
      (* if we reach an Empty hash, we know the key is not in the hash and we can just return an empty hamt *)
       Empty A
   | CollisionNode _ hash hmes => 
       (* if we reach a collision node, send the list to the helper function *)
       let newl := (remove_ass A k hmes) in 
       match newl with 
       |[] => Empty A
       |_ :: _ => CollisionNode A hash newl
       end
   | HashMapEntry _ hash1 key val1 => 
       (* if we find the entry, return an empty hash in its place *)
       Empty A
   end.

(* function to add a key val pair to the hamt *)
Fixpoint add (A : Type) (hamt : HAMT A) (k : key) (val : A) (shifter : int) : HAMT A :=
    match hamt with 
    | ArrayNode _ shift1 map => 
      (* if we find an ArrayNode, we need to index into that array using the hashed key, and recursively call add *)
      let index := (Uint63.land (lsr (hasher2 k) shift1) mask) in
      let newArr := copy map in 
      let newVal := add A (get map index) k val (shifter + shift) in 
      ArrayNode A shift1 (set map index newVal)
    | Empty _ => 
      (* once we find an empty hamt, we can insert a hashmapentry holding the key val pair *)
      HashMapEntry A (hasher2 k) k val
    | CollisionNode _ hash hmes => 
      (* if we have already had a collision at this hash, add to the collision list the key val pair *)
      CollisionNode A hash ((k, val) :: hmes)
    | HashMapEntry _ hash1 key val1 => 
      (* if we collide with another hash, then get the index of each key, test to see if they are equal (if so make a 
      collision node), and then create an ArrayNode holding each hashmapentry *)
      let index1 := (Uint63.land (lsr (hasher2 key) shifter) mask) in 
      let index2 := (Uint63.land (lsr (hasher2 k) shifter) mask) in
      let newArr := make 32 (empty_HAMT A) in 
      if (Uint63.eqb index1 index2) then 
      (ArrayNode A (shifter + shift) (set newArr index1 ((CollisionNode A hash1 ((key, val1) :: (k, val)::[]))))) else
        let newArr1 := set newArr index1 (HashMapEntry A hash1 key val1) in 
        let newArr2 := set newArr index2 (HashMapEntry A (hasher2 k) k val) in
        ArrayNode A (shifter + shift) newArr2 
    end.

(* Correctness Axioms to Prove *)

(* axiom stating that a find command on any key for an empty hamt returns non *)
Axiom get_empty_default : forall (k : key) (A: Type),
      find A (empty_HAMT A) k = None.

(* axiom stating that a hamt always returns the key that has been added to the structure *)
Axiom get_set_same : forall (A: Type) (k : key) (v : A) (hamt : HAMT A),
      find A (add A hamt k v 0) k = Some v.
       
(* axiom stating that if two keys are not the same, adding one key doesn't disrupt the finding of another key *)
Axiom get_set_other : forall (A: Type) (k k' : key) (v : A) (hamt : HAMT A),
     not (eq k k') -> find A (add A hamt k v 0) k' = find A hamt k'.

(* Correctness Proof Theorems *)

(* completed theorem resolving axiom 1 *)
Theorem get_empty_default1: forall (A: Type) (k : key),
      find A (empty_HAMT A) k = None. 
  Proof.
  intros. unfold find. simpl. reflexivity.
Qed.

(* Incomplete theorem for axiom 2 *)
Theorem get_set_same': forall (A: Type) (k : key) (v : A) (hamt : HAMT A),
      find A (add A hamt k v 0) k = Some v.
   Proof. Admitted.
   
(* Incomplete theorem for axiom 3 *)
Theorem get_set_other' : forall (A: Type) (k k' : key) (v : A) (hamt : HAMT A),
not (eq k k') -> find A (add A hamt k v 0) k' = find A hamt k'.
    Proof. Admitted.
    
(* Efficiency Proofs (Next Phase of Work)*)

(* Extraction for Benchmarking *)

Require Coq.extraction.Extraction.
Extraction Language OCaml.

Extract Inlined Constant int => "int".
Extract Inlined Constant Uint63.land => "Int.logand".
Extract Inlined Constant Uint63.lxor => "Int.logxor".
Extract Inlined Constant Uint63.mul => "Int.mul".

(* Extract hashing function and dependencies *)
Extraction "hamt_int_hash" hasher2 FMV_offset FMV_prime mask. 

(* Extract hamt data structure and dependencies *)
Extraction "hamt_bench" HAMT add remove find hasher2 empty_HAMT. 


  
  




