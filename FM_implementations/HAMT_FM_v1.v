Require Import Coq.Arith.EqNat.
Require Import Lia.
Require Import Coq.Strings.String.
Require Import List.
Import ListNotations.

Module Type FiniteMapHash.

Parameter finiteMapHash : Type.

Parameter K : Type.

Parameter V : Type.

Parameter H : Type.

Parameter default : V.

Parameter hash : K -> H.

Parameter eq : K -> K -> bool. 

Parameter finiteMap : K -> H -> V. 

Parameter empty : finiteMapHash.

Parameter get : K -> finiteMapHash -> V.

Parameter set : K -> V -> finiteMapHash -> finiteMapHash.

Axiom get_empty_default : forall (k : K),
      get k empty = default.
  Axiom get_set_same : forall (k : K) (v : V) (t : finiteMapHash),
      get k (set k v t) = v.
  Axiom get_set_other : forall (k k' : K) (v : V) (t : finiteMapHash),
      k <> k' -> get k' (set k v t) = get k' t.
End FiniteMapHash.

Module Type LayeredMap.

Parameter layeredMap : Type.

Parameter K1 : Type.

Parameter K2 : Type.

Parameter V : Type.

Parameter default : V.

Parameter finiteMap1 : K2 -> V. 

Parameter finiteMap2 : K1 -> (K2 -> V). 

Parameter empty : layeredMap.

Parameter get : K1 -> K2 -> layeredMap -> V.

Parameter set : K1 -> K2 -> V -> layeredMap -> layeredMap.

  Axiom get_empty_default : forall (k1 : K1) (k2 : K2),
      get k1 k2 empty = default.
  Axiom get_set_same : forall (k1 : K1) (k2 : K2) (v : V) (t : layeredMap),
      get k1 k2 (set k1 k2 v t) = v.
  Axiom get_set_other : forall (k1 k1': K1) (k2 k2': K2) (v : V) (t : layeredMap),
      k1 <> k1' -> get k1' k2' (set k1 k2 v t) = get k1' k2' t.
End LayeredMap.





Module Type ValType.
    Parameter V : Type.
    Parameter K : Type. 
    Parameter K2 : Type. 
    Parameter H : Type. 
    Parameter default : V.
    Parameter hash : K -> H. 
    Parameter map : K -> H -> V. 
    Parameter map2 : K2 -> (K -> V). 
    Parameter eq: K -> K -> bool. 
  End ValType.

Module HashMapF (VT : ValType) <: FiniteMapHash.
  Definition V := VT.V.
  Definition default := VT.default.
  Definition K := VT.K.
  Definition H := VT.H.
  Definition hash := VT.hash.
  Definition finiteMap := VT.map.
  Definition finiteMapHash := K -> V.
  Definition eq := VT.eq. 
  Definition empty : finiteMapHash :=
    fun _ => default.

  Definition get (k : K) (f : finiteMapHash) : V :=
    f k.

  Definition set (k : K) (v : V) (f : finiteMapHash): finiteMapHash :=
    fun k' => 
    let h := hash k in 
    if eq k' k then v else finiteMap k' h.

  Axiom eq_refl : forall (k : K), eq k k = true. 

  Axiom eq_not : forall (k k1: K), k1 <> k -> eq k k1 = false. 

  Theorem get_empty_default : forall (k : K),
    get k empty = default.
  Proof.
    intros. simpl. unfold get. simpl. unfold empty. reflexivity.
    Qed.        
  Theorem get_set_same : forall (k : K) (v : V) (t : finiteMapHash),
    get k (set k v t) = v.
  Proof. intros. simpl. unfold set. unfold get. simpl. rewrite -> eq_refl. reflexivity.     
  Qed. 
  Theorem get_set_other : forall (k k' : K) (v : V) (t : finiteMapHash),
    k <> k' -> get k' (set k v t) = get k' t. 
    Proof. intros. unfold set. unfold get. rewrite -> eq_not.
    - simpl. admit.
    - apply H0.
    Admitted.
End HashMapF. 

(*The main abstract data type takes types K1 K2 V and two finite maps as arguments,
one of type K1->(finite map K2->V) and one of type K2->V, 
and is itself a finite map (K1,K2)->V. To look up the key (k1,k2) 
it looks up k1 in the first finite map. If it returns something, 
it returns a finite map K2->V, in which case it looks up k2 in that finite map.*)

Module HM2 (VT : ValType) <: LayeredMap.
  Definition V := VT.V.
  Definition default := VT.default.
  Definition K := VT.K.
  Definition K2 := VT.K2. 
  Definition H := VT.H.
  Definition hash := VT.hash.
  Definition finiteMap1 := VT.map.
  Definition finiteMap2 := VT.map2. 
  Definition layeredMap := K -> K2 -> V. 
  Definition empty : layeredMap :=
    fun _ _ => default.


