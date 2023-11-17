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
    Parameter H : Type. 
    Parameter default : V.
    Parameter hash : K -> H. 
    Parameter map : K -> H -> V. 
  End ValType.

Module HashMapF (VT : ValType) <: FiniteMapHash.
  Definition V := VT.V.
  Definition default := VT.default.
  Definition K := VT.K.
  Definition H := VT.H.
  Definition hash := VT.hash.
  Definition finiteMap := VT.map.
  Definition finiteMapHash := K -> V.
  Definition empty : finiteMapHash :=
    fun _ => default.

  Definition get (k : K) : V :=
    finiteMap k (hash k).

  Definition set (k : K) (v : V) : finiteMapHash :=
    let h := hash k in 
    fun k => finiteMap k (hash k).
End HashMapF. 


