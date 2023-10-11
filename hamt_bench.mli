
type bool =
| True
| False

type 'a option =
| Some of 'a
| None

type ('a, 'b) prod =
| Pair of 'a * 'b

type 'a list =
| Nil
| Cons of 'a * 'a list

type 'a hAMT =
| Empty
| HashMapEntry of int * key * 'a
| ArrayNode of int * 'a hAMT 'a Parray.t
| CollisionNode of int * (key, 'a) prod list

val empty_HAMT : 'a1 hAMT

val hasher2 : int -> int

val findv : (key, 'a1) prod list -> key -> 'a1 option

val find : 'a1 hAMT -> key -> 'a1 option

val remove_ass : key -> (key, 'a1) prod list -> (key, 'a1) prod list

val remove : 'a1 hAMT -> key -> 'a1 hAMT

val add : 'a1 hAMT -> key -> 'a1 -> int -> 'a1 hAMT
