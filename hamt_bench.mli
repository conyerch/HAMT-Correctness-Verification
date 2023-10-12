
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
| HashMapEntry of int * int * 'a
| ArrayNode of int * 'a hAMT Array.t
| CollisionNode of int * (int, 'a) prod list

val empty_HAMT : 'a1 hAMT

val hasher2 : int -> int

val findv : (int, 'a1) prod list -> int -> 'a1 option

val find : 'a1 hAMT -> int -> 'a1 option

val remove_ass : int -> (int, 'a1) prod list -> (int, 'a1) prod list

val remove : 'a1 hAMT -> int -> 'a1 hAMT

val add : 'a1 hAMT -> int -> 'a1 -> int -> 'a1 hAMT
