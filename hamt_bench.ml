
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

(** val empty_HAMT : 'a1 hAMT **)

let empty_HAMT =
  Empty

(** val hasher2 : int -> int **)

let hasher2 key0 =
  let hash = Int.mul fMV_prime fMV_offset in
  let hash0 = Int.logxor hash (Int.logand key0 mask1) in
  let hash1 = Int.mul fMV_prime hash0 in
  let hash2 = Int.logxor hash1 (Int.logand key0 mask2) in
  let hash3 = Int.mul fMV_prime hash2 in
  let hash4 = Int.logxor hash3 (Int.logand key0 mask3) in
  let hash5 = Int.mul fMV_prime hash4 in
  Int.logxor hash5 (Int.logand key0 mask4)

(** val findv : (key, 'a1) prod list -> key -> 'a1 option **)

let rec findv hmes k1 =
  match hmes with
  | Nil -> None
  | Cons (p, t) ->
    let Pair (k, v) = p in
    (match Int.equal k k1 with
     | True -> Some v
     | False -> findv t k1)

(** val find : 'a1 hAMT -> key -> 'a1 option **)

let rec find hamt k =
  match hamt with
  | Empty -> None
  | HashMapEntry (_, k1, val0) ->
    (match Int.equal k k1 with
     | True -> Some val0
     | False -> None)
  | ArrayNode (shift0, map) ->
    find
      (Array.get map
        (Int.logand (Int.shift_right (hasher2 k) shift0) mask)) k
  | CollisionNode (_, hmes) -> findv hmes k

(** val remove_ass :
    key -> (key, 'a1) prod list -> (key, 'a1) prod list **)

let rec remove_ass k = function
| Nil -> Nil
| Cons (p, tl) ->
  let Pair (k1, v) = p in
  (match Int.equal k k1 with
   | True -> remove_ass k tl
   | False -> Cons ((Pair (k1, v)), (remove_ass k tl)))

(** val remove : 'a1 hAMT -> key -> 'a1 hAMT **)

let rec remove hamt k =
  match hamt with
  | ArrayNode (shifter, map) ->
    let index = Int.logand (Int.shift_right (hasher2 k) shifter) mask in
    let newVal = remove (Array.get map index) k in
    ArrayNode (shift, (Array.set map index newVal))
  | CollisionNode (hash, hmes) ->
    let newl = remove_ass k hmes in
    (match newl with
     | Nil -> Empty
     | Cons (_, _) -> CollisionNode (hash, newl))
  | _ -> Empty

(** val add : 'a1 hAMT -> key -> 'a1 -> int -> 'a1 hAMT **)

let rec add hamt k val0 shifter =
  match hamt with
  | Empty -> HashMapEntry ((hasher2 k), k, val0)
  | HashMapEntry (hash1, key0, val1) ->
    let index1 = Int.logand (Int.shift_right (hasher2 key0) shifter) mask
    in
    let index2 = Int.logand (Int.shift_right (hasher2 k) shifter) mask in
    let newArr = Array.make (Uint63.of_int (32)) empty_HAMT in
    (match Int.equal index1 index2 with
     | True ->
       ArrayNode ((Int.add shifter shift),
         (Array.set newArr index1 (CollisionNode (hash1, (Cons ((Pair
           (key0, val1)), (Cons ((Pair (k, val0)), Nil))))))))
     | False ->
       let newArr2 =
         Array.set newArr index2 (HashMapEntry ((hasher2 k), k, val0))
       in
       ArrayNode ((Int.add shifter shift), newArr2))
  | ArrayNode (shift1, map) ->
    let index = Int.logand (Int.shift_right (hasher2 k) shift1) mask in
    let newVal = add (Array.get map index) k val0 (Int.add shifter shift)
    in
    ArrayNode (shift1, (Array.set map index newVal))
  | CollisionNode (hash, hmes) ->
    CollisionNode (hash, (Cons ((Pair (k, val0)), hmes)))
