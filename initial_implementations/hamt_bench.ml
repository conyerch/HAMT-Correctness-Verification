let fMV_prime = int_of_float 16777619.
let fMV_offset = int_of_float 2166136261.

let mask1 = int_of_float 255.
let mask2 = int_of_float 65280.
let mask3 = int_of_float 16711680.
let mask4 = int_of_float 4278190080.

let mask = int_of_float 31.
let shift = int_of_float 5.

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

(** val empty_HAMT : 'a1 hAMT **)

let empty_HAMT =
  Empty

(** val hasher2 : int -> int **)

let hasher2 key =
  let hash = Int.mul fMV_prime fMV_offset in
  let hash0 = Int.logxor hash (Int.logand key mask1) in
  let hash1 = Int.mul fMV_prime hash0 in
  let hash2 = Int.logxor hash1 (Int.logand key mask2) in
  let hash3 = Int.mul fMV_prime hash2 in
  let hash4 = Int.logxor hash3 (Int.logand key mask3) in
  let hash5 = Int.mul fMV_prime hash4 in
  Int.logxor hash5 (Int.logand key mask4)

(** val findv : (int, 'a1) prod list -> int -> 'a1 option **)

let rec findv hmes k1 =
  match hmes with
  | Nil -> None
  | Cons (p, t) ->
    let Pair (k, v) = p in if Int.equal k k1 then Some v else findv t k1

(** val find : 'a1 hAMT -> int -> 'a1 option **)

let rec find hamt k =
  match hamt with
  | Empty -> None
  | HashMapEntry (_, k1, val0) ->
    if Int.equal k k1 then Some val0 else None
  | ArrayNode (shift0, map) ->
    find
      (Array.get map
        (Int.logand (Int.shift_right (hasher2 k) shift0) mask)) k
  | CollisionNode (_, hmes) -> findv hmes k

(** val remove_ass :
    int -> (int, 'a1) prod list -> (int, 'a1) prod list **)

let rec remove_ass k = function
| Nil -> Nil
| Cons (p, tl) ->
  let Pair (k1, v) = p in
  if Int.equal k k1
  then remove_ass k tl
  else Cons ((Pair (k1, v)), (remove_ass k tl))

(** val remove : 'a1 hAMT -> int -> 'a1 hAMT **)

let rec remove hamt k =
  match hamt with
  | ArrayNode (shifter, map) ->
    let index = Int.logand (Int.shift_right (hasher2 k) shifter) mask in
    let newVal = remove (Array.get map index) k in
    let () = (Array.set map index newVal) in
    ArrayNode (shift, map)
  | CollisionNode (hash, hmes) ->
    let newl = remove_ass k hmes in
    (match newl with
     | Nil -> Empty
     | Cons (_, _) -> CollisionNode (hash, newl))
  | _ -> Empty

(** val add : 'a1 hAMT -> int -> 'a1 -> int -> 'a1 hAMT **)

let rec add hamt k val0 shifter =
  match hamt with
  | Empty -> HashMapEntry ((hasher2 k), k, val0)
  | HashMapEntry (hash1, key, val1) ->
    let index1 = Int.logand (Int.shift_right (hasher2 key) shifter) mask
    in
    let index2 = Int.logand (Int.shift_right (hasher2 k) shifter) mask in
    let newArr = Array.make ((32)) empty_HAMT in
    if Int.equal index1 index2
    then let () = Array.set newArr index1 (CollisionNode (hash1, (Cons ((Pair
    (key, val1)), (Cons ((Pair (k, val0)), Nil)))))) in ArrayNode ((Int.add shifter shift),
           (newArr))
    else let () =
           Array.set newArr index2 (HashMapEntry ((hasher2 k), k, val0))
         in
         ArrayNode ((Int.add shifter shift), newArr)
  | ArrayNode (shift1, map) ->
    let index = Int.logand (Int.shift_right (hasher2 k) shift1) mask in
    let newVal = add (Array.get map index) k val0 (Int.add shifter shift)
    in
    let () = Array.set map index newVal in
    ArrayNode (shift1, (map))
  | CollisionNode (hash, hmes) ->
    CollisionNode (hash, (Cons ((Pair (k, val0)), hmes)))
