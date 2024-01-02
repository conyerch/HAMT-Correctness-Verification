
(** val hasher2 : int -> int **)
let fMV_prime = int_of_float 16777619.
let fMV_offset = int_of_float 2166136261.

let mask1 = int_of_float 255.
let mask2 = int_of_float 65280.
let mask3 = int_of_float 16711680.
let mask4 = int_of_float 4278190080.

let hasher2 key =
  let hash = Int.mul fMV_prime fMV_offset in
  let hash0 = Int.logxor hash (Int.logand key mask1) in
  let hash1 = Int.mul fMV_prime hash0 in
  let hash2 = Int.logxor hash1 (Int.logand key mask2) in
  let hash3 = Int.mul fMV_prime hash2 in
  let hash4 = Int.logxor hash3 (Int.logand key mask3) in
  let hash5 = Int.mul fMV_prime hash4 in
  Int.logxor hash5 (Int.logand key mask4)
