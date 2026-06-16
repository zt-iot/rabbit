(* String helper functions *)

(* [equal_substring s1 n1 s2 n2 len] returns true when
   the substring of [s1] starting at position [n1] of length [len]
   is equal to the substring of [s2] starting at position [n2] 
   of length [len].
   Assumes that [n1 >= 0, n2 >= 0, len >= 0],
   the length of [s1] is at least [n1+len]
   and the length of [s2] is at least [n2+len]. *)

let rec equal_substring s1 n1 s2 n2 len =
  (len == 0) ||
  ((s1.[n1] == s2.[n2]) && equal_substring s1 (n1+1) s2 (n2+1) (len-1))

(* [starts_with s sub] is true when the string [s] starts with
   [sub]. *)
	
let starts_with s sub =
  let len = String.length sub in
  (String.length s >= len) &&
  (equal_substring s 0 sub 0 len)

(* [ends_with s sub] is true when the string [s] ends with
   [sub]. *)
	
let ends_with s sub =
  let l_s = String.length s in
  let l_sub = String.length sub in
  (l_s >= l_sub) && (equal_substring s (l_s - l_sub) sub 0 l_sub)

(* [contains_from s sub n] is true when the substring of [s]
   starting at position [n] contains [sub] *)
    
let rec contains_from s sub n =
  let l_sub = String.length sub in
  (l_sub + n <= String.length s) &&
  ((equal_substring s n sub 0 l_sub) || contains_from s sub (n+1))

(* [contains s sub] is true when [s] contains [sub] *)
    
let contains s sub =
  contains_from s sub 0

(* [pos_from s sub n] returns [Some n'] when the substring of [s]
   starting at position [n] contains [sub] at position [n'], 
   and [None] when the substring of [s] starting at position [n] 
   does not contain [sub]. *)
    
let rec pos_from s sub n =
  let l_sub = String.length sub in
  if l_sub + n > String.length s then
    None
  else if equal_substring s n sub 0 l_sub then
    Some n
  else
    pos_from s sub (n+1)

(* [pos s sub] returns [Some n'] when [s] contains [sub] at 
   position [n'], and [None] when [s] does not contain [sub]. *)

let pos s sub =
  pos_from s sub 0

(* [case_insensitive_equal_substring s1 n1 s2 n2 len] returns true when
   the substring of [s1] starting at position [n1] of length [len]
   is equal to the substring of [s2] starting at position [n2] 
   of length [len]. Comparison is case insensitive.
   Assumes that [n1 >= 0, n2 >= 0, len >= 0],
   the length of [s1] is at least [n1+len]
   and the length of [s2] is at least [n2+len]. *)

let rec case_insensitive_equal_substring s1 n1 s2 n2 len =
  (len == 0) ||
  ((Char.lowercase_ascii s1.[n1] == Char.lowercase_ascii s2.[n2]) &&
   case_insensitive_equal_substring s1 (n1+1) s2 (n2+1) (len-1))

(* [case_insensitive_ends_with s sub] is true when the string [s] ends with
   [sub]. Comparison is case insensitive. *)
	
let case_insensitive_ends_with s sub =
  let l_s = String.length s in
  let l_sub = String.length sub in
  (l_s >= l_sub) &&
  (case_insensitive_equal_substring s (l_s - l_sub) sub 0 l_sub)

(* [case_insensitive_contains_from s sub n] is true when the substring of [s]
   starting at position [n] contains [sub]. Comparison is case insensitive. *)
    
let rec case_insensitive_contains_from s sub n =
  let l_sub = String.length sub in
  (l_sub + n <= String.length s) &&
  ((case_insensitive_equal_substring s n sub 0 l_sub) ||
  case_insensitive_contains_from s sub (n+1))

(* [case_insensitive_contains s sub] is true when [s] contains [sub]. 
   Comparison is case insensitive. *)
    
let case_insensitive_contains s sub =
  case_insensitive_contains_from s sub 0
