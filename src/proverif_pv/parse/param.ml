let allow_tilde = ref false
let has_integer = ref false
let has_choice = ref false
let has_barrier = ref false

let reset () =
  allow_tilde := false;
  has_integer := false;
  has_choice := false;
  has_barrier := false
