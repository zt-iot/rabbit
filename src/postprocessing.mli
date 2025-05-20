(** Post-processing module for Rabbit models
    This module provides functions to optimize and transform Rabbit models before
    they are processed by the verification backends (Tamarin and ProVerif). *)

(** Type representing errors that can occur during post-processing *)
type postprocessing_error =
  | UnintendedError of string
  | ConflictingCondition' (** Error when there are conflicting conditions in the model *)

(** Exception raised when a post-processing error occurs *)
exception Error of postprocessing_error

(** Print a human-readable description of a post-processing error
    @param err The error to print
    @param ppf The formatter to print to *)
val print_error : postprocessing_error -> Format.formatter -> unit

(** Optimize a Rabbit model by:
    - Unifying variables where possible
    - Removing redundant transitions
    - Simplifying conditions
    - Ensuring well-formedness of the model
    @param model The input Totamarin model to optimize
    @return The optimized Totamarin model *)
val optimize : Totamarin.model -> Totamarin.model
