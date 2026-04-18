From Calculus.Chapter21 Require Import Prelude.

(* Problem 6: Since so many sets turn out to be countable, it is important to note
   that the set of all real numbers between 0 and 1 is not countable. *)

Lemma lemma_21_6 :
  ~ countable (fun x : R => 0 < x < 1).
Abort.
