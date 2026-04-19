From Calculus.Chapter18 Require Import Prelude.

(* Problem 13: Find
   (a) \lim_{x \to \infty} a^x for 0 < a < 1. (Remember the definition!)
   ...
   (e) \lim_{x \to 0^+} x^x. *)
Lemma problem_18_13_e : ⟦ lim 0⁺ ⟧ (fun x => exp (x * log x)) = 1. Abort.
