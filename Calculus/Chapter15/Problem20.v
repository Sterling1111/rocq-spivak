From Calculus.Chapter15 Require Import Prelude.

(* Problem 20: lim_{x->∞} x sin(1/x) = 1 *)
Lemma lemma_15_20 :
  ⟦ lim ∞ ⟧ (fun x => x * sin (1 / x)) = 1.
Abort.
