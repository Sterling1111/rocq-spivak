From Calculus.Chapter19 Require Import Prelude.

Lemma lemma_19_45 : forall x,
  x > 0 ->
  ∫ 0 ∞ (fun t => exp (-t) * t^(x - 1)) = 1 / x * ∫ 0 ∞ (fun u => exp (-u^(1/x))).
Admitted.
