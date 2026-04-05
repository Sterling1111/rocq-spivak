From Calculus.Chapter19 Require Import Prelude.

Lemma lemma_19_43 : forall a b,
  0 < a -> a < b ->
  ∫ a b (fun x => sin x / x) = cos a / a - cos b / b - ∫ a b (fun x => cos x / x^2).
Admitted.
