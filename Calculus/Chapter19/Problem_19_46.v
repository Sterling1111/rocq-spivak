From Calculus.Chapter19 Require Import Prelude.

Lemma lemma_19_46 : forall f A B alpha beta,
  (forall a b, 0 < a -> a < b -> integrable_on a b (fun x => f x / x)) ->
  limit_at_point f 0 A ->
  limit_at_infinity f B ->
  alpha > 0 -> beta > 0 ->
  ∫ 0 ∞ (fun x => (f (alpha * x) - f (beta * x)) / x) = (A - B) * log (beta / alpha).
Admitted.
