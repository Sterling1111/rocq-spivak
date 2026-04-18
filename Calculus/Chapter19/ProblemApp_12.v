From Calculus.Chapter19 Require Import Prelude.

Lemma lemma_19_App_12_a : forall a b,
  a > 0 -> b > 0 ->
  2 * π * ∫ (-a) a (fun x => b * √(1 - x^2/a^2) * √(1 + (-b*x / (a^2 * √(1 - x^2/a^2)))^2)) > 0.
Abort.

Lemma lemma_19_App_12_b : forall a b,
  a > b -> b > 0 ->
  2 * π * ∫ (-b) b (fun y => (a + √(b^2 - y^2)) * √(1 + (-y / √(b^2 - y^2))^2)) > 0.
Abort.
