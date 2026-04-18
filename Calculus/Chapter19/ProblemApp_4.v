From Calculus.Chapter19 Require Import Prelude.

Lemma lemma_19_App_4 : forall a b,
  a > b -> b > 0 ->
  ∫ (-b) b (fun y => π * ((a + √(b^2 - y^2))^2 - (a - √(b^2 - y^2))^2)) = 2 * π^2 * a * b^2.
Abort.
