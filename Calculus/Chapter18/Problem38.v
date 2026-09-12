From Calculus.Chapter18 Require Import Prelude.

Lemma lemma_18_38 : ∀ f,
  continuous f -> (∀ x y, f (x+y) = f x * f y) ->
  f = (λ _, 0) \/ (f 1 > 0 /\ ∀ x, f x = (f 1) ^^ x).
Abort.
