From Calculus.Chapter18 Require Import Prelude.

Lemma problem_18_37 : ∀ f,
  ⟦ der ⟧ f = f ->
  (∀ x y, f (x + y)= f x * f y) ->
  f = exp \/ f = λ _, 0.
Proof.
  
Abort.