From Calculus.Chapter15 Require Import Prelude.

(* Problem 10: arcsin α + arcsin β = arcsin(α√(1-β²) + β√(1-α²)) *)
Lemma lemma_15_10 : forall α β,
  -1 <= α <= 1 -> -1 <= β <= 1 ->
  α^2 + β^2 <= 1 ->
  arcsin α + arcsin β = arcsin (α * √(1 - β^2) + β * √(1 - α^2)).
Admitted.
