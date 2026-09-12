From Calculus.Chapter20 Require Import Prelude.

Lemma lemma_20_16 : ∀ n x, -1 < x <= 0 ->
  |R(n,0,λ y, log (1+y)) x| <= |x|^(S n) / ((1+x) * (S n)).
Abort.
