From Calculus.Chapter20 Require Import Prelude.

Lemma lemma_20_15 : ∀ n x, x <= 0 ->
  |R(n,0,exp) x| <= |x|^(S n) / (fact (S n)).
Abort.
