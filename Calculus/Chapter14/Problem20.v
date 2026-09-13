From Calculus.Chapter14 Require Import Prelude.

Definition f_20 (x : R) : R :=
  match Req_dec_T x 0 with left _ => 0 | right _ => cos (1 / x) end.

Lemma lemma_14_20 :
  differentiable_at (λ x, ∫ 0 x f_20) 0.
Abort.
