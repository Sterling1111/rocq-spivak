From Calculus.Chapter20 Require Import Prelude.

Definition exp_quotient x := if Req_EM_T x 0 then 1 else (exp x - 1) / x.

Lemma lemma_20_13_a_polynomial : ∀ n x,
  P(n,0,exp_quotient) x = ∑ 0 n (λ k, x^k / (fact (S k))).
Abort.

Lemma lemma_20_13_a_derivatives : ∀ k,
  ⟦ der ^ k 0 ⟧ exp_quotient = (λ _, 1 / (S k)).
Abort.

Lemma lemma_20_13_a_remainder : ∀ n x,
  |R(n,0,exp_quotient) x| <= exp (Rmax 0 x) * |x|^(S n) / (fact (n+2)).
Abort.

Lemma lemma_20_13_b :
  |(∫ 0 1 exp_quotient) - ∑ 0 6 (λ k, 1 / ((S k) * (fact (S k))))| < / 10^4.
Abort.
