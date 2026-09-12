From Calculus.Chapter20 Require Import Prelude.

Definition sinc x := if Req_EM_T x 0 then 1 else sin x / x.

Lemma lemma_20_12_polynomial : ∀ n x,
  P(2*n,0,sinc) x = ∑ 0 n (λ k, (-1)^k * x^(2*k) / (fact (2*k+1))).
Abort.
Lemma lemma_20_12_remainder : ∀ n x,
  |R(2*n,0,sinc) x| <= |x|^(2*n+1) / (fact (2*n+2)).
Abort.
Lemma lemma_20_12_integral : |(∫ 0 1 sinc) - 1703/1800| < / 10^3.
Abort.
