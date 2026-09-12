From Calculus.Chapter20 Require Import Prelude.

Lemma lemma_20_3_i :
  |sin 1 - ∑ 0 9 (λ k, (-1)^k / (fact (2*k+1)))| < / 10^17.
Abort.

Lemma lemma_20_3_ii :
  |sin 2 - ∑ 0 9 (λ k, (-1)^k * 2^(2*k+1) / (fact (2*k+1)))| < / 10^12.
Abort.

Lemma lemma_20_3_iii :
  |sin (1/2) - ∑ 0 8 (λ k, (-1)^k * (1/2)^(2*k+1) / (fact (2*k+1)))| < / 10^20.
Abort.

Lemma lemma_20_3_iv :
  |e - ∑ 0 8 (λ k, / (fact k))| < / 10^4.
Abort.

Lemma lemma_20_3_v :
  |exp 2 - ∑ 0 14 (λ k, 2^k / (fact k))| < / 10^5.
Abort.
