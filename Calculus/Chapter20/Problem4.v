From Calculus.Chapter20 Require Import Prelude.

Lemma lemma_20_4_i :
  |sin 1 - ∑ 0 (10^10) (λ k, (-1)^k / (fact (2*k+1)))| < / 10^(10^10).
Abort.

Lemma lemma_20_4_ii :
  |e - ∑ 0 10000 (λ k, / (fact k))| < / 10^1000.
Abort.

Lemma lemma_20_4_iii :
  |sin 10 - ∑ 0 40 (λ k, (-1)^k * 10^(2*k+1) / (fact (2*k+1)))| < / 10^20.
Abort.

Lemma lemma_20_4_iv :
  |exp 10 - ∑ 0 120 (λ k, 10^k / (fact k))| < / 10^30.
Abort.

Lemma lemma_20_4_v :
  |arctan (1/10) - ∑ 0 (10^10) (λ k, (-1)^k * (1/10)^(2*k+1) / (2*k+1))|
    < / 10^(10^10).
Abort.
