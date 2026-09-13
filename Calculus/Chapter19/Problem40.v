From Calculus.Chapter19 Require Import Prelude.

Lemma lemma_19_40_a : ∀ x, 0 < x -> gamma_value_19 x (gamma_19 x).
Abort.
Lemma lemma_19_40_b : ∀ x, 0 < x -> gamma_19 (x+1) = x*gamma_19 x.
Abort.
Lemma lemma_19_40_c_one : gamma_19 1 = 1.
Abort.
Lemma lemma_19_40_c : ∀ n : nat, (0 < n)%nat -> gamma_19 n = fact (n-1).
Abort.
