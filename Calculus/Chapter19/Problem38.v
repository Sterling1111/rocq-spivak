From Calculus.Chapter19 Require Import Prelude.

Lemma lemma_19_38_a : improper_left_19 0 1 log (-1).
Abort.

Lemma lemma_19_38_b : ∃ L, improper_both_19 0 π (λ x, log (sin x)) L.
Abort.

Lemma lemma_19_38_c : ∀ I J K,
  improper_both_19 0 π (λ x, log (sin x)) I ->
  improper_left_19 0 (π/2) (λ x, log (sin x)) J ->
  improper_right_19 0 (π/2) (λ x, log (cos x)) K ->
  I = 2*J + 2*K + π*log 2.
Abort.

Lemma lemma_19_38_d : improper_right_19 0 (π/2) (λ x, log (cos x)) (-π*log 2/2).
Abort.

Lemma lemma_19_38_e :
  improper_left_19 0 (π/2) (λ x, log (sin x)) (-π*log 2/2) /\
  improper_both_19 0 π (λ x, log (sin x)) (-π*log 2).
Abort.
