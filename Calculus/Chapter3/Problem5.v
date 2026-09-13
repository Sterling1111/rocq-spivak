From Calculus.Chapter3 Require Export Prelude.

From Calculus.Chapter3 Require Import Problem4.

Lemma lemma_3_5_i : (λ x, 2 ^^ (sin x)) = (P3 ∘ s3).
Proof.
  reflexivity.
Qed.

Lemma lemma_3_5_ii : (λ x, sin (2 ^^ x)) = (s3 ∘ P3).
Proof.
  reflexivity.
Qed.

Lemma lemma_3_5_iii : (λ x, sin (x^2)) = (s3 ∘ S3).
Proof.
  reflexivity.
Qed.

Lemma lemma_3_5_iv : (λ x, (sin x)^2) = (S3 ∘ s3).
Proof.
  reflexivity.
Qed.

Lemma lemma_3_5_v : (λ t, 2 ^^ (2 ^^ t)) = (P3 ∘ P3).
Proof.
  reflexivity.
Qed.

Lemma lemma_3_5_vi : (λ u, sin (2 ^^ u + 2 ^^ (u^2))) =
  (s3 ∘ (P3 + (P3 ∘ S3)))%function.
Proof.
  reflexivity.
Qed.

Lemma lemma_3_5_vii :
  (λ y, sin (sin (sin (2 ^^ (2 ^^ (2 ^^ (sin y))))))) =
  (s3 ∘ s3 ∘ s3 ∘ P3 ∘ P3 ∘ P3 ∘ s3).
Proof.
  reflexivity.
Qed.

Lemma lemma_3_5_viii :
  (λ a, 2 ^^ ((sin a)^2) + sin (a^2) + 2 ^^ (sin (a^2 + sin a))) =
  (((P3 ∘ S3 ∘ s3) + (s3 ∘ S3))%function +
    (P3 ∘ s3 ∘ (S3 + s3)%function))%function.
Proof.
  reflexivity.
Qed.
