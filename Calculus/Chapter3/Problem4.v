From Calculus.Chapter3 Require Export Prelude.

From Lib Require Export Exponential.

Definition S3 (x : R) := x^2.
Definition P3 (x : R) := 2 ^^ x.
Definition s3 : R -> R := sin.

Lemma lemma_3_4_i : ∀ y, (S3 ∘ P3) y = (2 ^^ y)^2.
Proof.
  reflexivity.
Qed.

Lemma lemma_3_4_ii : ∀ y, (S3 ∘ s3) y = (sin y)^2.
Proof.
  reflexivity.
Qed.

Lemma lemma_3_4_iii : ∀ t,
  (S3 ∘ P3 ∘ s3) t + (s3 ∘ P3) t = (2 ^^ (sin t))^2 + sin (2 ^^ t).
Proof.
  reflexivity.
Qed.

Lemma lemma_3_4_iv : ∀ t, s3 (t^3) = sin (t^3).
Proof.
  reflexivity.
Qed.
