From Calculus.Chapter12 Require Import Prelude.

Lemma lemma_12_4_a : ∀ f g,
  increasing f ->
  increasing g ->
  increasing (λ x, f x + g x).
Proof.
  intros f g H1 H2 x y H3 H4 H5.
  specialize (H1 x y H3 H4 H5).
  specialize (H2 x y H3 H4 H5).
  lra.
Qed.

Lemma lemma_12_4_b : ∀ f g,
  increasing f ->
  increasing g ->
  increasing (f ∘ g).
Proof.
  intros f g H1 H2 x y H3 H4 H5.
  apply H1; auto; apply Full_intro.
Qed.