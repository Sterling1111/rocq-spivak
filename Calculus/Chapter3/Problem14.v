From Calculus.Chapter3 Require Export Prelude.

Lemma lemma_3_14_max : ∀ (f g : R -> R) x,
  Rmax (f x) (g x) = (f x + g x + |f x - g x|) / 2.
Proof.
  intros f g x. solve_R.
Qed.

Lemma lemma_3_14_min : ∀ (f g : R -> R) x,
  Rmin (f x) (g x) = (f x + g x - |f x - g x|) / 2.
Proof.
  intros f g x. solve_R.
Qed.
