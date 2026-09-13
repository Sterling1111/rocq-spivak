From Calculus.Chapter5 Require Import Prelude.

Definition wrong_def_5_26_a (f : R → R) (a l : R) : Prop :=
  ∀ δ, δ > 0 → ∃ ε, ε > 0 /\ ∀ x, 0 < |x - a| < δ → |f x - l| < ε.

Lemma lemma_5_26_a : ∃ (f : R → R) (a l : R),
  wrong_def_5_26_a f a l /\ ¬ (⟦ lim a ⟧ f = l).
Proof.
  exists (λ _, 0), 0, 1. split.
  - intros δ H1. exists 2. split; solve_R.
  - intros H1. pose proof (limit_unique (λ _, 0) 0 1 0 H1 (limit_const 0 0)) as H2.
    lra.
Qed.

Definition wrong_def_5_26_b (f : R → R) (a l : R) : Prop :=
  ∀ ε, ε > 0 → ∃ δ, δ > 0 /\ ∀ x, |f x - l| < ε → 0 < |x - a| < δ.

Lemma lemma_5_26_b : ∃ (f : R → R) (a l : R),
  wrong_def_5_26_b f a l /\ ¬ (⟦ lim a ⟧ f = l).
Proof. Abort.
