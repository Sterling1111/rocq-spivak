From Calculus.Chapter20 Require Import Prelude.

Lemma lemma_20_18 : ∀ n a f,
  nth_differentiable_at (S n) f a ->
  ⟦ lim a ⟧ (λ x, R(n,a,f) x / (x-a)^n) = 0.
Proof.
  intros n a f H1. destruct n as [| n].
  - unfold Taylor_remainder, Taylor_polynomial.
    simpl.
    apply limit_eq with (f1 := λ x, f x - f a).
    + exists 1. split; [lra |]. intros x H2. rewrite sum_f_0_0. simpl. lra.
    + replace 0 with (f a - f a) by lra. apply limit_minus.
      * apply differentiable_at_imp_continuous_at.
        apply nth_differentiable_at_imp_differentiable_at with (n := 1%nat); auto.
      * apply limit_const.
  - apply theorem_20_1; [lia |].
    apply nth_differentiable_at_le with (m := S (S n)); auto; lia.
Qed.
