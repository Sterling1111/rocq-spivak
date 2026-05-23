From Calculus.Chapter9 Require Import Prelude.

Section section_9_27.

Variable n : ℕ.

Definition S_n x := x^n.

Lemma fact_choose_shift : forall k x,
  (k < n)%nat -> k! * (n ∁ k) * ((n - k) * x ^ (n - k - 1)) = (S k)! * (n ∁ (S k)) * x ^ (n - S k).
Proof.
  intros k x H1.
  replace (n - k - 1)%nat with (n - S k)%nat by lia.
  replace ((S k)! * n ∁ (S k)) with (k! * n ∁ k * ((n - k))); [lra|].
  do 2 (rewrite n_choose_k_def; [|lia]).
  repeat rewrite fact_simpl.
  field_simplify.
  2 : { split. apply INR_fact_neq_0. apply not_0_INR. pose proof fact_neq_0 k. lia. }
  2 : { split; apply INR_fact_neq_0. }
  replace (INR ((n - k)!)) with ((INR n - INR k) * INR ((n - S k)!)).
  2 : {
    rewrite <- minus_INR; [| lia].
    replace (n - k)%nat with (S (n - S k))%nat at 2 by lia.
    replace (fact (S (n - S k))) with (S (n - S k) * fact (n - S k))%nat by reflexivity.
    rewrite mult_INR; do 2 f_equal; lia.
  }
  field.
  split; [apply INR_fact_neq_0 | solve_R].
Qed.

Lemma lemma_9_27 : forall k,
  (0 <= k <= n)%nat -> ⟦ der ^ k ⟧ (S_n) = (fun x => k! * (n ∁ k) * x ^ (n - k)).
Proof.
  intros k H1. induction k as [| k IH].
  - simpl. rewrite n_choose_0. extensionality x. rewrite Nat.sub_0_r. unfold S_n. lra.
  - exists (fun x : R => k! * n ∁ k * x ^ (n - k)).
    split.
    + apply IH; lia.
    + apply derivative_ext with (f1' := fun x => k! * n ∁ k * ((n - k)%nat * x ^ (n - k - 1))).
      { intros x. rewrite <- fact_choose_shift; solve_R. }
      apply derivative_mult_const_l.
      apply derivative_pow.
Qed.

End section_9_27.