From Calculus.Chapter22 Require Import Prelude.

Lemma lemma_22_20 : ∀ f x L,
  continuous f ->
  (∃ b, b 0%nat = x /\ (∀ n, b (S n) = f (b n)) /\ ⟦ lim ⟧ b = L) ->
  f L = L.
Proof.
  intros f x L H1 [b [H2 [H3 H4]]].
  apply limit_of_sequence_unique with (a := λ n, f (b n)).
  - intros ε H5. destruct (H1 L ε H5) as [δ [H6 H7]].
    destruct (H4 δ H6) as [N H8]. exists N. intros n H9.
    destruct (Req_dec (b n) L) as [H10 | H10].
    + rewrite H10. solve_R.
    + apply H7. specialize (H8 n H9). solve_R.
  - intros ε H5. destruct (H4 ε H5) as [N H6].
    exists N. intros n H7. rewrite <- H3. apply H6. rewrite S_INR. lra.
Qed.
