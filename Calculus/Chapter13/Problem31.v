From Calculus.Chapter13 Require Import Prelude.

Lemma lemma_13_31_a : ∀ a b,
  a < b -> ∃ f : R -> R,
  integrable_on a b f /\ nonnegative_on f [a, b] /\
  (∃ x, x ∈ [a, b] /\ 0 < f x) /\ ∫ a b f = 0.
Abort.

Lemma lemma_13_31_b : ∀ f a b x0,
  a < b ->
  integrable_on a b f ->
  (∀ x, x ∈ [a, b] -> f x >= 0) ->
  ⟦ lim x0 ⟧ f [a, b] = f x0 ->
  x0 ∈ [a, b] ->
  f x0 > 0 ->
  ∫ a b f > 0.
Proof.
  intros f a b x0 H1 H2 H3 H4 H5 H6.
  destruct (H4 (f x0/2) ltac:(lra)) as [δ [H7 H8]].
  set (u := Rmax a (x0-δ/2)).
  set (v := Rmin b (x0+δ/2)).
  assert (H9 : a <= u < v /\ v <= b) by (unfold u, v; solve_R).
  assert (H10 : ∀ x, x ∈ [u, v] -> f x0/2 <= f x).
  {
    intros x H10. destruct (Req_dec x x0) as [H11 | H11]; [subst; lra |].
    specialize (H8 x ltac:(solve_R) ltac:(unfold u, v in H10; solve_R)). solve_R.
  }
  pose proof integrable_imp_bounded f a b ltac:(lra) H2 as [_ [M H11]].
  assert (H12 : integrable_on u v f).
  { apply integrable_on_sub_interval with (a := a) (b := b); auto; lra. }
  pose proof theorem_13_7 u v f (f x0/2) M ltac:(lra) H12
    ltac:(intros x H13; split; [apply H10; auto | apply H11; exists x; split; [solve_R | reflexivity]])
    as H13.
  assert (H14 : 0 < ∫ u v f).
  { assert (0 < (f x0/2)*(v-u)) by (apply Rmult_lt_0_compat; lra). lra. }
  assert (H15 : 0 <= ∫ a u f).
  {
    apply integral_nonneg; try lra.
    - intros x H15. apply Rge_le, H3. solve_R.
    - apply integrable_on_sub_interval with (a := a) (b := b); auto; lra.
  }
  assert (H16 : 0 <= ∫ v b f).
  {
    apply integral_nonneg; try lra.
    - intros x H16. apply Rge_le, H3. solve_R.
    - apply integrable_on_sub_interval with (a := a) (b := b); auto; lra.
  }
  assert (H17 : ∫ a b f = ∫ a u f + ∫ u b f).
  { apply integral_split'. apply integrable_on_sub_interval with (a := a) (b := b); auto; solve_R. }
  assert (H18 : ∫ u b f = ∫ u v f + ∫ v b f).
  { apply integral_split'. apply integrable_on_sub_interval with (a := a) (b := b); auto; solve_R. }
  lra.
Qed.

Lemma lemma_13_31_c : ∀ f a b,
  a < b ->
  integrable_on a b f ->
  (∀ x, x ∈ [a, b] -> f x > 0) ->
  ∫ a b f > 0.
Abort.
