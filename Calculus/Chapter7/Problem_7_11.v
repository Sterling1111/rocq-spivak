From Calculus.Chapter7 Require Import Prelude.

Lemma lemma_7_11 : forall f,
  continuous_on f [0, 1] ->
  (forall x, x ∈ [0, 1] -> f x ∈ [0, 1]) ->
  exists x, x ∈ [0, 1] /\ f x = x.
Proof.
  intros f H1 H2.
  set (h := fun x => x - f x).
  assert (H3 : continuous_on h [0, 1]).
  { unfold h. intros x H4. apply limit_on_minus; auto. apply limit_on_id. }
  assert (h 0 <= 0 <= h 1) as H4.
  {
    unfold h. specialize (H2 0 ltac:(solve_R)) as H4.
    specialize (H2 1 ltac:(solve_R)). solve_R.
  }
  pose proof intermediate_value_theorem h 0 1 0 ltac:(solve_R) H3 H4 as [x [H5 H6]].
  exists x; split; auto; unfold h in *; solve_R.
Qed.