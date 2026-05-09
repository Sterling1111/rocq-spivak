From Calculus.Chapter11 Require Import Prelude.

Lemma lemma_11_9 : forall f f' x,
  ⟦ der x ⟧ f = f' ->
  (⟦ der x ⟧ (fun y => (f y)^2) = (fun _ => 0) <-> f' x = 0 \/ f x = 0).
Proof.
  intros f f' x H1.
  replace (f ^ 2)%function with (f ⋅ f)%function by (extensionality y; simpl; nra).
  split; intros H2.
  - pose proof derivative_at_mult f f f' f' x H1 H1 as H3.
    pose proof derivative_at_unique (f ⋅ f)%function (f' ⋅ f + f ⋅ f')%function (λ _ : ℝ, 0) x H3 H2 as H4.
    replace ((f' ⋅ f + f ⋅ f')%function x) with (f' x * f x + f x * f' x) in H4 by reflexivity.
    simpl in H4.
    nra.
  - pose proof derivative_at_mult f f f' f' x H1 H1 as H3.
    apply derivative_at_ext_val with (f' := (f' ⋅ f + f ⋅ f')%function); auto.
    nra.
Qed.