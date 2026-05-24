From Calculus.Chapter9 Require Import Prelude.

Lemma lemma_9_11_a : forall s s' k,
  ⟦ der ⟧ s = s' -> (forall t, s' t = k * s t) -> ~ (exists c, c <> 0 /\ forall t, s t = c * t^2).
Proof.
  intros s s' k H1 H2 [c [H3 H4]].

  assert (H5 : ⟦ der ⟧ s = (λ t, 2 * c * t)).
  { replace s with (λ t, c * t^2); [auto_diff|]. extensionality t. rewrite H4. lra. } 

  assert (H6 : forall t, s' t = 2 * c * t).
  { intros t. rewrite (derivative_unique s s' (λ t : ℝ, 2 * c * t) H1 H5); auto. }

  pose proof (H6 1) as H7.
  pose proof (H2 1) as H8.
  pose proof (H4 1) as H9.
  pose proof (H6 2) as H10.
  pose proof (H2 2) as H11.
  pose proof (H4 2) as H12.

  assert (H13 : 2 * c = k * c).
  {
    rewrite <- Rmult_1_r with (r := 2 * c).
    rewrite <- H7, H8, H9, pow1, Rmult_1_r.
    reflexivity.
  }

  assert (H14 : 4 * c = 4 * k * c).
  {
    replace (4 * c) with (2 * c * 2) by ring.
    rewrite <- H10, H11, H12. field.
  }

  apply Rmult_eq_compat_r with (r := 1 / c) in H13; 
  apply Rmult_eq_compat_r with (r := 1 / (4 * c)) in H14.
  field_simplify in H13; auto.
  field_simplify in H14; auto.

  rewrite <- H13 in H14.

  lra.
Qed.

Lemma lemma_9_11_b_i : forall s s' s'' a,
  s = (fun t => (a / 2) * t^2) -> ⟦ der ⟧ s = s' -> ⟦ der ⟧ s' = s'' -> forall t, s'' t = a.
Proof.
  intros s s' s'' a H1 H2 H3 t.
  
  assert (H4 : ⟦ der ⟧ s = (λ t, a * t)).
  { rewrite H1. auto_diff. }
  
  assert (H5 : forall x, s' x = a * x).
  { intros x. rewrite (derivative_unique s s' (λ t, a * t) H2 H4); reflexivity. }
  
  assert (H6 : ⟦ der ⟧ s' = (λ t, a)).
  { replace s' with (λ t, a * t); [auto_diff|]. extensionality x. rewrite H5; lra. }
  
  rewrite (derivative_unique s' s'' (λ t, a) H3 H6).
  reflexivity.
Qed.

Lemma lemma_9_11_b_ii : forall s s' a,
  s = (fun t => (a / 2) * t^2) -> ⟦ der ⟧ s = s' -> forall t, (s' t)^2 = 2 * a * s t.
Proof.
  intros s s' a H1 H2 t.
  
  assert (H3 : ⟦ der ⟧ s = (λ t, a * t)).
  { rewrite H1; auto_diff. }
  
  assert (H4 : forall x, s' x = a * x).
  { intros x. rewrite (derivative_unique s s' (λ t, a * t) H2 H3); reflexivity. }
  
  rewrite H4.
  rewrite H1.
  lra.
Qed.

Lemma lemma_9_11_c : forall s s' t1 t2,
  s = (fun t => (32 / 2) * t^2) ->
  ⟦ der ⟧ s = s' ->
  t1 > 0 ->
  s t1 = 400 ->
  t2 > 0 ->
  s' t2 = (s' t1) / 2 ->
  t1 = 5 /\ s' t1 = 160 /\ s t2 = 100.
Proof.
  intros s s' t1 t2 H1 H2 H3 H4 H5 H6.

  assert (H7 : forall t, s' t = 32 * t).
  {
    intros t.
    assert (H7 : ⟦ der ⟧ s = (λ x, 32 * x)).
    { rewrite H1; auto_diff. }
    rewrite (derivative_unique s s' (λ x, 32 * x) H2 H7); reflexivity.
  }
  
  pose proof (lemma_9_11_b_ii s s' 32 H1 H2) as H8.
  
  assert (H9 : t1 = 5).
  { rewrite H1 in H4. nra. }
  split; auto.
  
  assert (H10 : s' t1 = 160).
  { rewrite H7, H9. lra. }

  split; auto.
  
  pose proof (H8 t2) as H11.
  rewrite H6, H10 in H11.
  nra.
Qed.