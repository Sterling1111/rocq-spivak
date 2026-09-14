From Backprop Require Export Correctness.
From Lib Require Import Limit.
Open Scope R_scope.
Open Scope derivative_value_scope.

Fixpoint negate_params {n} (s : Architecture n) : Params s -> Params s :=
  match s return Params s -> Params s with
  | Output _ => fun _ => tt
  | Dense _ _ rest => fun p =>
      ((fun j k => - fst (fst p) j k, fun j => - snd (fst p) j),
       negate_params rest (snd p))
  end.

Lemma dot_neg n (a b : Vec n) : dot a (fun j => - b j) = - dot a b.
Proof. unfold dot. transitivity (vsum (fun j => (-1) * (a j * b j))).
  - apply vsum_ext. intro j. ring.
  - rewrite vsum_scale. ring.
Qed.
Lemma pairing_neg n (s : Architecture n) p q :
  pairing s p (negate_params s q) = - pairing s p q.
Proof. induction s; cbn [pairing negate_params fst snd]; [ring|].
  rewrite dot_neg, IHs.
  assert (E : vsum (fun j => dot (fst (fst p) j) (fun k => - fst (fst q) j k)) =
    - vsum (fun j => dot (fst (fst p) j) (fst (fst q) j))).
  { transitivity (vsum (fun j => (-1) * dot (fst (fst p) j) (fst (fst q) j))).
    - apply vsum_ext. intro j. rewrite dot_neg. ring.
    - rewrite vsum_scale. ring. }
  rewrite E. ring.
Qed.
Lemma step_zero n (s : Architecture n) p g : step s 0 p g = p.
Proof. induction s; [destruct p; reflexivity|].
  destruct p as [[w b] p]. cbn [step fst snd]. rewrite IHs.
  assert (Ew : (fun j k => w j k - 0 * fst (fst g) j k) = w).
  { apply fmatrix_ext. intros j k. ring. }
  assert (Eb : (fun j => b j - 0 * snd (fst g) j) = b).
  { apply fvector_ext. intro j. ring. }
  rewrite Ew, Eb. reflexivity.
Qed.
Lemma derivative_at_val_step_entry p g x : ⟦ der x ⟧ (fun eta => p - eta * g) = -g.
Proof.
  pose proof (derivative_at_val_minus _ _ _ _ _ (derivative_at_val_const p x)
    (derivative_at_val_mult _ _ _ _ _ (derivative_at_val_id x) (derivative_at_val_const g x))) as H.
  cbn beta in H. replace (0 - (1 * g + x * 0)) with (-g) in H by ring. exact H.
Qed.
Lemma parameter_derivative_at_step n (s : Architecture n) p g x :
  parameter_derivative_at s (fun eta => step s eta p g) x (negate_params s g).
Proof. induction s; cbn [parameter_derivative_at step negate_params fst snd]; [exact I|].
  split; [intros; apply derivative_at_val_step_entry|]. split; [intro j; apply derivative_at_val_step_entry|apply IHs].
Qed.

(** The derivative of the actual, simultaneous gradient step is -||gradient||². *)
Theorem training_direction_derivative n (s : Architecture n) p a target :
  ⟦ der 0 ⟧ (fun eta => C s (step s eta p (snd (backprop s p a target))) a target) =
    - gradient_norm_sq s p a target.
Proof.
  set (g := snd (backprop s p a target)).
  pose proof (backprop_derivative n s (fun eta => step s eta p g) (fun _ => a)
    target 0 (negate_params s g) (fun _ => 0)
    (parameter_derivative_at_step n s p g 0) (fun j => derivative_at_val_const (a j) 0)) as H.
  cbn beta in H.
  rewrite step_zero, dot_zero, Rplus_0_l, pairing_neg in H. exact H.
Qed.

(** The epsilon/delta definition of the derivative supplies the learning-rate
    threshold. Epsilon measures the error in the first-order prediction. *)
Lemma scalar_descent_remainder f G : ⟦ der 0 ⟧ f = -G ->
  forall epsilon, 0 < epsilon -> exists eta0, 0 < eta0 /\
  forall eta, 0 < eta < eta0 ->
    Rabs (f eta - f 0 + eta * G) < eta * epsilon.
Proof.
  intros Hd epsilon He. unfold derivative_at_val, limit in Hd.
  destruct (Hd epsilon He) as [eta0 [Heta0 H]]. exists eta0. split; [exact Heta0|].
  intros eta Heta.
  specialize (H eta). rewrite Rminus_0_r, Rabs_pos_eq in H by lra.
  specialize (H Heta). cbn beta in H. rewrite Rplus_0_l in H.
  assert (E : f eta - f 0 + eta * G = eta * ((f eta - f 0) / eta - - G)) by (field; lra).
  rewrite E, Rabs_mult, Rabs_pos_eq by lra.
  apply Rmult_lt_compat_l; lra.
Qed.

Theorem learning_rate_remainder n (s : Architecture n) p a target epsilon :
  0 < epsilon -> exists eta0, 0 < eta0 /\
  forall eta, 0 < eta < eta0 ->
    Rabs (C s (step s eta p (snd (backprop s p a target))) a target -
          C s p a target + eta * gradient_norm_sq s p a target) < eta * epsilon.
Proof.
  intro He. pose proof (scalar_descent_remainder _ _
    (training_direction_derivative n s p a target) epsilon He) as H.
  cbn beta in H. rewrite step_zero in H. exact H.
Qed.

(** For any 0 < epsilon < ||gradient||², sufficiently small positive eta
    decreases the loss by more than eta (||gradient||² - epsilon). *)
Theorem error_decreases_epsilon n (s : Architecture n) p a target epsilon :
  0 < epsilon < gradient_norm_sq s p a target ->
  exists eta0, 0 < eta0 /\ forall eta, 0 < eta < eta0 ->
    C s (step s eta p (snd (backprop s p a target))) a target <
    C s p a target - eta * (gradient_norm_sq s p a target - epsilon).
Proof.
  intro He. destruct (learning_rate_remainder n s p a target epsilon (proj1 He))
    as [eta0 [Heta0 H]]. exists eta0. split; [exact Heta0|].
  intros eta Heta. specialize (H eta Heta).
  pose proof (Rle_abs (C s (step s eta p (snd (backprop s p a target))) a target -
    C s p a target + eta * gradient_norm_sq s p a target)). nra.
Qed.

Theorem one_step_decreases_error n (s : Architecture n) (net : NeuralNet s) a target :
  0 < gradient_norm_sq s (parameters net) a target ->
  exists eta0, 0 < eta0 /\ forall eta, 0 < eta < eta0 ->
    C s (parameters (train_once net a target eta)) a target <
    C s (parameters net) a target - eta * gradient_norm_sq s (parameters net) a target / 2.
Proof.
  intro HG.
  destruct (error_decreases_epsilon n s (parameters net) a target
    (gradient_norm_sq s (parameters net) a target / 2) ltac:(lra)) as [eta0 [Heta0 H]].
  exists eta0. split; [exact Heta0|]. intros eta Heta. specialize (H eta Heta).
  change (C s (step s eta (parameters net) (snd (backprop s (parameters net) a target))) a target <
    C s (parameters net) a target - eta * gradient_norm_sq s (parameters net) a target / 2).
  nra.
Qed.

Lemma dot_self_nonneg n (v : Vec n) : 0 <= dot v v.
Proof. unfold dot. apply vsum_nonneg. intro j. nra. Qed.
Lemma pairing_self_nonneg n (s : Architecture n) p : 0 <= pairing s p p.
Proof. induction s; cbn [pairing]; [lra|].
  pose proof (vsum_nonneg m (fun j => dot (fst (fst p) j) (fst (fst p) j))
    (fun j => dot_self_nonneg n (fst (fst p) j))).
  pose proof (dot_self_nonneg m (snd (fst p))). specialize (IHs (snd p)). lra.
Qed.

(** A nonzero gradient is the precise extra condition needed for strict descent. *)
Lemma vsum_nonneg_zero n (f : Vec n) :
  (forall j, 0 <= f j) -> vsum f = 0 -> forall j, f j = 0.
Proof.
  induction n; intros Hpos Hzero j; [inversion j|].
  cbn in Hzero. pose proof (Hpos Fin.F1) as Hfirst.
  pose proof (vsum_nonneg n (fun i => f (Fin.FS i)) (fun i => Hpos (Fin.FS i))) as Htail.
  refine (Fin.caseS' j (fun j => f j = 0) _ _).
  - lra.
  - intro i. apply (IHn (fun k => f (Fin.FS k))); [intro k; apply Hpos|lra].
Qed.
Lemma dot_self_zero n (v : Vec n) : dot v v = 0 -> v = (fun _ => 0).
Proof.
  intro H. apply fvector_ext. intro j.
  pose proof (vsum_nonneg_zero n (fun j => v j * v j) ltac:(intro i; nra) H j). nra.
Qed.
Lemma pairing_self_zero n (s : Architecture n) p :
  pairing s p p = 0 -> p = zero_params s.
Proof.
  induction s; [destruct p; reflexivity|]. destruct p as [[w b] p].
  cbn [pairing zero_params fst snd]. intro H.
  pose proof (dot_self_nonneg m b) as Hb.
  pose proof (pairing_self_nonneg m s p) as Hp.
  pose proof (vsum_nonneg m (fun j => dot (w j) (w j)) (fun j => dot_self_nonneg n (w j))) as Hw.
  assert (Eb : b = (fun _ => 0)) by (apply dot_self_zero; lra).
  assert (Ep : p = zero_params s) by (apply IHs; lra).
  assert (Ew : w = (fun _ _ => 0)).
  { apply fvector_ext. intro j. apply dot_self_zero.
    apply (vsum_nonneg_zero m (fun j => dot (w j) (w j))
      (fun j => dot_self_nonneg n (w j)) ltac:(lra) j). }
  now rewrite Ew, Eb, Ep.
Qed.

Corollary nonzero_gradient_decreases_error n (s : Architecture n) (net : NeuralNet s) a target :
  snd (backprop s (parameters net) a target) <> zero_params s ->
  exists eta0, 0 < eta0 /\ forall eta, 0 < eta < eta0 ->
    C s (parameters (train_once net a target eta)) a target <
    C s (parameters net) a target.
Proof.
  intro Hne. assert (HG : 0 < gradient_norm_sq s (parameters net) a target).
  { unfold gradient_norm_sq. pose proof (pairing_self_nonneg n s
      (snd (backprop s (parameters net) a target))) as Hpos.
    assert (Hnz : pairing s (snd (backprop s (parameters net) a target))
      (snd (backprop s (parameters net) a target)) <> 0).
    { intro H. apply Hne. now apply pairing_self_zero. } lra. }
  destruct (one_step_decreases_error n s net a target HG) as [eta0 [Heta0 H]].
  exists eta0. split; [exact Heta0|]. intros eta Heta. specialize (H eta Heta). nra.
Qed.

Lemma step_zero_gradient n (s : Architecture n) eta p : step s eta p (zero_params s) = p.
Proof.
  induction s; [destruct p; reflexivity|]. destruct p as [[w b] p].
  cbn [step zero_params fst snd]. rewrite IHs.
  assert (Ew : (fun j k => w j k - eta * 0) = w) by
    (apply fmatrix_ext; intros j k; ring).
  assert (Eb : (fun j => b j - eta * 0) = b) by
    (apply fvector_ext; intro j; ring).
  rewrite Ew, Eb. reflexivity.
Qed.

Theorem stationary_step n (s : Architecture n) (net : NeuralNet s) a target eta :
  gradient_norm_sq s (parameters net) a target = 0 ->
  parameters (train_once net a target eta) = parameters net.
Proof.
  intro H. apply pairing_self_zero in H.
  change (step s eta (parameters net) (snd (backprop s (parameters net) a target)) = parameters net).
  rewrite H. apply step_zero_gradient.
Qed.
