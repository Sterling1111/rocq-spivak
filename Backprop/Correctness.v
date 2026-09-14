From Backprop Require Export NeuralNet.
From Lib Require Import Functions Limit.
Open Scope R_scope.
Open Scope derivative_value_scope.

Lemma C_dense n m (s : Architecture m) w b p a target :
  C (Dense n m s) ((w,b),p) a target =
  C s p (vmap sigma (weighted_input w b a)) target.
Proof. reflexivity. Qed.

Lemma backprop_dense n m (s : Architecture m) w b p a target :
  let z := weighted_input w b a in
  let r := backprop s p (vmap sigma z) target in
  let delta := hadamard (fst r) (vmap sigma' z) in
  backprop (Dense n m s) ((w,b),p) a target =
    (mv (fmatrix_transpose w) delta,
      ((fun j k => a k * delta j, delta), snd r)).
Proof. cbn zeta. unfold backprop. cbn [forward_pass backward_pass fst snd].
  destruct (backward_pass s p (forward_pass s p (vmap sigma (weighted_input w b a))) target).
  reflexivity.
Qed.

Fixpoint zero_params {n} (s : Architecture n) : Params s :=
  match s return Params s with
  | Output _ => tt
  | Dense _ _ rest => ((fun _ _ => 0, fun _ => 0), zero_params rest)
  end.

Lemma dot_zero n (a : Vec n) : dot a (fun _ => 0) = 0.
Proof. unfold dot. transitivity (@vsum n (fun _ => 0));
  [apply vsum_ext; intro i; ring|apply vsum_zero]. Qed.
Lemma pairing_zero n (s : Architecture n) p : pairing s p (zero_params s) = 0.
Proof. induction s; cbn [pairing zero_params fst snd]; [reflexivity|].
  rewrite dot_zero, IHs. assert (E : vsum (fun j => dot (fst (fst p) j) (fun _ => 0)) = 0).
  { transitivity (@vsum m (fun _ => 0)); [apply vsum_ext; intro j; apply dot_zero|apply vsum_zero]. }
  rewrite E. ring.
Qed.

(** Differentiability of a curve of parameters: each matrix entry uses the
    existing one-variable calculus. No multivariable chain rule is assumed. *)
Fixpoint parameter_derivative_at {n} (s : Architecture n) : (R -> Params s) -> R -> Params s -> Prop :=
  match s return (R -> Params s) -> R -> Params s -> Prop with
  | Output _ => fun _ _ _ => True
  | Dense _ _ rest => fun p x dp =>
      (forall j k, ⟦ der x ⟧ (fun t => fst (fst (p t)) j k) = fst (fst dp) j k) /\
      (forall j, ⟦ der x ⟧ (fun t => snd (fst (p t)) j) = snd (fst dp) j) /\
      parameter_derivative_at rest (fun t => snd (p t)) x (snd dp)
  end.

Lemma affine_pullback m n (w dw : Mat m n) (a da : Vec n) (r db : Vec m) :
  dot r (fun j => vsum (fun k => dw j k * a k + w j k * da k) + db j) =
  dot (mv (fmatrix_transpose w) r) da +
  vsum (fun j => dot (fun k => a k * r j) (dw j)) + dot r db.
Proof.
  unfold dot.
  transitivity (vsum (fun j =>
    vsum (fun k => (a k * r j) * dw j k) +
    vsum (fun k => (w j k * r j) * da k) + r j * db j)).
  { apply vsum_ext. intro j. rewrite vsum_plus.
    replace (r j * (vsum (fun k => dw j k * a k) + vsum (fun k => w j k * da k) + db j))
      with (r j * vsum (fun k => dw j k * a k) + r j * vsum (fun k => w j k * da k) + r j * db j) by ring.
    rewrite <- !vsum_scale. f_equal. f_equal; apply vsum_ext; intro k; ring. }
  rewrite !vsum_plus. rewrite (vsum_swap m n (fun j k => (w j k * r j) * da k)).
  assert (H : vsum (fun k => vsum (fun j => w j k * r j * da k)) =
    vsum (fun k => mv (fmatrix_transpose w) r k * da k)).
  { apply vsum_ext. intro k. rewrite mv_sum. unfold fmatrix_transpose.
    transitivity (vsum (fun j => da k * (w j k * r j))).
    - apply vsum_ext. intro j. ring.
    - rewrite vsum_scale. ring. }
  rewrite H. ring.
Qed.

(** The main chain rule, proved by induction on the network. It allows both
    inputs and every weight/bias to vary along any differentiable real curve. *)
Theorem backprop_derivative n (s : Architecture n) :
  forall (p : R -> Params s) (a : R -> Vec n) target x dp da,
  parameter_derivative_at s p x dp ->
  (forall k, ⟦ der x ⟧ (fun t => a t k) = da k) ->
  ⟦ der x ⟧ (fun t => C s (p t) (a t) target) = dot (fst (backprop s (p x) (a x) target)) da +
     pairing s (snd (backprop s (p x) (a x) target)) dp.
Proof.
  induction s as [n|n m s IH]; intros p a target x dp da Hp Ha.
  - cbn [C forward_pass output_activation backprop backward_pass pairing].
    rewrite Rplus_0_r. apply derivative_at_val_quadratic. exact Ha.
  - destruct Hp as [Hw [Hb Hp]].
    set (w := fun t => fst (fst (p t))).
    set (b := fun t => snd (fst (p t))).
    set (q := fun t => snd (p t)).
    set (z := fun t => weighted_input (w t) (b t) (a t)).
    set (dz := fun j => vsum (fun k => fst (fst dp) j k * a x k + w x j k * da k) + snd (fst dp) j).
    assert (Hz : forall j, ⟦ der x ⟧ (fun t => z t j) = dz j).
    { intro j. unfold z, dz. eapply derivative_at_val_ext with
        (f := fun t => vsum (fun k => w t j k * a t k) + b t j).
      - intro t. symmetry. apply weighted_input_sum.
      - apply derivative_at_val_plus; [apply derivative_at_val_sum; intro k; apply derivative_at_val_mult; [apply Hw|apply Ha]|apply Hb]. }
    set (az := fun t => vmap sigma (z t)).
    set (daz := fun j => sigma' (z x j) * dz j).
    assert (Haz : forall j, ⟦ der x ⟧ (fun t => az t j) = daz j).
    { intro j. apply derivative_at_val_sigma_comp. apply Hz. }
    pose proof (IH q az target x (snd dp) daz Hp Haz) as Htail.
    set (r := backprop s (q x) (az x) target).
    set (delta := hadamard (fst r) (vmap sigma' (z x))).
    assert (Hcost : (fun t => C (Dense n m s) (p t) (a t) target) =
      (fun t => C s (q t) (az t) target)).
    { apply functional_extensionality. intro t. unfold q, az, z, w, b. destruct (p t) as [[ww bb] pp]. reflexivity. }
    rewrite Hcost.
    assert (Hbp : backprop (Dense n m s) (p x) (a x) target =
      (mv (fmatrix_transpose (w x)) delta,
        ((fun j k => a x k * delta j, delta), snd r))).
    { unfold delta, r, az, z, w, b, q. destruct (p x) as [[ww bb] pp]. apply backprop_dense. }
    rewrite Hbp. cbn [fst snd pairing].
    replace (dot (mv (fmatrix_transpose (w x)) delta) da +
       (vsum (fun j => dot (fun k => a x k * delta j) (fst (fst dp) j)) +
        dot delta (snd (fst dp)) + pairing s (snd r) (snd dp)))
      with (dot (fst r) daz + pairing s (snd r) (snd dp)).
    + exact Htail.
    + assert (E : dot (fst r) daz = dot delta dz).
      { unfold dot, daz, delta, hadamard, vmap. apply vsum_ext. intro j. ring. }
      rewrite E. unfold dz. rewrite affine_pullback. ring.
Qed.

Lemma parameter_derivative_at_const n (s : Architecture n) p x :
  parameter_derivative_at s (fun _ => p) x (zero_params s).
Proof. induction s; cbn [parameter_derivative_at zero_params fst snd]; [exact I|].
  split; [intros; apply derivative_at_val_const|]. split; [intros; apply derivative_at_val_const|apply IHs].
Qed.

Lemma input_curve_derivative n (s : Architecture n) p (a : R -> Vec n) target x da :
  (forall j, ⟦ der x ⟧ (fun t => a t j) = da j) ->
  ⟦ der x ⟧ (fun t => C s p (a t) target) = dot (fst (backprop s p (a x) target)) da.
Proof.
  intro Ha. pose proof (backprop_derivative n s (fun _ => p) a target x
    (zero_params s) da (parameter_derivative_at_const n s p x) Ha) as H.
  rewrite pairing_zero, Rplus_0_r in H. exact H.
Qed.

Definition shift {n} (v direction : Vec n) (h : R) : Vec n :=
  fun j => v j + h * direction j.
Lemma shift_zero n (v d : Vec n) : shift v d 0 = v.
Proof. apply functional_extensionality. intro j. unfold shift. ring. Qed.
Lemma derivative_at_val_shift n (v d : Vec n) x j : ⟦ der x ⟧ (fun h => shift v d h j) = d j.
Proof.
  replace (d j) with (0 + (1 * d j + x * 0)) by ring.
  apply derivative_at_val_plus; [apply derivative_at_val_const|apply derivative_at_val_mult; [apply derivative_at_val_id|apply derivative_at_val_const]].
Qed.

(** A partial derivative is the ordinary derivative when exactly one coordinate
    varies. Thus the four equations below concern derivatives of the loss,
    not definitions of the backward algorithm. *)
Definition partial {n} (F : Vec n -> R) (v : Vec n) : Vec n :=
  fun j => derive_at (fun h => F (shift v (basis j) h)) 0.
Definition matrix_partial {m n} (F : Mat m n -> R) (w : Mat m n)
    (j : Fin.t m) (k : Fin.t n) : R :=
  derive_at (fun h => F (fun r c => w r c + h * (basis j r * basis k c))) 0.

Module PartialDerivativeNotations.
  Notation "⟦ '∂' v , j ⟧ F" := (partial F v j)
    (at level 70, v at level 0, j at level 0, F at level 0, no associativity,
      format "⟦  '∂'  v ,  j  ⟧  F").
  Notation "⟦ '∂' w , j , k ⟧ F" := (matrix_partial F w j k)
    (at level 70, w at level 0, j at level 0, k at level 0, F at level 0, no associativity,
      format "⟦  '∂'  w ,  j ,  k  ⟧  F").
End PartialDerivativeNotations.
Import PartialDerivativeNotations.

Definition nabla_a_C {n} (a target : Vec n) : Vec n :=
  fun j => ⟦ ∂ a, j ⟧ (fun u => quadratic u target).
Definition delta {n} (s : Architecture n) (p : Params s) (z : Vec n)
    (target : Vec (output_size s)) : Vec n :=
  fun j => ⟦ ∂ z, j ⟧ (fun u => C s p (vmap sigma u) target).

Module BackpropNotations.
  Export DerivativeValueNotations PartialDerivativeNotations.
  Notation "'σ'" := sigma.
  Notation "'σ′'" := sigma'.
  Infix "⊙" := hadamard (at level 40, left associativity).
  Notation "'∇aC'" := nabla_a_C.
  Notation "'δ'" := delta.
End BackpropNotations.
Import BackpropNotations.

Lemma nabla_a_C_value n (a target : Vec n) :
  ∇aC a target = (fun j => a j - target j).
Proof.
  apply functional_extensionality. intro j. unfold nabla_a_C, partial.
  apply derivative_at_imp_derive_at with (f' := fun _ => a j - target j).
  change (⟦ der 0 ⟧ (fun h => quadratic (shift a (basis j) h) target) = a j - target j).
  pose proof (derivative_at_val_quadratic n (shift a (basis j)) target 0 (basis j)
    (derivative_at_val_shift n a (basis j) 0)) as H.
  rewrite shift_zero, dot_basis in H. exact H.
Qed.

Lemma logits_curve_derivative n (s : Architecture n) p (z : R -> Vec n) target x dz :
  (forall j, ⟦ der x ⟧ (fun h => z h j) = dz j) ->
  ⟦ der x ⟧ (fun h => C s p (vmap σ (z h)) target) = dot (fst (backprop s p (vmap σ (z x)) target) ⊙ vmap σ′ (z x)) dz.
Proof.
  intro Hz. pose proof (input_curve_derivative n s p (fun h => vmap σ (z h)) target x
    (fun j => σ′ (z x j) * dz j) (fun j => derivative_at_val_sigma_comp _ _ _ (Hz j))) as H.
  replace (dot (fst (backprop s p (vmap σ (z x)) target) ⊙ vmap σ′ (z x)) dz)
    with (dot (fst (backprop s p (vmap σ (z x)) target)) (fun j => σ′ (z x j) * dz j)).
  - exact H.
  - unfold dot, hadamard, vmap. apply vsum_ext. intro j. ring.
Qed.

Lemma delta_correct n (s : Architecture n) p z target :
  δ s p z target = fst (backprop s p (vmap σ z) target) ⊙ vmap σ′ z.
Proof.
  apply functional_extensionality. intro j. unfold delta, partial.
  apply derivative_at_imp_derive_at with (f' := fun _ =>
    (fst (backprop s p (vmap σ z) target) ⊙ vmap σ′ z) j).
  pose proof (logits_curve_derivative n s p (shift z (basis j)) target 0 (basis j)
    (derivative_at_val_shift n z (basis j) 0)) as H.
  rewrite shift_zero, dot_basis in H. exact H.
Qed.

(** Theorem 1 (output layer): δ^L = ∇_a C ⊙ σ′(z^L). *)
Theorem theorem_1 n (z target : Vec n) :
  δ (Output n) tt z target = ∇aC (vmap σ z) target ⊙ vmap σ′ z.
Proof. rewrite delta_correct, nabla_a_C_value. reflexivity. Qed.

(** Theorem 2 (hidden layer): δ^l = ((w^(l+1))^T δ^(l+1)) ⊙ σ′(z^l).
    [s,p] are the network strictly after the next layer. *)
Theorem theorem_2 n m (s : Architecture m) (w : Mat m n) b p z target :
  δ (Dense n m s) ((w,b),p) z target =
    mv (fmatrix_transpose w)
      (δ s p (weighted_input w b (vmap σ z)) target) ⊙ vmap σ′ z.
Proof. rewrite delta_correct, backprop_dense, delta_correct. reflexivity. Qed.

(** Theorem 3: ∂C/∂b_j^l = δ_j^l. *)
Theorem theorem_3 n m (s : Architecture m) (w : Mat m n) b p a target j :
  ⟦ ∂ b, j ⟧ (fun b => C (Dense n m s) ((w,b),p) a target) =
    δ s p (weighted_input w b a) target j.
Proof.
  unfold partial. rewrite delta_correct.
  apply derivative_at_imp_derive_at with (f' := fun _ =>
    (fst (backprop s p (vmap σ (weighted_input w b a)) target) ⊙
      vmap σ′ (weighted_input w b a)) j).
  set (zc := fun h => weighted_input w (shift b (basis j) h) a).
  assert (Hz : forall r, ⟦ der 0 ⟧ (fun h => zc h r) = basis j r).
  { intro r. unfold zc. eapply derivative_at_val_ext with
      (f := fun h => vsum (fun k => w r k * a k) + shift b (basis j) h r).
    - intro h. symmetry. apply weighted_input_sum.
    - replace (basis j r) with (0 + basis j r) by ring.
      apply derivative_at_val_plus; [apply derivative_at_val_const|apply derivative_at_val_shift]. }
  pose proof (logits_curve_derivative m s p zc target 0 (basis j) Hz) as H.
  unfold zc in H. rewrite shift_zero, dot_basis in H. exact H.
Qed.

(** Theorem 4: ∂C/∂w_jk^l = a_k^(l-1) δ_j^l. *)
Theorem theorem_4 n m (s : Architecture m) (w : Mat m n) b p a target j k :
  ⟦ ∂ w, j, k ⟧ (fun w => C (Dense n m s) ((w,b),p) a target) =
    a k * δ s p (weighted_input w b a) target j.
Proof.
  unfold matrix_partial. rewrite delta_correct.
  set (wc := fun h r c => w r c + h * (basis j r * basis k c)).
  set (zc := fun h => weighted_input (wc h) b a).
  assert (Hz : forall r, ⟦ der 0 ⟧ (fun h => zc h r) = a k * basis j r).
  { intro r.
    assert (E : forall h, zc h r = weighted_input w b a r + h * (a k * basis j r)).
    { intro h. unfold zc, wc. rewrite !weighted_input_sum.
      transitivity (vsum (fun c => w r c * a c + (h * basis j r) * (a c * basis k c)) + b r).
      - f_equal. apply vsum_ext. intro c. ring.
      - rewrite vsum_plus, vsum_scale. fold (dot a (basis k)).
        rewrite dot_basis. ring. }
    eapply derivative_at_val_ext with (f := fun h => weighted_input w b a r + h * (a k * basis j r));
      [intro h; symmetry; apply E|].
    pose proof (derivative_at_val_plus _ _ _ _ _ (derivative_at_val_const (weighted_input w b a r) 0)
      (derivative_at_val_mult _ _ _ _ _ (derivative_at_val_id 0) (derivative_at_val_const (a k * basis j r) 0))) as Hlin.
    cbn beta in Hlin.
    replace (0 + (1 * (a k * basis j r) + 0 * 0)) with (a k * basis j r) in Hlin by ring.
    exact Hlin. }
  pose proof (logits_curve_derivative m s p zc target 0 (fun r => a k * basis j r) Hz) as H.
  assert (E0 : zc 0 = weighted_input w b a).
  { unfold zc, wc. f_equal. apply fmatrix_ext. intros r c. ring. }
  rewrite E0 in H.
  set (d := fst (backprop s p (vmap σ (weighted_input w b a)) target) ⊙ vmap σ′ (weighted_input w b a)) in *.
  assert (Ed : dot d (fun r => a k * basis j r) = a k * d j).
  { unfold dot. transitivity (vsum (fun r => a k * (d r * basis j r))).
    - apply vsum_ext. intro r. ring.
    - rewrite vsum_scale. fold (dot d (basis j)). rewrite dot_basis. reflexivity. }
  rewrite Ed in H.
  apply derivative_at_imp_derive_at with (f' := fun _ => a k * d j). exact H.
Qed.
