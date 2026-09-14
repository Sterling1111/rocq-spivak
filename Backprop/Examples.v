From Backprop Require Import Descent.
Import BackpropNotations.
Open Scope R_scope.
Open Scope derivative_value_scope.

(** One input, one output neuron, x = target = 1, initially w = b = 0. *)
Definition tiny_shape := Dense 1 1 (Output 1).
Definition tiny : NeuralNet tiny_shape :=
  @Build_NeuralNet 1 tiny_shape ((fun _ _ => 0, fun _ => 0), tt).
Definition x : Vec 1 := fun _ => 1.
Definition target : Vec 1 := fun _ => 1.
Definition cache := forward_pass tiny_shape (parameters tiny) x.
Definition gradients := snd (backward_pass tiny_shape (parameters tiny) cache target).
Definition trained (eta : R) := train_once tiny x target eta.

Lemma sigma_zero : σ 0 = 1/2.
Proof. unfold sigma. rewrite Ropp_0, Exponential.exp_0. field. Qed.

Example tiny_forward : output_activation tiny_shape cache Fin.F1 = 1/2.
Proof.
  change (σ (weighted_input ((fun _ _ => 0) : Mat 1 1) (fun _ => 0) x Fin.F1) = 1/2).
  rewrite weighted_input_sum. cbn [vsum]. cbv beta iota zeta delta [x target].
  replace (0 * 1 + 0 + 0) with 0 by ring. apply sigma_zero.
Qed.

Example tiny_backward :
  fst (fst gradients) Fin.F1 Fin.F1 = -1/8 /\
  snd (fst gradients) Fin.F1 = -1/8.
Proof.
  change (fst (fst (snd (backprop tiny_shape (parameters tiny) x target))) Fin.F1 Fin.F1 = -1/8 /\
    snd (fst (snd (backprop tiny_shape (parameters tiny) x target))) Fin.F1 = -1/8).
  unfold tiny_shape, tiny, parameters. rewrite backprop_dense.
  cbn [backprop backward_pass forward_pass fst snd hadamard vmap x target].
  unfold hadamard, vmap, x, target. rewrite !weighted_input_sum. cbn [vsum].
  replace (0 * 1 + 0 + 0) with 0 by ring.
  unfold sigma'. rewrite sigma_zero. split; field.
Qed.

Example tiny_update eta :
  fst (fst (parameters (trained eta))) Fin.F1 Fin.F1 = eta/8 /\
  snd (fst (parameters (trained eta))) Fin.F1 = eta/8.
Proof.
  change (0 - eta * fst (fst gradients) Fin.F1 Fin.F1 = eta/8 /\
    0 - eta * snd (fst gradients) Fin.F1 = eta/8).
  destruct tiny_backward as [Hw Hb]. rewrite Hw, Hb. split; field.
Qed.

Example tiny_gradient_norm : gradient_norm_sq tiny_shape (parameters tiny) x target = 1/32.
Proof.
  change (pairing tiny_shape gradients gradients = 1/32).
  cbn [pairing tiny_shape dot vsum]. destruct tiny_backward as [Hw Hb].
  rewrite Hw, Hb. field.
Qed.

Example tiny_loss : C tiny_shape (parameters tiny) x target = 1/8.
Proof.
  change (quadratic (output_activation tiny_shape cache) target = 1/8).
  change ((output_activation tiny_shape cache Fin.F1 - 1) *
    (output_activation tiny_shape cache Fin.F1 - 1) / 2 + 0 = 1/8).
  rewrite tiny_forward. field.
Qed.

Example tiny_strict_descent : exists eta0, 0 < eta0 /\ forall eta, 0 < eta < eta0 ->
  C tiny_shape (parameters (trained eta)) x target < 1/8 - eta/64.
Proof.
  pose proof (one_step_decreases_error 1 tiny_shape tiny x target
    ltac:(rewrite tiny_gradient_norm; lra)) as H.
  rewrite tiny_gradient_norm, tiny_loss in H.
  destruct H as [eta0 [Heta0 H]]. exists eta0. split; [exact Heta0|].
  intros eta Heta. specialize (H eta Heta). unfold trained. nra.
Qed.

(** A hidden layer requires only another [Dense]; widths need not match. *)
Definition two_layer_shape := Dense 2 3 (Dense 3 1 (Output 1)).
Definition two_layer : NeuralNet two_layer_shape :=
  @Build_NeuralNet 2 two_layer_shape
    ((fun _ _ => 0, fun _ => 0), ((fun _ _ => 0, fun _ => 0), tt)).

(** Stationary case: x = 1, target = 1/2 already equals the output. *)
Example tiny_stationary :
  snd (backprop tiny_shape (parameters tiny) x (fun _ => 1/2)) = zero_params tiny_shape.
Proof.
  unfold tiny_shape, tiny, parameters. rewrite backprop_dense.
  cbn [backprop backward_pass forward_pass zero_params fst snd hadamard vmap].
  assert (E : (fun j : Fin.t 1 =>
    (σ (weighted_input ((fun _ _ => 0) : Mat 1 1) (fun _ => 0) x j) - 1/2) *
    σ′ (weighted_input ((fun _ _ => 0) : Mat 1 1) (fun _ => 0) x j)) = (fun _ => 0)).
  { apply fvector_ext. intro j. rewrite weighted_input_sum. cbn [vsum]. cbv beta iota zeta delta [x target].
    replace (0 * 1 + 0 + 0) with 0 by ring. rewrite sigma_zero. ring. }
  unfold hadamard, vmap. rewrite E. cbn. f_equal. f_equal. apply fmatrix_ext. intros j k.
  pose proof (f_equal (fun f : Vec 1 => f j) E) as Ej. cbn beta in Ej. rewrite Ej. ring.
Qed.
