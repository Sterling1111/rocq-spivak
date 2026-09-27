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

From Stdlib Require Import QArith Qround NArith List.

Import ListNotations.
Open Scope Q_scope.

Definition nat_Q (n : nat) : Q :=
  inject_Z (Z.of_nat n).

Fixpoint halve_Q (n : nat) (x : Q) : Q :=
  match n with
  | O => Qred x
  | S n => halve_Q n (Qred (x / 2))
  end.

Definition reduction_steps (x : Q) : nat :=
  match Qnum x with
  | Z0 => 0%nat
  | Zpos p =>
      let n :=
        (Pos.size_nat p - Pos.size_nat (Qden x))%nat in
      if Qle_bool (halve_Q n x) 1
      then n
      else S n
  | Zneg p =>
      let n :=
        (Pos.size_nat p - Pos.size_nat (Qden x))%nat in
      if Qle_bool (-1) (halve_Q n x)
      then n
      else S n
  end.

Fixpoint Q_exp_taylor
    (x : Q)
    (n k : nat)
    (term sum : Q) : Q :=
  match n with
  | O => Qred sum
  | S n =>
      let k' := S k in
      let term' :=
        Qred (term * x / nat_Q k') in
      Q_exp_taylor
        x n k'
        term'
        (Qred (sum + term'))
  end.

Fixpoint square_Q (x : Q) (n : nat) : Q :=
  match n with
  | O => Qred x
  | S n => square_Q (Qred (x * x)) n
  end.

Definition round5 (x : Q) : Q :=
  Qmake
    (Qfloor (x * 100000 + 0.5))
    100000%positive.

(** Evaluate the Taylor polynomial with one common denominator.  At step
    [k], [power] is a^k, [denominator] is b^k k!, and [numerator] is
    the partial sum multiplied by that denominator.  This avoids a gcd
    for every term and every addition; only the final fraction is reduced. *)
Fixpoint Q_exp_integer_terms
    (a : Z) (b : positive) (remaining k : nat)
    (power numerator : Z) (denominator : positive) : Q :=
  match remaining with
  | O => Qred (Qmake numerator denominator)
  | S remaining' =>
      let k' := S k in
      let factor := (b * Pos.of_nat k')%positive in
      let power' := (power * a)%Z in
      Q_exp_integer_terms a b remaining' k'
        power'
        (numerator * Zpos factor + power')%Z
        (denominator * factor)%positive
  end.

Definition Q_exp_taylor_fast (x : Q) (terms : nat) : Q :=
  Q_exp_integer_terms (Qnum x) (Qden x) terms 0 1%Z 1%Z 1%positive.

Definition Q_exp_raw (x : Q) : Q :=
  let n := reduction_steps x in
  let y := halve_Q n x in
  square_Q
    (Q_exp_taylor_fast y 10)
    n.

Definition Q_exp (x : Q) : Q :=
  round5 (Q_exp_raw x).

Definition Q_sigmoid (x : Q) : Q :=
  round5
    (1 / (1 + Q_exp (-x))).

Definition Q_sigmoid'_from_output (y : Q) : Q :=
  round5
    (y * (1 - y)).

Definition QVec := list Q.
Definition QMat := list QVec.

Fixpoint qmap2
    (f : Q -> Q -> Q)
    (xs ys : QVec) : QVec :=
  match xs, ys with
  | x :: xs', y :: ys' =>
      f x y :: qmap2 f xs' ys'
  | _, _ => []
  end.

Fixpoint qdot
    (xs ys : QVec) : Q :=
  match xs, ys with
  | x :: xs', y :: ys' =>
      x * y + qdot xs' ys'
  | _, _ => 0
  end.

Definition qvec_add
    (xs ys : QVec) : QVec :=
  qmap2
    (fun x y => x + y)
    xs ys.

Definition qhadamard
    (xs ys : QVec) : QVec :=
  qmap2
    (fun x y => x * y)
    xs ys.

Definition qscale
    (c : Q)
    (xs : QVec) : QVec :=
  map
    (fun x => c * x)
    xs.

Definition qmv
    (w : QMat)
    (x : QVec) : QVec :=
  map
    (fun row => qdot row x)
    w.

Definition qweighted_input
    (w : QMat)
    (b : QVec)
    (x : QVec) : QVec :=
  qvec_add
    (qmv w x)
    b.

Definition qouter
    (a b : QVec) : QMat :=
  map
    (fun x =>
       map
         (fun y => x * y)
         b)
    a.

Fixpoint qmat_map2
    (f : Q -> Q -> Q)
    (a b : QMat) : QMat :=
  match a, b with
  | row1 :: a',
    row2 :: b' =>
      qmap2 f row1 row2
      ::
      qmat_map2 f a' b'
  | _, _ => []
  end.

Definition qmat_update
    (eta : Q)
    (w dw : QMat) : QMat :=
  qmat_map2
    (fun x dx =>
       round5
         (x - eta * dx))
    w dw.

Definition qvec_update
    (eta : Q)
    (b db : QVec) : QVec :=
  qmap2
    (fun x dx =>
       round5
         (x - eta * dx))
    b db.

Record AdditionNet := {
  w1 : QMat;
  b1 : QVec;

  w2 : QVec;
  b2 : Q
}.

Record ForwardCache := {
  cache_input : QVec;

  cache_hidden : QVec;
  cache_hidden_prime : QVec;

  cache_output : Q;
  cache_output_prime : Q
}.

Record AdditionGradient := {
  grad_w1 : QMat;
  grad_b1 : QVec;

  grad_w2 : QVec;
  grad_b2 : Q
}.

Definition addition_encode
    (x y : Q) : Q :=
  round5
    (0.1 + 0.4 * (x + y)).

Definition addition_decode
    (y : Q) : Q :=
  round5
    ((y - 0.1) / 0.4).

Definition addition_forward
    (net : AdditionNet)
    (input : QVec) : ForwardCache :=

  let z1 :=
    qweighted_input
      (w1 net)
      (b1 net)
      input in

  let a1 :=
    map Q_sigmoid z1 in

  let sp1 :=
    map
      Q_sigmoid'_from_output
      a1 in

  let z2 :=
    qdot
      (w2 net)
      a1
    +
    b2 net in

  let output :=
    Q_sigmoid z2 in

  let output_prime :=
    Q_sigmoid'_from_output
      output in

  {|
    cache_input :=
      input;

    cache_hidden :=
      a1;

    cache_hidden_prime :=
      sp1;

    cache_output :=
      output;

    cache_output_prime :=
      output_prime
  |}.

Definition addition_backward
    (net : AdditionNet)
    (cache : ForwardCache)
    (target : Q) :
    AdditionGradient :=

  let delta2 :=
    (cache_output cache - target)
    *
    cache_output_prime cache in

  let incoming :=
    map
      (fun w =>
         w * delta2)
      (w2 net) in

  let delta1 :=
    qhadamard
      incoming
      (cache_hidden_prime cache) in

  {|
    grad_w1 :=
      qouter
        delta1
        (cache_input cache);

    grad_b1 :=
      delta1;

    grad_w2 :=
      qscale
        delta2
        (cache_hidden cache);

    grad_b2 :=
      delta2
  |}.

Definition addition_step
    (eta : Q)
    (net : AdditionNet)
    (g : AdditionGradient) :
    AdditionNet :=

  {|
    w1 :=
      qmat_update
        eta
        (w1 net)
        (grad_w1 g);

    b1 :=
      qvec_update
        eta
        (b1 net)
        (grad_b1 g);

    w2 :=
      qvec_update
        eta
        (w2 net)
        (grad_w2 g);

    b2 :=
      round5
        (b2 net -
         eta * grad_b2 g)
  |}.

Definition addition_train_once
    (eta : Q)
    (net : AdditionNet)
    (x y : Q) :
    AdditionNet :=

  let input :=
    [x; y] in

  let target :=
    addition_encode x y in

  let cache :=
    addition_forward
      net
      input in

  let gradient :=
    addition_backward
      net
      cache
      target in

  addition_step
    eta
    net
    gradient.

Definition qlcg
    (seed : N) : N :=
  ((1664525 * seed +
    1013904223)
   mod
   4294967296)%N.

Definition qrand
    (seed : N) :
    Q * N :=

  let seed' :=
    qlcg seed in

  let n :=
    (seed' mod 1001)%N in

  let x :=
    (inject_Z (Z.of_N n) -
     500) / 1000 in

  (x, seed').

Fixpoint qrandom_vec
    (n : nat)
    (seed : N) :
    QVec * N :=
  match n with
  | O =>
      ([], seed)

  | S n' =>
      let '(x, seed1) :=
        qrand seed in

      let '(xs, seed2) :=
        qrandom_vec
          n'
          seed1 in

      (x :: xs,
       seed2)
  end.

Fixpoint qrandom_mat
    (rows cols : nat)
    (seed : N) :
    QMat * N :=
  match rows with
  | O =>
      ([], seed)

  | S rows' =>
      let '(row, seed1) :=
        qrandom_vec
          cols
          seed in

      let '(rest, seed2) :=
        qrandom_mat
          rows'
          cols
          seed1 in

      (row :: rest,
       seed2)
  end.

Definition addition_random_net
    (seed : N) :
    AdditionNet :=

  let '(rw1, seed1) :=
    qrandom_mat
      3 2 seed in

  let '(rb1, seed2) :=
    qrandom_vec
      3 seed1 in

  let '(rw2, seed3) :=
    qrandom_vec
      3 seed2 in

  let '(rb2, _) :=
    qrand seed3 in

  {|
    w1 := rw1;
    b1 := rb1;

    w2 := rw2;
    b2 := rb2
  |}.

Definition addition_net0 :=
  addition_random_net
    42%N.

Definition AdditionExample :=
  (Q * Q)%type.

Definition addition_data :
    list AdditionExample :=
  [
    (0,    0);
    (0,    0.25);
    (0,    0.5);
    (0,    0.75);
    (0,    1);

    (0.25, 0);
    (0.25, 0.25);
    (0.25, 0.5);
    (0.25, 0.75);
    (0.25, 1);

    (0.5,  0);
    (0.5,  0.25);
    (0.5,  0.5);
    (0.5,  0.75);
    (0.5,  1);

    (0.75, 0);
    (0.75, 0.25);
    (0.75, 0.5);
    (0.75, 0.75);
    (0.75, 1);

    (1,    0);
    (1,    0.25);
    (1,    0.5);
    (1,    0.75);
    (1,    1)
  ].

Definition addition_eta : Q :=
  0.5.

Fixpoint addition_train_epoch
    (data : list AdditionExample)
    (net : AdditionNet) :
    AdditionNet :=
  match data with
  | [] =>
      net

  | (x, y) :: rest =>
      let net' :=
        addition_train_once
          addition_eta
          net
          x y in

      addition_train_epoch
        rest
        net'
  end.

Fixpoint addition_train_epochs
    (epochs : nat)
    (net : AdditionNet) :
    AdditionNet :=
  match epochs with
  | O =>
      net

  | S epochs' =>
      let net' :=
        addition_train_epoch
          addition_data
          net in

      addition_train_epochs
        epochs'
        net'
  end.

Definition addition_predict_raw
    (net : AdditionNet)
    (x y : Q) : Q :=
  cache_output
    (addition_forward
      net
      [x; y]).

Definition addition_predict
    (net : AdditionNet)
    (x y : Q) : Q :=
  addition_decode
    (addition_predict_raw
      net x y).

Definition addition_example_loss_raw
    (net : AdditionNet)
    (x y : Q) : Q :=

  let cache :=
    addition_forward
      net
      [x; y] in

  let target :=
    addition_encode
      x y in

  let error :=
    cache_output cache -
    target in

  error * error / 2.

Fixpoint addition_total_loss
    (net : AdditionNet)
    (data : list AdditionExample) : Q :=
  match data with
  | [] =>
      0

  | (x, y) :: rest =>
      addition_example_loss_raw
        net x y
      +
      addition_total_loss
        net rest
  end.

Definition addition_average_loss
    (net : AdditionNet) : Q :=
  round5
    (addition_total_loss
      net
      addition_data
      / 25).

Definition addition_test
    (net : AdditionNet) :=
  (
    addition_predict net 0.1 0.2,
    addition_predict net 0.17 0.61,
    addition_predict net 0.33 0.66,
    addition_predict net 0.42 0.37,
    addition_predict net 0.8 0.15,
    addition_predict net 1 1
  ).

(** Reporting a saved checkpoint does not repeat training. *)
Definition addition_report (net : AdditionNet) :=
  (addition_average_loss addition_net0,
   addition_average_loss net,
   addition_test net).

Definition addition_run (epochs : nat) :=
  addition_report (addition_train_epochs epochs addition_net0).

(** Materialize successive checkpoints so the examples train for a total of
    100 epochs, rather than restarting for 1, 10, 50, 100, and 100 epochs.
    [vm_compute] stores the computed parameters, not a suspended training call. *)
Time Definition addition_net1 : AdditionNet :=
  ltac:(let net := eval vm_compute in
    (addition_train_epochs 1 addition_net0) in exact net).

Time Eval vm_compute in addition_report addition_net1.

Time Definition addition_net10 : AdditionNet :=
  ltac:(let net := eval vm_compute in
    (addition_train_epochs 9 addition_net1) in exact net).

Time Eval vm_compute in addition_report addition_net10.

Time Definition addition_net50 : AdditionNet :=
  ltac:(let net := eval vm_compute in
    (addition_train_epochs 40 addition_net10) in exact net).

Time Eval vm_compute in addition_report addition_net50.

Time Definition addition_net100 : AdditionNet :=
  ltac:(let net := eval vm_compute in
    (addition_train_epochs 50 addition_net50) in exact net).

Time Eval vm_compute in addition_report addition_net100.

(** Compare exact reduced fractions with the original Taylor implementation,
    including negative inputs, non-decimal fractions, and zero terms. *)
Example addition_taylor_regression :
  let inputs := [-2; -1; -(1/3); 0; 1/7; 1; 2] in
  let orders := [0%nat; 1%nat; 2%nat; 10%nat; 12%nat] in
  map (fun x => map (Q_exp_taylor_fast x) orders) inputs =
  map (fun x => map (fun n => Q_exp_taylor x n 0 1 1) orders) inputs.
Proof. vm_compute. reflexivity. Qed.

(** Golden output from the original rational trainer, before optimization. *)
Example addition_ten_epoch_regression :
  addition_report addition_net10 =
    (0.01910, 0.01880,
     (1.09293, 1.12808, 1.14590, 1.13420, 1.15238, 1.22370)).
Proof. vm_compute. reflexivity. Qed.

Eval vm_compute in
  addition_predict addition_net100 0.12 0.34.

Eval vm_compute in
  addition_predict addition_net100 0.7 0.15.

Eval vm_compute in
  addition_predict addition_net100 0.01 0.99.

Eval vm_compute in
  addition_predict addition_net100 0.456 0.123.

Eval vm_compute in
  addition_predict addition_net100 1 1.

Eval vm_compute in
  addition_predict addition_net100 0.2 0.6.

Eval vm_compute in addition_net100.