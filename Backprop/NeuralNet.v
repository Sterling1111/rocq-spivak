From Backprop Require Export Calculus.
Open Scope R_scope.

(** A shape records layer widths. [Output] has no trainable parameters.
    For example, [Dense 2 3 (Dense 3 1 (Output 1))] is a 2 -> 3 -> 1 net. *)
Inductive Architecture : nat -> Type :=
| Output (n : nat) : Architecture n
| Dense (n m : nat) (rest : Architecture m) : Architecture n.

Fixpoint output_size {n} (s : Architecture n) : nat :=
  match s with Output n => n | Dense _ _ rest => output_size rest end.

Fixpoint Params {n} (s : Architecture n) : Type :=
  match s with
  | Output _ => unit
  | Dense n m rest => ((Mat m n * Vec m) * Params rest)%type
  end.

Record NeuralNet {n} (shape : Architecture n) := {
  parameters : Params shape
}.
Arguments parameters {n shape} _.

(** Matrix-vector multiplication is matrix multiplication by a column. *)
Definition mv {m n} (w : Mat m n) (a : Vec n) : Vec m :=
  fun j => fmatrix_mult w (fun k (_ : Fin.t 1) => a k) j Fin.F1.
Definition weighted_input {m n} (w : Mat m n) (b : Vec m) (a : Vec n) : Vec m :=
  fvector_add (mv w a) b.

(** Cache only the previous activation and the weighted input of each layer. *)
Fixpoint Cache {n} (s : Architecture n) : Type :=
  match s with
  | Output n => Vec n
  | Dense n m rest => ((Vec n * Vec m) * Cache rest)%type
  end.

Fixpoint forward_pass {n} (s : Architecture n) : Params s -> Vec n -> Cache s :=
  match s in Architecture n return Params s -> Vec n -> Cache s with
  | Output _ => fun _ a => a
  | Dense _ _ rest => fun p a =>
      let z := weighted_input (fst (fst p)) (snd (fst p)) a in
      ((a, z), forward_pass rest (snd p) (vmap sigma z))
  end.

Fixpoint output_activation {n} (s : Architecture n) : Cache s -> Vec (output_size s) :=
  match s return Cache s -> Vec (output_size s) with
  | Output _ => fun a => a
  | Dense _ _ rest => fun cache => output_activation rest (snd cache)
  end.

Definition C {n} (s : Architecture n) (p : Params s) (a : Vec n)
    (target : Vec (output_size s)) : R :=
  quadratic (output_activation s (forward_pass s p a)) target.

(** Return (derivative with respect to the input activation, parameter gradients).
    The recursive call walks to the output; the return path is the backward pass. *)
Fixpoint backward_pass {n} (s : Architecture n) :
    Params s -> Cache s -> Vec (output_size s) -> (Vec n * Params s) :=
  match s in Architecture n return Params s -> Cache s -> Vec (output_size s) -> (Vec n * Params s) with
  | Output _ => fun _ a target => ((fun j => a j - target j), tt)
  | Dense _ _ rest => fun p cache target =>
      let '(incoming, gradients) := backward_pass rest (snd p) (snd cache) target in
      let a := fst (fst cache) in
      let z := snd (fst cache) in
      let delta := hadamard incoming (vmap sigma' z) in
      (mv (fmatrix_transpose (fst (fst p))) delta,
       ((fun j k => a k * delta j, delta), gradients))
  end.

Definition backprop {n} (s : Architecture n) (p : Params s) a target :=
  backward_pass s p (forward_pass s p a) target.

(** All updates use gradients evaluated at the original parameters. *)
Fixpoint step {n} (s : Architecture n) : R -> Params s -> Params s -> Params s :=
  match s return R -> Params s -> Params s -> Params s with
  | Output _ => fun _ _ _ => tt
  | Dense _ _ rest => fun eta p g =>
      (((fun j k => fst (fst p) j k - eta * fst (fst g) j k),
        (fun j => snd (fst p) j - eta * snd (fst g) j)),
       step rest eta (snd p) (snd g))
  end.

Definition train_once {n s} (net : @NeuralNet n s) a target eta : NeuralNet s :=
  let cache := forward_pass s (parameters net) a in
  let gradients := snd (backward_pass s (parameters net) cache target) in
  {| parameters := step s eta (parameters net) gradients |}.

(** Expose the finite sum underneath the library's matrix multiplication. *)
Lemma library_dot n (a b : Vec n) : fvector_dot a b = dot a b.
Proof. unfold fvector_dot, dot, fvector_mul, fvector_map2.
  induction n; simpl; [reflexivity|rewrite IHn; reflexivity]. Qed.
Lemma mv_sum m n (w : Mat m n) a j : mv w a j = vsum (fun k => w j k * a k).
Proof. unfold mv, fmatrix_mult. apply library_dot. Qed.
Lemma weighted_input_sum m n (w : Mat m n) b a j :
  weighted_input w b a j = vsum (fun k => w j k * a k) + b j.
Proof. unfold weighted_input, fvector_add, fvector_map2. rewrite mv_sum. reflexivity. Qed.

(** Squared Euclidean norm on all weights and biases, expressed recursively. *)
Fixpoint pairing {n} (s : Architecture n) : Params s -> Params s -> R :=
  match s return Params s -> Params s -> R with
  | Output _ => fun _ _ => 0
  | Dense _ _ rest => fun p q =>
      vsum (fun j => dot (fst (fst p) j) (fst (fst q) j)) +
      dot (snd (fst p)) (snd (fst q)) + pairing rest (snd p) (snd q)
  end.
Definition gradient_norm_sq {n} (s : Architecture n) p a target :=
  let g := snd (backprop s p a target) in pairing s g g.
