From Lib Require Import Imports.
From Lib Require Export Matrix FunctionalVector.

(** Rows and columns are indexed independently, including zero dimensions. *)
Definition fmatrix (A : Type) (m n : nat) := Fin.t m -> Fin.t n -> A.

Definition fmatrix_row {A m n} (M : fmatrix A m n) (i : Fin.t m) : fvector A n := M i.
Definition fmatrix_col {A m n} (M : fmatrix A m n) (j : Fin.t n) : fvector A m :=
  fun i => M i j.
Definition fmatrix_const {A m n} (x : A) : fmatrix A m n := fun _ _ => x.
Definition fmatrix_add {A m n} `{Add A} (M N : fmatrix A m n) : fmatrix A m n :=
  fun i j => add (M i j) (N i j).
Definition fmatrix_mul {A m n} `{Mul A} (M N : fmatrix A m n) : fmatrix A m n :=
  fun i j => mul (M i j) (N i j).
Definition fmatrix_scale {S A m n} `{Scale S A} (s : S) (M : fmatrix A m n) : fmatrix A m n :=
  fun i j => scale s (M i j).
Definition fmatrix_transpose {A m n} (M : fmatrix A m n) : fmatrix A n m :=
  fun j i => M i j.
Definition fmatrix_mult {A m n p} `{Add A} `{Mul A} `{Zero A}
    (M : fmatrix A m n) (N : fmatrix A n p) : fmatrix A m p :=
  fun i j => fvector_dot (fmatrix_row M i) (fmatrix_col N j).
Definition fmatrix_identity {A n} `{Zero A} `{One A} : fmatrix A n n :=
  fun i j => if Nat.eqb (proj1_sig (Fin.to_nat i)) (proj1_sig (Fin.to_nat j)) then one else zero.
Definition fmatrix_rel {A B m n} (P : A -> B -> Prop)
    (M : fmatrix A m n) (N : fmatrix B m n) : Prop := forall i j, P (M i j) (N i j).

Lemma fmatrix_ext {A m n} (M N : fmatrix A m n) :
  (forall i j, M i j = N i j) -> M = N.
Proof. intros H. apply fvector_ext. intros i. apply fvector_ext. apply H. Qed.

Definition matrix_to_function {A m n} (M : matrix A m n) : fmatrix A m n :=
  fun i => vector_to_function (vector_to_function M i).
Definition function_to_matrix {A m n} (M : fmatrix A m n) : matrix A m n :=
  function_to_vector (fun i => function_to_vector (M i)).

Lemma matrix_function_roundtrip {A m n} (M : fmatrix A m n) :
  matrix_to_function (function_to_matrix M) = M.
Proof.
  unfold matrix_to_function, function_to_matrix.
  rewrite vector_function_roundtrip. apply fvector_ext. intros i.
  apply vector_function_roundtrip.
Qed.

Lemma function_matrix_roundtrip {A m n} (M : matrix A m n) :
  function_to_matrix (matrix_to_function M) = M.
Proof.
  unfold matrix_to_function, function_to_matrix.
  transitivity (function_to_vector (vector_to_function M)).
  - f_equal. apply fvector_ext. intros i. apply function_vector_roundtrip.
  - apply function_vector_roundtrip.
Qed.

Lemma matrix_function_eq_iff {A m n} (M N : matrix A m n) :
  M = N <-> forall i j, matrix_to_function M i j = matrix_to_function N i j.
Proof.
  split; [intros ->; reflexivity | intros H].
  rewrite <- (function_matrix_roundtrip M), <- (function_matrix_roundtrip N).
  f_equal. apply fmatrix_ext. exact H.
Qed.

(** Compatibility with the existing natural-number accessors. *)
Lemma vector_to_function_init {A n} (f : nat -> A) (i : Fin.t n) :
  vector_to_function (@vector_init A n f) i = f (proj1_sig (Fin.to_nat i)).
Proof.
  rewrite (vector_to_function_nth _ i (f (proj1_sig (Fin.to_nat i)))).
  apply vector_init_nth. exact (proj2_sig (Fin.to_nat i)).
Qed.

Lemma matrix_to_function_row {A m n} `{Zero A} (M : matrix A m n) (i : Fin.t m) :
  vector_to_function (get_row M (proj1_sig (Fin.to_nat i))) =
  fmatrix_row (matrix_to_function M) i.
Proof.
  unfold fmatrix_row, matrix_to_function, get_row, vector_nth.
  rewrite (vector_to_function_nth M i zero). reflexivity.
Qed.

Lemma matrix_to_function_col {A m n} `{Zero A} (M : matrix A m n) (j : Fin.t n) :
  vector_to_function (get_col M (proj1_sig (Fin.to_nat j))) =
  fmatrix_col (matrix_to_function M) j.
Proof.
  unfold get_col. rewrite vector_to_function_map. apply fvector_ext. intros i.
  unfold fvector_map, fmatrix_col, matrix_to_function, vector_nth.
  symmetry. apply vector_to_function_nth.
Qed.

Lemma matrix_to_function_entry {A m n} (M : matrix A m n) (i : Fin.t m) (j : Fin.t n) (d : A) :
  matrix_to_function M i j =
  Matrix.vector_nth (Matrix.vector_nth M (proj1_sig (Fin.to_nat i)) (vector_const d n))
    (proj1_sig (Fin.to_nat j)) d.
Proof.
  unfold matrix_to_function, Matrix.vector_nth.
  rewrite (vector_to_function_nth M i (vector_const d n)).
  apply vector_to_function_nth.
Qed.

Lemma matrix_to_function_nth {m n} (M : matrix R m n) (i : Fin.t m) (j : Fin.t n) :
  matrix_to_function M i j = mat_nth M (proj1_sig (Fin.to_nat i)) (proj1_sig (Fin.to_nat j)).
Proof. apply matrix_to_function_entry. Qed.

Lemma matrix_to_function_zero {A m n} `{Zero A} :
  matrix_to_function (zero : matrix A m n) = fmatrix_const zero.
Proof.
  unfold matrix_to_function. rewrite (@vector_to_function_zero (vector A n) m _).
  apply fmatrix_ext. intros i j. unfold fvector_const, fmatrix_const.
  rewrite vector_to_function_zero. reflexivity.
Qed.

Lemma matrix_to_function_add {A m n} `{Add A} (M N : matrix A m n) :
  matrix_to_function (add M N) = fmatrix_add (matrix_to_function M) (matrix_to_function N).
Proof.
  unfold matrix_to_function. rewrite (@vector_to_function_add (vector A n) m _ M N).
  apply fmatrix_ext. intros i j. unfold fvector_add, fvector_map2.
  rewrite vector_to_function_add. reflexivity.
Qed.

Lemma matrix_to_function_mul {A m n} `{Mul A} (M N : matrix A m n) :
  matrix_to_function (mul M N) = fmatrix_mul (matrix_to_function M) (matrix_to_function N).
Proof.
  unfold matrix_to_function. rewrite (@vector_to_function_mul (vector A n) m _ M N).
  apply fmatrix_ext. intros i j. unfold fvector_mul, fvector_map2.
  rewrite vector_to_function_mul. reflexivity.
Qed.

Lemma matrix_to_function_scale {S A m n} `{Scale S A} (s : S) (M : matrix A m n) :
  matrix_to_function (scale s M) = fmatrix_scale s (matrix_to_function M).
Proof.
  unfold matrix_to_function. rewrite (@vector_to_function_scale S (vector A n) m _ s M).
  apply fmatrix_ext. intros i j. unfold fvector_scale, fvector_map.
  rewrite vector_to_function_scale. reflexivity.
Qed.

Lemma matrix_to_function_transpose {A m n} (M : matrix A m n) :
  matrix_to_function (matrix_transpose M) = fmatrix_transpose (matrix_to_function M).
Proof.
  apply fmatrix_ext. intros i j. unfold fmatrix_transpose.
  pose (d := matrix_to_function M j i).
  rewrite (matrix_to_function_entry (matrix_transpose M) i j d),
    (matrix_to_function_entry M j i d).
  apply matrix_transpose_nth_default; apply proj2_sig.
Qed.

Lemma matrix_to_function_mult {A m n p} `{Add A} `{Mul A} `{Zero A}
    (M : matrix A m n) (N : matrix A n p) :
  matrix_to_function (matrix_mult M N) = fmatrix_mult (matrix_to_function M) (matrix_to_function N).
Proof.
  apply fmatrix_ext. intros i j. unfold matrix_to_function, matrix_mult.
  rewrite !vector_to_function_init, vector_to_function_dot.
  rewrite matrix_to_function_row, matrix_to_function_col. reflexivity.
Qed.

Lemma matrix_to_function_identity {A n} `{Zero A} `{One A} :
  matrix_to_function (@identity_matrix A n _ _) = fmatrix_identity.
Proof.
  apply fmatrix_ext. intros i j. unfold matrix_to_function, identity_matrix.
  rewrite !vector_to_function_init. reflexivity.
Qed.

Lemma matrix_to_function_rel {A B m n} (P : A -> B -> Prop)
    (M : matrix A m n) (N : matrix B m n) :
  List.Forall2 (fun v w => List.Forall2 P (vlist v) (vlist w)) (vlist M) (vlist N) <->
  fmatrix_rel P (matrix_to_function M) (matrix_to_function N).
Proof.
  rewrite vector_to_function_rel. unfold fvector_rel, fmatrix_rel, matrix_to_function.
  split; intros H i.
  - apply (proj1 (vector_to_function_rel P _ _)). apply H.
  - apply (proj2 (vector_to_function_rel P _ _)). exact (H i).
Qed.

Lemma matrix_to_function_le {A m n} `{Le A} (M N : matrix A m n) :
  le_op M N <-> fmatrix_rel le_op (matrix_to_function M) (matrix_to_function N).
Proof. apply matrix_to_function_rel. Qed.

Lemma matrix_to_function_lt {A m n} `{Lt A} (M N : matrix A m n) :
  lt_op M N <-> fmatrix_rel lt_op (matrix_to_function M) (matrix_to_function N).
Proof. apply matrix_to_function_rel. Qed.

Lemma matrix_to_function_ge {A m n} `{Ge A} (M N : matrix A m n) :
  ge_op M N <-> fmatrix_rel ge_op (matrix_to_function M) (matrix_to_function N).
Proof. apply matrix_to_function_rel. Qed.

Lemma matrix_to_function_gt {A m n} `{Gt A} (M N : matrix A m n) :
  gt_op M N <-> fmatrix_rel gt_op (matrix_to_function M) (matrix_to_function N).
Proof. apply matrix_to_function_rel. Qed.

(** Reverse-direction rewrite rules for displaying functional calculations as lists. *)
Lemma function_to_matrix_add {A m n} `{Add A} (M N : fmatrix A m n) :
  function_to_matrix (fmatrix_add M N) = add (function_to_matrix M) (function_to_matrix N).
Proof.
  apply matrix_function_eq_iff. intros i j.
  rewrite matrix_to_function_add, !matrix_function_roundtrip. reflexivity.
Qed.

Lemma function_to_matrix_mul {A m n} `{Mul A} (M N : fmatrix A m n) :
  function_to_matrix (fmatrix_mul M N) = mul (function_to_matrix M) (function_to_matrix N).
Proof.
  apply matrix_function_eq_iff. intros i j.
  rewrite matrix_to_function_mul, !matrix_function_roundtrip. reflexivity.
Qed.

Lemma function_to_matrix_scale {S A m n} `{Scale S A} (s : S) (M : fmatrix A m n) :
  function_to_matrix (fmatrix_scale s M) = scale s (function_to_matrix M).
Proof.
  apply matrix_function_eq_iff. intros i j.
  rewrite matrix_to_function_scale, !matrix_function_roundtrip. reflexivity.
Qed.

Lemma function_to_matrix_transpose {A m n} (M : fmatrix A m n) :
  function_to_matrix (fmatrix_transpose M) = matrix_transpose (function_to_matrix M).
Proof.
  apply matrix_function_eq_iff. intros i j.
  rewrite matrix_to_function_transpose, !matrix_function_roundtrip. reflexivity.
Qed.

Lemma function_to_matrix_mult {A m n p} `{Add A} `{Mul A} `{Zero A}
    (M : fmatrix A m n) (N : fmatrix A n p) :
  function_to_matrix (fmatrix_mult M N) = matrix_mult (function_to_matrix M) (function_to_matrix N).
Proof.
  apply matrix_function_eq_iff. intros i j.
  rewrite matrix_to_function_mult, !matrix_function_roundtrip. reflexivity.
Qed.

Definition fvector_to_col {A n} (v : fvector A n) : fmatrix A n 1 := fun i _ => v i.
Definition fmatrix_to_scalar {A} (M : fmatrix A 1 1) : A := M Fin.F1 Fin.F1.

Lemma vector_to_function_col {A n} `{Zero A} (v : vector A n) :
  matrix_to_function (vec_to_col v) = fvector_to_col (vector_to_function v).
Proof.
  apply fmatrix_ext. intros i j. unfold matrix_to_function, vec_to_col.
  rewrite !vector_to_function_init. unfold fvector_to_col, vector_nth.
  symmetry. apply vector_to_function_nth.
Qed.

Lemma matrix_to_function_scalar {A} `{Zero A} (M : matrix A 1 1) :
  to_scalar M = fmatrix_to_scalar (matrix_to_function M).
Proof.
  unfold to_scalar, fmatrix_to_scalar, matrix_to_function, vector_nth.
  rewrite (vector_to_function_nth M Fin.F1 zero).
  symmetry. apply vector_to_function_nth.
Qed.

Module FunctionalMatrixNotations.
  Declare Scope FM_scope.
  Delimit Scope FM_scope with FM.
  Notation "M + N" := (fmatrix_add M N) (at level 50, left associativity) : FM_scope.
  Notation "M ⊙ N" := (fmatrix_mul M N) (at level 40, left associativity) : FM_scope.
  Notation "M × N" := (fmatrix_mult M N) (at level 40, left associativity) : FM_scope.
  Notation "s * M" := (fmatrix_scale s M) (at level 40, left associativity) : FM_scope.
  Notation "M ^T" := (fmatrix_transpose M) (at level 30, format "M ^T") : FM_scope.
  Notation "'I'" := fmatrix_identity (at level 0) : FM_scope.
  Notation "'0'" := (fmatrix_const zero) : FM_scope.
  Notation "M <= N" := (fmatrix_rel le_op M N) (at level 70, no associativity) : FM_scope.
  Notation "M < N" := (fmatrix_rel lt_op M N) (at level 70, no associativity) : FM_scope.
  Notation "M >= N" := (fmatrix_rel ge_op M N) (at level 70, no associativity) : FM_scope.
  Notation "M > N" := (fmatrix_rel gt_op M N) (at level 70, no associativity) : FM_scope.
End FunctionalMatrixNotations.

(** These identities need no list induction, default entries, or dimension hypotheses. *)
Lemma fmatrix_transpose_involutive {A m n} (M : fmatrix A m n) :
  fmatrix_transpose (fmatrix_transpose M) = M.
Proof. reflexivity. Qed.

Lemma matrix_transpose_involutive {A m n} (M : matrix A m n) :
  matrix_transpose (matrix_transpose M) = M.
Proof.
  apply matrix_function_eq_iff. intros i j.
  rewrite !matrix_to_function_transpose.
  rewrite fmatrix_transpose_involutive.
  reflexivity.
Qed.

#[export] Hint Rewrite @matrix_transpose_involutive : matrix_algebra.

Lemma fmatrix_assoc_R {m n p q} (M : fmatrix R m n) (N : fmatrix R n p) (P : fmatrix R p q) :
  fmatrix_mult (fmatrix_mult M N) P = fmatrix_mult M (fmatrix_mult N P).
Proof.
  rewrite <- (matrix_function_roundtrip M), <- (matrix_function_roundtrip N),
    <- (matrix_function_roundtrip P).
  rewrite <- !matrix_to_function_mult, matrix_assoc. reflexivity.
Qed.

Lemma fmatrix_list_ext {A m n} (M N : fmatrix A m n) :
  function_to_matrix M = function_to_matrix N -> M = N.
Proof.
  intros H. rewrite <- (matrix_function_roundtrip M), <- (matrix_function_roundtrip N).
  now rewrite H.
Qed.

Lemma function_to_matrix_zero {A m n} `{Zero A} :
  function_to_matrix (@fmatrix_const A m n zero) = zero.
Proof.
  apply matrix_function_eq_iff. intros i j.
  rewrite matrix_function_roundtrip, matrix_to_function_zero. reflexivity.
Qed.

Lemma function_to_matrix_identity {A n} `{Zero A} `{One A} :
  function_to_matrix (@fmatrix_identity A n _ _) = identity_matrix.
Proof.
  apply matrix_function_eq_iff. intros i j.
  rewrite matrix_function_roundtrip, matrix_to_function_identity. reflexivity.
Qed.

Lemma function_to_matrix_col {A n} `{Zero A} (v : fvector A n) :
  function_to_matrix (fvector_to_col v) = vec_to_col (function_to_vector v).
Proof.
  apply matrix_function_eq_iff. intros i j.
  rewrite matrix_function_roundtrip, vector_to_function_col, vector_function_roundtrip. reflexivity.
Qed.

Create HintDb functional_matrix_lists.
#[export] Hint Rewrite @function_matrix_roundtrip @matrix_function_roundtrip
  @function_to_matrix_zero @function_to_matrix_identity @function_to_matrix_add
  @function_to_matrix_mul @function_to_matrix_scale @function_to_matrix_transpose
  @function_to_matrix_mult @function_to_matrix_col : functional_matrix_lists.

Ltac functional_matrix_to_lists :=
  repeat first
    [ progress autorewrite with functional_matrix_lists functional_vector_lists
    | rewrite function_to_matrix_transpose
    | rewrite function_to_matrix_col ].

Ltac matrix_solver_extension ::=
  first
    [ solve [apply fmatrix_ext; let i := fresh "i" in let j := fresh "j" in intros i j;
        cbv beta iota zeta delta [fmatrix_add fmatrix_mul fmatrix_scale fmatrix_const
          fmatrix_transpose fmatrix_row fmatrix_col fvector_to_col];
        functional_vector_scalar]
    | solve [apply fmatrix_list_ext;
        functional_matrix_to_lists; solve_mat]
    | progress functional_matrix_to_lists; solve_mat ].
