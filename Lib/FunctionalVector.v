From Lib Require Import Imports.
From Lib Require Export Vector.
From Stdlib Require Vectors.Fin.

(** A coordinate function with exactly [n] valid indices. *)
Definition fvector (A : Type) (n : nat) := Fin.t n -> A.

Definition fvector_map {A B n} (f : A -> B) (v : fvector A n) : fvector B n :=
  fun i => f (v i).
Definition fvector_map2 {A B C n} (f : A -> B -> C)
    (v : fvector A n) (w : fvector B n) : fvector C n :=
  fun i => f (v i) (w i).
Definition fvector_const {A n} (x : A) : fvector A n := fun _ => x.
Definition fvector_add {A n} `{Add A} : fvector A n -> fvector A n -> fvector A n :=
  fvector_map2 add.
Definition fvector_mul {A n} `{Mul A} : fvector A n -> fvector A n -> fvector A n :=
  fvector_map2 mul.
Definition fvector_scale {S A n} `{Scale S A} (s : S) : fvector A n -> fvector A n :=
  fvector_map (scale s).

(** Increasing coordinate order, with the same right association as [vector_fold]. *)
Fixpoint fvector_fold {A B n} (f : A -> B -> B) (b : B) : fvector A n -> B :=
  match n return fvector A n -> B with
  | 0 => fun _ => b
  | S k => fun v => f (v Fin.F1) (fvector_fold f b (fun i : Fin.t k => v (Fin.FS i)))
  end.

Definition fvector_dot {A n} `{Add A} `{Mul A} `{Zero A}
    (v w : fvector A n) : A := fvector_fold add zero (fvector_mul v w).
Definition fvector_norm {n} (v : fvector R n) : R := sqrt (fvector_dot v v).
Definition fvector_rel {A B n} (P : A -> B -> Prop)
    (v : fvector A n) (w : fvector B n) : Prop := forall i, P (v i) (w i).

Lemma fvector_ext {A n} (v w : fvector A n) :
  (forall i, v i = w i) -> v = w.
Proof. apply functional_extensionality. Qed.

(** Internal list tabulation and total lookup; neither requires a default element. *)
Fixpoint function_list {A n} : fvector A n -> list A :=
  match n return fvector A n -> list A with
  | 0 => fun _ => []
  | S k => fun v => v Fin.F1 :: function_list (fun i : Fin.t k => v (Fin.FS i))
  end.

Fixpoint list_function {A} (l : list A) : fvector A (List.length l) :=
  match l return fvector A (List.length l) with
  | [] => fun i => Fin.case0 (fun _ => A) i
  | x :: xs => fun i => Fin.caseS' i (fun _ => A) x (list_function xs)
  end.

Lemma function_list_length {A n} (v : fvector A n) : List.length (function_list v) = n.
Proof. induction n; simpl; [reflexivity | now rewrite IHn]. Qed.

Definition function_to_vector {A n} (v : fvector A n) : vector A n :=
  mk_vector (function_list v) (function_list_length v).

(** [Fin.cast] computes from the index and list length, even when the stored
    length proof is opaque. Transporting the whole function along that proof
    would prevent concrete lookup from reducing. *)
Definition vector_to_function {A n} (v : vector A n) : fvector A n :=
  fun i => list_function (vlist v) (Fin.cast i (eq_sym (vlist_length A n v))).

Lemma fin_cast_refl {n} (i : Fin.t n) : Fin.cast i eq_refl = i.
Proof. induction i; simpl; [reflexivity | now f_equal]. Qed.

Lemma list_function_nth {A} (l : list A) (i : Fin.t (List.length l)) (d : A) :
  list_function l i = List.nth (proj1_sig (Fin.to_nat i)) l d.
Proof.
  induction l as [|x xs IH].
  - exact (Fin.case0 (fun i => list_function [] i = List.nth (proj1_sig (Fin.to_nat i)) [] d) i).
  - revert i. intros i. refine (Fin.caseS' i
      (fun j => list_function (x :: xs) j = List.nth (proj1_sig (Fin.to_nat j)) (x :: xs) d) _ _).
    + reflexivity.
    + intros j. simpl. destruct (Fin.to_nat j) eqn:E. simpl.
      exact (eq_trans (IH j)
        (f_equal (fun k => List.nth k xs d) (f_equal (@proj1_sig nat _) E))).
Qed.

Lemma vector_to_function_nth {A n} (v : vector A n) (i : Fin.t n) (d : A) :
  vector_to_function v i = List.nth (proj1_sig (Fin.to_nat i)) (vlist v) d.
Proof.
  destruct v as [l H]. subst n. unfold vector_to_function. simpl.
  rewrite fin_cast_refl. apply list_function_nth.
Qed.

Lemma function_list_nth {A n} (v : fvector A n) (i : Fin.t n) (d : A) :
  List.nth (proj1_sig (Fin.to_nat i)) (function_list v) d = v i.
Proof.
  induction i as [n|n i IH]; simpl.
  - reflexivity.
  - destruct (Fin.to_nat i). simpl.
    exact (IH (fun j => v (Fin.FS j))).
Qed.

Lemma vector_function_roundtrip {A n} (v : fvector A n) :
  vector_to_function (function_to_vector v) = v.
Proof.
  apply fvector_ext. intros i. rewrite (vector_to_function_nth _ i (v i)).
  apply function_list_nth.
Qed.

Lemma function_list_list_function {A} (l : list A) :
  function_list (list_function l) = l.
Proof. induction l; simpl; [reflexivity | f_equal; exact IHl]. Qed.

Lemma function_vector_roundtrip {A n} (v : vector A n) :
  function_to_vector (vector_to_function v) = v.
Proof.
  destruct v as [l H]. subst n. apply vector_eq.
  change (function_list (vector_to_function (mk_vector l eq_refl)) = l).
  transitivity (function_list (list_function l)).
  - f_equal. apply fvector_ext. intros i.
    unfold vector_to_function. simpl. now rewrite fin_cast_refl.
  - apply function_list_list_function.
Qed.

Lemma vector_function_eq_iff {A n} (v w : vector A n) :
  v = w <-> forall i, vector_to_function v i = vector_to_function w i.
Proof.
  split; [intros ->; reflexivity | intros H].
  rewrite <- (function_vector_roundtrip v), <- (function_vector_roundtrip w).
  f_equal. apply fvector_ext. exact H.
Qed.

Lemma function_list_map {A B n} (f : A -> B) (v : fvector A n) :
  function_list (fvector_map f v) = List.map f (function_list v).
Proof. induction n; simpl; [reflexivity | now rewrite <- IHn]. Qed.

Lemma function_list_map2 {A B C n} (f : A -> B -> C)
    (v : fvector A n) (w : fvector B n) :
  function_list (fvector_map2 f v w) =
  List.map (fun p => f (fst p) (snd p)) (List.combine (function_list v) (function_list w)).
Proof. induction n; simpl; [reflexivity | now rewrite <- IHn]. Qed.

Lemma function_to_vector_map {A B n} (f : A -> B) (v : fvector A n) :
  function_to_vector (fvector_map f v) = vector_map f (function_to_vector v).
Proof. apply vector_eq. simpl. apply function_list_map. Qed.

Lemma function_to_vector_map2 {A B C n} (f : A -> B -> C)
    (v : fvector A n) (w : fvector B n) :
  function_to_vector (fvector_map2 f v w) =
  vector_map2 f (function_to_vector v) (function_to_vector w).
Proof. apply vector_eq. simpl. apply function_list_map2. Qed.

Lemma vector_to_function_map {A B n} (f : A -> B) (v : vector A n) :
  vector_to_function (vector_map f v) = fvector_map f (vector_to_function v).
Proof.
  rewrite <- (vector_function_roundtrip (fvector_map f (vector_to_function v))).
  rewrite function_to_vector_map, function_vector_roundtrip. reflexivity.
Qed.

Lemma vector_to_function_map2 {A B C n} (f : A -> B -> C)
    (v : vector A n) (w : vector B n) :
  vector_to_function (vector_map2 f v w) =
  fvector_map2 f (vector_to_function v) (vector_to_function w).
Proof.
  rewrite <- (vector_function_roundtrip (fvector_map2 f (vector_to_function v) (vector_to_function w))).
  rewrite function_to_vector_map2, !function_vector_roundtrip. reflexivity.
Qed.

Lemma function_list_const {A n} (x : A) :
  function_list (@fvector_const A n x) = List.repeat x n.
Proof. induction n; simpl; [reflexivity | f_equal; exact IHn]. Qed.

Lemma vector_to_function_zero {A n} `{Zero A} :
  vector_to_function (zero : vector A n) = fvector_const zero.
Proof.
  rewrite <- (vector_function_roundtrip (@fvector_const A n zero)).
  f_equal. apply vector_eq. simpl. symmetry. apply function_list_const.
Qed.

Lemma vector_to_function_add {A n} `{Add A} (v w : vector A n) :
  vector_to_function (add v w) = fvector_add (vector_to_function v) (vector_to_function w).
Proof. apply vector_to_function_map2. Qed.

Lemma vector_to_function_mul {A n} `{Mul A} (v w : vector A n) :
  vector_to_function (mul v w) = fvector_mul (vector_to_function v) (vector_to_function w).
Proof. apply vector_to_function_map2. Qed.

Lemma vector_to_function_scale {S A n} `{Scale S A} (s : S) (v : vector A n) :
  vector_to_function (scale s v) = fvector_scale s (vector_to_function v).
Proof. apply vector_to_function_map. Qed.

Lemma function_list_fold {A B n} (f : A -> B -> B) (b : B) (v : fvector A n) :
  List.fold_right f b (function_list v) = fvector_fold f b v.
Proof. induction n; simpl; [reflexivity | now rewrite IHn]. Qed.

Lemma vector_to_function_fold {A B n} (f : A -> B -> B) (b : B) (v : vector A n) :
  vector_fold f b v = fvector_fold f b (vector_to_function v).
Proof.
  rewrite <- function_list_fold. change (vector_fold f b v =
    vector_fold f b (function_to_vector (vector_to_function v))).
  now rewrite function_vector_roundtrip.
Qed.

Lemma vector_to_function_dot {A n} `{Add A} `{Mul A} `{Zero A} (v w : vector A n) :
  vector_dot v w = fvector_dot (vector_to_function v) (vector_to_function w).
Proof.
  unfold vector_dot, fvector_dot, fvector_mul.
  rewrite vector_to_function_fold, vector_to_function_map2. reflexivity.
Qed.

Lemma vector_to_function_norm {n} (v : vector R n) :
  vector_norm v = fvector_norm (vector_to_function v).
Proof. unfold vector_norm, fvector_norm. now rewrite vector_to_function_dot. Qed.

Lemma function_list_rel {A B n} (P : A -> B -> Prop)
    (v : fvector A n) (w : fvector B n) :
  List.Forall2 P (function_list v) (function_list w) <-> fvector_rel P v w.
Proof.
  induction n as [|n IH]; simpl.
  - split; intros H; [intros i; exact (Fin.case0 (fun _ => P (v i) (w i)) i) | constructor].
  - split.
    + intros H. inversion H; subst. intros i. refine (Fin.caseS' i (fun j => P (v j) (w j)) _ _).
      * assumption.
      * apply (proj1 (IH _ _)). assumption.
    + intros H. constructor.
      * apply H.
      * apply (proj2 (IH _ _)). intros i. apply H.
Qed.

Lemma vector_to_function_rel {A B n} (P : A -> B -> Prop)
    (v : vector A n) (w : vector B n) :
  List.Forall2 P (vlist v) (vlist w) <->
  fvector_rel P (vector_to_function v) (vector_to_function w).
Proof.
  rewrite <- function_list_rel.
  change (List.Forall2 P (vlist v) (vlist w) <->
    List.Forall2 P (vlist (function_to_vector (vector_to_function v)))
      (vlist (function_to_vector (vector_to_function w)))).
  now rewrite !function_vector_roundtrip.
Qed.

Lemma vector_to_function_le {A n} `{Le A} (v w : vector A n) :
  le_op v w <-> fvector_rel le_op (vector_to_function v) (vector_to_function w).
Proof. apply vector_to_function_rel. Qed.

Lemma vector_to_function_lt {A n} `{Lt A} (v w : vector A n) :
  lt_op v w <-> fvector_rel lt_op (vector_to_function v) (vector_to_function w).
Proof. apply vector_to_function_rel. Qed.

Lemma vector_to_function_ge {A n} `{Ge A} (v w : vector A n) :
  ge_op v w <-> fvector_rel ge_op (vector_to_function v) (vector_to_function w).
Proof. apply vector_to_function_rel. Qed.

Lemma vector_to_function_gt {A n} `{Gt A} (v w : vector A n) :
  gt_op v w <-> fvector_rel gt_op (vector_to_function v) (vector_to_function w).
Proof. apply vector_to_function_rel. Qed.

Lemma function_to_vector_dot {A n} `{Add A} `{Mul A} `{Zero A} (v w : fvector A n) :
  vector_dot (function_to_vector v) (function_to_vector w) = fvector_dot v w.
Proof. rewrite vector_to_function_dot, !vector_function_roundtrip. reflexivity. Qed.

Module FunctionalVectorNotations.
  Declare Scope FV_scope.
  Delimit Scope FV_scope with FV.
  Notation "v + w" := (fvector_add v w) (at level 50, left associativity) : FV_scope.
  Notation "v ⊙ w" := (fvector_mul v w) (at level 40, left associativity) : FV_scope.
  Notation "v · w" := (fvector_dot v w) (at level 40, left associativity) : FV_scope.
  Notation "s * v" := (fvector_scale s v) (at level 40, left associativity) : FV_scope.
  Notation "∥ v ∥" := (fvector_norm v) (at level 40) : FV_scope.
  Notation "'0'" := (fvector_const zero) : FV_scope.
  Notation "v <= w" := (fvector_rel le_op v w) (at level 70, no associativity) : FV_scope.
  Notation "v < w" := (fvector_rel lt_op v w) (at level 70, no associativity) : FV_scope.
  Notation "v >= w" := (fvector_rel ge_op v w) (at level 70, no associativity) : FV_scope.
  Notation "v > w" := (fvector_rel gt_op v w) (at level 70, no associativity) : FV_scope.
End FunctionalVectorNotations.

(** Algebra can now be proved coordinatewise and transferred to lists. *)
Lemma fvector_add_comm_R {n} (v w : fvector R n) : fvector_add v w = fvector_add w v.
Proof. apply fvector_ext. intros i. apply Rplus_comm. Qed.

Lemma fvector_add_assoc_R {n} (u v w : fvector R n) :
  fvector_add (fvector_add u v) w = fvector_add u (fvector_add v w).
Proof. apply fvector_ext. intros i. apply Rplus_assoc. Qed.

(** Rewrite functional expressions to the list algebra when a proof needs
    bilinearity, rather than just coordinatewise scalar arithmetic. *)
Lemma fvector_list_ext {A n} (v w : fvector A n) :
  function_to_vector v = function_to_vector w -> v = w.
Proof.
  intros H. rewrite <- (vector_function_roundtrip v), <- (vector_function_roundtrip w).
  now rewrite H.
Qed.

Lemma function_to_vector_zero {A n} `{Zero A} :
  function_to_vector (@fvector_const A n zero) = zero.
Proof. apply vector_eq. apply function_list_const. Qed.

Lemma function_to_vector_add {A n} `{Add A} (v w : fvector A n) :
  function_to_vector (fvector_add v w) = add (function_to_vector v) (function_to_vector w).
Proof. apply function_to_vector_map2. Qed.

Lemma function_to_vector_mul {A n} `{Mul A} (v w : fvector A n) :
  function_to_vector (fvector_mul v w) = mul (function_to_vector v) (function_to_vector w).
Proof. apply function_to_vector_map2. Qed.

Lemma function_to_vector_scale {S A n} `{Scale S A} (s : S) (v : fvector A n) :
  function_to_vector (fvector_scale s v) = scale s (function_to_vector v).
Proof. apply function_to_vector_map. Qed.

Lemma function_to_vector_norm {n} (v : fvector R n) :
  vector_norm (function_to_vector v) = fvector_norm v.
Proof. unfold vector_norm, fvector_norm. now rewrite function_to_vector_dot. Qed.

Create HintDb functional_vector_lists.
#[export] Hint Rewrite @function_vector_roundtrip @vector_function_roundtrip
  @function_to_vector_zero @function_to_vector_add @function_to_vector_mul
  @function_to_vector_scale @function_to_vector_map @function_to_vector_map2 : functional_vector_lists.
#[export] Hint Rewrite <- @function_to_vector_dot @function_to_vector_norm : functional_vector_lists.

Ltac functional_vector_scalar :=
  cbv beta iota zeta delta [fvector_map fvector_map2 fvector_const fvector_add
    fvector_mul fvector_scale]; linear_scalar.

Ltac vector_solver_extension ::=
  first
    [ solve [apply fvector_ext; let i := fresh "i" in intros i; functional_vector_scalar]
    | solve [apply fvector_list_ext; autorewrite with functional_vector_lists; solve_vec]
    | progress autorewrite with functional_vector_lists; solve_vec ].
