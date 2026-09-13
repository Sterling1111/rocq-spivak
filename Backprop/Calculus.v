From Lib Require Export Imports FunctionalMatrix Derivative Exponential.
From Lib Require Import Functions Limit.
Import FunctionNotations DerivativeNotations.
Open Scope R_scope.

(** A small bridge to the project's epsilon/delta derivative. [D f x d]
    means that the derivative of [f] at [x] is the real number [d]. *)
Definition D (f : R -> R) (x d : R) := derivative_at f (fun _ => d) x.

Lemma D_const c x : D (fun _ => c) x 0.
Proof. apply derivative_at_const. Qed.
Lemma D_id x : D (fun t => t) x 1.
Proof. apply derivative_at_id. Qed.
Lemma D_ext f g x d : (forall t, f t = g t) -> D f x d -> D g x d.
Proof. apply derivative_at_eq'. Qed.
Lemma D_plus f g x df dg : D f x df -> D g x dg ->
  D (fun t => f t + g t) x (df + dg).
Proof. intros Hf Hg. exact (derivative_at_plus _ _ _ _ _ Hf Hg). Qed.
Lemma D_minus f g x df dg : D f x df -> D g x dg ->
  D (fun t => f t - g t) x (df - dg).
Proof. intros Hf Hg. exact (derivative_at_minus _ _ _ _ _ Hf Hg). Qed.
Lemma D_mult f g x df dg : D f x df -> D g x dg ->
  D (fun t => f t * g t) x (df * g x + f x * dg).
Proof. intros Hf Hg. exact (derivative_at_mult _ _ _ _ _ Hf Hg). Qed.
Lemma D_comp f g x df dg : D f x df -> D g (f x) dg ->
  D (fun t => g (f t)) x (dg * df).
Proof. intros Hf Hg. exact (derivative_at_comp _ _ _ _ _ Hf Hg). Qed.

Definition Vec n := fvector R n.
Definition Mat m n := fmatrix R m n.
Fixpoint vsum {n} : Vec n -> R :=
  match n with
  | O => fun _ => 0
  | S k => fun v => v Fin.F1 + vsum (fun i : Fin.t k => v (Fin.FS i))
  end.
Definition dot {n} (u v : Vec n) := vsum (fun i => u i * v i).
Definition hadamard {n} (u v : Vec n) : Vec n := fun i => u i * v i.
Definition vmap {n} (f : R -> R) (v : Vec n) : Vec n := fun i => f (v i).
Definition transpose_mul {m n} (w : Mat m n) (v : Vec m) : Vec n :=
  fun k => vsum (fun j => w j k * v j).

Lemma vsum_ext n (f g : Vec n) : (forall i, f i = g i) -> vsum f = vsum g.
Proof. intro H. now replace f with g by (apply functional_extensionality; auto). Qed.
Lemma vsum_zero n : @vsum n (fun _ => 0) = 0.
Proof. induction n; simpl; lra. Qed.
Lemma vsum_plus n (f g : Vec n) :
  vsum (fun i => f i + g i) = vsum f + vsum g.
Proof. induction n; simpl; [ring|rewrite IHn; ring]. Qed.
Lemma vsum_scale n c (f : Vec n) :
  vsum (fun i => c * f i) = c * vsum f.
Proof. induction n; simpl; [ring|rewrite IHn; ring]. Qed.
Lemma vsum_swap m n (f : Fin.t m -> Fin.t n -> R) :
  vsum (fun j => vsum (f j)) = vsum (fun k => vsum (fun j => f j k)).
Proof.
  induction m; simpl; [symmetry; apply vsum_zero|].
  rewrite vsum_plus, IHm. reflexivity.
Qed.
Lemma vsum_nonneg n (f : Vec n) :
  (forall i, 0 <= f i) -> 0 <= vsum f.
Proof. induction n; simpl; intros H; [lra|]. specialize (IHn _ (fun i => H (Fin.FS i))). specialize (H Fin.F1). lra. Qed.
Lemma D_sum n (f : R -> Vec n) x (df : Vec n) :
  (forall i, D (fun t => f t i) x (df i)) ->
  D (fun t => vsum (f t)) x (vsum df).
Proof. induction n; simpl; intros H; [apply D_const|]. apply D_plus; auto. Qed.

Definition basis {n} (j : Fin.t n) : Vec n :=
  fun k => if Fin.eq_dec k j then 1 else 0.
Lemma dot_basis n (v : Vec n) j : dot v (basis j) = v j.
Proof.
  unfold dot, basis. induction n as [|n IH]; [inversion j|].
  refine (Fin.caseS' j (fun j =>
    vsum (fun i => v i * (if Fin.eq_dec i j then 1 else 0)) = v j) _ _).
  - simpl. destruct (Fin.eq_dec Fin.F1 Fin.F1); [|contradiction].
    assert (E : vsum (fun i : Fin.t n => v (Fin.FS i) *
      (if Fin.eq_dec (Fin.FS i) Fin.F1 then 1 else 0)) = 0).
    { transitivity (@vsum n (fun _ => 0)); [apply vsum_ext; intro i;
        destruct (Fin.eq_dec (Fin.FS i) Fin.F1); [discriminate|ring]|apply vsum_zero]. }
    cbn in E. rewrite E. ring.
  - intro k. simpl. destruct (Fin.eq_dec Fin.F1 (Fin.FS k)); [discriminate|].
    rewrite Rmult_0_r, Rplus_0_l. rewrite <- (IH (fun i => v (Fin.FS i)) k).
    apply vsum_ext. intro i. destruct (Fin.eq_dec (Fin.FS i) (Fin.FS k)), (Fin.eq_dec i k); try ring.
    + exfalso. apply n1. now apply Fin.FS_inj.
    + subst. contradiction.
Qed.

(** The sigmoid in the paper, using the calculus library's exponential. *)
Definition sigma (x : R) := / (1 + Exponential.exp (-x)).
Definition sigma' (x : R) := sigma x * (1 - sigma x).
Lemma D_sigma x : D sigma x (sigma' x).
Proof.
  assert (He : D (fun t => Exponential.exp (-t)) x
    (Exponential.exp (-x) * (-1))).
  { apply D_comp with (df := -1).
    - replace (-1) with (0 - 1) by ring.
      eapply D_ext with (f := fun t => 0 - t); [intro t; ring|]. apply D_minus; [apply D_const|apply D_id].
    - apply derivative_at_exp. }
  assert (Hd : D (fun t => 1 + Exponential.exp (-t)) x
    (0 + Exponential.exp (-x) * (-1))) by (apply D_plus; [apply D_const|exact He]).
  pose proof (Exponential.exp_pos (-x)) as Hpos.
  unfold D, sigma, sigma'.
  eapply derivative_at_ext_val.
  - apply derivative_at_inv; [exact Hd|lra].
  - cbn. unfold sigma. field. lra.
Qed.

Lemma D_sigma_comp f x df : D f x df ->
  D (fun t => sigma (f t)) x (sigma' (f x) * df).
Proof. intro H. apply D_comp; [exact H|apply D_sigma]. Qed.

Definition quadratic {n} (a target : Vec n) :=
  vsum (fun j => (a j - target j) * (a j - target j) / 2).

Lemma D_quadratic n (a : R -> Vec n) target x da :
  (forall j, D (fun t => a t j) x (da j)) ->
  D (fun t => quadratic (a t) target) x
    (dot (fun j => a x j - target j) da).
Proof.
  intros H. unfold quadratic, dot. apply D_sum. intro j.
  pose proof (D_minus _ _ _ _ _ (H j) (D_const (target j) x)) as Hj.
  pose proof (D_mult _ _ _ _ _ Hj Hj) as Hsq.
  pose proof (D_mult _ _ _ _ _ Hsq (D_const (/2) x)) as Hhalf.
  replace ((a x j - target j) * da j) with
    (((da j - 0) * (a x j - target j) + (a x j - target j) * (da j - 0)) * /2 +
       (a x j - target j) * (a x j - target j) * 0) by field.
  exact Hhalf.
Qed.
