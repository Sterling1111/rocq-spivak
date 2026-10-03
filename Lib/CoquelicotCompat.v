From Coquelicot Require Import Coquelicot.

From Lib Require Import Imports Limit Derivative Integral Continuity Sequence Series StdlibCompat Reals_util Trigonometry.
Import LimitNotations DerivativeNotations SequenceNotations SeriesNotations IntegralNotations.

Open Scope R_scope.

Lemma lim_coquelicot_compat : forall f a L,
  ⟦ lim a ⟧ f = L <-> is_lim f a L.
Proof.
  intros f a L. split; intros H1.
  - apply is_lim_Reals_1. apply limit_compat. exact H1.
  - apply limit_compat. apply is_lim_Reals_0. exact H1.
Qed.

Lemma der_coquelicot_compat : forall f f' a,
  ⟦ der a ⟧ f = f' <-> is_derive f a (f' a).
Proof.
  intros f f' a. split; intros H1.
  - apply is_derive_Reals. apply derivative_compat. exact H1.
  - apply derivative_compat. apply is_derive_Reals. exact H1.
Qed.

Lemma continuous_coquelicot_compat : forall f a,
  continuous_at f a <-> Coquelicot.Continuity.continuous f a.
Proof.
  intros f a. split; intros H1.
  - apply -> continuity_pt_filterlim. apply continuous_compat. exact H1.
  - apply continuous_compat. apply <- continuity_pt_filterlim. exact H1.
Qed.

Lemma lim_seq_coquelicot_compat : forall a L,
  ⟦ lim ⟧ a = L <-> is_lim_seq a L.
Proof.
  intros a L. split; intros H1.
  - apply is_lim_seq_Reals. apply limit_s_compat. exact H1.
  - apply limit_s_compat. apply is_lim_seq_Reals. exact H1.
Qed.

Lemma series_sum_coquelicot_compat : forall a L,
  ∑ 0 ∞ a = L <-> is_series a L.
Proof.
  intros a L. split; intros H1.
  - apply is_series_Reals. apply series_sum_compat. exact H1.
  - apply series_sum_compat. apply is_series_Reals. exact H1.
Qed.

(* Existence bridges use finite limits: ex_lim also permits infinity. *)
Lemma finite_lim_coquelicot_compat : forall f a,
  (exists L, limit f a L) <-> ex_finite_lim f a.
Proof.
  intros f a. split; intros [L H]; exists L;
    apply lim_coquelicot_compat; exact H.
Qed.

Lemma derivative_val_coquelicot_compat : forall f a L,
  derivative_at_val f a L <-> is_derive f a L.
Proof.
  intros f a L. exact (der_coquelicot_compat f (fun _ => L) a).
Qed.

Lemma differentiable_coquelicot_compat : forall f a,
  differentiable_at f a <-> ex_derive f a.
Proof.
  intros f a. split; intros [L H]; exists L;
    apply derivative_val_coquelicot_compat; exact H.
Qed.

Lemma derivative_all_coquelicot_compat : forall f f',
  derivative f f' <-> (forall x, is_derive f x (f' x)).
Proof. intros f f'. split; intros H x; apply der_coquelicot_compat, H. Qed.

Lemma continuous_all_coquelicot_compat : forall f,
  Continuity.continuous f <-> (forall x, Coquelicot.Continuity.continuous f x).
Proof. intros f. split; intros H x; apply continuous_coquelicot_compat, H. Qed.

Lemma convergent_sequence_coquelicot_compat : forall a,
  convergent_sequence a <-> ex_finite_lim_seq a.
Proof.
  intros a. split; intros [L H]; exists L;
    apply lim_seq_coquelicot_compat; exact H.
Qed.

Lemma series_converges_coquelicot_compat : forall a,
  series_converges a <-> ex_series a.
Proof.
  intros a. split; intros [L H]; exists L;
    apply series_sum_coquelicot_compat; exact H.
Qed.

(* Value operators are only rewritten under a convergence/derivative proof. *)
Lemma Lim_coquelicot_compat : forall f a L,
  limit f a L -> Lim f a = Rbar.Finite L.
Proof. intros f a L H. apply is_lim_unique, lim_coquelicot_compat, H. Qed.

Lemma Derive_coquelicot_compat : forall f f' a,
  derivative_at f f' a -> Derive f a = f' a.
Proof. intros f f' a H. apply is_derive_unique, der_coquelicot_compat, H. Qed.

Lemma Lim_seq_coquelicot_compat : forall a L,
  limit_s a L -> Lim_seq a = Rbar.Finite L.
Proof. intros a L H. apply is_lim_seq_unique, lim_seq_coquelicot_compat, H. Qed.

Lemma Series_coquelicot_compat : forall a L,
  series_sum a L -> Coquelicot.Series.Series a = L.
Proof. intros a L H. apply is_series_unique, series_sum_coquelicot_compat, H. Qed.

(* Darboux integrability is an ordered-interval predicate. Equal endpoints
   are allowed; for arbitrary orientation use Rmin/Rmax below. *)
Lemma integrable_coquelicot_compat : forall f a b,
  a <= b -> (integrable_on a b f <-> ex_RInt f a b).
Proof.
  intros f a b Hab. rewrite darboux_integrable_stdlib_compat by exact Hab.
  split.
  - intros [pr]. apply ex_RInt_Reals_1. exact pr.
  - intros H. constructor. apply ex_RInt_Reals_0. exact H.
Qed.

Lemma riemann_integrable_coquelicot_compat : forall f a b,
  a <= b -> (riemann_integrable_on a b f <-> ex_RInt f a b).
Proof.
  intros f a b Hab. rewrite riemann_darboux_integrable_equiv.
  apply integrable_coquelicot_compat, Hab.
Qed.

Lemma integrable_coquelicot_compat_general : forall f a b,
  integrable_on (Rmin a b) (Rmax a b) f <-> ex_RInt f a b.
Proof.
  intros f a b. destruct (Rle_dec a b) as [Hab|Hab].
  - rewrite Rmin_left, Rmax_right by exact Hab.
    apply integrable_coquelicot_compat, Hab.
  - rewrite Rmin_right, Rmax_left by lra.
    rewrite integrable_coquelicot_compat by lra.
    split; apply ex_RInt_swap.
Qed.

Lemma RInt_coquelicot_compat_general : forall f a b,
  ex_RInt f a b -> definite_integral a b f = RInt f a b.
Proof.
  intros f a b H. pose proof (ex_RInt_Reals_0 f a b H) as pr.
  rewrite (RInt_Reals f a b pr).
  apply definite_integral_compat_general.
Qed.

Lemma RInt_coquelicot_compat : forall f a b,
  a <= b -> integrable_on a b f -> definite_integral a b f = RInt f a b.
Proof.
  intros f a b Hab H. apply RInt_coquelicot_compat_general.
  apply integrable_coquelicot_compat; assumption.
Qed.

Lemma riemann_integral_coquelicot_compat : forall f a b,
  ex_RInt f a b -> riemann_integral a b f = RInt f a b.
Proof.
  intros f a b H. rewrite riemann_darboux_integral_equiv.
  apply RInt_coquelicot_compat_general, H.
Qed.

Lemma is_RInt_coquelicot_compat : forall f a b L,
  is_RInt f a b L <->
  integrable_on (Rmin a b) (Rmax a b) f /\ definite_integral a b f = L.
Proof.
  intros f a b L. split.
  - intros H. assert (Hex : ex_RInt f a b) by (exists L; exact H).
    split.
    + apply integrable_coquelicot_compat_general, Hex.
    + rewrite RInt_coquelicot_compat_general by exact Hex.
      apply is_RInt_unique, H.
  - intros [H HL]. apply integrable_coquelicot_compat_general in H.
    rewrite RInt_coquelicot_compat_general in HL by exact H.
    rewrite <- HL. exact (RInt_correct f a b H).
Qed.

(* The tagged-partition predicate is only meaningful for a < b. At a = b
   it is vacuous, whereas Coquelicot requires the integral value to be zero. *)
Lemma is_riemann_integral_coquelicot_compat : forall f a b L,
  a < b -> (is_riemann_integral a b f L <-> is_RInt f a b L).
Proof.
  intros f a b L Hab. rewrite is_riemann_integral_stdlib_compat by exact Hab.
  split.
  - intros [pr HL]. rewrite HL, <- (RInt_Reals f a b pr).
    exact (RInt_correct f a b (ex_RInt_Reals_1 f a b pr)).
  - intros H. assert (Hex : ex_RInt f a b) by (exists L; exact H).
    exists (ex_RInt_Reals_0 f a b Hex).
    rewrite <- RInt_Reals. symmetry. apply is_RInt_unique, H.
Qed.
