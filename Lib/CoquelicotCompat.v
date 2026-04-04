From Coquelicot Require Import Coquelicot.

From Lib Require Import Imports Tactics Limit Derivative Integral Continuity Sequence Series StdlibCompat Reals_util.
Import LimitNotations DerivativeNotations SequenceNotations SeriesNotations IntegralNotations.

Open Scope R_scope.

From Interval Require Import Plot Tactic.
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

Lemma integrable_coquelicot_compat : forall f a b,
  integrable_on a b f <-> ex_RInt f a b.
Proof.
  split; intros H1.
  - admit.
  - admit.
Admitted.

Lemma RInt_coquelicot_compat : forall f a b,
  integrable_on a b f ->
  ∫ a b f = RInt f a b.
Proof.
  intros f a b H1.
Admitted.

Lemma improper_integrable_pinf_coquelicot_compat : forall f a,
  improper_integrable_pinf a f <-> ex_RInt_gen f (at_point a) (Rbar_locally p_infty).
Proof.
  split; intros H1.
  - admit.
  - admit.
Admitted.

Lemma improper_integral_pinf_coquelicot_compat : forall f a L,
  ∫ a ∞ f = L <-> is_RInt_gen f (at_point a) (Rbar_locally p_infty) L.
Proof.
  split; intros H1.
  - admit.
  - admit.
Admitted.

Lemma cos_integral_bound :
  1 / 2 <= ∫ 0 1 cos <= 1.
Proof.
  rewrite RInt_coquelicot_compat.
  - (* Goal 1: 1 / 2 <= RInt cos 0 1 <= 1 *)
    integral. 
    
  - apply theorem_13_3; try lra. apply continuous_imp_continuous_on. auto_cont.
    (* Add your proof of `continuous_on cos [0, 1]` here *)
Admitted.