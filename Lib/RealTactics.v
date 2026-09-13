From Lib Require Export Imports Real.
From Lib Require Import Reals_util.
From Stdlib Require Import Qreals.

Delimit Scope Real_scope with Real.
Bind Scope Real_scope with Real.
Open Scope Real_scope.

(* Numerals denote cuts exactly; they do not evaluate a cut's choice functions. *)
Definition Real_of_Z (z : Z) : Real := cut_of_R (IZR z).
Definition Real_of_Q (q : Q) : Real := cut_of_R (Q2R q).

Module RealNumerals.
  Inductive numeral := of_Z : Z -> numeral.
  Definition parse (z : Z) : numeral := of_Z z.
  Definition print (n : numeral) : Z := match n with of_Z z => z end.
End RealNumerals.

Number Notation Real RealNumerals.parse RealNumerals.print
  (via RealNumerals.numeral mapping [Real_of_Z => RealNumerals.of_Z]) : Real_scope.

Fixpoint Real_pow (a : Real) (n : nat) : Real :=
  match n with
  | O => 1
  | S k => a * Real_pow a k
  end.
Infix "^" := Real_pow : Real_scope.

Lemma cut_value_of_R : forall r, cut_value (cut_of_R r) = r.
Proof. intros r. apply cut_value_unique. intros q. reflexivity. Qed.

Lemma cut_value_of_Z : forall z, cut_value (Real_of_Z z) = IZR z.
Proof. intros z. apply cut_value_of_R. Qed.

Lemma cut_value_of_Q : forall q, cut_value (Real_of_Q q) = Q2R q.
Proof. intros q. apply cut_value_of_R. Qed.

Lemma cut_value_eq : forall a b : Real,
  a = b <-> cut_value a = cut_value b.
Proof. split; [intros ->; reflexivity|apply cut_value_injective]. Qed.

(* Total inversion also covers /0, so transfer never drops a side condition. *)
Lemma cut_value_inv_total : forall a,
  cut_value (/a) = (/ cut_value a)%R.
Proof.
  intros a. destruct (classic (a = 0)) as [Ha|Ha]; [subst a|apply cut_value_inv; exact Ha].
  rewrite cut_value_zero, Rinv_0.
  unfold Rinv. destruct (Rtotal_order_dec 0 0) as [[Hlt|Heq]|Hgt].
  - destruct Hlt as [_ Hne]. exfalso. apply Hne. reflexivity.
  - apply cut_value_zero.
  - destruct Hgt as [_ Hne]. exfalso. apply Hne. reflexivity.
Qed.

Lemma cut_value_abs : forall a,
  cut_value (Rabs a) = Rbasic_fun.Rabs (cut_value a).
Proof.
  intros a. unfold Rabs. destruct (Rle_dec 0 a) as [Ha|Ha].
  - apply cut_value_le in Ha. rewrite cut_value_zero in Ha.
    symmetry. apply Rabs_pos_eq. exact Ha.
  - assert (Hneg : (cut_value a < 0)%R).
    { apply Rnot_le_lt. intros H. apply Ha, cut_value_le.
      rewrite cut_value_zero. exact H. }
    rewrite cut_value_opp, Rabs_left; [reflexivity|exact Hneg].
Qed.

Lemma cut_value_pow : forall a n,
  cut_value (a ^ n) = (cut_value a ^ n)%R.
Proof.
  intros a n. induction n as [|n IH]; simpl.
  - apply cut_value_one.
  - rewrite cut_value_mult, IH. reflexivity.
Qed.

Lemma cut_field_lt : forall a b : Real, Field.lt a b <-> a < b.
Proof. intros a b. apply cut_field_gt. Qed.

#[export] Hint Rewrite cut_field_gt cut_field_ge cut_field_lt cut_field_le : real_order.
#[export] Hint Rewrite cut_value_eq cut_value_le cut_value_lt
  cut_value_plus cut_value_mult cut_value_opp cut_value_inv_total cut_value_abs
  cut_value_pow cut_value_zero cut_value_one cut_value_of_Z cut_value_of_Q
  cut_value_of_R : real_transfer.
#[export] Hint Rewrite Rinv_0 Rinv_1 : real_transfer.

(* This tactic exposes the standard-real goal for further manual tactics.
   The solving tactics below are atomic: failure preserves the original goal. *)
Ltac real_to_R :=
  intros;
  unfold Ensembles.In, Real.P in *;
  autorewrite with real_order in *;
  unfold Real.Rgt, Real.Rge, Real.Rminus, Real.Rdiv in *;
  autorewrite with real_transfer in *.

Ltac real_lra := solve [real_to_R; Lra.lra].
Ltac real_nra := solve [real_to_R; Lra.nra].
Ltac real_field := solve [real_to_R; field; repeat split; Lra.nra].
Ltac solve_real := solve [real_to_R;
  solve [Lra.lra | Lra.nra | field; repeat split; Lra.nra | solve_R]].
