(* External library first: check both directions and actual value transport. *)
From Coquelicot Require Import Coquelicot.
From Lib Require Import Imports Tactics Limit Derivative Continuity Integral
  Sequence Series CoquelicotCompat.
Import IntegralNotations.
Open Scope R_scope.

Example compat_limit_from_coquelicot (a : R) : limit (fun x => x) a a.
Proof. apply lim_coquelicot_compat. apply is_lim_id. Qed.

Example compat_limit_to_coquelicot (a : R) :
  is_lim (fun x => x^2 + 1) a (a^2 + 1).
Proof. apply lim_coquelicot_compat. auto_limit. Qed.

Example compat_derivative_from_coquelicot (c a : R) :
  derivative_at_val (fun _ => c) a 0.
Proof. apply derivative_val_coquelicot_compat. exact (@is_derive_const R_AbsRing R_NormedModule c a). Qed.

Example compat_derivative_value (a : R) : Derive (fun x => x^2) a = 2*a.
Proof.
  apply (Derive_coquelicot_compat _ (fun x => 2*x)). auto_diff.
Qed.

Example compat_continuity (a : R) :
  Coquelicot.Continuity.continuous (fun x => x^2 + 1) a.
Proof. apply continuous_coquelicot_compat. auto_cont. Qed.

Example compat_sequence (c : R) : limit_s (fun _ => c) c.
Proof. apply lim_seq_coquelicot_compat. apply is_lim_seq_const. Qed.

Example compat_series_value (a : nat -> R) (L : R) :
  series_sum a L -> Coquelicot.Series.Series a = L.
Proof. apply Series_coquelicot_compat. Qed.

Example compat_constant_integral (a b c : R) :
  definite_integral a b (fun _ => c) = (b-a)*c.
Proof.
  apply (proj1 (is_RInt_coquelicot_compat _ _ _ _)).
  exact (@is_RInt_const R_NormedModule a b c).
Qed.

Example compat_integral_reversed :
  definite_integral 3 1 (fun _ => 2) = -4.
Proof. rewrite compat_constant_integral. ring. Qed.

Example compat_integral_point (f : R -> R) (a : R) :
  is_RInt f a a (definite_integral a a f).
Proof.
  apply is_RInt_coquelicot_compat. split; [|reflexivity].
  rewrite Rmin_left, Rmax_left by lra. apply integrable_on_n_n.
Qed.

Example compat_integrability_point (f : R -> R) (a : R) : ex_RInt f a a.
Proof.
  apply integrable_coquelicot_compat; [lra|apply integrable_on_n_n].
Qed.

Example compat_tagged_integral (f : R -> R) (a b L : R) :
  a < b -> is_RInt f a b L -> is_riemann_integral a b f L.
Proof. intros Hab H. apply is_riemann_integral_coquelicot_compat; assumption. Qed.

(* Regression: no value equality may bypass the integrability obligation. *)
Example compat_value_requires_integrability (f : R -> R) (a b : R) : True.
Proof.
  Fail assert (definite_integral a b f = RInt f a b)
    by apply RInt_coquelicot_compat_general.
  exact I.
Qed.

Example compat_tactics_after_imports : ∫ 0 1 (fun x => x^2) = 1/3.
Proof. auto_int. Qed.

(* Importing the bridges must not switch Stdlib nat comparisons to bool. *)
Example compat_nat_scope : forall n : nat, (n <= S n)%nat.
Proof. lia. Qed.
