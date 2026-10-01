From Lib Require Import Imports Tactics Integral Trigonometry Exponential.
Import IntegralNotations.
Open Scope R_scope.

Example polynomial : ∫ 0 1 (fun x => x^2) = 1/3.
Proof. auto_int. Qed.

Example trigonometric : ∫ 0 π (fun x => sin x) = 2.
Proof. auto_int. Qed.

Example exponential : ∫ 0 1 (fun x => exp x) = e - 1.
Proof. auto_int. Qed.

Example reversed_bounds : ∫ 1 0 (fun x => 2*x) = -1.
Proof. auto_int. Qed.

(* A false result must not be accepted from the candidate generator. *)
Example reject_wrong_integral : True.
Proof.
  Fail assert (∫ 0 1 (fun x => x^2) = 42) by auto_int.
  exact I.
Qed.
