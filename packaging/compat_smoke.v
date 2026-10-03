(* Also compile a copy outside the checkout after installing the package. *)
From Lib Require Import Imports Tactics CoquelicotCompat Integral Derivative.
From Coquelicot Require Import Coquelicot.
Import IntegralNotations.
Open Scope R_scope.

Example installed_integral : ∫ 1 0 (fun x => 2*x) = -1.
Proof. auto_int. Qed.

Example installed_derive (a : R) : Derive (fun x => x^2) a = 2*a.
Proof. apply (Derive_coquelicot_compat _ (fun x => 2*x)). auto_diff. Qed.

Print Assumptions is_RInt_coquelicot_compat.
Print Assumptions is_riemann_integral_coquelicot_compat.
