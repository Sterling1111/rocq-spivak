From Calculus.Chapter20 Require Import Prelude.

(* Degree eight previously overflowed while reducing unary factorials.
   The product also exercises simplification between derivative steps. *)
Example compute_tp_product : ∀ x,
  P(8, 0, λ y, exp y * sin y) x =
    x + x^2 + x^3/3 - x^5/30 - x^6/90 - x^7/630.
Proof. compute_tp. Qed.

Example compute_tp_high_degree : ∀ x,
  P(10, 0, cos) x =
    1 - x^2/2 + x^4/24 - x^6/720 + x^8/40320 - x^10/3628800.
Proof. compute_tp. Qed.

Example compute_tp_parameter : ∀ a x,
  P(3, 0, λ y, exp (a*y)) x =
    1 + a*x + a^2*x^2/2 + a^3*x^3/6.
Proof. compute_tp. Qed.

Example compute_tp_shifted_polynomial : ∀ x,
  P(4, 1, λ y, y^5 + y^3 + y) x =
    3 + 9*(x-1) + 13*(x-1)^2 + 11*(x-1)^3 + 5*(x-1)^4.
Proof. compute_tp. Qed.

Example compute_tp_degree_zero : ∀ f a x, P(0, a, f) x = f a.
Proof. compute_tp. Qed.

(* Symbolic degrees must retain the sum for subsequent manual reasoning. *)
Example compute_tp_symbolic_degree : ∀ n x,
  P(n, 1, exp) x = ∑ 0 n (λ k, exp 1 / (fact k) * (x-1)^k).
Proof.
  compute_tp.
  apply sum_f_equiv; try lia.
  intros k Hk. rewrite nth_derive_exp. lra.
Qed.

(* Check the shared derivative tactic still uses derivatives in the context. *)
Example compute_tp_context_derivative : ∀ f f' c b,
  ⟦ der ⟧ f = f' ->
  ⟦ Der b ⟧ (λ x, f (c*x)) = c * f' (c*b).
Proof. intros f f' c b H. compute_Der. lra. Qed.
