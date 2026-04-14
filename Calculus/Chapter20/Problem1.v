From Calculus.Chapter20 Require Import Prelude.

Lemma lemma_20_1_i : forall x,
  P(3, 0, λ x, exp (exp x)) x = exp 1 * (1 + x + x^2 + 5 / 6 * x^3).
Proof.
  compute_tp.
Qed.

Lemma lemma_20_1_ii : forall x,
  P(3, 0, fun x => exp (sin x)) x = 1 + x + x^2 / 2.
Proof.
  compute_tp.
Qed.  

Lemma lemma_20_1_iii : forall n x,
  P(2 * n, π / 2, sin) x = ∑ 0 n (fun k => (-1)^k / INR (fact (2 * k)) * (x - π / 2)^(2 * k)).
Proof.
  compute_tp.

Admitted.

Lemma lemma_20_1_iv : forall n x,
  P(2 * n, π, cos) x = ∑ 0 n (fun k => (-1)^(k+1) / INR (fact (2 * k)) * (x - π)^(2 * k)).
Proof.
  compute_tp.
Admitted.

Lemma lemma_20_1_v : forall n x,
  P(n, 1, exp) x = ∑ 0 n (fun k => exp 1 / INR (fact k) * (x - 1)^k).
Proof.
  compute_tp.
Admitted.

Lemma lemma_20_1_vi : forall n x,
  (n > 0)%nat ->
  P(n, 2, log) x = log 2 + ∑ 0 (n-1) (fun k => (-1)^(k) / (INR (k+1) * 2^(k+1)) * (x - 2)^(k+1)).
Proof.
  compute_tp.
Admitted.

Lemma lemma_20_1_vii : forall x,
  P(4, 0, fun x => x^5 + x^3 + x) x = x^3 + x.
Proof.
  compute_tp.
Qed.

Lemma lemma_20_1_viii : forall x,
  P(4, 1, fun x => x^5 + x^3 + x) x = 3 + 9*(x-1) + 13*(x-1)^2 + 11*(x-1)^3 + 5*(x-1)^4.
Proof.
  compute_tp. 
Qed.

Lemma lemma_20_1_ix : forall n x,
  P(2 * n + 1, 0, fun x => 1 / (1 + x^2)) x = ∑ 0 n (fun k => (-1)^k * x^(2 * k)).
Proof.
  compute_tp.
Admitted.

Lemma lemma_20_1_x : forall n x,
  P(n, 0, fun x => 1 / (1 + x)) x = ∑ 0 n (fun k => (-1)^k * x^k).
Proof.
  compute_tp.
Admitted.