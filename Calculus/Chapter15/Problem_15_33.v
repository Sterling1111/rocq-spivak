From Calculus.Chapter15 Require Import Prelude.

(* Problem 33 *)

(* (a) sin(k+1/2)x - sin(k-1/2)x = 2 sin(x/2) cos(kx) *)
Lemma lemma_15_33_a : forall k x,
  sin ((k + 1/2) * x) - sin ((k - 1/2) * x) = 2 * sin (x / 2) * cos (k * x).
Admitted.

(* (b) Dirichlet kernel: 1/2 + cos x + cos 2x + ... + cos nx = sin((n+1/2)x) / (2 sin(x/2)) *)
Lemma lemma_15_33_b : forall (n : nat) x,
  sin (x / 2) <> 0 ->
  1/2 + ∑ 1 n (fun i => cos (INR i * x)) = sin ((INR n + 1/2) * x) / (2 * sin (x / 2)).
Admitted.

(* (c) sin x + sin 2x + ... + sin nx = sin((n+1)/2 * x) * sin(n/2 * x) / sin(x/2) *)
Lemma lemma_15_33_c : forall (n : nat) x,
  sin (x / 2) <> 0 ->
  ∑ 1 n (fun i => sin (INR i * x)) = sin ((INR n + 1) / 2 * x) * sin (INR n / 2 * x) / sin (x / 2).
Admitted.
