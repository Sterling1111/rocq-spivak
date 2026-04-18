From Calculus.Chapter15 Require Import Prelude.

(* Problem 12: Orthogonality of trig functions *)

Lemma lemma_15_12_a : forall (m n : nat),
  m <> n ->
  ∫ (-π) π (fun x => sin (INR m * x) * sin (INR n * x)) = 0.
Abort.

Lemma lemma_15_12_a' : forall (n : nat),
  (n > 0)%nat ->
  ∫ (-π) π (fun x => sin (INR n * x) * sin (INR n * x)) = π.
Abort.

Lemma lemma_15_12_b : forall (m n : nat),
  m <> n ->
  ∫ (-π) π (fun x => cos (INR m * x) * cos (INR n * x)) = 0.
Abort.

Lemma lemma_15_12_b' : forall (n : nat),
  (n > 0)%nat ->
  ∫ (-π) π (fun x => cos (INR n * x) * cos (INR n * x)) = π.
Abort.

Lemma lemma_15_12_c : forall (m n : nat),
  ∫ (-π) π (fun x => sin (INR m * x) * cos (INR n * x)) = 0.
Abort.
