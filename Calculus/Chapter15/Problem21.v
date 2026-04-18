From Calculus.Chapter15 Require Import Prelude.

(* Problem 21 *)

Definition sin_deg (x : R) : R := sin (π * x / 180).
Definition cos_deg (x : R) : R := cos (π * x / 180).

(* (a) Derivatives of sin° and cos° *)
Lemma lemma_15_21_a_sin :
  ⟦ der ⟧ sin_deg = (fun x => (π / 180) * cos_deg x).
Abort.

Lemma lemma_15_21_a_cos :
  ⟦ der ⟧ cos_deg = (fun x => -(π / 180) * sin_deg x).
Abort.

(* (b) Limits *)
Lemma lemma_15_21_b_1 :
  ⟦ lim 0 ⟧ (fun x => sin_deg x / x) = π / 180.
Abort.

Lemma lemma_15_21_b_2 :
  ⟦ lim ∞ ⟧ (fun x => x * sin_deg (1 / x)) = π / 180.
Abort.
