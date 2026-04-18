From Calculus.Chapter15 Require Import Prelude.

(* Problem 26: Riemann-Lebesgue lemma *)

(* (a) *)
Lemma lemma_15_26_a : forall c d,
  c < d ->
  ⟦ lim ∞ ⟧ (fun l => ∫ c d (fun x => sin (l * x))) = 0.
Abort.

(* (b) *)
Lemma lemma_15_26_b : forall s a b,
  a < b ->
  integrable_on a b s ->
  (exists (parts : list R) (vals : list R), True) -> (* s is a step function *)
  ⟦ lim ∞ ⟧ (fun l => ∫ a b (fun x => s x * sin (l * x))) = 0.
Abort.

(* (c) *)
Lemma lemma_15_26_c : forall f a b,
  a < b ->
  integrable_on a b f ->
  ⟦ lim ∞ ⟧ (fun l => ∫ a b (fun x => f x * sin (l * x))) = 0.
Abort.
