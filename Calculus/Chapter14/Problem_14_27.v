From Calculus.Chapter14 Require Import Prelude.

(* Problem 27: Improper integrals from -∞ to ∞. *)

(* (a) ∫ -∞ ∞ (1/(1+x^2)) dx exists *)
Lemma lemma_14_27_a :
  improper_integrable_inf (fun x => 1 / (1 + x^2)).
Admitted.

(* (b) ∫ -∞ ∞ x dx does not exist, but lim_{N→∞} ∫ -N N x dx does *)
Lemma lemma_14_27_b :
  ~ improper_integrable_inf (fun x => x).
Admitted.

Lemma lemma_14_27_b' :
  ⟦ lim ∞ ⟧ (fun N => ∫ (-N) N (fun x => x)) = 0.
Admitted.

(* (c) If ∫ -∞ ∞ f exists, then lim_{N→∞} ∫ -N N f = ∫ -∞ ∞ f *)
Lemma lemma_14_27_c : forall f L,
  improper_integral_inf f L ->
  ⟦ lim ∞ ⟧ (fun N => ∫ (-N) N f) = L.
Admitted.
