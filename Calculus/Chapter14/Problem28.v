From Calculus.Chapter14 Require Import Prelude.

(* Problem 28: Improper integrals with unbounded functions *)

(* (a) If a > 0, find lim_{ε→0+} ∫ ε a (1/√x) dx *)
Lemma lemma_14_28_a : forall a,
  a > 0 ->
  ⟦ lim 0⁺ ⟧ (fun ε => ∫ ε a (fun x => 1 / √x)) = 2 * √a.
Abort.

(* (b) Find ∫ 0 a x^r dx if -1 < r < 0 *)
Lemma lemma_14_28_b : forall a r,
  a > 0 -> -1 < r < 0 ->
  ⟦ lim 0⁺ ⟧ (fun ε => ∫ ε a (fun x => Rpower x r)) = Rpower a (r+1) / (r+1).
Abort.

(* (c) ∫ 0 1 x^(-1) dx does not make sense *)
Lemma lemma_14_28_c :
  ~ exists L, ⟦ lim 0⁺ ⟧ (fun ε => ∫ ε 1 (fun x => 1 / x)) = L.
Abort.

(* (d) ∫ a 0 |x|^r dx for a < 0 and -1 < r < 0 *)
Lemma lemma_14_28_d : forall a r,
  a < 0 -> -1 < r < 0 ->
  ⟦ lim 0⁺ ⟧ (fun ε => ∫ a (-ε) (fun x => Rpower (|x|) r)) = Rpower (-a) (r+1) / (r+1).
Abort.

(* (e) ∫ -1 1 (1-x^2)^(-1/2) dx exists *)
Lemma lemma_14_28_e :
  exists L,
  ⟦ lim 0⁺ ⟧ (fun ε => ∫ (-1 + ε) (1 - ε) (fun x => 1 / √(1 - x^2))) = L.
Abort.
