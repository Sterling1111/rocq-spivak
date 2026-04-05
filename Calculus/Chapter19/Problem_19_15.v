From Calculus.Chapter19 Require Import Prelude.

(* Problem 15: Suppose f'' is continuous and ∫_0^π [f(x) + f''(x)] sin x dx = 2. Given f(π) = 1, compute f(0). *)

Lemma lemma_19_15 : forall f,
  continuous (⟦ der ⟧ (⟦ der ⟧ f)) ->
  f PI = 1 ->
  ∫ 0 PI (fun x => (f x + ⟦ der ⟧ (⟦ der ⟧ f) x) * sin x) = 2 ->
  f 0 = 1.
Admitted.
