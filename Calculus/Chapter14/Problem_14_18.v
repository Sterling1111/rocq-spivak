From Calculus.Chapter14 Require Import Prelude.

(* Problem 18: Prove that if h is continuous, f and g are differentiable, and
   F(x) = ∫ f(x) g(x) h(t) dt, then
   F'(x) = h(g(x)) * g'(x) - h(f(x)) * f'(x). *)

Lemma lemma_14_18 : forall h f g f' g',
  continuous h ->
  ⟦ der ⟧ f = f' ->
  ⟦ der ⟧ g = g' ->
  ⟦ der ⟧ (fun x => ∫ (f x) (g x) h) =
    (fun x => h (g x) * g' x - h (f x) * f' x).
Admitted.
