From Calculus.Chapter20 Require Import Prelude.

(* One additional derivative, as required by this route via Taylor's theorem. *)
Lemma lemma_20_18 : ∀ n a f,
  nth_differentiable_at (S n) f a ->
  ⟦ lim a ⟧ (λ x, R(n,a,f) x / (x-a)^n) = 0.
Abort.
