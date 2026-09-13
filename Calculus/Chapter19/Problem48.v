From Calculus.Chapter19 Require Import Prelude.

Definition quadratic_19 (P : R -> R) := ∃ A B C, ∀ x, P x = A*x^2+B*x+C.
Definition cubic_19 (Q : R -> R) := ∃ A B C D, ∀ x, Q x = A*x^3+B*x^2+C*x+D.
Lemma lemma_19_48_a : ∀ f P, quadratic_19 P -> P 0 = f 0 -> P 1 = f 1 -> P 2 = f 2 ->
  ∫ 0 2 P = (f 0+4*f 1+f 2)/3.
Abort.

Lemma lemma_19_48_b : ∀ f P a b, a < b -> quadratic_19 P ->
  P a = f a -> P ((a+b)/2) = f ((a+b)/2) -> P b = f b ->
  ∫ a b P = (b-a)/6*(f a+4*f ((a+b)/2)+f b).
Abort.

Lemma lemma_19_48_c : ∀ f a b, a < b -> cubic_19 f ->
  ∫ a b f = (b-a)/6*(f a+4*f ((a+b)/2)+f b).
Abort.
