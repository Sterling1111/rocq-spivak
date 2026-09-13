From Calculus.Chapter19 Require Import Prelude.

(* Finite elementary expressions; no integration constructor is allowed. *)
Inductive elementary_19 : (R -> R) -> Prop :=
| elementary_19_const : ∀ c, elementary_19 (λ _, c)
| elementary_19_id : elementary_19 (λ x, x)
| elementary_19_add : ∀ f g, elementary_19 f -> elementary_19 g -> elementary_19 (λ x, f x + g x)
| elementary_19_mul : ∀ f g, elementary_19 f -> elementary_19 g -> elementary_19 (λ x, f x * g x)
| elementary_19_div : ∀ f g, elementary_19 f -> elementary_19 g -> elementary_19 (λ x, f x / g x)
| elementary_19_exp : ∀ f, elementary_19 f -> elementary_19 (λ x, exp (f x))
| elementary_19_logabs : ∀ f, elementary_19 f -> elementary_19 (λ x, log (Rabs (f x)))
| elementary_19_atan : ∀ f, elementary_19 f -> elementary_19 (λ x, arctan (f x)).

Lemma lemma_19_20 : ∃ F, elementary_19 F /\
  (⟦ der ⟧ F = (λ x, exp x / (exp (5*x) + exp x + 1))).
Abort.
