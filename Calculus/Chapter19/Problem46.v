From Calculus.Chapter19 Require Import Prelude.

Lemma lemma_19_46_a : ∀ f A B α β, 0 < α -> 0 < β ->
  (∀ a b, 0 < a < b -> integrable_on a b (λ x, f x/x)) ->
  right_limit f 0 A -> limit_pinf f B ->
  improper_positive_19 (λ x, (f (α*x)-f (β*x))/x) ((A-B)*log (β/α)).
Abort.

Lemma lemma_19_46_b : ∀ f A α β, 0 < α -> 0 < β ->
  (∀ a, 0 < a -> improper_integrable_pinf a (λ x, f x/x)) ->
  right_limit f 0 A ->
  improper_positive_19 (λ x, (f (α*x)-f (β*x))/x) (A*log (β/α)).
Abort.

Lemma lemma_19_46_c_i : ∀ α β, 0 < α -> 0 < β ->
  improper_positive_19 (λ x, (exp (-α*x)-exp (-β*x))/x) (log (β/α)).
Abort.

Lemma lemma_19_46_c_ii : ∀ α β, 0 < α -> 0 < β ->
  improper_positive_19 (λ x, (cos (α*x)-cos (β*x))/x) (log (β/α)).
Abort.
