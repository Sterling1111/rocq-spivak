From Calculus.Chapter14 Require Import Prelude.

(* Problem 19: Let f be integrable on [a, b], let c be in (a,b), and let
   F(x) = ∫ a x f, a ≤ x ≤ b. Prove or give counterexamples. *)

(* (a) If f is differentiable at c, then F is differentiable at c. *)
Lemma lemma_14_19_a : forall f a b c,
  a < b ->
  c ∈ (a, b) ->
  integrable_on a b f ->
  differentiable_at f c ->
  differentiable_at (fun x => ∫ a x f) c.
Admitted.

(* (b) If f is differentiable at c, then F' is continuous at c. *)
(* This is actually true *)
Lemma lemma_14_19_b : forall f a b c,
  a < b ->
  c ∈ (a, b) ->
  integrable_on a b f ->
  differentiable_at f c ->
  continuous_at (⟦ Der ⟧ (fun x => ∫ a x f)) c.
Admitted.

(* (c) If f' is continuous at c, then F' is continuous at c. *)
Lemma lemma_14_19_c : forall f f' a b c,
  a < b ->
  c ∈ (a, b) ->
  integrable_on a b f ->
  ⟦ der ⟧ f = f' ->
  continuous_at f' c ->
  continuous_at (⟦ Der ⟧ (fun x => ∫ a x f)) c.
Admitted.
