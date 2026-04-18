From Calculus.Chapter14 Require Import Prelude.

(* Problem 23: Separable differential equations *)

(* (a) Suppose G' = g and F' = f. Prove that if y satisfies g(y(x)) * y'(x) = f(x),
   then there is a number c such that G(y(x)) = F(x) + c. *)
Lemma lemma_14_23_a : forall f g F G y y',
  ⟦ der ⟧ F = f ->
  ⟦ der ⟧ G = g ->
  ⟦ der ⟧ y = y' ->
  (forall x, g (y x) * y' x = f x) ->
  exists c, forall x, G (y x) = F x + c.
Abort.

(* (b) Converse: if G(y(x)) = F(x) + c, then y satisfies the equation in (a) *)
Lemma lemma_14_23_b : forall f g F G y y' c,
  ⟦ der ⟧ F = f ->
  ⟦ der ⟧ G = g ->
  ⟦ der ⟧ y = y' ->
  (forall x, G (y x) = F x + c) ->
  forall x, g (y x) * y' x = f x.
Abort.

(* (c) Find what condition y must satisfy if y'(x) = (1 + x^2) / (1 + y(x)) *)
Lemma lemma_14_23_c : forall y y',
  ⟦ der ⟧ y = y' ->
  (forall x, y' x = (1 + x^2) / (1 + y x)) ->
  exists c, forall x, y x + (y x)^2 / 2 = x + x^3 / 3 + c.
Abort.

(* (d) Find what condition y must satisfy if y'(x) = -1 / (1 + 5 * (y(x))^4) *)
Lemma lemma_14_23_d : forall y y',
  ⟦ der ⟧ y = y' ->
  (forall x, y' x = -1 / (1 + 5 * (y x)^4)) ->
  exists c, forall x, y x + (y x)^5 = -x + c.
Abort.

(* (e) Find all functions y satisfying y(x) * y'(x) = -x.
   Find the solution y satisfying y(0) = -1. *)
Lemma lemma_14_23_e : forall y y',
  ⟦ der ⟧ y = y' ->
  (forall x, y x * y' x = - x) ->
  exists c, forall x, (y x)^2 = -x^2 + c.
Abort.

Lemma lemma_14_23_e' : forall y y',
  ⟦ der ⟧ y = y' ->
  (forall x, y x * y' x = - x) ->
  y 0 = -1 ->
  forall x, (y x)^2 = 1 - x^2.
Abort.
