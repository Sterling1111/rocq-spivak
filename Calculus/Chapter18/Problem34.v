From Calculus.Chapter18 Require Import Prelude.

Definition log_over_x x := log x / x.

(* These limits, slope, and turning point specify the requested sketch. *)
Lemma lemma_18_34_a :
  (⟦ lim 0⁺ ⟧ log_over_x = -∞) /\
  (⟦ lim ∞ ⟧ log_over_x = 0) /\
  (⟦ der ⟧ log_over_x (0, ∞) = (λ x, (1 - log x) / x^2)) /\
  (∀ x, x > 0 -> log_over_x x <= log_over_x e).
Abort.

Lemma lemma_18_34_b : e ^^ π > π ^^ e.
Abort.

Lemma lemma_18_34_c_i : ∀ x y,
  (0 < x <= 1 \/ x = e) -> y > 0 -> x ^^ y = y ^^ x -> y = x.
Abort.

Lemma lemma_18_34_c_ii : ∀ x, x > 1 -> x <> e ->
  ∃ y, y > 1 /\ y <> x /\ x ^^ y = y ^^ x /\
    (x < e -> y > e) /\ (x > e -> y < e) /\
    ∀ z, z > 0 -> z <> x -> x ^^ z = z ^^ x -> z = y.
Abort.

Lemma lemma_18_34_d : ∀ x y : nat,
  (0 < x)%nat -> (0 < y)%nat -> (x^y = y^x)%nat ->
  x = y \/ (x = 2 /\ y = 4)%nat \/ (x = 4 /\ y = 2)%nat.
Abort.

(* Parametrize the other branch by t=y/x, extending through t=1. *)
Definition power_curve_x t := if Req_EM_T t 1 then e else t ^^ (1/(t-1)).
Definition power_curve_y t := t * power_curve_x t.

Lemma lemma_18_34_e :
  (∀ x y, x > 0 -> y > 0 ->
    (x ^^ y = y ^^ x <-> x = y \/
      ∃ t, t > 0 /\ x = power_curve_x t /\ y = power_curve_y t)) /\
  (∀ t, t > 0 -> (power_curve_x t = power_curve_y t <-> t = 1)) /\
  power_curve_x 1 = e /\ power_curve_y 1 = e /\
  continuous_on power_curve_x (0, ∞) /\ continuous_on power_curve_y (0, ∞).
Abort.

Lemma lemma_18_34_f : ∀ g,
  (∀ x, 1 < x < e -> g x > e /\ x ^^ (g x) = (g x) ^^ x) ->
  ⟦ der ⟧ g (1,e) = (λ x, (g x)^2 / (1 - log (g x)) * (1 - log x) / x^2).
Abort.
