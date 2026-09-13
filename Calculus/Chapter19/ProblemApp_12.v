From Calculus.Chapter19 Require Import Prelude.

Definition ellipsoid_area_19 (a b : R) :=
  2*π * ∫ 0 π (λ θ, b*sin θ*√(a^2*sin θ^2+b^2*cos θ^2)).
Lemma lemma_19_App_12_a_prolate : ∀ a b, 0 < b < a ->
  let e := √(1-b^2/a^2) in
  ellipsoid_area_19 a b = 2*π*b^2*(1+a/(b*e)*arcsin e).
Abort.

Lemma lemma_19_App_12_a_oblate : ∀ a b, 0 < a < b ->
  let e := √(1-a^2/b^2) in
  ellipsoid_area_19 a b = 2*π*b^2 + π*a^2/e*log ((1+e)/(1-e)).
Abort.

Lemma lemma_19_App_12_a_sphere : ∀ a, 0 < a -> ellipsoid_area_19 a a = 4*π*a^2.
Abort.

Lemma lemma_19_App_12_b : ∀ a b, 0 < b < a ->
  2*π * ∫ 0 (2*π) (λ θ, (a+b*cos θ)*b) = 4*π^2*a*b.
Abort.
