From Calculus.Chapter18 Require Import Prelude.

Lemma lemma_18_1_i : 
  ⟦ der ⟧ (λ x, e^^e^^e^^e^^x) = (λ x, e^^e^^e^^e^^x * e^^e^^e^^x * e^^e^^x * e^^x).
Proof.
  auto_diff.
Qed.

Lemma lemma_18_1_ii : ⟦ der ⟧ (λ x, log(1 + log(1 + log(1 + e^^(1 + e^^(1 + x)))))) = (λ x, (1 / (1 + log(1 + log(1 + e^^(1 + e^^(1 + x)))))) * ((1 / (1 + log(1 + e^^(1 + e^^(1 + x))))) * ((1 / (1 + e^^(1 + e^^(1 + x)))) * (e^^(1 + e^^(1 + x)) * e^^(1 + x))))).
Proof.
  auto_diff.
Qed.

Lemma lemma_18_1_iii : ⟦ der ⟧ (λ x, (sin x)^^(sin (sin x))) (0, π) = (λ x, (sin x)^^(sin (sin x)) * (cos (sin x) * cos x * log (sin x) + sin (sin x) * (cos x / sin x))).
Proof.
  auto_diff.
Qed.

Lemma lemma_18_1_iv : ⟦ der ⟧ (λ x, e^^(∫ 0 x (λ t, e^^(- t^2)))) = (λ x, e^^(∫ 0 x (λ t, e^^(- t^2))) * e^^(- x^2)).
Proof.
  pose (F := λ y, ∫ 0 y (λ t, e^^(- t^2))).
  assert (H1 : ⟦ der ⟧ F = (λ y, e^^(- y^2))).
  { unfold F. apply FTC1_global; auto_cont. }
  replace (λ x, e^^(∫ 0 x (λ t, e^^(- t^2)))) with (λ x, e^^F x) by reflexivity.
  replace (λ x, e^^(∫ 0 x (λ t, e^^(- t^2))) * e^^(- x^2)) with (λ x, e^^F x * e^^(- x^2)) by reflexivity.
  auto_diff.
Qed.

Lemma lemma_18_1_v : ⟦ der ⟧ (λ x, (sin x)^^((sin x)^^(sin x))) (0, π) = (λ x, (sin x)^^((sin x)^^(sin x)) * (((sin x)^^(sin x) * (cos x * log (sin x) + sin x * (cos x / sin x))) * log (sin x) + ((sin x)^^(sin x)) * (cos x / sin x))).
Proof.
  auto_diff.
Qed.

Lemma lemma_18_1_vi : ⟦ der ⟧ (λ x, log (sin x) / x) (0, π) = (λ x, ((cos x / sin x) * x - log (sin x) * 1) / x^2).
Proof.
  auto_diff.
Qed.

(* As printed, x / sin x is outside [-1,1] whenever it is defined.
   Thus part (vii) has no real domain and no real derivative to compute. *)
Lemma lemma_18_1_vii : ∀ x,
  sin x <> 0 -> ~ (-1 <= x / sin x <= 1).
Abort.

Lemma lemma_18_1_viii : ⟦ der ⟧ (λ x, log (3 + e^^4) * e^^(4 * x) + (arcsin x)^^(log 3)) (0, 1) = (λ x, log (3 + e^^4) * (e^^(4 * x) * 4) + log 3 * (arcsin x)^^(log 3 - 1) * (1 / sqrt (1 - x^2))).
Proof.
  auto_diff.
Qed.

Lemma lemma_18_1_ix : ⟦ der ⟧ (λ x, (log x)^^(log x)) (1, ∞) = (λ x, (log x)^^(log x) * ((1 / x) * log (log x) + log x * ((1 / x) / log x))).
Proof.
  auto_diff.
Qed.

Lemma lemma_18_1_x : ⟦ der ⟧ (λ x, x^^(x^^x)) (0, ∞) = (λ x, x^^(x^^x) * ((x^^x * (1 * log x + x * (1 / x))) * log x + (x^^x) * (1 / x))).
Proof.
  auto_diff.
Qed.

Lemma lemma_18_1_xi : ⟦ der ⟧ (λ x, sin (x^^(sin (x^^(sin x))))) (0, ∞) = (λ x, cos (x^^(sin (x^^(sin x)))) * (x^^(sin (x^^(sin x))) * ((cos (x^^(sin x)) * (x^^(sin x) * (cos x * log x + sin x * (1 / x)))) * log x + sin (x^^(sin x)) * (1 / x)))).
Proof.
  auto_diff.
Qed.