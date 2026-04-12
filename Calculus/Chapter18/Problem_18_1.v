From Calculus.Chapter18 Require Import Prelude.

Lemma lemma_18_1_i : 
  ⟦ der ⟧ (fun x => e^^e^^e^^e^^x) = (fun x => e^^e^^e^^e^^x * e^^e^^e^^x * e^^e^^x * e^^x).
Proof.
  auto_diff.
Qed.

Lemma lemma_18_1_ii : ⟦ der ⟧ (fun x => log(1 + log(1 + log(1 + e^^(1 + e^^(1 + x)))))) = (fun x => (1 / (1 + log(1 + log(1 + e^^(1 + e^^(1 + x)))))) * ((1 / (1 + log(1 + e^^(1 + e^^(1 + x))))) * ((1 / (1 + e^^(1 + e^^(1 + x)))) * (e^^(1 + e^^(1 + x)) * e^^(1 + x))))).
Proof.
  auto_diff.
Qed.

Lemma lemma_18_1_iii : ⟦ der ⟧ (fun x => (sin x)^^(sin (sin x))) (0, π) = (fun x => (sin x)^^(sin (sin x)) * (cos (sin x) * cos x * log (sin x) + sin (sin x) * (cos x / sin x))).
Proof.
  auto_diff.
Qed.

Lemma lemma_18_1_iv : ⟦ der ⟧ (fun x => e^^(∫ 0 x (fun t => e^^(- t^2)))) = (fun x => e^^(∫ 0 x (fun t => e^^(- t^2))) * e^^(- x^2)).
Proof.
  pose (F := fun y => ∫ 0 y (fun t => e^^(- t^2))).
  assert (H1 : ⟦ der ⟧ F = (fun y => e^^(- y^2))).
  { unfold F. apply FTC1_global; auto_cont. }
  replace (fun x => e^^(∫ 0 x (fun t => e^^(- t^2)))) with (fun x => e^^F x) by reflexivity.
  replace (fun x => e^^(∫ 0 x (fun t => e^^(- t^2))) * e^^(- x^2)) with (fun x => e^^F x * e^^(- x^2)) by reflexivity.
  auto_diff.
Qed.

Lemma lemma_18_1_v : ⟦ der ⟧ (fun x => (sin x)^^((sin x)^^(sin x))) (0, π) = (fun x => (sin x)^^((sin x)^^(sin x)) * (((sin x)^^(sin x) * (cos x * log (sin x) + sin x * (cos x / sin x))) * log (sin x) + ((sin x)^^(sin x)) * (cos x / sin x))).
Proof.
  auto_diff.
Qed.

Lemma lemma_18_1_vi : ⟦ der ⟧ (fun x => log (sin x) / x) (0, π) = (fun x => ((cos x / sin x) * x - log (sin x) * 1) / x^2).
Proof.
  auto_diff.
Qed.

Lemma lemma_18_1_vii : ⟦ der ⟧ (fun x => (arcsin (x / sin x))^^(log (sin (e^^x)))) (0, 1) = (fun x => (arcsin (x / sin x))^^(log (sin (e^^x))) * ((cos (e^^x) * e^^x / sin (e^^x)) * log (arcsin (x / sin x)) + log (sin (e^^x)) * ((((1 * sin x - x * cos x) / (sin x)^2) / sqrt (1 - (x / sin x)^2)) / arcsin (x / sin x)))).
Proof.
  auto_diff.
Admitted.

Lemma lemma_18_1_viii : ⟦ der ⟧ (fun x => log (3 + e^^4) * e^^(4 * x) + (arcsin x)^^(log 3)) (0, 1) = (fun x => log (3 + e^^4) * (e^^(4 * x) * 4) + log 3 * (arcsin x)^^(log 3 - 1) * (1 / sqrt (1 - x^2))).
Proof.
  auto_diff.
Qed.

Lemma lemma_18_1_ix : ⟦ der ⟧ (fun x => (log x)^^(log x)) (1, ∞) = (fun x => (log x)^^(log x) * ((1 / x) * log (log x) + log x * ((1 / x) / log x))).
Proof.
  auto_diff.
Qed.

Lemma lemma_18_1_x : ⟦ der ⟧ (fun x => x^^(x^^x)) (0, ∞) = (fun x => x^^(x^^x) * ((x^^x * (1 * log x + x * (1 / x))) * log x + (x^^x) * (1 / x))).
Proof.
  auto_diff.
Qed.

Lemma lemma_18_1_xi : ⟦ der ⟧ (fun x => sin (x^^(sin (x^^(sin x))))) (0, ∞) = (fun x => cos (x^^(sin (x^^(sin x)))) * (x^^(sin (x^^(sin x))) * ((cos (x^^(sin x)) * (x^^(sin x) * (cos x * log x + sin x * (1 / x)))) * log x + sin (x^^(sin x)) * (1 / x)))).
Proof.
  auto_diff.
Qed.