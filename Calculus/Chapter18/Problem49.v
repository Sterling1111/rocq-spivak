From Calculus.Chapter18 Require Import Prelude.
From Stdlib Require Import ZArith.Zdivisibility.

Lemma lemma_18_49 : irrational (log_ 10 2).
Proof.
  intros Hr.
  destruct (rational_representation_positive (log_ 10 2) Hr
    (log_b_pos 10 2 ltac:(lra) ltac:(lra))) as [a [b [Hab [Ha Hb]]]].
  assert (HaZ : (0 < a)%Z) by (apply lt_IZR; exact Ha).
  assert (HbZ : (0 < b)%Z) by (apply lt_IZR; exact Hb).
  assert (Hbase : 2 = 10 ^^ (a / b)).
  { apply (proj2 (log_b_spec 2 10 (a / b) ltac:(lra) ltac:(lra) ltac:(lra))).
    symmetry. exact Hab. }
  assert (Hpowers : 2 ^^ (IZR b) = 10 ^^ (IZR a)).
  { rewrite Hbase at 1. rewrite Rpower_mult by lra.
    replace (a / b * b) with (IZR a) by (field; lra). reflexivity. }
  rewrite !Rpower_IZR_Znonneg in Hpowers by (try lra; lia).
  change ((IZR 2) ^ Z.to_nat b = (IZR 10) ^ Z.to_nat a) in Hpowers.
  rewrite !pow_IZR, !Z2Nat.id in Hpowers by lia.
  apply eq_IZR in Hpowers.
  assert (Hfive : (5 | 10 ^ a)%Z).
  { replace a with (Z.succ (a - 1)) at 1 by lia.
    rewrite Z.pow_succ_r by lia.
    exists (2 * 10 ^ (a - 1))%Z. ring. }
  rewrite <- Hpowers in Hfive.
  assert (Hp5 : Z.prime 5).
  { split; [lia |]. intros n Hn [k Hk].
    assert (n = 2 \/ n = 3 \/ n = 4)%Z by lia.
    destruct H as [H | [H | H]]; subst n; lia. }
  assert (Hp2 : Z.prime 2) by apply Z.prime_2.
  pose proof (Z.divide_prime_pp 5 2 b Hp5 Hp2 ltac:(lia) Hfive). discriminate.
Qed.
