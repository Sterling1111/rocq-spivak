(* Compatibility with MathComp SSReflect and Analysis, using Stdlib reals.
   Explicit operations distinguish boolean nat order from propositional order
   and real arithmetic. *)
(* Program's exported morphism arrow conflicts with MathComp's convergence
   arrow. Import the common definitions/tactics without their notations. *)

(*
From Lib Require Imports.
Import -(notations) Imports.
From Stdlib Require Import Reals.
From Lib Require Import Sets Sums.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq bigop.

Lemma mc_nat_le_compat (m n : nat) :
  Peano.le m n <-> is_true (leq m n).
Proof. split; [intro H; apply/leP; exact H | intro H; exact (elimT leP H)]. Qed.

Lemma mc_nat_lt_compat (m n : nat) :
  Peano.lt m n <-> is_true (leq (S m) n).
Proof. split; [intro H; apply/ltP; exact H | intro H; exact (elimT ltP H)]. Qed.

Lemma mc_INR_le_compat (m n : nat) :
  (INR m <= INR n)%R <-> is_true (leq m n).
Proof.
  rewrite <- mc_nat_le_compat.
  split; [apply INR_le | apply le_INR].
Qed.

Lemma mc_INR_lt_compat (m n : nat) :
  (INR m < INR n)%R <-> is_true (leq (S m) n).
Proof.
  rewrite <- mc_nat_lt_compat.
  split; [apply INR_lt | apply lt_INR].
Qed.

Lemma mc_INR_add (m n : nat) :
  INR (addn m n) = (INR m + INR n)%R.
Proof. rewrite addnE. apply plus_INR. Qed.

Lemma mc_INR_mul (m n : nat) :
  INR (muln m n) = (INR m * INR n)%R.
Proof. rewrite mulnE. apply mult_INR. Qed.

(* MathComp sequences and standard lists share their underlying type. *)
Lemma mc_list_mem_compat (T : eqType) (s : seq T) (x : T) :
  List.In x s <-> is_true (x \in s).
Proof.
  induction s as [| y s IH].
  - simpl. split; [contradiction | discriminate].
  - simpl List.In. rewrite in_cons.
    split.
    + intros [H | H]; apply/orP.
      * left. apply/eqP. symmetry. exact H.
      * right. apply IH. exact H.
    + intro H. destruct (elimT orP H) as [Hxy | Hxs].
      * left. symmetry. exact (elimT eqP Hxy).
      * right. apply IH. exact Hxs.
Qed.

Lemma mc_FromList_compat (T : eqType) (s : seq T) (x : T) :
  SetNotations.FromList s x <-> is_true (x \in s).
Proof. apply mc_list_mem_compat. Qed.

(* A finite real sum over a MathComp sequence, without requiring the algebra
   package's canonical real structures. *)
Definition mc_sum (f : nat -> R) (s : seq nat) : R :=
  foldr (fun i acc => Rplus (f i) acc) 0%R s.

Lemma mc_sum_iota (f : nat -> R) (start count : nat) :
  mc_sum f (iota start (S count)) =
  sum_f_R0 (fun k => f (Nat.add k start)) count.
Proof.
  revert start. induction count as [| count IH]; intro start.
  - simpl. unfold mc_sum. simpl. lra.
  - change ((f start + mc_sum f (iota (S start) (S count)))%R =
      sum_f_R0 (fun k => f (Nat.add k start)) (S count)).
    rewrite IH.
    replace (fun k => f (Nat.add k (S start)))
      with (fun k => f (S (Nat.add k start))).
    2: { apply functional_extensionality. intro k. f_equal. lia. }
    rewrite sum_f_R0_fSxplusa_n. lra.
Qed.

(* sum_f has inclusive endpoints. Even when last < first it returns f first,
   so the sequence length is always S (last - first), never zero. *)
Lemma mc_sum_f_compat (f : nat -> R) (first last : nat) :
  sum_f first last f = mc_sum f (iota first (S (Nat.sub last first))).
Proof. symmetry. apply mc_sum_iota. Qed.

Lemma mc_sum_big_compat (f : nat -> R) (s : seq nat) :
  mc_sum f s = \big[Rplus/0%R]_(i <- s) f i.
Proof.
  induction s as [| i s IH].
  - rewrite big_nil. reflexivity.
  - rewrite big_cons. change ((f i + mc_sum f s)%R =
      (f i + \big[Rplus/0%R]_(j <- s) f j)%R).
    rewrite IH. reflexivity.
Qed.

Lemma mc_sum_f_big_compat (f : nat -> R) (first last : nat) :
  sum_f first last f =
  \big[Rplus/0%R]_(i <- iota first (S (Nat.sub last first))) f i.
Proof. rewrite mc_sum_f_compat. apply mc_sum_big_compat. Qed.

From Lib Require Import Limit.
From mathcomp Require Import order ssralg ssrnum boolp classical_sets.
From mathcomp Require Import topology normedtype Rstruct Rstruct_topology.
Import LimitNotations.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.

(* Restricted neighborhoods expressed using the standard real absolute value.
   No assumption that the domain contains or accumulates at a is needed. *)
Lemma mc_within_limit_compat (f : R -> R) (D : R -> Prop) (a L : R) :
  (forall eps, (0 < eps)%R -> exists delta, (0 < delta)%R /\
    forall x, (Rabs (x - a) < delta)%R -> D x ->
      (Rabs (f x - L) < eps)%R) <->
  (f @ within D (nbhs a) --> L).
Proof.
  rewrite cvgrPdistC_lt.
  split.
  - intros H eps Heps.
    destruct (H eps (elimT RltP Heps)) as [delta [Hdelta Hball]].
    rewrite /within -nbhs_ballE.
    exists delta; first exact (introT RltP Hdelta).
    intros x Hx HD. apply/RltP.
    rewrite <- RabsE, <- RminusE.
    apply Hball; last exact HD.
    move: Hx. rewrite /ball /=.
    rewrite <- RabsE, <- RminusE.
    move/RltP. rewrite Rabs_minus_sym. exact (fun H => H).
  - intros H eps Heps.
    specialize (H eps (introT RltP Heps)).
    move: H. rewrite /within -nbhs_ballE.
    intros [delta Hdelta Hball].
    exists delta. split; first exact (elimT RltP Hdelta).
    intros x Hx HD.
    have Hxd : ball a delta x.
    { rewrite /ball /=. apply/RltP.
      rewrite <- RabsE, <- RminusE, Rabs_minus_sym. exact Hx. }
    have Hfx := Hball x Hxd HD.
    move/RltP: Hfx. rewrite <- RabsE, <- RminusE. exact (fun H => H).
Qed.

Lemma mc_limit_compat (f : R -> R) (a L : R) :
  ⟦ lim a ⟧ f = L <-> (f @ within [set~ a] (nbhs a) --> L).
Proof.
  rewrite <- mc_within_limit_compat.
  unfold limit. split; intros H eps Heps;
    destruct (H eps Heps) as [delta [Hdelta Hball]];
    exists delta; split; try exact Hdelta.
  - intros x Hx Hneq. apply Hball. split; last exact Hx.
    apply Rabs_pos_lt. intro Heq. apply Hneq.
    change (x = a). lra.
  - intros x [Hpos Hx]. apply Hball; first exact Hx.
    intro Heq. change (x = a) in Heq. subst x.
    rewrite Rminus_diag, Rabs_R0 in Hpos. lra.
Qed.

Lemma mc_right_limit_compat (f : R -> R) (a L : R) :
  ⟦ lim a⁺ ⟧ f = L <->
  (f @ within [set x | (a < x)%R] (nbhs a) --> L).
Proof.
  rewrite <- mc_within_limit_compat.
  unfold right_limit. split; intros H eps Heps;
    destruct (H eps Heps) as [delta [Hdelta Hball]];
    exists delta; split; try exact Hdelta.
  - intros x Hx Hside. apply Hball.
    rewrite Rabs_right in Hx; lra.
  - intros x Hx. apply Hball; last (simpl; lra).
    rewrite Rabs_right; lra.
Qed.

Lemma mc_left_limit_compat (f : R -> R) (a L : R) :
  ⟦ lim a⁻ ⟧ f = L <->
  (f @ within [set x | (x < a)%R] (nbhs a) --> L).
Proof.
  rewrite <- mc_within_limit_compat.
  unfold left_limit. split; intros H eps Heps;
    destruct (H eps Heps) as [delta [Hdelta Hball]];
    exists delta; split; try exact Hdelta.
  - intros x Hx Hside. apply Hball.
    rewrite Rabs_left in Hx; lra.
  - intros x Hx. apply Hball; last (simpl; lra).
    rewrite Rabs_left; lra.
Qed.
*)