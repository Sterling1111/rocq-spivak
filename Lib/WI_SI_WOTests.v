From Lib Require Import Imports WI_SI_WO.

Local Open Scope nat_scope.

(** The recursive call changes an already introduced accumulator. *)
Example strong_nat_generalizes : forall n acc : nat, n + acc = acc + n.
Proof.
  intros n acc. strong_induction n as recurse. intro acc.
  destruct n as [|k]; [lia |].
  specialize (recurse k ltac:(lia) (S acc)). lia.
Qed.

(** The induction variable can still be quantified, and default names are fresh. *)
Example strong_nat_unintroduced : forall n : nat, n + 0 = n.
Proof.
  strong_induction n. destruct n as [|k]; [reflexivity |].
  simpl. rewrite IH by lia. reflexivity.
Qed.

Definition induction_test_nat := nat.

Example strong_nat_type_alias : forall q : induction_test_nat, q + 0 = q.
Proof.
  strong_induction q as smaller. destruct q as [|k]; [reflexivity |].
  simpl. rewrite smaller by lia. reflexivity.
Qed.

Example strong_nat_name_collision (IH : nat) : forall n : nat, n + IH = IH + n.
Proof.
  intro n. strong_induction n. intro IH.
  destruct n as [|k]; [lia |]. specialize (IH0 k ltac:(lia) (S IH)). lia.
Qed.

(** Local definitions and hypotheses whose types depend on n are generalized. *)
Example strong_nat_local_definition (m : nat) : m + 0 = m.
Proof.
  set (n := m). change (n + 0 = n).
  strong_induction_nat n. intro m.
  destruct n as [|k]; [reflexivity |].
  simpl. rewrite (IH k ltac:(lia) m). reflexivity.
Qed.

Inductive counted : nat -> Type :=
| counted_zero : counted 0
| counted_next : forall n, counted n -> counted (S n).

Fixpoint counted_size n (c : counted n) : nat :=
  match c with
  | counted_zero => 0
  | counted_next k c' => S (counted_size k c')
  end.

Example strong_nat_dependent : forall n (c : counted n), counted_size n c = n.
Proof.
  intros n c. strong_induction n as recurse. intro c.
  destruct c as [|k c]; [reflexivity |].
  simpl. rewrite (recurse k ltac:(lia) c). reflexivity.
Qed.

(** A second generalized parameter and its dependent hypotheses remain usable. *)
Example strong_nat_hypotheses : forall n m : nat, m = n -> n + m = m + n.
Proof.
  intros n m H. strong_induction n as recurse. intros m H.
  destruct n as [|k]; [lia |].
  specialize (recurse k ltac:(lia) k eq_refl). lia.
Qed.

(** Measures allow recursion on lists other than the immediate tail. *)
Example strong_list_measure : forall (A : Type) (xs : list A),
  List.length (rev xs) = List.length xs.
Proof.
  intros A xs. strong_induction xs using (@List.length A) as shorter.
  destruct xs as [|x xs]; [reflexivity |].
  simpl. rewrite length_app, shorter by (simpl; lia). simpl. lia.
Qed.

Example strong_measure_generalizes : forall n acc : nat, n + acc = acc + n.
Proof.
  intros n acc. strong_induction n using (fun k : nat => k). intro acc.
  destruct n as [|k]; [lia |].
  specialize (IH k ltac:(simpl; lia) (S acc)). lia.
Qed.

Inductive reverse_peels : list nat -> Prop :=
| peels_nil : reverse_peels nil
| peels_cons : forall h xs, reverse_peels (rev xs) -> reverse_peels (h :: xs).

Example strong_measure_nonstructural : forall xs, reverse_peels xs.
Proof.
  strong_induction xs using (@List.length nat) as shorter.
  destruct xs as [|h xs]; constructor.
  apply shorter. rewrite length_rev. simpl. lia.
Qed.

Local Open Scope Z_scope.

(** Keep the existing integer interface and its first-premise introduction. *)
Example strong_Z_legacy : forall z : Z, 0 <= z -> exists k : nat, z = Z.of_nat k.
Proof.
  intro z. strong_induction z.
  destruct (Z.eq_dec z 0) as [-> | Hne]; [exists 0%nat; reflexivity |].
  destruct (IH (z - 1) ltac:(lia) ltac:(lia)) as [k Hk].
  exists (S k). rewrite Nat2Z.inj_succ. lia.
Qed.

(** No generalized premise is required, and existing H1 names cause no clash. *)
Example strong_Z_no_premise : (0 = 0)%Z.
Proof.
  set (z := 0%Z). change (z = z).
  strong_induction_Z_pos z. reflexivity.
Qed.

Example strong_Z_unintroduced : forall z : Z, 0 <= z -> z + 0 = z.
Proof. strong_induction z as smaller. lia. Qed.

Example strong_Z_custom_bound_name : forall z : Z, 0 <= z -> z + 0 = z.
Proof. strong_induction z as Hlower. lia. Qed.

Example strong_Z_named (H1 : Z) : forall z : Z, 0 <= z -> z + H1 = H1 + z.
Proof.
  intro z. strong_induction z as recurse. intro Hz.
  destruct (Z.eq_dec z 0) as [-> | Hne]; [lia |].
  specialize (recurse (z - 1) ltac:(lia) H1 ltac:(lia)). lia.
Qed.

(** Arbitrary, even negative, lower bounds. *)
Inductive above_minus_three : Z -> Prop :=
| above_base : above_minus_three (-3)
| above_step : forall z, above_minus_three z -> above_minus_three (z + 1).

Example strong_Z_negative_bound : forall z, -3 <= z -> above_minus_three z.
Proof.
  intro z. strong_induction z from (-3) as recurse. intro Hz.
  destruct (Z.eq_dec z (-3)) as [-> | Hne]; [constructor |].
  replace z with ((z - 1) + 1) by lia. constructor.
  apply recurse; lia.
Qed.

Example strong_Z_symbolic_bound : forall lower z, lower <= z ->
  exists k : nat, z = lower + Z.of_nat k.
Proof.
  intros lower z Hz. strong_induction z from lower. intro Hz.
  destruct (Z.eq_dec z lower) as [-> | Hne]; [exists 0%nat; lia |].
  destruct (IH (z - 1) ltac:(lia) ltac:(lia)) as [k Hk].
  exists (S k). rewrite Nat2Z.inj_succ. lia.
Qed.

(** Missing lower-bound evidence becomes an obligation, never an assumption. *)
Example strong_Z_bound_obligation (P : Z -> Prop) (z : Z)
  (bound : P z -> 4 <= z) (given : P z) : 4 <= z.
Proof.
  strong_induction z from 4 as recurse.
  - exact (bound given).
  - intros P bound given. assumption.
Qed.

(** Invalid inputs fail without changing the proof state. *)
Example strong_rejects_unbounded_Z : forall z : Z, z = z.
Proof.
  intro z. Fail strong_induction z. reflexivity.
Qed.

Example strong_rejects_other_types : forall b : bool, b = b.
Proof.
  intro b. Fail strong_induction b. reflexivity.
Qed.
