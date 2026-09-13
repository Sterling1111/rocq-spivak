From Lib Require Import Imports.
From Lib Require Export FunctionalMatrix.
From Stdlib Require Export QArith.Qcanon.
From Stdlib Require Import Sorting.Permutation.

#[export] Instance Zero_Qc : Zero Qc := 0%Qc.
#[export] Instance One_Qc : One Qc := 1%Qc.
#[export] Instance Add_Qc : Add Qc := Qcplus.
#[export] Instance Mul_Qc : Mul Qc := Qcmult.
#[export] Instance Scale_Qc : Scale Qc Qc := Qcmult.

(** Extend the standard Qc scope to all rational numerals, including finite
    decimals. Literals remain exact: 1.5 denotes the rational number 3/2. *)
Inductive QcNumeral := QcNumeral_of_Q : QArith_base.IQ -> QcNumeral.
Definition Qc_of_number (n : Number.number) : QcNumeral :=
  QcNumeral_of_Q (QArith_base.of_number n).
Definition Qc_to_number (q : QcNumeral) : option Number.number :=
  match q with QcNumeral_of_Q x => QArith_base.to_number x end.
Number Notation Qc Qc_of_number Qc_to_number (via QcNumeral
  mapping [Q2Qc => QcNumeral_of_Q,
           Qmake => QArith_base.IQmake, Qmult => QArith_base.IQmult,
           Qdiv => QArith_base.IQdiv, Z.pow_pos => QArith_base.IZpow_pos,
           Z0 => QArith_base.IZ0, Zpos => QArith_base.IZpos, Zneg => QArith_base.IZneg])
  : Qc_scope.

(** A span includes all finite linear combinations of its generating rows. *)
Inductive row_span {K : Type} `{Zero K} `{Add K} `{Mul K}
    (rows : list (nat -> K)) : (nat -> K) -> Prop :=
| span_zero : row_span rows (fun _ => zero)
| span_row : forall r, In r rows -> row_span rows r
| span_add : forall r s, row_span rows r -> row_span rows s ->
    row_span rows (fun j => add (r j) (s j))
| span_scale : forall a r, row_span rows r ->
    row_span rows (fun j => mul a (r j)).

Definition rows_equivalent {K : Type} `{Zero K} `{Add K} `{Mul K}
    (xs ys : list (nat -> K)) : Prop :=
  (forall r, In r xs -> row_span ys r) /\
  (forall r, In r ys -> row_span xs r).

Lemma row_span_substitute {K} `{Zero K} `{Add K} `{Mul K} xs ys :
  (forall r, In r xs -> row_span ys r) ->
  forall r, row_span xs r -> row_span ys r.
Proof. intros Hsub r Hr. induction Hr; eauto using row_span. Qed.

Lemma rows_equivalent_refl {K} `{Zero K} `{Add K} `{Mul K} xs :
  rows_equivalent xs xs.
Proof. split; intros; now apply span_row. Qed.

Lemma rows_equivalent_sym {K} `{Zero K} `{Add K} `{Mul K} xs ys :
  rows_equivalent xs ys -> rows_equivalent ys xs.
Proof. intros [Hxy Hyx]. split; assumption. Qed.

Lemma rows_equivalent_trans {K} `{Zero K} `{Add K} `{Mul K} xs ys zs :
  rows_equivalent xs ys -> rows_equivalent ys zs -> rows_equivalent xs zs.
Proof.
  intros [Hxy Hyx] [Hyz Hzy]. split; intros r Hr.
  - eapply row_span_substitute; [exact Hyz | now apply Hxy].
  - eapply row_span_substitute; [exact Hyx | now apply Hzy].
Qed.

Lemma rows_equivalent_cons {K} `{Zero K} `{Add K} `{Mul K} r xs ys :
  rows_equivalent xs ys -> rows_equivalent (r :: xs) (r :: ys).
Proof.
  intros [Hxy Hyx]. split; intros s [<- | Hs]; try (apply span_row; now left).
  - eapply row_span_substitute; [|now apply Hxy].
    intros t Ht. apply span_row. now right.
  - eapply row_span_substitute; [|now apply Hyx].
    intros t Ht. apply span_row. now right.
Qed.

Lemma rows_equivalent_permutation {K} `{Zero K} `{Add K} `{Mul K} xs ys :
  Permutation xs ys -> rows_equivalent xs ys.
Proof.
  intro Hp. split; intros r Hr; apply span_row.
  - eapply Permutation_in; eauto.
  - eapply Permutation_in; [apply Permutation_sym; exact Hp | exact Hr].
Qed.

(** A pivot is the first nonzero entry of its row. Pivot columns strictly
    increase, and zero rows come last. In reduced form each pivot is one and
    its column is zero in all the other rows. *)
Definition zero_before {K : Type} `{Zero K} (column : nat) (r : nat -> K) :=
  forall j, (j < column)%nat -> r j = zero.

Inductive echelon_shape {K : Type} `{Zero K} `{One K}
    (width : nat) (reduced : bool) : nat -> list (nat -> K) -> list nat -> Prop :=
| shape_zero : forall start rows,
    Forall (zero_before width) rows ->
    echelon_shape width reduced start rows []
| shape_pivot : forall start p r rows pivots,
    (start <= p < width)%nat ->
    r p <> zero -> zero_before p r ->
    echelon_shape width reduced (S p) rows pivots ->
    (reduced = true -> r p = one /\ Forall (fun k => r k = zero) pivots) ->
    echelon_shape width reduced start (r :: rows) (p :: pivots).

Lemma echelon_shape_weaken {K} `{Zero K} `{One K} n reduced c d rows ps :
  (c <= d)%nat -> echelon_shape n reduced d rows ps ->
  echelon_shape n reduced c rows ps.
Proof.
  intros Hcd Hshape. inversion Hshape; subst.
  - now apply shape_zero.
  - eapply shape_pivot; eauto; lia.
Qed.

Lemma echelon_shape_before {K} `{Zero K} `{One K} n reduced c rows ps :
  echelon_shape n reduced c rows ps -> (c <= n)%nat ->
  Forall (zero_before c) rows.
Proof.
  intro Hshape. induction Hshape; intro Hcn.
  - eapply Forall_impl; [|eassumption]. unfold zero_before; intros r Hr j Hj. apply Hr; lia.
  - constructor.
    + unfold zero_before in *. intros j Hj. apply H3; lia.
    + eapply Forall_impl; [|apply IHHshape; lia].
      unfold zero_before; intros s Hs j Hj. apply Hs; lia.
Qed.

Lemma echelon_shape_pivots {K} `{Zero K} `{One K} n reduced c rows ps :
  echelon_shape n reduced c rows ps ->
  Forall (fun p => (c <= p < n)%nat) ps.
Proof.
  intro Hshape. induction Hshape; [constructor|].
  constructor; [assumption|]. eapply Forall_impl; [|exact IHHshape]. intros k Hk. cbn in Hk. lia.
Qed.

Module RationalElimination.
Local Open Scope Qc_scope.
Definition row := nat -> Qc.
Definition normalize (p : nat) (r : row) : row := fun j => r j / r p.
Definition subtract (p : nat) (s r : row) : row := fun j => r j - r p * s j.

Fixpoint pick (p : nat) (rows : list row) : option (row * list row) :=
  match rows with
  | [] => None
  | r :: rs =>
      if Qc_eq_dec (r p) 0 then
        match pick p rs with
        | None => None
        | Some (s, ss) => Some (s, r :: ss)
        end
      else Some (r, rs)
  end.

(** Remove the components in the pivot rows of an already reduced matrix. *)
Fixpoint clear (r : row) (rows : list row) (pivots : list nat) : row :=
  match rows, pivots with
  | s :: ss, p :: ps => clear (subtract p s r) ss ps
  | _, _ => r
  end.

(** One recursive call per column. Zero rows are retained, preserving shape.
    [reduced = false] computes normalized REF; [true] computes RREF. *)
Fixpoint reduce (reduced : bool) (fuel column : nat) (rows : list row)
    : list row * list nat :=
  match fuel with
  | O => (rows, [])
  | S fuel' =>
      match pick column rows with
      | None => reduce reduced fuel' (S column) rows
      | Some (r, rs) =>
          let pivot := normalize column r in
          let '(tail, pivots) :=
            reduce reduced fuel' (S column) (map (subtract column pivot) rs) in
          ((if reduced then clear pivot tail pivots else pivot) :: tail,
           column :: pivots)
      end
  end.

Lemma pick_some p rows r rs :
  pick p rows = Some (r, rs) ->
  r p <> 0 /\ Permutation rows (r :: rs).
Proof.
  revert r rs. induction rows as [|s ss IH]; intros r rs Hp; simpl in Hp; [discriminate|].
  destruct (Qc_eq_dec (s p) 0).
  - destruct (pick p ss) as [[t ts]|] eqn:Ht; [|discriminate].
    inversion Hp; subst. destruct (IH _ _ eq_refl) as [Hnz Hperm]. split; [exact Hnz|].
    eapply Permutation_trans; [apply perm_skip; exact Hperm|apply perm_swap].
  - inversion Hp; subst. split; [assumption|apply Permutation_refl].
Qed.

Lemma pick_none p rows :
  pick p rows = None -> Forall (fun r => r p = 0) rows.
Proof.
  induction rows as [|r rs IH]; simpl; intro Hp; [constructor|].
  destruct (Qc_eq_dec (r p) 0); [|discriminate].
  destruct (pick p rs) as [[s ss]|] eqn:Hs; [discriminate|].
  constructor; [assumption|now apply IH].
Qed.

Lemma normalize_equivalent p r rs : r p <> 0 ->
  rows_equivalent (r :: rs) (normalize p r :: rs).
Proof.
  intro Hnz. split; intros s [<-|Hs]; try (apply span_row; now right).
  - replace r with (fun j => mul (r p) (normalize p r j)) at 2.
    + apply span_scale. apply span_row. now left.
    + apply functional_extensionality; intro j.
      unfold normalize, mul, Mul_Qc. field. exact Hnz.
  - change (row_span (r :: rs) (fun j => r j / r p)).
    replace (fun j => r j / r p) with (fun j => mul (/ r p) (r j)).
    + apply span_scale. apply span_row. now left.
    + apply functional_extensionality; intro j. unfold mul, Mul_Qc. field. exact Hnz.
Qed.

Lemma subtract_span p s r rows :
  row_span rows s -> row_span rows r -> row_span rows (subtract p s r).
Proof.
  intros Hs Hr. unfold subtract.
  replace (fun j => r j - r p * s j)
    with (fun j => add (r j) (mul (- r p) (s j))).
  - apply span_add; [exact Hr|now apply span_scale].
  - apply functional_extensionality; intro j. unfold add, mul, Add_Qc, Mul_Qc. ring.
Qed.

Lemma subtract_equivalent p s rs :
  rows_equivalent (s :: rs) (s :: map (subtract p s) rs).
Proof.
  split; intros r [<-|Hr]; try (apply span_row; now left).
  - replace r with (fun j => add (subtract p s r j) (mul (r p) (s j))).
    + apply span_add.
      * apply span_row. right. now apply in_map.
      * apply span_scale. apply span_row. now left.
    + apply functional_extensionality; intro j.
      unfold subtract, add, mul, Add_Qc, Mul_Qc. ring.
  - apply in_map_iff in Hr. destruct Hr as [t [<- Ht]].
    apply subtract_span; apply span_row; [now left|now right].
Qed.

Lemma replace_head r s rs :
  row_span (r :: rs) s -> row_span (s :: rs) r ->
  rows_equivalent (r :: rs) (s :: rs).
Proof.
  intros Hs Hr. split; intros t [<-|Ht]; try assumption; apply span_row; now right.
Qed.

Lemma clear_equivalent r rs ps :
  rows_equivalent (r :: rs) (clear r rs ps :: rs).
Proof.
  revert r ps. induction rs as [|s ss IH]; intros r [|p ps]; simpl;
    try apply rows_equivalent_refl.
  eapply rows_equivalent_trans with (ys := subtract p s r :: s :: ss).
  - apply replace_head.
    + apply subtract_span; apply span_row; simpl; auto.
    + replace r with (fun j => add (subtract p s r j) (mul (r p) (s j))) at 2.
      * apply span_add; [apply span_row; now left|].
        apply span_scale. apply span_row. right; now left.
      * apply functional_extensionality; intro j.
        unfold subtract, add, mul, Add_Qc, Mul_Qc. ring.
  - eapply rows_equivalent_trans.
    + apply rows_equivalent_permutation. apply perm_swap.
    + eapply rows_equivalent_trans.
      * apply rows_equivalent_cons. apply IH.
      * apply rows_equivalent_permutation. apply perm_swap.
Qed.

Lemma reduce_equivalent reduced fuel column rows :
  rows_equivalent rows (fst (reduce reduced fuel column rows)).
Proof.
  revert column rows. induction fuel as [|fuel IH]; intros column rows; simpl.
  - apply rows_equivalent_refl.
  - destruct (pick column rows) as [[r rs]|] eqn:Hp; [|apply IH].
    destruct (pick_some _ _ _ _ Hp) as [Hnz Hperm].
    destruct (reduce reduced fuel (S column)
      (map (subtract column (normalize column r)) rs)) as [tail ps] eqn:Ht; simpl.
    eapply rows_equivalent_trans; [apply rows_equivalent_permutation; exact Hperm|].
    eapply rows_equivalent_trans; [apply normalize_equivalent; exact Hnz|].
    eapply rows_equivalent_trans; [apply subtract_equivalent|].
    eapply rows_equivalent_trans.
    + apply rows_equivalent_cons.
      specialize (IH (S column) (map (subtract column (normalize column r)) rs)).
      rewrite Ht in IH. exact IH.
    + destruct reduced; [apply clear_equivalent|apply rows_equivalent_refl].
Qed.

Lemma reduce_length reduced fuel column rows :
  length (fst (reduce reduced fuel column rows)) = length rows.
Proof.
  revert column rows. induction fuel as [|fuel IH]; intros column rows; simpl; [reflexivity|].
  destruct (pick column rows) as [[r rs]|] eqn:Hp; [|apply IH].
  destruct (pick_some _ _ _ _ Hp) as [_ Hperm].
  pose proof (Permutation_length Hperm) as Hlen.
  specialize (IH (S column) (map (subtract column (normalize column r)) rs)).
  destruct (reduce reduced fuel (S column)
    (map (subtract column (normalize column r)) rs)) as [tail ps].
  simpl in *. rewrite length_map in IH. lia.
Qed.
Lemma clear_at r rows ps j :
  Forall (fun s => s j = 0) rows -> clear r rows ps j = r j.
Proof.
  revert r ps. induction rows as [|s ss IH]; intros r [|p ps] Hz; simpl; try reflexivity.
  inversion Hz; subst. rewrite IH by assumption. unfold subtract. rewrite H1. ring.
Qed.

Lemma clear_before c r rows ps :
  zero_before c r -> Forall (zero_before c) rows -> zero_before c (clear r rows ps).
Proof.
  intros Hr Hrows j Hj. rewrite clear_at; [now apply Hr|].
  eapply Forall_impl; [|exact Hrows]. intros s Hs. now apply Hs.
Qed.

Lemma clear_pivots n c rows ps r :
  echelon_shape n true c rows ps -> Forall (fun p => clear r rows ps p = 0) ps.
Proof.
  intro Hshape. revert r. induction Hshape as
    [c rows Hz | c p r rows ps Hbounds Hnz Hbefore Hshape IH Hred];
    intro t; [constructor|].
  cbn [clear]. constructor.
  - rewrite clear_at.
    + unfold subtract. destruct (Hred eq_refl) as [Hp _].
      change (r p = 1) in Hp. rewrite Hp. ring.
    + pose proof (echelon_shape_before _ _ _ _ _ Hshape ltac:(lia)) as Htailbefore.
      eapply Forall_impl; [|exact Htailbefore]. intros s Hs. apply Hs. lia.
  - apply IH.
Qed.

Lemma reduce_shape reduced fuel column rows :
  Forall (zero_before column) rows ->
  echelon_shape (column + fuel) reduced column
    (fst (reduce reduced fuel column rows)) (snd (reduce reduced fuel column rows)).
Proof.
  revert column rows. induction fuel as [|fuel IH]; intros c rows Hbefore.
  - simpl. apply shape_zero. now rewrite Nat.add_0_r.
  - cbn [reduce]. destruct (pick c rows) as [[r rs]|] eqn:Hp.
    + destruct (pick_some _ _ _ _ Hp) as [Hnz Hperm].
      assert (Hsplit : Forall (zero_before c) (r :: rs)).
      { eapply Permutation_Forall; eauto. }
      inversion Hsplit as [|? ? Hr Hrs]; subst.
      assert (Hnorm : normalize c r c = 1).
      { unfold normalize. field. exact Hnz. }
      assert (Hnorm_before : zero_before c (normalize c r)).
      { intros j Hj. unfold normalize. rewrite Hr by exact Hj. change (0 / r c = 0). field. exact Hnz. }
      assert (Hnext : Forall (zero_before (S c)) (map (subtract c (normalize c r)) rs)).
      { apply Forall_forall. intros s Hs. apply in_map_iff in Hs.
        destruct Hs as [t [<- Ht]]. intros j Hj.
        unfold subtract. destruct (Nat.eq_dec j c) as [->|Hjc].
        - rewrite Hnorm. change (t c - t c * 1 = 0). ring.
        - assert (Hj' : (j < c)%nat) by lia.
          rewrite Hnorm_before by exact Hj'.
          rewrite (proj1 (Forall_forall _ _) Hrs t Ht j Hj'). change (0 - t c * 0 = 0). ring. }
      specialize (IH (S c) _ Hnext).
      destruct (reduce reduced fuel (S c)
        (map (subtract c (normalize c r)) rs)) as [tail ps] eqn:Ht.
      cbn in IH |- *. replace (S c + fuel)%nat with (c + S fuel)%nat in IH by lia.
      assert (Htail : Forall (zero_before (S c)) tail).
      { eapply echelon_shape_before; [exact IH|lia]. }
      assert (Htail_c : Forall (fun s => s c = 0) tail).
      { eapply Forall_impl; [|exact Htail]. intros s Hs. apply Hs. lia. }
      assert (Htail_before : Forall (zero_before c) tail).
      { eapply Forall_impl; [|exact Htail]. intros s Hs j Hj. apply Hs. lia. }
      replace (c + S fuel)%nat with (S (c + fuel))%nat by lia.
      eapply shape_pivot with (p := c); try lia; try exact IH.
      * destruct reduced; [rewrite clear_at by exact Htail_c|];
          rewrite Hnorm; discriminate.
      * destruct reduced; [apply clear_before; assumption|exact Hnorm_before].
      * destruct reduced; intro Heq; [|discriminate]. split.
        -- rewrite clear_at by exact Htail_c. exact Hnorm.
        -- eapply clear_pivots. exact IH.
    + pose proof (pick_none _ _ Hp) as Hz.
      assert (Hnext : Forall (zero_before (S c)) rows).
      { apply Forall_forall. intros r Hr j Hj.
        destruct (Nat.eq_dec j c) as [->|Hjc].
        - exact (proj1 (Forall_forall _ _) Hz r Hr).
        - apply (proj1 (Forall_forall _ _) Hbefore r Hr). lia. }
      specialize (IH (S c) _ Hnext).
      replace (S c + fuel)%nat with (c + S fuel)%nat in IH by lia.
      eapply echelon_shape_weaken with (d := S c); [lia|exact IH].
Qed.
Lemma reduce_zero_at reduced fuel column rows j :
  Forall (fun r => r j = 0) rows ->
  Forall (fun r => r j = 0) (fst (reduce reduced fuel column rows)).
Proof.
  revert column rows. induction fuel as [|fuel IH]; intros c rows Hz; cbn [reduce]; [exact Hz|].
  destruct (pick c rows) as [[r rs]|] eqn:Hp; [|now apply IH].
  destruct (pick_some _ _ _ _ Hp) as [Hnz Hperm].
  assert (Hsplit : Forall (fun s => s j = 0) (r :: rs)).
  { eapply Permutation_Forall; eauto. }
  inversion Hsplit as [|? ? Hr Hrs]; subst.
  assert (Hnorm : normalize c r j = 0).
  { unfold normalize. rewrite Hr. field. exact Hnz. }
  assert (Hnext : Forall (fun s => s j = 0) (map (subtract c (normalize c r)) rs)).
  { apply Forall_forall. intros s Hs. apply in_map_iff in Hs.
    destruct Hs as [t [<- Ht]]. unfold subtract.
    rewrite Hnorm, (proj1 (Forall_forall _ _) Hrs t Ht). ring. }
  specialize (IH (S c) _ Hnext).
  destruct (reduce reduced fuel (S c)
    (map (subtract c (normalize c r)) rs)) as [tail ps]; cbn in IH |- *.
  constructor; [|exact IH]. destruct reduced; [rewrite clear_at by exact IH|]; exact Hnorm.
Qed.
(** Materialize intermediate coordinates so evaluating a later pivot does
    not repeatedly expand the entire history of previous row operations. *)
Definition cache (width : nat) (r : row) : row :=
  let values := map r (seq 0 width) in
  fun j => List.nth j values 0.

Definition supported (width : nat) (r : row) : Prop :=
  forall j, (width <= j)%nat -> r j = 0.

Lemma cache_eq width r : supported width r -> cache width r = r.
Proof.
  intro Hr. apply functional_extensionality; intro j.
  destruct (lt_dec j width) as [Hj|Hj].
  - change (Matrix.vector_nth (@vector_init Qc width r) j 0 = r j).
    now apply vector_init_nth.
  - unfold cache. rewrite nth_overflow.
    + symmetry. apply Hr. lia.
    + rewrite length_map, length_seq. lia.
Qed.

Lemma normalize_supported width p r : supported width r -> supported width (normalize p r).
Proof.
  intros Hr j Hj. unfold normalize, Qcdiv. rewrite Hr by exact Hj. ring.
Qed.

Lemma subtract_supported width p r s :
  supported width r -> supported width s -> supported width (subtract p s r).
Proof.
  intros Hr Hs j Hj. unfold subtract. rewrite Hr, Hs by exact Hj. ring.
Qed.

Lemma reduce_supported width reduced fuel c rows :
  Forall (supported width) rows ->
  Forall (supported width) (fst (reduce reduced fuel c rows)).
Proof.
  intros Hrows. apply Forall_forall. intros r Hr j Hj.
  assert (Hz : Forall (fun s => s j = 0) rows).
  { eapply Forall_impl; [|exact Hrows]. intros s Hs. now apply Hs. }
  exact (proj1 (Forall_forall _ _) (reduce_zero_at _ _ _ _ _ Hz) r Hr).
Qed.

Fixpoint clear_cached width (r : row) (rows : list row) (pivots : list nat) : row :=
  match rows, pivots with
  | s :: ss, p :: ps => clear_cached width (cache width (subtract p s r)) ss ps
  | _, _ => r
  end.

Fixpoint reduce_cached width (reduced : bool) (fuel column : nat) (rows : list row)
    : list row * list nat :=
  match fuel with
  | O => (rows, [])
  | S fuel' =>
      match pick column rows with
      | None => reduce_cached width reduced fuel' (S column) rows
      | Some (r, rs) =>
          let pivot := cache width (normalize column r) in
          let '(tail, pivots) := reduce_cached width reduced fuel' (S column)
            (map (fun s => cache width (subtract column pivot s)) rs) in
          ((if reduced then clear_cached width pivot tail pivots else pivot) :: tail,
           column :: pivots)
      end
  end.

Lemma clear_cached_eq width rows ps r :
  supported width r -> Forall (supported width) rows ->
  clear_cached width r rows ps = clear r rows ps.
Proof.
  revert ps r. induction rows as [|s ss IH]; intros [|p ps] r Hr Hrows;
    cbn [clear_cached clear]; try reflexivity.
  inversion Hrows; subst. rewrite cache_eq by (apply subtract_supported; assumption).
  apply IH; [apply subtract_supported; assumption|assumption].
Qed.

Lemma reduce_cached_eq width reduced fuel c rows :
  Forall (supported width) rows ->
  reduce_cached width reduced fuel c rows = reduce reduced fuel c rows.
Proof.
  revert c rows. induction fuel as [|fuel IH]; intros c rows Hrows; cbn [reduce_cached reduce];
    [reflexivity|].
  destruct (pick c rows) as [[r rs]|] eqn:Hp; [|now apply IH].
  destruct (pick_some _ _ _ _ Hp) as [_ Hperm].
  assert (Hsplit : Forall (supported width) (r :: rs)).
  { eapply Permutation_Forall; eauto. }
  inversion Hsplit as [|? ? Hr Hrs]; subst.
  assert (Hnorm : supported width (normalize c r)) by now apply normalize_supported.
  rewrite (cache_eq width (normalize c r) Hnorm).
  assert (Hnext : Forall (supported width) (map (subtract c (normalize c r)) rs)).
  { apply Forall_forall. intros s Hs. apply in_map_iff in Hs.
    destruct Hs as [t [<- Ht]]. apply subtract_supported; [|exact Hnorm].
    exact (proj1 (Forall_forall _ _) Hrs t Ht). }
  assert (Hmap : map (fun s => cache width (subtract c (normalize c r) s)) rs =
    map (subtract c (normalize c r)) rs).
  { apply map_ext_in. intros s Hs. apply cache_eq, subtract_supported; [|exact Hnorm].
    exact (proj1 (Forall_forall _ _) Hrs s Hs). }
  rewrite Hmap, IH by exact Hnext.
  pose proof (reduce_supported width reduced fuel (S c) _ Hnext) as Htail.
  destruct (reduce reduced fuel (S c) (map (subtract c (normalize c r)) rs))
    as [tail ps]. cbn in Htail |- *. destruct reduced; [|reflexivity].
  now rewrite clear_cached_eq.
Qed.

End RationalElimination.

(** Public predicates use the ordinary list-backed matrix type. Entries beyond
    the declared width are extended by zero only in this internal row view. *)
Definition matrix_rows {K m n} `{Zero K} (M : matrix K m n) : list (nat -> K) :=
  map (fun r j => List.nth j (vlist r) zero) (vlist M).

Definition row_equivalent {K m n} `{Zero K} `{Add K} `{Mul K}
    (A B : matrix K m n) : Prop := rows_equivalent (matrix_rows A) (matrix_rows B).

Definition is_ref {K m n} `{Zero K} `{One K} (M : matrix K m n) : Prop :=
  exists pivots, echelon_shape n false 0 (matrix_rows M) pivots.

Definition is_rref {K m n} `{Zero K} `{One K} (M : matrix K m n) : Prop :=
  exists pivots, echelon_shape n true 0 (matrix_rows M) pivots.

Definition rows_to_matrix {K m n} (rows : list (nat -> K))
    (Hlength : length rows = m) : matrix K m n.
Proof.
  refine (mk_vector (map (fun r => @vector_init K n r) rows) _).
  now rewrite length_map.
Defined.

Lemma matrix_rows_length {K m n} `{Zero K} (M : matrix K m n) :
  length (matrix_rows M) = m.
Proof. unfold matrix_rows. rewrite length_map. apply vlist_length. Qed.

Lemma matrix_rows_outside {K m n} `{Zero K} (M : matrix K m n) j :
  (n <= j)%nat -> Forall (fun r => r j = zero) (matrix_rows M).
Proof.
  intro Hj. unfold matrix_rows. apply Forall_forall. intros r Hr.
  apply in_map_iff in Hr. destruct Hr as [v [<- Hv]].
  apply nth_overflow. rewrite (vlist_length K n v). exact Hj.
Qed.

Lemma rows_to_matrix_rows {K m n} `{Zero K} rows Hlength :
  (forall j, (n <= j)%nat -> Forall (fun r => r j = zero) rows) ->
  matrix_rows (@rows_to_matrix K m n rows Hlength) = rows.
Proof.
  intro Houtside. unfold matrix_rows, rows_to_matrix; cbn [vlist]. rewrite map_map.
  rewrite <- (map_id rows) at 2. apply map_ext_in. intros r Hr.
  apply functional_extensionality. intro j. destruct (lt_dec j n) as [Hj|Hj].
  - change (Matrix.vector_nth (@vector_init K n r) j zero = r j).
    now apply vector_init_nth.
  - rewrite nth_overflow.
    + symmetry. exact (proj1 (Forall_forall _ _) (Houtside j ltac:(lia)) r Hr).
    + rewrite vlist_length. lia.
Qed.

Definition matrix_reduce {m n} (reduced : bool) (M : matrix Qc m n) : matrix Qc m n.
Proof.
  refine (rows_to_matrix (fst (RationalElimination.reduce_cached n reduced n 0 (matrix_rows M))) _).
  rewrite RationalElimination.reduce_cached_eq.
  2: { apply Forall_forall. intros r Hr j Hj.
       exact (proj1 (Forall_forall _ _) (matrix_rows_outside M j Hj) r Hr). }
  rewrite RationalElimination.reduce_length. apply matrix_rows_length.
Defined.

Definition matrix_ref {m n} (M : matrix Qc m n) : matrix Qc m n := matrix_reduce false M.
Definition matrix_rref {m n} (M : matrix Qc m n) : matrix Qc m n := matrix_reduce true M.
Definition matrix_pivots {m n} (M : matrix Qc m n) : list nat :=
  snd (RationalElimination.reduce_cached n false n 0 (matrix_rows M)).

Lemma matrix_reduce_rows {m n} reduced (M : matrix Qc m n) :
  matrix_rows (matrix_reduce reduced M) =
  fst (RationalElimination.reduce reduced n 0 (matrix_rows M)).
Proof.
  unfold matrix_reduce. rewrite rows_to_matrix_rows.
  - rewrite RationalElimination.reduce_cached_eq; [reflexivity|].
    apply Forall_forall. intros r Hr j Hj.
    exact (proj1 (Forall_forall _ _) (matrix_rows_outside M j Hj) r Hr).
  - intros j Hj. rewrite RationalElimination.reduce_cached_eq.
    + apply RationalElimination.reduce_zero_at. now apply matrix_rows_outside.
    + apply Forall_forall. intros r Hr k Hk.
      exact (proj1 (Forall_forall _ _) (matrix_rows_outside M k Hk) r Hr).
Qed.

Theorem matrix_reduce_row_equivalent {m n} reduced (M : matrix Qc m n) :
  row_equivalent M (matrix_reduce reduced M).
Proof.
  unfold row_equivalent. rewrite matrix_reduce_rows. apply RationalElimination.reduce_equivalent.
Qed.

Theorem matrix_reduce_shape {m n} reduced (M : matrix Qc m n) :
  exists pivots, echelon_shape n reduced 0 (matrix_rows (matrix_reduce reduced M)) pivots.
Proof.
  rewrite matrix_reduce_rows. eexists. apply (RationalElimination.reduce_shape reduced n 0 (matrix_rows M)).
  apply Forall_forall. intros r Hr j Hj. lia.
Qed.

Theorem matrix_ref_correct {m n} (M : matrix Qc m n) :
  row_equivalent M (matrix_ref M) /\ is_ref (matrix_ref M).
Proof. split; [apply matrix_reduce_row_equivalent|apply matrix_reduce_shape]. Qed.

Theorem matrix_rref_correct {m n} (M : matrix Qc m n) :
  row_equivalent M (matrix_rref M) /\ is_rref (matrix_rref M).
Proof. split; [apply matrix_reduce_row_equivalent|apply matrix_reduce_shape]. Qed.


(** Embedding exact rational calculations into the usual real matrices. *)
From Stdlib Require Import Reals.Qreals.

Definition Qc_to_R (q : Qc) : R := Q2R (this q).
Definition matrix_Qc_to_R {m n} (M : matrix Qc m n) : matrix R m n :=
  vector_map (vector_map Qc_to_R) M.

Lemma Qc_to_R_of_Q q : Qc_to_R (Q2Qc q) = Q2R q.
Proof. unfold Qc_to_R, Q2Qc; cbn [this]. apply Qeq_eqR, Qred_correct. Qed.

Lemma Qc_to_R_zero : Qc_to_R 0%Qc = 0%R.
Proof. rewrite Qc_to_R_of_Q. unfold Q2R; simpl. ring. Qed.

Lemma Qc_to_R_one : Qc_to_R 1%Qc = 1%R.
Proof. rewrite Qc_to_R_of_Q. unfold Q2R; simpl. field. Qed.

Lemma Qc_to_R_add x y : Qc_to_R (x + y)%Qc = (Qc_to_R x + Qc_to_R y)%R.
Proof. unfold Qcplus. rewrite Qc_to_R_of_Q. apply Q2R_plus. Qed.

Lemma Qc_to_R_mul x y : Qc_to_R (x * y)%Qc = (Qc_to_R x * Qc_to_R y)%R.
Proof. unfold Qcmult. rewrite Qc_to_R_of_Q. apply Q2R_mult. Qed.

Lemma Qc_to_R_injective x y : Qc_to_R x = Qc_to_R y -> x = y.
Proof. intro Heq. apply Qc_is_canon. now apply eqR_Qeq. Qed.

Definition map_row {K L} (f : K -> L) (r : nat -> K) : nat -> L := fun j => f (r j).

Lemma row_span_map {K L} `{Zero K} `{Add K} `{Mul K}
    `{Zero L} `{Add L} `{Mul L} (f : K -> L) :
  f zero = zero ->
  (forall x y, f (add x y) = add (f x) (f y)) ->
  (forall x y, f (mul x y) = mul (f x) (f y)) ->
  forall rows r, row_span rows r -> row_span (map (map_row f) rows) (map_row f r).
Proof.
  intros Hzero Hplus Htimes rows r Hr. induction Hr; unfold map_row in *.
  - replace (fun _ : nat => f zero) with (fun _ : nat => zero).
    + apply span_zero.
    + apply functional_extensionality; intro j. symmetry. exact Hzero.
  - apply span_row. apply in_map_iff. exists r. split; [reflexivity|assumption].
  - replace (fun j => f (add (r j) (s j)))
      with (fun j => add (f (r j)) (f (s j))).
    + now apply span_add.
    + apply functional_extensionality; intro j. symmetry. apply Hplus.
  - replace (fun j => f (mul a (r j))) with (fun j => mul (f a) (f (r j))).
    + now apply span_scale.
    + apply functional_extensionality; intro j. symmetry. apply Htimes.
Qed.

Lemma rows_equivalent_map {K L} `{Zero K} `{Add K} `{Mul K}
    `{Zero L} `{Add L} `{Mul L} (f : K -> L) :
  f zero = zero ->
  (forall x y, f (add x y) = add (f x) (f y)) ->
  (forall x y, f (mul x y) = mul (f x) (f y)) ->
  forall xs ys, rows_equivalent xs ys ->
  rows_equivalent (map (map_row f) xs) (map (map_row f) ys).
Proof.
  intros Hzero Hplus Htimes xs ys [Hxy Hyx]. split; intros r Hr;
    apply in_map_iff in Hr; destruct Hr as [s [<- Hs]];
    apply row_span_map; auto.
Qed.

Lemma echelon_shape_map {K L} `{Zero K} `{One K} `{Zero L} `{One L}
    (f : K -> L) :
  f zero = zero -> f one = one ->
  (forall x y, f x = f y -> x = y) ->
  forall n reduced c rows ps, echelon_shape n reduced c rows ps ->
  echelon_shape n reduced c (map (map_row f) rows) ps.
Proof.
  intros Hzero Hone Hinj n reduced c rows ps Hshape.
  induction Hshape as [c rows Hz|c p r rows ps Hbounds Hnz Hbefore Hshape IH Hred].
  - apply shape_zero. apply Forall_forall. intros s Hs.
    apply in_map_iff in Hs. destruct Hs as [r [<- Hr]].
    intros j Hj. unfold map_row.
    rewrite (proj1 (Forall_forall _ _) Hz r Hr j Hj). exact Hzero.
  - cbn [map]. eapply shape_pivot; [exact Hbounds| | |exact IH|].
    + unfold map_row. intro Heq. apply Hnz, Hinj. now rewrite Hzero.
    + intros j Hj. unfold map_row. rewrite Hbefore by exact Hj. exact Hzero.
    + intro Heq. destruct (Hred Heq) as [Hp Hps]. split.
      * unfold map_row. now rewrite Hp.
      * eapply Forall_impl; [|exact Hps]. intros k Hk. unfold map_row. now rewrite Hk.
Qed.

Lemma nth_map_zero {K L} `{Zero K} `{Zero L} (f : K -> L) :
  f zero = zero -> forall xs j,
  List.nth j (map f xs) zero = f (List.nth j xs zero).
Proof.
  intro Hz. induction xs as [|x xs IH]; intros [|j]; simpl; auto.
Qed.

Lemma matrix_Qc_to_R_rows {m n} (M : matrix Qc m n) :
  matrix_rows (matrix_Qc_to_R M) = map (map_row Qc_to_R) (matrix_rows M).
Proof.
  destruct M as [rows Hrows].
  unfold matrix_rows, matrix_Qc_to_R, vector_map; cbn [vlist].
  rewrite !map_map. apply map_ext. intros [r Hr]. cbn [vlist].
  apply functional_extensionality. intro j.
  unfold map_row. apply nth_map_zero. exact Qc_to_R_zero.
Qed.

Theorem matrix_Qc_to_R_row_equivalent {m n} (A B : matrix Qc m n) :
  row_equivalent A B -> row_equivalent (matrix_Qc_to_R A) (matrix_Qc_to_R B).
Proof.
  unfold row_equivalent. rewrite !matrix_Qc_to_R_rows.
  apply rows_equivalent_map; [exact Qc_to_R_zero|exact Qc_to_R_add|exact Qc_to_R_mul].
Qed.

Theorem matrix_Qc_to_R_ref {m n} (M : matrix Qc m n) :
  is_ref M -> is_ref (matrix_Qc_to_R M).
Proof.
  intros [ps Hps]. exists ps. rewrite matrix_Qc_to_R_rows.
  eapply echelon_shape_map; [exact Qc_to_R_zero|exact Qc_to_R_one|exact Qc_to_R_injective|exact Hps].
Qed.

Theorem matrix_Qc_to_R_rref {m n} (M : matrix Qc m n) :
  is_rref M -> is_rref (matrix_Qc_to_R M).
Proof.
  intros [ps Hps]. exists ps. rewrite matrix_Qc_to_R_rows.
  eapply echelon_shape_map; [exact Qc_to_R_zero|exact Qc_to_R_one|exact Qc_to_R_injective|exact Hps].
Qed.

Theorem matrix_ref_real_correct {m n} (M : matrix Qc m n) :
  row_equivalent (matrix_Qc_to_R M) (matrix_Qc_to_R (matrix_ref M)) /\
  is_ref (matrix_Qc_to_R (matrix_ref M)).
Proof.
  destruct (matrix_ref_correct M) as [Heq Hshape]. split.
  - now apply matrix_Qc_to_R_row_equivalent.
  - now apply matrix_Qc_to_R_ref.
Qed.

Theorem matrix_rref_real_correct {m n} (M : matrix Qc m n) :
  row_equivalent (matrix_Qc_to_R M) (matrix_Qc_to_R (matrix_rref M)) /\
  is_rref (matrix_Qc_to_R (matrix_rref M)).
Proof.
  destruct (matrix_rref_correct M) as [Heq Hshape]. split.
  - now apply matrix_Qc_to_R_row_equivalent.
  - now apply matrix_Qc_to_R_rref.
Qed.

(** A computation-based equality solver for concrete rational matrices. The
    decision procedure compares entries, never the stored length proofs. *)
Definition vector_decidable_eq {K n} (dec : forall x y : K, {x = y} + {x <> y})
    (v w : vector K n) : {v = w} + {v <> w}.
Proof.
  destruct (list_eq_dec dec (vlist v) (vlist w)) as [Heq|Hneq].
  - left. now apply vector_eq.
  - right. intro Heq. apply Hneq. now rewrite Heq.
Defined.

Definition matrix_Qc_eq_dec {m n} (A B : matrix Qc m n) : {A = B} + {A <> B} :=
  vector_decidable_eq (vector_decidable_eq Qc_eq_dec) A B.

Definition matrix_Qc_eqb {m n} (A B : matrix Qc m n) : bool :=
  if matrix_Qc_eq_dec A B then true else false.

Lemma matrix_Qc_eqb_eq {m n} (A B : matrix Qc m n) :
  matrix_Qc_eqb A B = true <-> A = B.
Proof.
  unfold matrix_Qc_eqb. destruct (matrix_Qc_eq_dec A B); split; congruence.
Qed.

Ltac qc_mat_compute :=
  solve [apply (proj1 (matrix_Qc_eqb_eq _ _)); vm_compute; reflexivity].

(** A display view without vector-length or rational-normalization proofs. *)
Definition matrix_Qc_entries {m n} (M : matrix Qc m n) : list (list Q) :=
  map (fun r => map this (vlist r)) (vlist M).

Lemma row_equivalent_refl {K m n} `{Zero K} `{Add K} `{Mul K} (M : matrix K m n) :
  row_equivalent M M.
Proof. apply rows_equivalent_refl. Qed.

Lemma row_equivalent_sym {K m n} `{Zero K} `{Add K} `{Mul K} (A B : matrix K m n) :
  row_equivalent A B -> row_equivalent B A.
Proof. apply rows_equivalent_sym. Qed.

Lemma row_equivalent_trans {K m n} `{Zero K} `{Add K} `{Mul K} (A B C : matrix K m n) :
  row_equivalent A B -> row_equivalent B C -> row_equivalent A C.
Proof. apply rows_equivalent_trans. Qed.

Lemma row_equivalent_same_span {K m n} `{Zero K} `{Add K} `{Mul K} (A B : matrix K m n) :
  row_equivalent A B <->
  forall r, row_span (matrix_rows A) r <-> row_span (matrix_rows B) r.
Proof.
  split.
  - intros [HAB HBA] r. split; apply row_span_substitute; assumption.
  - intro Hspan. split; intros r Hr; apply Hspan; now apply span_row.
Qed.

Lemma echelon_shape_forget_reduced {K} `{Zero K} `{One K} n c rows ps :
  echelon_shape n true c rows ps -> echelon_shape n false c rows ps.
Proof.
  intro Hshape. induction Hshape.
  - now apply shape_zero.
  - eapply shape_pivot; eauto.
Qed.

Theorem is_rref_is_ref {K m n} `{Zero K} `{One K} (M : matrix K m n) :
  is_rref M -> is_ref M.
Proof. intros [ps Hps]. exists ps. now apply echelon_shape_forget_reduced. Qed.

Theorem matrix_ref_pivots {m n} (M : matrix Qc m n) :
  echelon_shape n false 0 (matrix_rows (matrix_ref M)) (matrix_pivots M).
Proof.
  unfold matrix_ref, matrix_pivots. rewrite matrix_reduce_rows.
  rewrite RationalElimination.reduce_cached_eq.
  2: { apply Forall_forall. intros r Hr j Hj.
       exact (proj1 (Forall_forall _ _) (matrix_rows_outside M j Hj) r Hr). }
  apply (RationalElimination.reduce_shape false n 0 (matrix_rows M)).
  apply Forall_forall. intros r Hr j Hj. lia.
Qed.

Theorem matrix_pivots_bounds {m n} (M : matrix Qc m n) :
  Forall (fun p => (p < n)%nat) (matrix_pivots M).
Proof.
  pose proof (echelon_shape_pivots _ _ _ _ _ (matrix_ref_pivots M)) as Hp.
  eapply Forall_impl; [|exact Hp]. intros p Hbound. cbn in Hbound. lia.
Qed.
