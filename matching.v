Require Import Coq.Strings.Ascii.
Require Import Coq.Strings.String.
Require Import Coq.NArith.BinNat.
From stdpp Require Import fin_sets gmap option.
From mininix Require Import expr maptools.

Open Scope string_scope.
Open Scope N_scope.
Open Scope Z_scope.
Open Scope nat_scope.

Reserved Notation "bs '~' m '~>' brs" (at level 55).

Inductive matches_r : gmap string expr → matcher → gmap string b_rhs -> Prop :=
  | E_MatchEmpty strict : ∅ ~ M_Matcher ∅ strict ~> ∅
  | E_MatchAny bs : bs ~ M_Matcher ∅ false ~> ∅
  | E_MatchMandatory bs x e m bs' strict :
      bs !! x = None →
      m !! x = None →
      delete x bs ~ M_Matcher m strict ~> bs' →
      <[x := e]>bs ~ M_Matcher (<[x := M_Mandatory]>m) strict
        ~> <[x := B_Nonrec e]>bs'
  | E_MatchOptAvail bs x d e m bs' strict :
      bs !! x = None →
      m !! x = None →
      delete x bs ~ M_Matcher m strict ~> bs' →
      <[x := d]>bs ~ M_Matcher (<[x := M_Optional e]>m) strict
        ~> <[x := B_Nonrec d]>bs'
  | E_MatchOptDefault bs x e m bs' strict :
      bs !! x = None →
      m !! x = None →
      bs ~ M_Matcher m strict ~> bs' →
      bs ~ M_Matcher (<[x := M_Optional e]>m) strict ~> <[x := B_Rec e]>bs'
where "bs ~ m ~> brs" := (matches_r bs m brs).

Definition map_foldM `{Countable K} `{FinMap K M} `{MBind F} `{MRet F} {A B}
  (f : K → A → B → F B) (init : B) (m : M A) : F B :=
    map_fold (λ i x acc, acc ≫= f i x) (mret init) m.

Definition matches_aux_f (x : string) (rhs : m_rhs)
  (acc : option (gmap string expr * gmap string b_rhs)) :=
    acc ← acc;
    let (bs, brs) := (acc : gmap string expr * gmap string b_rhs) in
    match rhs with
    | M_Mandatory  =>
        e ← bs !! x;
        Some (bs, <[x := B_Nonrec e]>brs)
    | M_Optional e =>
        match bs !! x with
        | Some e' => Some (bs, <[x := B_Nonrec e']>brs)
        | None => Some (bs, <[x := B_Rec e]>brs)
        end
    end.

Definition matches_aux (ms : gmap string m_rhs) (bs : gmap string expr) :
  option (gmap string expr * gmap string b_rhs) :=
    map_fold matches_aux_f (Some (bs, ∅)) ms.

Definition matches (m : matcher) (bs : gmap string expr) :
  option (gmap string b_rhs) :=
    match m with
    | M_Matcher ms strict =>
        guard (strict → dom bs ⊆ matcher_keys m);;
        snd <$> matches_aux ms bs
    end.

Lemma matches_aux_empty bs : matches_aux ∅ bs = Some (bs, ∅).
Proof. done. Qed.

Lemma matches_aux_f_comm (x : string) (rhs : m_rhs) (m : gmap string m_rhs)
  (y z : string) (rhs1 rhs2 : m_rhs)
  (acc : option (gmap string expr * gmap string b_rhs)) :
    m !! x = None → y ≠ z →
    <[x:=rhs]> m !! y = Some rhs1 →
    <[x:=rhs]> m !! z = Some rhs2 →
    matches_aux_f y rhs1 (matches_aux_f z rhs2 acc) =
    matches_aux_f z rhs2 (matches_aux_f y rhs1 acc).
Proof.
  intros Hxm Hyz Hym Hzm.
  unfold matches_aux_f.
  destruct acc.
  repeat (simplify_option_eq || done ||
          destruct (g !! y) eqn:Egy || destruct (g !! z) eqn:Egz ||
          case_match || rewrite insert_commute). done.
Qed.

Lemma matches_aux_insert m bs x rhs :
  m !! x = None →
  matches_aux (<[x := rhs]>m) bs = matches_aux_f x rhs (matches_aux m bs).
Proof.
  intros Hnotin. unfold matches_aux.
  rewrite map_fold_insert_L; try done.
  clear bs.
  intros y z rhs1 rhs2 acc Hyz Hym Hzm.
  by eapply matches_aux_f_comm.
Qed.

Lemma matches_aux_bs m bs bs' brs :
  matches_aux m bs = Some (bs', brs) → bs = bs'.
Proof.
  revert bs bs' brs.
  induction m using map_ind; intros bs bs' brs Hmatches.
  - rewrite matches_aux_empty in Hmatches. congruence.
  - rewrite matches_aux_insert in Hmatches; try done.
    unfold matches_aux_f in Hmatches.
    simplify_option_eq.
    destruct H0.
    case_match; try case_match;
      simplify_option_eq; by apply IHm with (brs := g0).
Qed.

Lemma matches_aux_impl m bs brs x e :
  m !! x = None →
  bs !! x = None →
  matches_aux m (<[x := e]>bs) = Some (<[x := e]>bs, brs) →
  matches_aux m bs = Some (bs, brs).
Proof.
  intros Hxm Hxbs Hmatches.
  revert bs brs Hxm Hxbs Hmatches.
  induction m using map_ind; intros bs brs Hxm Hxbs Hmatches.
  - rewrite matches_aux_empty.
    rewrite matches_aux_empty in Hmatches.
    by simplify_option_eq.
  - rewrite matches_aux_insert in Hmatches by done.
    rewrite matches_aux_insert by done.
    apply lookup_insert_None in Hxm as [Hxm1 Hxm2].
    unfold matches_aux_f in Hmatches. simplify_option_eq.
    destruct H0. case_match.
    + simplify_option_eq.
      rewrite lookup_insert_ne in Heqo0 by done.
      pose proof (IHm bs g0 Hxm1 Hxbs Heqo).
      rewrite H1. by simplify_option_eq.
    + case_match; simplify_option_eq;
        rewrite lookup_insert_ne in H1 by done;
        pose proof (IHm bs g0 Hxm1 Hxbs Heqo);
        rewrite H0; by simplify_option_eq.
Qed.

Lemma matches_aux_impl_2 m bs brs x e :
  m !! x = None →
  bs !! x = None →
  matches_aux m bs = Some (bs, brs) →
  matches_aux m (<[x := e]>bs) = Some (<[x := e]>bs, brs).
Proof.
  intros Hxm Hxbs Hmatches.
  revert bs brs Hxm Hxbs Hmatches.
  induction m using map_ind; intros bs brs Hxm Hxbs Hmatches.
  - rewrite matches_aux_empty.
    rewrite matches_aux_empty in Hmatches.
    by simplify_option_eq.
  - rewrite matches_aux_insert in Hmatches by done.
    rewrite matches_aux_insert by done.
    apply lookup_insert_None in Hxm as [Hxm1 Hxm2].
    unfold matches_aux_f in Hmatches. simplify_option_eq.
    destruct H0. case_match.
    + simplify_option_eq.
      rewrite <-lookup_insert_ne with (i := x) (x := e) in Heqo0 by done.
      pose proof (IHm bs g0 Hxm1 Hxbs Heqo).
      rewrite H1. by simplify_option_eq.
    + case_match; simplify_option_eq;
        rewrite <-lookup_insert_ne with (i := x) (x := e) in H1 by done;
        pose proof (IHm bs g0 Hxm1 Hxbs Heqo);
        rewrite H0; by simplify_option_eq.
Qed.

Lemma matches_aux_dom m bs brs :
  matches_aux m bs = Some (bs, brs) → dom m = dom brs.
Proof.
  revert bs brs.
  induction m using map_ind; intros bs brs Hmatches.
  - rewrite matches_aux_empty in Hmatches. by simplify_eq.
  - rewrite matches_aux_insert in Hmatches by done.
    unfold matches_aux_f in Hmatches. simplify_option_eq. destruct H0.
    case_match; try case_match;
      simplify_option_eq; apply IHm in Heqo; set_solver.
Qed.

Lemma matches_aux_inv m bs brs x e :
  m !! x = None → bs !! x = None → brs !! x = None →
  matches_aux (<[x := M_Mandatory]>m) (<[x := e]>bs) =
    Some (<[x := e]>bs, <[x := B_Nonrec e]>brs) →
  matches_aux m bs = Some (bs, brs).
Proof.
  intros Hxm Hxbs Hxbrs Hmatches.
  rewrite matches_aux_insert in Hmatches by done.
  unfold matches_aux_f in Hmatches. simplify_option_eq.
  destruct H. simplify_option_eq.
  rewrite lookup_insert in Heqo0. simplify_option_eq.
  apply matches_aux_impl in Heqo; try done.
  simplify_option_eq.
  apply matches_aux_dom in Heqo as Hdom.
  rewrite Heqo. do 2 f_equal.
  assert (g0 !! x = None).
    { apply not_elem_of_dom in Hxm.
      rewrite Hdom in Hxm.
      by apply not_elem_of_dom. }
  replace g0 with (delete x (<[x:=B_Nonrec H]> g0));
    try by rewrite delete_insert.
  replace brs with (delete x (<[x:=B_Nonrec H]> brs));
    try by rewrite delete_insert.
  by rewrite H1.
Qed.

Lemma disjoint_union_subseteq_l `{FinSet A C} `{!LeibnizEquiv C} (X Y Z : C) :
  X ## Y → X ## Z → X ∪ Y ⊆ X ∪ Z → Y ⊆ Z.
Proof.
  revert Y Z.
  induction X using set_ind_L; intros Y Z Hdisj1 Hdisj2 Hsubs.
  - by do 2 rewrite union_empty_l_L in Hsubs.
  - do 2 rewrite <-union_assoc_L in Hsubs.
    apply IHX; set_solver.
Qed.

Lemma singleton_notin_union_disjoint `{FinMapDom K M D} {A} (m : M A) (i : K) :
  m !! i = None →
  {[i]} ## dom m.
Proof.
  intros Hlookup. apply disjoint_singleton_l.
  by apply not_elem_of_dom in Hlookup.
Qed.

Lemma matches_step bs brs m strict x :
  matches (M_Matcher (<[x := M_Mandatory]>m) strict) bs = Some brs →
  ∃ e, bs !! x = Some e ∧ brs !! x = Some (B_Nonrec e).
Proof.
  intros Hmatches.
  destruct (decide (is_Some (bs !! x))).
  - destruct i. exists x0. split; [done|].
    unfold matches in Hmatches.
    destruct strict; simplify_option_eq.
    + replace (<[x := M_Mandatory]>m) with (<[x := M_Mandatory]>(delete x m))
      in Heqo0; try by rewrite insert_delete_insert.
      rewrite matches_aux_insert in Heqo0 by apply lookup_delete.
      unfold matches_aux_f in Heqo0. simplify_option_eq.
      destruct H3. simplify_option_eq.
      apply matches_aux_bs in Heqo as Hdom. simplify_option_eq.
      apply lookup_insert.
    + replace (<[x := M_Mandatory]>m) with (<[x := M_Mandatory]>(delete x m))
      in Heqo; try by rewrite insert_delete_insert.
      rewrite matches_aux_insert in Heqo by apply lookup_delete.
      unfold matches_aux_f in Heqo. simplify_option_eq.
      destruct H1. simplify_option_eq.
      apply matches_aux_bs in Heqo0 as Hdom. simplify_option_eq.
      apply lookup_insert.
  - unfold matches in Hmatches.
    destruct strict; simplify_option_eq.
    + replace (<[x := M_Mandatory]>m) with (<[x := M_Mandatory]>(delete x m))
      in Heqo0; try by rewrite insert_delete_insert.
      rewrite matches_aux_insert in Heqo0 by apply lookup_delete.
      unfold matches_aux_f in Heqo0. simplify_option_eq.
      destruct H2. simplify_option_eq.
      apply matches_aux_bs in Heqo as Hdom. simplify_option_eq.
      rewrite Heqo1 in n.
      exfalso. by apply n.
    + replace (<[x := M_Mandatory]>m) with (<[x := M_Mandatory]>(delete x m))
      in Heqo; try by rewrite insert_delete_insert.
      rewrite matches_aux_insert in Heqo by apply lookup_delete.
      unfold matches_aux_f in Heqo. simplify_option_eq.
      destruct H0. simplify_option_eq.
      apply matches_aux_bs in Heqo0 as Hdom. simplify_option_eq.
      rewrite Heqo1 in n.
      exfalso. by apply n.
Qed.

Lemma matches_step' bs brs m strict x :
  matches (M_Matcher (<[x := M_Mandatory]>m) strict) bs = Some brs →
  ∃ e bs' brs',
    bs' !! x = None ∧ bs = <[x := e]>bs' ∧
    brs' !! x = None ∧ brs = <[x := B_Nonrec e]>brs'.
Proof.
  intros Hmatches.
  apply matches_step in Hmatches as He.
  destruct He as [e [He1 He2]].
  exists e, (delete x bs), (delete x brs).
  split_and!; by apply lookup_delete || rewrite insert_delete.
Qed.

Lemma matches_opt_step bs brs m strict x d :
  matches (M_Matcher (<[x := M_Optional d]>m) strict) bs = Some brs →
  (∃ e, bs !! x = Some e ∧ brs !! x = Some (B_Nonrec e)) ∨
  bs !! x = None ∧ brs !! x = Some (B_Rec d).
Proof.
  intros Hmatches.
  destruct (decide (is_Some (bs !! x))).
  - destruct i. left. exists x0. split; [done|].
    unfold matches in Hmatches.
    destruct strict; simplify_option_eq.
    + replace (<[x := M_Optional d]>m) with (<[x := M_Optional d]>(delete x m))
      in Heqo0; try by rewrite insert_delete_insert.
      rewrite matches_aux_insert in Heqo0 by apply lookup_delete.
      unfold matches_aux_f in Heqo0. simplify_option_eq.
      destruct H3. simplify_option_eq.
      apply matches_aux_bs in Heqo as Hdom. simplify_option_eq.
      apply lookup_insert.
    + replace (<[x := M_Optional d]>m) with (<[x := M_Optional d]>(delete x m))
      in Heqo; try by rewrite insert_delete_insert.
      rewrite matches_aux_insert in Heqo by apply lookup_delete.
      unfold matches_aux_f in Heqo. simplify_option_eq.
      destruct H1. simplify_option_eq.
      apply matches_aux_bs in Heqo0 as Hdom. simplify_option_eq.
      apply lookup_insert.
  - unfold matches in Hmatches.
    destruct strict; simplify_option_eq.
    + right. apply eq_None_not_Some in n. split; [done|].
      destruct H0. simplify_option_eq.
      apply matches_aux_bs in Heqo0 as Hbs. subst.
      replace (<[x := M_Optional d]>m) with (<[x := M_Optional d]>(delete x m))
      in Heqo0; try by rewrite insert_delete_insert.
      rewrite matches_aux_insert in Heqo0 by apply lookup_delete.
      unfold matches_aux_f in Heqo0. simplify_option_eq.
      destruct H0. simplify_option_eq.
      apply matches_aux_bs in Heqo as Hdom. simplify_option_eq.
      apply lookup_insert.
    + right. apply eq_None_not_Some in n. split; [done|].
      destruct H. simplify_option_eq.
      apply matches_aux_bs in Heqo as Hbs. subst.
      replace (<[x := M_Optional d]>m) with (<[x := M_Optional d]>(delete x m))
      in Heqo; try by rewrite insert_delete_insert.
      rewrite matches_aux_insert in Heqo by apply lookup_delete.
      unfold matches_aux_f in Heqo. simplify_option_eq.
      destruct H. simplify_option_eq.
      apply matches_aux_bs in Heqo0 as Hdom. simplify_option_eq.
      apply lookup_insert.
Qed.

Lemma matches_opt_step' bs brs m strict x d :
  matches (M_Matcher (<[x := M_Optional d]>m) strict) bs = Some brs →
  (∃ e bs' brs',
     bs' !! x = None ∧ bs = <[x := e]>bs' ∧
     brs' !! x = None ∧ brs = <[x := B_Nonrec e]>brs') ∨
  (∃ brs',
     bs !! x = None ∧ brs' !! x = None ∧
     brs = <[x := B_Rec d]>brs').
Proof.
  intros Hmatches.
  apply matches_opt_step in Hmatches as He.
  destruct He as [He|He].
  - destruct He as [e [He1 He2]]. left.
    exists e, (delete x bs), (delete x brs).
    split; try split; try split.
    + apply lookup_delete.
    + by rewrite insert_delete.
    + apply lookup_delete.
    + by rewrite insert_delete.
  - destruct He as [He1 He2]. right.
    exists (delete x brs). split; try split; try done.
    + apply lookup_delete.
    + by rewrite insert_delete.
Qed.

Lemma matches_inv m bs brs strict x e :
  m !! x = None → bs !! x = None → brs !! x = None →
  matches (M_Matcher (<[x := M_Mandatory]>m) strict) (<[x := e]>bs) =
    Some (<[x := B_Nonrec e]>brs) →
  matches (M_Matcher m strict) bs = Some brs.
Proof.
  intros Hxm Hxbs Hxbrs Hmatch.
  destruct strict.
  - simplify_option_eq.
    + destruct H0. apply matches_aux_bs in Heqo0 as Hbs.
      simplify_option_eq. by erewrite matches_aux_inv.
    + exfalso. apply H2.
      repeat rewrite dom_insert in H1.
      assert ({[x]} ## dom bs). { by apply singleton_notin_union_disjoint. }
      assert ({[x]} ## dom m). { by apply singleton_notin_union_disjoint. }
      by apply disjoint_union_subseteq_l with (X := {[x]}).
  - simplify_option_eq.
    destruct H. apply matches_aux_bs in Heqo as Hbs.
    simplify_option_eq. by erewrite matches_aux_inv.
Qed.

Lemma matches_aux_avail_inv m bs brs x d e :
  m !! x = None → bs !! x = None → brs !! x = None →
  matches_aux (<[x := M_Optional d]>m) (<[x := e]>bs) =
    Some (<[x := e]>bs, <[x := B_Nonrec e]>brs) →
  matches_aux m bs = Some (bs, brs).
Proof.
  intros Hxm Hxbs Hxbrs Hmatches.
  rewrite matches_aux_insert in Hmatches by done.
  unfold matches_aux_f in Hmatches. simplify_option_eq.
  destruct H. simplify_option_eq.
  apply matches_aux_bs in Heqo as Hbs. subst.
  rewrite lookup_insert in Hmatches. simplify_option_eq.
  apply matches_aux_impl in Heqo; try done.
  simplify_option_eq.
  apply matches_aux_dom in Heqo as Hdom.
  rewrite Heqo. do 2 f_equal.
  assert (g0 !! x = None).
    { apply not_elem_of_dom in Hxm.
      rewrite Hdom in Hxm.
      by apply not_elem_of_dom. }
  replace g0 with (delete x (<[x:=B_Nonrec e]> g0));
    try by rewrite delete_insert.
  replace brs with (delete x (<[x:=B_Nonrec e]> brs));
    try by rewrite delete_insert.
  by rewrite Hmatches.
Qed.

Lemma matches_avail_inv m bs brs strict x d e :
  m !! x = None → bs !! x = None → brs !! x = None →
  matches (M_Matcher (<[x := M_Optional d]>m) strict) (<[x := e]>bs) =
    Some (<[x := B_Nonrec e]>brs) →
  matches (M_Matcher m strict) bs = Some brs.
Proof.
  intros Hxm Hxbs Hxbrs Hmatch.
  destruct strict.
  - simplify_option_eq.
    + destruct H0. apply matches_aux_bs in Heqo0 as Hbs.
      simplify_option_eq. by erewrite matches_aux_avail_inv.
    + exfalso. apply H2.
      repeat rewrite dom_insert in H1.
      assert ({[x]} ## dom bs). { by apply singleton_notin_union_disjoint. }
      assert ({[x]} ## dom m). { by apply singleton_notin_union_disjoint. }
      by apply disjoint_union_subseteq_l with (X := {[x]}).
  - simplify_option_eq.
    destruct H. apply matches_aux_bs in Heqo as Hbs.
    simplify_option_eq. by erewrite matches_aux_avail_inv.
Qed.

Lemma matches_aux_default_inv m bs brs x e :
  m !! x = None → bs !! x = None → brs !! x = None →
  matches_aux (<[x := M_Optional e]>m) bs =
    Some (bs, <[x := B_Rec e]>brs) →
  matches_aux m bs = Some (bs, brs).
Proof.
  intros Hxm Hxbs Hxbrs Hmatches.
  rewrite matches_aux_insert in Hmatches by done.
  unfold matches_aux_f in Hmatches. simplify_option_eq.
  destruct H. simplify_option_eq.
  apply matches_aux_bs in Heqo as Hbs. subst.
  rewrite Hxbs in Hmatches. simplify_option_eq.
  apply matches_aux_dom in Heqo as Hdom.
  do 2 f_equal.
  assert (g0 !! x = None).
    { apply not_elem_of_dom in Hxm.
      rewrite Hdom in Hxm.
      by apply not_elem_of_dom. }
  replace g0 with (delete x (<[x:=B_Rec e]> g0));
    try by rewrite delete_insert.
  replace brs with (delete x (<[x:=B_Rec e]> brs));
    try by rewrite delete_insert.
  by rewrite Hmatches.
Qed.

Lemma matches_default_inv m bs brs strict x e :
  m !! x = None → bs !! x = None → brs !! x = None →
  matches (M_Matcher (<[x := M_Optional e]>m) strict) bs =
    Some (<[x := B_Rec e]>brs) →
  matches (M_Matcher m strict) bs = Some brs.
Proof.
  intros Hxm Hxbs Hxbrs Hmatch.
  destruct strict.
  - simplify_option_eq.
    + destruct H0. apply matches_aux_bs in Heqo0 as Hbs.
      simplify_option_eq. by erewrite matches_aux_default_inv.
    + exfalso. apply H2.
      rewrite dom_insert in H1.
      assert ({[x]} ## dom bs). { by apply singleton_notin_union_disjoint. }
      assert ({[x]} ## dom m). { by apply singleton_notin_union_disjoint. }
      apply disjoint_union_subseteq_l with (X := {[x]}); set_solver.
  - simplify_option_eq.
    destruct H. apply matches_aux_bs in Heqo as Hbs.
    simplify_option_eq. by erewrite matches_aux_default_inv.
Qed.

Theorem matches_sound m bs brs : matches m bs = Some brs → bs ~ m ~> brs.
Proof.
  intros Hmatches.
  destruct m.
  revert strict bs brs Hmatches.
  induction ms using map_ind; intros strict bs brs Hmatches.
  - destruct strict; simplify_option_eq.
    + apply map_dom_empty_subset in H0. simplify_eq. constructor.
    + constructor.
  - destruct x.
    + apply matches_step' in Hmatches as He.
      destruct He as [e [bs' [brs' [Hbs'1 [Hbs'2 [Hbrs'1 Hbrs'2]]]]]].
      subst. constructor; try done.
      rewrite delete_notin by done.
      apply IHms.
      by apply matches_inv in Hmatches.
    + apply matches_opt_step' in Hmatches as He. destruct He as [He|He].
      * destruct He as [d [bs' [brs' [Hibs' [Hbs' [Hibrs' Hbrs']]]]]].
        subst. constructor; try done.
        rewrite delete_notin by done.
        apply IHms.
        by apply matches_avail_inv in Hmatches.
      * destruct He as [brs' [Hibs [Hibrs' Hbrs']]].
        subst. constructor; try done.
        apply IHms.
        by apply matches_default_inv in Hmatches.
Qed.

Theorem matches_complete m bs brs : bs ~ m ~> brs → matches m bs = Some brs.
Proof.
  intros Hbs.
  induction Hbs.
  - unfold matches. by simplify_option_eq.
  - unfold matches. by simplify_option_eq.
  - unfold matches in *. destruct strict.
    + simplify_option_eq.
      * simplify_option_eq. destruct H2. simplify_option_eq.
        apply fmap_Some. exists (<[x := e]>bs, <[x := B_Nonrec e]>g0).
        split; [|done].
        rewrite matches_aux_insert by done.
        apply matches_aux_bs in Heqo0 as Hbs'. simplify_option_eq.
        apply matches_aux_impl_2 with (x := x) (e := e) in Heqo0;
          [| done | apply lookup_delete].
        replace bs with (delete x bs); try by apply delete_notin.
        unfold matches_aux_f.
        simplify_option_eq. apply bind_Some. exists e.
        split; [apply lookup_insert | done].
      * exfalso. apply H4.
        replace bs with (delete x bs); try by apply delete_notin.
        apply map_dom_delete_insert_subseteq_L.
        set_solver.
    + simplify_option_eq. destruct H1. simplify_option_eq.
      apply fmap_Some. exists (<[x := e]>bs, <[x := B_Nonrec e]>g0).
      split; [|done].
      rewrite matches_aux_insert by done.
      apply matches_aux_bs in Heqo as Hbs'. simplify_option_eq.
      apply matches_aux_impl_2 with (x := x) (e := e) in Heqo;
        [| done | apply lookup_delete].
      replace bs with (delete x bs); try by apply delete_notin.
      unfold matches_aux_f.
      simplify_option_eq. apply bind_Some. exists e.
      split; [apply lookup_insert | done].
  - unfold matches in *. destruct strict.
    + simplify_option_eq.
      * simplify_option_eq. destruct H2. simplify_option_eq.
        apply fmap_Some. exists (<[x := d]>bs, <[x := B_Nonrec d]>g0).
        split; [|done].
        rewrite matches_aux_insert by done.
        apply matches_aux_bs in Heqo0 as Hbs'. simplify_option_eq.
        apply matches_aux_impl_2 with (x := x) (e := d) in Heqo0;
          [| done | apply lookup_delete].
        replace bs with (delete x bs); try by apply delete_notin.
        unfold matches_aux_f.
        simplify_option_eq. case_match.
        -- rewrite lookup_insert in H2. congruence.
        -- by rewrite lookup_insert in H2.
      * exfalso. apply H4.
        replace bs with (delete x bs); try by apply delete_notin.
        apply map_dom_delete_insert_subseteq_L.
        set_solver.
    + simplify_option_eq. destruct H1. simplify_option_eq.
      apply fmap_Some. exists (<[x := d]>bs, <[x := B_Nonrec d]>g0).
      split; [|done].
      rewrite matches_aux_insert by done.
      apply matches_aux_bs in Heqo as Hbs'. simplify_option_eq.
      apply matches_aux_impl_2 with (x := x) (e := d) in Heqo;
        [| done | apply lookup_delete].
      replace bs with (delete x bs); try by apply delete_notin.
      unfold matches_aux_f.
      simplify_option_eq. case_match.
      * rewrite lookup_insert in H1. congruence.
      * by rewrite lookup_insert in H1.
  - unfold matches in *. destruct strict.
    + simplify_option_eq.
      * simplify_option_eq. destruct H2. simplify_option_eq.
        apply fmap_Some. exists (bs, <[x := B_Rec e]>g0).
        split; [|done].
        rewrite matches_aux_insert by done.
        apply matches_aux_bs in Heqo0 as Hbs'. simplify_option_eq.
        unfold matches_aux_f.
        by simplify_option_eq.
      * exfalso. apply H4. set_solver.
    + simplify_option_eq. destruct H1. simplify_option_eq.
      apply fmap_Some. exists (bs, <[x := B_Rec e]>g0).
      split; [|done].
      rewrite matches_aux_insert by done.
      apply matches_aux_bs in Heqo as Hbs'. simplify_option_eq.
      unfold matches_aux_f.
      by simplify_option_eq.
Qed.

Theorem matches_correct m bs brs : matches m bs = Some brs ↔ bs ~ m ~> brs.
Proof. split; [apply matches_sound | apply matches_complete]. Qed.

Theorem matches_deterministic m bs brs1 brs2 :
  bs ~ m ~> brs1 → bs ~ m ~> brs2 → brs1 = brs2.
Proof. intros H1 H2. apply matches_correct in H1, H2. congruence. Qed.
