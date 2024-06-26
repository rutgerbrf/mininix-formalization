Require Import Coq.Strings.String.
From stdpp Require Import countable fin_maps fin_map_dom.

(** Generic lemmas for finite maps and their domains *)

Lemma map_insert_empty_lookup {A} `{FinMap K M}
  (i j : K) (u v : A) :
    <[i := u]> (∅ : M A) !! j = Some v → i = j ∧ v = u.
Proof.
  intros Hiel.
  destruct (decide (i = j)).
  - split; try done. simplify_eq /=.
    rewrite lookup_insert in Hiel. congruence.
  - rewrite lookup_insert_ne in Hiel; try done.
    exfalso. eapply lookup_empty_Some, Hiel.
Qed.

Lemma map_insert_ne_inv `{FinMap K M} {A}
  (m1 m2 : M A) i j x y :
    i ≠ j →
    <[i := x]>m1 = <[j := y]>m2 →
    m2 !! i = Some x ∧ m1 !! j = Some y ∧
    delete i (delete j m1) = delete i (delete j m2).
Proof.
  intros Hneq Heq.
  split; try split.
  - rewrite <-lookup_delete_ne with (i := j) by congruence.
    rewrite <-delete_insert_delete with (x := y).
    rewrite <-Heq.
    rewrite lookup_delete_ne by congruence.
    by rewrite lookup_insert.
  - rewrite <-lookup_delete_ne with (i := i) by congruence.
    rewrite <-delete_insert_delete with (x := x).
    rewrite Heq.
    rewrite lookup_delete_ne by congruence.
    by rewrite lookup_insert.
  - setoid_rewrite <-delete_insert_delete with (x := x) at 1.
    setoid_rewrite <-delete_insert_delete with (x := y) at 4.
    rewrite <-delete_insert_ne by congruence.
    by do 2 f_equal.
Qed.

Lemma map_insert_inv `{FinMap K M} {A}
  (m1 m2 : M A) i x y :
    <[i := x]>m1 = <[i := y]>m2 →
    x = y ∧ delete i m1 = delete i m2.
Proof.
  intros Heq.
  split; try split.
  - apply Some_inj.
    replace (Some x) with (<[i := x]>m1 !! i) by apply lookup_insert.
    replace (Some y) with (<[i := y]>m2 !! i) by apply lookup_insert.
    by rewrite Heq.
  - replace (delete i m1) with (delete i (<[i := x]>m1))
    by apply delete_insert_delete.
    replace (delete i m2) with (delete i (<[i := y]>m2))
    by apply delete_insert_delete.
    by rewrite Heq.
Qed.

Lemma fmap_insert_lookup `{FinMap K M} {A B}
  (f : A → B) (m1 : M A) (m2 : M B) i x :
    f <$> m1 = <[i := x]>m2 →
    f <$> m1 !! i = Some x.
Proof.
  intros Hmap.
  rewrite <-lookup_fmap.
  rewrite Hmap.
  apply lookup_insert.
Qed.

Lemma map_dom_delete_insert_L `{FinMapDom K M D} `{!LeibnizEquiv D} {A B}
  (m1 : M A) (m2 : M B) i x y :
    dom (delete i m1) = dom (delete i m2) →
    dom (<[i := x]>m1) = dom (<[i := y]> m2).
Proof.
  intros Hdel.
  setoid_rewrite <-insert_delete_insert at 1 2.
  rewrite 2 dom_insert_L.
  set_solver.
Qed.

Lemma map_dom_delete_insert_subseteq_L `{FinMapDom K M D} `{!LeibnizEquiv D}
  {A B} (m1 : M A) (m2 : M B) i x y :
    dom (delete i m1) ⊆ dom (delete i m2) →
    dom (<[i := x]>m1) ⊆ dom (<[i := y]> m2).
Proof.
  intros Hdel.
  setoid_rewrite <-insert_delete_insert at 1 2.
  rewrite 2 dom_insert_L.
  set_solver.
Qed.

Lemma map_dom_empty_eq_L `{FinMapDom K M D} `{!LeibnizEquiv D} {A}
  (m : M A) : dom (∅ : M A) = dom m → m = ∅.
Proof.
  intros Hdom.
  rewrite dom_empty_L in Hdom.
  symmetry in Hdom.
  by apply dom_empty_inv_L.
Qed.

Lemma map_dom_insert_eq_L `{FinMapDom K M D} `{!LeibnizEquiv D} {A}
  (i : K) (x : A) (m1 m2 : M A) :
    dom (<[i := x]>m1) = dom m2 →
    dom (delete i m1) = dom (delete i m2) ∧ i ∈ dom m2.
Proof. set_solver. Qed.

(** map_mapM *)

Definition map_mapM {M : Type → Type} `{MBind F} `{MRet F} `{FinMap K M} {A B}
  (f : A → F B) (m : M A) : F (M B) :=
    map_fold (λ i x om', m' ← om'; x' ← f x; mret $ <[i := x']>m') (mret ∅) m.

Lemma map_mapM_dom_L `{FinMapDom K M D} `{!LeibnizEquiv D} {A B}
  (f : A → option B) (m1 : M A) (m2 : M B) :
    map_mapM f m1 = Some m2 → dom m1 = dom m2.
Proof.
  revert m2.
  induction m1 using map_ind; intros m2 HmapM.
  - unfold map_mapM in HmapM. rewrite map_fold_empty in HmapM.
    simplify_option_eq.
    by rewrite 2 dom_empty_L.
  - unfold map_mapM in HmapM.
    rewrite map_fold_insert_L in HmapM.
    + simplify_option_eq.
      apply IHm1 in Heqo.
      rewrite 2 dom_insert_L.
      by f_equal.
    + intros.
      destruct y; simplify_option_eq; try done.
      destruct (f z2); simplify_option_eq.
      * destruct (f z1); simplify_option_eq; try done.
        f_equal. by apply insert_commute.
      * destruct (f z1); by simplify_option_eq.
    + done.
Qed.

Lemma map_mapM_option_insert_L `{FinMapDom K M D} `{!LeibnizEquiv D} {A B}
  (f : A → option B) (m1 : M A) (m2 m2' : M B)
  (i : K) (x : A) (x' : B) :
  m1 !! i = None →
  map_mapM f (<[i := x]>m1) = Some m2 →
  ∃ x', f x = Some x' ∧ map_mapM f m1 = Some (delete i m2).
Proof.
  intros Helem HmapM.
  unfold map_mapM in HmapM.
  rewrite map_fold_insert_L in HmapM.
  - simplify_option_eq.
    exists H15.
    split; try done.
    rewrite delete_insert.
    apply Heqo.
    apply map_mapM_dom_L in Heqo.
    apply not_elem_of_dom in Helem.
    apply not_elem_of_dom.
    set_solver.
  - intros.
    destruct y; simplify_option_eq; try done.
    destruct (f z2); simplify_option_eq.
    + destruct (f z1); simplify_option_eq; try done.
      f_equal. by apply insert_commute.
    + destruct (f z1); by simplify_option_eq.
  - done.
Qed.

(** map_Forall2 *)

Definition map_Forall2 `{∀ A, Lookup K A (M A)} {A B}
  (R : A → B → Prop) :=
    map_relation (M := M) R (λ _, False) (λ _, False).

Global Instance map_Forall2_dec `{FinMap K M} {A B} (R : A → B → Prop)
  `{∀ a b, Decision (R a b)} : RelDecision (map_Forall2 (M := M) R).
Proof. apply map_relation_dec; intros; try done; apply False_dec. Qed.

Lemma map_Forall2_insert_L `{FinMapDom K M D} `{!LeibnizEquiv D} {A B}
  (m1 : M A) (m2 : M B) R i x y :
    m1 !! i = None →
    m2 !! i = None →
    R x y →
    map_Forall2 R m1 m2 →
    map_Forall2 R (<[i := x]>m1) (<[i := y]>m2).
Proof.
  unfold map_Forall2, map_relation, option_relation.
  intros Him1 Him2 HR HForall2 j.
  destruct (decide (i = j)).
  + simplify_option_eq. by rewrite 2 lookup_insert.
  + rewrite 2 lookup_insert_ne by done. apply HForall2.
Qed.

Lemma map_Forall2_insert_weak `{FinMap K M} {A B}
  (m1 : M A) (m2 : M B) R i x y :
    R x y →
    map_Forall2 R (delete i m1) (delete i m2) →
    map_Forall2 R (<[i := x]>m1) (<[i := y]>m2).
Proof.
  unfold map_Forall2, map_relation, option_relation.
  intros HR HForall2 j.
  destruct (decide (i = j)).
  - simplify_option_eq. by rewrite 2 lookup_insert.
  - rewrite 2 lookup_insert_ne by done.
    rewrite <-lookup_delete_ne with (i := i) by done.
    replace (m2 !! j) with (delete i m2 !! j); try by apply lookup_delete_ne.
    apply HForall2.
Qed.

Lemma map_Forall2_destruct `{FinMap K M} {A B}
  (m1 : M A) (m2 : M B) R i x :
    map_Forall2 R (<[i := x]>m1) m2 →
    ∃ y m2', m2' !! i = None ∧ m2 = <[i := y]>m2'.
Proof.
  intros HForall2.
  unfold map_Forall2, map_relation, option_relation in HForall2.
  pose proof (HForall2 i). clear HForall2.
  case_match.
  - case_match; try done.
    exists b, (delete i m2).
    split.
    * apply lookup_delete.
    * by rewrite insert_delete_insert, insert_id.
  - case_match; try done.
    by rewrite lookup_insert in H8.
Qed.

Lemma map_Forall2_insert_inv `{FinMap K M} {A B}
  (m1 : M A) (m2 : M B) R i x y :
    map_Forall2 R (<[i := x]>m1) (<[i := y]>m2) →
    R x y ∧ map_Forall2 R (delete i m1) (delete i m2).
Proof.
  intros HForall2.
  unfold map_Forall2, map_relation, option_relation in HForall2.
  pose proof (HForall2 i).
  case_match.
  - case_match; try done.
    rewrite lookup_insert in H8. rewrite lookup_insert in H9.
    simplify_eq /=. split; try done.
    unfold map_Forall2, map_relation, option_relation.
    intros j.
    destruct (decide (i = j)).
    + simplify_option_eq.
      case_match.
      * by rewrite lookup_delete in H8.
      * case_match; [|done].
        by rewrite lookup_delete in H9.
    + case_match; case_match;
        rewrite lookup_delete_ne in H8 by done;
        rewrite lookup_delete_ne in H9 by done;
        pose proof (HForall2 j);
        case_match; case_match; try done;
          rewrite lookup_insert_ne in H11 by done;
          rewrite lookup_insert_ne in H12 by done;
          by simplify_eq /=.
  - by rewrite lookup_insert in H8.
Qed.

Lemma map_Forall2_insert_inv_strict `{FinMap K M} {A B}
  (m1 : M A) (m2 : M B) R i x y :
    m1 !! i = None →
    m2 !! i = None →
    map_Forall2 R (<[i := x]>m1) (<[i := y]>m2) →
    R x y ∧ map_Forall2 R m1 m2.
Proof.
  intros Him1 Him2 HForall2.
  apply map_Forall2_insert_inv in HForall2 as [HPixy HForall2].
  split; try done.
  apply delete_notin in Him1, Him2.
  by rewrite Him1, Him2 in HForall2.
Qed.

Lemma map_Forall2_dom_L `{FinMapDom K M D} `{!LeibnizEquiv D} {A B}
  (R : A → B → Prop) (m1 : M A) (m2 : M B) :
    map_Forall2 R m1 m2 → dom m1 = dom m2.
Proof.
  revert m2.
  induction m1 using map_ind; intros m2.
  - intros HForall2.
    destruct m2 using map_ind; [set_solver|].
    unfold map_Forall2, map_relation, option_relation in HForall2.
    pose proof (HForall2 i). by rewrite lookup_empty, lookup_insert in H15.
  - intros HForall2.
    apply map_Forall2_destruct in HForall2 as Hm2.
    destruct Hm2 as [y [m2' [Hm21 Hm22]]]. simplify_eq /=.
    apply map_Forall2_insert_inv_strict in HForall2 as [_ HForall2]; try done.
    set_solver.
Qed.

Lemma map_Forall2_empty_l_L `{FinMapDom K M D} `{!LeibnizEquiv D} {A B}
  (R : A → B → Prop) (m2 : M B) :
    map_Forall2 R ∅ m2 → m2 = ∅.
Proof.
  intros HForall2.
  apply map_Forall2_dom_L in HForall2 as Hdom.
  rewrite dom_empty_L in Hdom.
  symmetry in Hdom.
  by apply dom_empty_inv_L in Hdom.
Qed.

Lemma map_Forall2_empty_r_L `{FinMapDom K M D} `{!LeibnizEquiv D} {A B}
  (R : A → B → Prop) (m1 : M A) :
    map_Forall2 R m1 ∅ → m1 = ∅.
Proof.
  intros HForall2.
  apply map_Forall2_dom_L in HForall2 as Hdom.
  rewrite dom_empty_L in Hdom.
  by apply dom_empty_inv_L in Hdom.
Qed.

Lemma map_Forall2_empty `{FinMap K M} {A B} (R : A → B → Prop):
  map_Forall2 R (∅ : M A) (∅ : M B).
Proof.
  unfold map_Forall2, map_relation.
  intros i. by rewrite 2 lookup_empty.
Qed.

Lemma map_Forall2_impl_L `{FinMapDom K M D} `{!LeibnizEquiv D} {A B}
  (R1 R2 : A → B → Prop) :
    (∀ a b, R1 a b → R2 a b) →
      ∀ (m1 : M A) (m2 : M B),
        map_Forall2 R1 m1 m2 → map_Forall2 R2 m1 m2.
Proof.
  intros HR1R2 ?? HForall2.
  unfold map_Forall2, map_relation, option_relation in *.
  intros j. pose proof (HForall2 j). clear HForall2.
  case_match; case_match; try done.
  by apply HR1R2.
Qed.

Lemma map_Forall2_fmap_r_L `{FinMapDom K M D} `{!LeibnizEquiv D} {A B C}
  (P : A → C → Prop) (m1 : M A) (m2 : M B) (f : B → C) :
    map_Forall2 P m1 (f <$> m2) → map_Forall2 (λ l r, P l (f r)) m1 m2.
Proof.
  intros HForall2.
  unfold map_Forall2, map_relation, option_relation in *.
  intros j. pose proof (HForall2 j). clear HForall2.
  case_match; case_match; try done; case_match;
    rewrite lookup_fmap in H16; rewrite H17 in H16; by simplify_eq/=.
Qed.

Lemma map_Forall2_eq_L `{FinMapDom K M D} `{!LeibnizEquiv D} {A}
  (m1 m2 : M A) :
    m1 = m2 ↔ map_Forall2 (=) m1 m2.
Proof.
  split; revert m2.
  - induction m1 using map_ind; intros m2 Heq; inv Heq.
    + apply map_Forall2_empty.
    + apply map_Forall2_insert_L; try done. by apply IHm1.
  - induction m1 using map_ind; intros m2 HForall2.
    + by apply map_Forall2_empty_l_L in HForall2.
    + apply map_Forall2_destruct in HForall2 as Hm.
      destruct Hm as [y [m2' [Him2' Heqm2]]]. subst.
      apply map_Forall2_insert_inv in HForall2 as [Heqxy HForall2].
      rewrite 2 delete_notin in HForall2 by done.
      apply IHm1 in HForall2. by subst.
Qed.

Lemma map_insert_L `{FinMapDom K M D} `{!LeibnizEquiv D} {A}
  (i : K) (x1 x2 : A) (m1 m2 : M A) :
    x1 = x2 →
    delete i m1 = delete i m2 →
    <[i := x1]>m1 = <[i := x2]>m2.
Proof.
  intros Heq Hdel.
  apply map_Forall2_eq_L.
  eapply map_Forall2_insert_weak; [done|].
  by apply map_Forall2_eq_L.
Qed.

Lemma map_insert_rev_L `{FinMapDom K M D} `{!LeibnizEquiv D} {A}
  (i : K) (x1 x2 : A) (m1 m2 : M A) :
    <[i := x1]>m1 = <[i := x2]>m2 → x1 = x2 ∧ delete i m1 = delete i m2.
Proof.
  intros Heq. apply map_Forall2_eq_L in Heq.
  apply map_Forall2_insert_inv in Heq as [Heq1 Heq2].
  by apply map_Forall2_eq_L in Heq2.
Qed.

Lemma map_insert_rev_1_L `{FinMapDom K M D} `{!LeibnizEquiv D} {A}
  (i : K) (x1 x2 : A) (m1 m2 : M A) :
    <[i := x1]>m1 = <[i := x2]>m2 → x1 = x2.
Proof. apply map_insert_rev_L. Qed.

Lemma map_insert_rev_2_L `{FinMapDom K M D} `{!LeibnizEquiv D} {A}
  (i : K) (x1 x2 : A) (m1 m2 : M A) :
    <[i := x1]>m1 = <[i := x2]>m2 → delete i m1 = delete i m2.
Proof. apply map_insert_rev_L. Qed.

Lemma map_Forall2_alt_L `{FinMapDom K M D} `{!LeibnizEquiv D} {A B}
  (R : A → B → Prop) (m1 : M A) (m2 : M B) :
    map_Forall2 R m1 m2 ↔
      dom m1 = dom m2 ∧ ∀ i x y, m1 !! i = Some x → m2 !! i = Some y → R x y.
Proof.
  split.
  - intros HForall2.
    split.
    + by apply map_Forall2_dom_L in HForall2.
    + intros i x y Him1 Him2.
      unfold map_Forall2, map_relation, option_relation in HForall2.
      pose proof (HForall2 i). clear HForall2.
      by simplify_option_eq.
  - intros [Hdom HForall2].
    unfold map_Forall2, map_relation, option_relation.
    intros j.
    case_match; case_match; try done.
    + by eapply HForall2.
    + apply mk_is_Some in H14.
      apply not_elem_of_dom in H15.
      apply elem_of_dom in H14.
      set_solver.
    + apply not_elem_of_dom in H14.
      apply mk_is_Some in H15.
      apply elem_of_dom in H15.
      set_solver.
Qed.

(** Relation between map_mapM and map_Forall2 *)

Lemma map_mapM_Some_1_L `{FinMapDom K M D} `{!LeibnizEquiv D} {A B}
  (f : A → option B) (m1 : M A) (m2 : M B) :
    map_mapM f m1 = Some m2 → map_Forall2 (λ x y, f x = Some y) m1 m2.
Proof.
  revert m1 m2 f.
  induction m1 using map_ind.
  - intros m2 f Hmap_mapM.
    unfold map_mapM in Hmap_mapM.
    rewrite map_fold_empty in Hmap_mapM.
    simplify_option_eq. apply map_Forall2_empty.
  - intros m2 f Hmap_mapM.
    csimpl in Hmap_mapM.
    unfold map_mapM in Hmap_mapM.
    csimpl in Hmap_mapM.
    rewrite map_fold_insert_L in Hmap_mapM.
    + simplify_option_eq.
      apply IHm1 in Heqo.
      apply map_Forall2_insert_L; try done.
      apply not_elem_of_dom in H14.
      apply not_elem_of_dom.
      apply map_Forall2_dom_L in Heqo.
      set_solver.
    + intros.
      destruct y; simplify_option_eq; try done.
      destruct (f z2); simplify_option_eq.
      * destruct (f z1); simplify_option_eq; try done.
        f_equal. by apply insert_commute.
      * destruct (f z1); by simplify_option_eq.
    + done.
Qed.

Lemma map_mapM_Some_2_L `{FinMapDom K M D} `{!LeibnizEquiv D} {A B}
  (f : A → option B) (m1 : M A) (m2 : M B) :
    map_Forall2 (λ x y, f x = Some y) m1 m2 → map_mapM f m1 = Some m2.
Proof.
  revert m2.
  induction m1 using map_ind; intros m2 HForall2.
  - unfold map_mapM. rewrite map_fold_empty.
    apply map_Forall2_empty_l_L in HForall2.
    by simplify_eq.
  - destruct (map_Forall2_destruct _ _ _ _ _ HForall2) as
      [y [m2' [HForall21 HForall22]]]. subst.
    destruct (map_Forall2_insert_inv_strict _ _ _ _ _ _ H14 HForall21 HForall2) as
      [Hfy HForall22].
    apply IHm1 in HForall22.
    unfold map_mapM.
    rewrite map_fold_insert_L; try by simplify_option_eq.
    intros.
    destruct y0; simplify_option_eq; try done.
    destruct (f z2); simplify_option_eq.
    * destruct (f z1); simplify_option_eq; try done.
      f_equal. by apply insert_commute.
    * destruct (f z1); by simplify_option_eq.
Qed.

Lemma map_mapM_Some_L `{FinMapDom K M D} `{!LeibnizEquiv D} {A B}
  (f : A → option B) (m1 : M A) (m2 : M B) :
    map_mapM f m1 = Some m2 ↔ map_Forall2 (λ x y, f x = Some y) m1 m2.
Proof. split; [apply map_mapM_Some_1_L | apply map_mapM_Some_2_L]. Qed.
