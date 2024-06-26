Require Import Coq.Strings.String.
From stdpp Require Import gmap relations.
From mininix Require Import binop expr interpreter maptools matching sem.

Lemma eval_le n uf e v' :
  eval n uf e = Some v' →
  ∀ m, n ≤ m → eval m uf e = Some v'.
Proof.
  revert uf e v'.
  induction n; [discriminate|].
  intros uf e v' Heval [] Hle; [lia|].
  apply le_S_n in Hle.
  rewrite eval_S in *.
  destruct e; repeat (case_match || simplify_option_eq || by eauto).
  apply bind_Some. exists H.
  split; try by reflexivity.
  apply map_mapM_Some_L in Heqo.
  apply map_mapM_Some_L.
  eapply map_Forall2_impl_L, Heqo.
  eauto.
Qed.

Lemma eval_value n (v : value) : 0 < n → eval n false v = Some v.
Proof. destruct n, v; by try lia. Qed.

Lemma eval_strong_value n (sv : strong_value) :
  0 < n →
  eval n false sv = Some (value_from_strong_value sv).
Proof. destruct n, sv; by try lia. Qed.

Lemma eval_force_strong_value v : ∃ n,
  eval n true (expr_from_strong_value v) = Some (value_from_strong_value v).
Proof.
  induction v using strong_value_ind'; try by exists 2.
  unfold expr_from_strong_value. simpl.
  fold expr_from_strong_value.
  induction bs using map_ind.
  + by exists 2.
  + apply map_Forall_insert in H as [[n Hn] H2]; try done.
    apply IHbs in H2 as [o Ho]. clear IHbs.
    exists (S (n `max` o)).
    rewrite eval_S. csimpl.
    setoid_rewrite map_mapM_Some_2_L
    with (m2 := value_from_strong_value <$> <[i := x]>m); csimpl.
    * by rewrite <-map_fmap_compose.
    * destruct o as [|o]; csimpl in *; try discriminate.
      apply map_Forall2_alt_L.
      split.
      -- set_solver.
      -- intros j u v ??. rewrite eval_S in Ho.
         apply bind_Some in Ho as [vs [Ho1 Ho2]].
         setoid_rewrite map_mapM_Some_L in Ho1. simplify_eq.
         unfold expr_from_strong_value in Ho2.
         rewrite map_fmap_compose in Ho2.
         simplify_eq.
         destruct (decide (i = j)).
         ++ simplify_eq.
            repeat rewrite lookup_fmap, lookup_insert in *.
            simplify_eq/=.
            apply eval_le with (n := n); lia || done.
         ++ repeat rewrite lookup_fmap, lookup_insert_ne in * by done.
            repeat rewrite <-lookup_fmap in *.
            apply map_Forall2_alt_L in Ho1.
            destruct Ho1 as [Ho1 Ho2].
            apply eval_le with (n := o); try lia.
            by apply Ho2 with (i := j).
Qed.

Lemma eval_force_strong_value' v :
  ∃ n, eval n false (X_Force (expr_from_strong_value v)) =
       Some (value_from_strong_value v).
Proof.
  destruct (eval_force_strong_value v) as [n Heval].
  exists (S n). by rewrite eval_S.
Qed.

Lemma rec_subst_lookup bs x e :
  bs !! x = Some (B_Nonrec e) → rec_subst bs !! x = Some e.
Proof. unfold rec_subst. rewrite lookup_fmap. by intros ->. Qed.

Lemma rec_subst_lookup_fmap bs x e :
  bs !! x = Some e → rec_subst (B_Nonrec <$> bs) !! x = Some e.
Proof. unfold rec_subst. do 2 rewrite lookup_fmap. by intros ->. Qed.

Lemma rec_subst_lookup_fmap' bs x :
  is_Some (bs !! x) ↔ is_Some (rec_subst (B_Nonrec <$> bs) !! x).
Proof.
  unfold rec_subst. split;
    do 2 rewrite lookup_fmap in *;
    intros [b H]; by simplify_option_eq.
Qed.

Lemma eval_base_step uf e e' v'' n :
  e -->base e' →
  eval n uf e' = Some v'' →
  ∃ m, eval m uf e = Some v''.
Proof.
  intros [] Heval.
  - (* E_Force *)
    destruct uf.
    + (* true *)
      exists (S n). rewrite eval_S. by csimpl.
    + (* false *)
      destruct n; try discriminate.
      rewrite eval_strong_value in Heval by lia.
      simplify_option_eq.
      apply eval_force_strong_value'.
  - (* E_Closed *)
    exists (S n). rewrite eval_S. by csimpl.
  - (* E_Placeholder *)
    exists (S n). rewrite eval_S. by csimpl.
  - (* E_MSelect *)
    destruct n; try discriminate.
    rewrite eval_S in Heval. simplify_option_eq.
    destruct ys. simplify_option_eq.
    destruct n as [|[|n]]; try discriminate.
    rewrite eval_S in Heqo. simplify_option_eq.
    rewrite eval_S in Heqo1. simplify_option_eq.
    exists (S (S (S (S n)))). rewrite eval_S. simplify_option_eq.
    rewrite eval_value by lia. simplify_option_eq.
    rewrite eval_S. simplify_option_eq.
    rewrite eval_le with (n := S n) (v' := V_Attrset H0) by done || lia.
    by simplify_option_eq.
  - (* E_Select *)
    exists (S n). rewrite eval_S. csimpl.
    apply bind_Some. exists (V_Attrset (<[x := e0]>bs)).
    destruct n; try discriminate. split; [done|].
    apply bind_Some. exists (<[x := e0]>bs). split; [done|].
    rewrite lookup_insert. by simplify_option_eq.
  - (* E_SelectOr *)
    destruct n; try discriminate.
    rewrite eval_S in Heval. simplify_option_eq.
    destruct n as [|[|n]]; try discriminate.
    rewrite eval_S in Heqo. simplify_option_eq.
    rewrite eval_S in Heqo0. simplify_option_eq.
    exists (S (S (S n))). rewrite eval_S. simplify_option_eq.
    rewrite eval_value by lia. simplify_option_eq.
    case_match.
    + rewrite bool_decide_eq_true in H. destruct H as [d Hd].
      simplify_option_eq. rewrite eval_S in Heval. simplify_option_eq.
      rewrite eval_S in Heqo. simplify_option_eq.
      apply eval_le with (n := S n); done || lia.
    + rewrite bool_decide_eq_false in H. apply eq_None_not_Some in H.
      by simplify_option_eq.
  - (* E_MSelectOr *)
    destruct n; try discriminate.
    rewrite eval_S in Heval. simplify_option_eq.
    destruct ys. simplify_option_eq.
    destruct n as [|[|n]]; try discriminate.
    rewrite eval_S in Heqo. simplify_option_eq.
    rewrite eval_S in Heqo0. simplify_option_eq.
    exists (S (S (S n))). rewrite eval_S. simplify_option_eq.
    rewrite eval_value by lia. simplify_option_eq.
    case_match.
    + rewrite bool_decide_eq_true in H. destruct H as [d Hd].
      simplify_option_eq. rewrite eval_S in Heval. simplify_option_eq.
      rewrite eval_S in Heqo. simplify_option_eq.
      destruct n; try discriminate. rewrite eval_S in Heqo0.
      simplify_option_eq. rewrite eval_S.
      simplify_option_eq.
      setoid_rewrite eval_le with (n := S n) (v' := V_Attrset H0); done || lia.
    + rewrite bool_decide_eq_false in H. apply eq_None_not_Some in H.
      by simplify_option_eq.
  - (* E_Rec *)
    exists (S n). rewrite eval_S. by csimpl.
  - (* E_Let *)
    exists (S n). rewrite eval_S. by csimpl.
  - (* E_With *)
    exists (S n). rewrite eval_S. csimpl.
    apply bind_Some. exists (V_Attrset bs).
    by destruct n; try discriminate.
  - (* E_WithNoAttrset *)
    exists (S n). rewrite eval_S. csimpl.
    apply bind_Some. exists v1.
    destruct v1; try by destruct n; try discriminate.
    exfalso. apply H. by exists bs.
  - (* E_ApplySimple *)
    exists (S n). rewrite eval_S. simpl.
    apply bind_Some. exists (V_Fn x e1).
    split; [|assumption].
    destruct n; try discriminate; reflexivity.
  - (* E_ApplyAttrset *)
    exists (S n). rewrite eval_S. csimpl.
    apply bind_Some. exists (V_AttrsetFn m e0).
    destruct n; try discriminate. split; [done|].
    apply bind_Some. exists (V_Attrset bs). split; [done|].
    apply bind_Some. exists bs. split; [done|].
    apply bind_Some. apply matches_complete in H.
    by exists bs'.
  - (* E_ApplyFunctor *)
    exists (S n). rewrite eval_S. csimpl.
    apply bind_Some. exists (V_Attrset (<["__functor" := e2]>bs)).
    destruct n; try discriminate. split; [done|].
    rewrite lookup_insert. by simplify_option_eq.
  - (* E_IfTrue *)
    exists (S n). rewrite eval_S. csimpl.
    apply bind_Some. exists true.
    by destruct n; try discriminate.
  - (* E_IfFalse *)
    exists (S n). rewrite eval_S. csimpl.
    apply bind_Some. exists false.
    by destruct n; try discriminate.
  - (* E_Op *)
    exists (S n). rewrite eval_S. simpl.
    apply bind_Some. exists v1.
    destruct n; try discriminate.
    split.
    + apply eval_value. lia.
    + apply bind_Some. exists v2. split.
      * apply eval_value. lia.
      * apply binop_eval_complete in H.
        apply bind_Some. by exists u.
  - (* E_OpHasAttrTrue *)
    exists (S n). rewrite eval_S. csimpl.
    apply bind_Some. exists (V_Attrset bs).
    destruct n; try discriminate. rewrite eval_S in Heval.
    simplify_option_eq. by rewrite bool_decide_eq_true_2.
  - (* E_OpHasAttrFalse *)
    exists (S n). rewrite eval_S. csimpl.
    apply bind_Some. exists (V_Attrset bs).
    destruct n; try discriminate. rewrite eval_S in Heval.
    simplify_option_eq. rewrite eq_None_not_Some in H.
    by rewrite bool_decide_eq_false_2.
  - (* E_OpHasAttrNoAttrset *)
    exists (S n). rewrite eval_S. csimpl.
    destruct n; try discriminate. rewrite eval_S in Heval.
    simplify_option_eq.
    apply bind_Some. exists v.
    split; [apply eval_value; lia|].
    case_match; try done.
    exfalso. apply H. by exists bs.
  - (* E_Assert *)
    exists (S n). rewrite eval_S. csimpl.
    apply bind_Some. exists true.
    split; [by destruct n | done].
Qed.

Lemma eval_step_ctx : ∀ e e' E uf_ext uf_int n v'',
  is_ctx uf_ext uf_int E →
  e -->base e' →
  eval n uf_ext (E e') = Some v'' →
  ∃ m, eval m uf_ext (E e) = Some v''.
Proof.
  intros e e' E uf_in uf_out n v'' Hctx Hbstep.
  revert v''.
  induction Hctx.
  - intros. by apply eval_base_step with (e' := e') (n := n).
  - inv H; intros.
    + destruct n as [|n]; try discriminate.
      rewrite eval_S in H. simplify_option_eq.
      destruct xs. simplify_option_eq.
      apply eval_le with (m := S n) in Heqo; try lia.
      apply IHHctx in Heqo as [m He].
      exists (S (n `max` m)).
      rewrite eval_S. simplify_option_eq.
      rewrite eval_le with (n := m) (v' := V_Attrset H1) by lia || done.
      simplify_option_eq.
      case_match; by rewrite eval_le with (n := n) (v' := v'') by lia || done.
    + intros.
      destruct n as [|n]; try discriminate.
      rewrite eval_S in H. simplify_option_eq.
      destruct xs. simplify_option_eq.
      apply eval_le with (m := S n) in Heqo; try lia.
      apply IHHctx in Heqo as [m He].
      exists (S (n `max` m)).
      rewrite eval_S. simplify_option_eq.
      setoid_rewrite eval_le with (n := m); try lia || done.
      simplify_option_eq. repeat case_match;
        apply eval_le with (n := n); lia || done.
    + intros.
      destruct n as [|n]; try discriminate.
      rewrite eval_S in H. simplify_option_eq.
      apply eval_le with (m := S n) in Heqo; try lia.
      apply IHHctx in Heqo as [m He].
      exists (S (n `max` m)).
      rewrite eval_S. simplify_option_eq.
      setoid_rewrite eval_le with (n := m); try lia || done.
      simplify_option_eq. repeat case_match;
        apply eval_le with (n := n); lia || done.
    + (* X_Apply *)
      intros.
      destruct n as [|n]; try discriminate.
      rewrite eval_S in H. simplify_option_eq.
      apply eval_le with (m := S n) in Heqo; try done || lia.
      apply IHHctx in Heqo as [m He].
      exists (S (n `max` m)).
      rewrite eval_S. simplify_option_eq.
      destruct H0; try discriminate.
      * setoid_rewrite eval_le with (n := m); try done || lia.
        simplify_option_eq.
        setoid_rewrite eval_le with (n := n); done || lia.
      * setoid_rewrite eval_le with (n := m); try done || lia.
        simplify_option_eq.
        rewrite eval_le with (n := n) at 1; try done || lia.
        simplify_option_eq.
        setoid_rewrite eval_le with (n := n); done || lia.
      * setoid_rewrite eval_le with (n := m); try done || lia.
        simplify_option_eq.
        setoid_rewrite eval_le with (n := n); done || lia.
    + intros.
      destruct n as [|n]; try discriminate.
      rewrite eval_S in H. simplify_option_eq.
      destruct n; try discriminate. rewrite eval_S in Heqo.
      simplify_option_eq.
      apply eval_le with (m := S (S n)) in Heqo; try lia.
      apply IHHctx in Heqo as [o He].
      exists (S (S (n `max` o))).
      rewrite eval_S. simplify_option_eq.
      destruct o as [|o]; try discriminate.
      setoid_rewrite eval_le with (n := S o) (v' := V_AttrsetFn m e1);
        try done || lia.
      simplify_option_eq.
      rewrite eval_le with (n := S o) (v' := V_Attrset H1);
        try by rewrite eval_S || lia.
      simplify_option_eq.
      rewrite eval_le with (n := S n) (v' := v''); done || lia.
    + intros.
      destruct n as [|n]; try discriminate.
      rewrite eval_S in H. simplify_option_eq.
      apply eval_le with (m := S n) in Heqo. 2: lia.
      apply IHHctx in Heqo as [m He].
      exists (S (n `max` m)).
      rewrite eval_S. simplify_option_eq.
      rewrite eval_le with (n := m) (v' := H1) by lia || done.
      setoid_rewrite eval_le with (n := n) (v' := v''); try lia || done.
    + intros.
      destruct n as [|n]; try discriminate.
      rewrite eval_S in H. simplify_option_eq.
      apply eval_le with (m := S n) in Heqo. 2: lia.
      apply IHHctx in Heqo as [m He].
      exists (S (n `max` m)).
      destruct H0; try discriminate.
      rewrite eval_S. simplify_option_eq.
      setoid_rewrite eval_le with (n := m) (v' := p); try lia || done.
      simplify_option_eq. destruct p; try discriminate.
      apply eval_le with (n := n); lia || done.
    + intros.
      destruct n as [|n]; try discriminate.
      rewrite eval_S in H. simplify_option_eq.
      apply eval_le with (m := S n) in Heqo. 2: lia.
      apply IHHctx in Heqo as [m He].
      exists (S (n `max` m)).
      rewrite eval_S. simplify_option_eq.
      rewrite eval_le with (n := n) (v' := H1) by lia || done.
      rewrite eval_le with (n := m) (v' := H0) by lia || done.
      simplify_option_eq.
      apply eval_le with (n := n); lia || done.
    + intros.
      destruct n as [|n]; try discriminate.
      rewrite eval_S in H. simplify_option_eq.
      apply eval_le with (m := S n) in Heqo0. 2: lia.
      apply IHHctx in Heqo0 as [m He].
      exists (S (n `max` m)).
      rewrite eval_S. simplify_option_eq.
      rewrite eval_le with (n := m) (v' := H1) by lia || done.
      rewrite eval_le with (n := n) (v' := H0) by lia || done.
      simplify_option_eq.
      apply eval_le with (n := n) (v' := v''); lia || done.
    + (* IsCtxItem_OpHasAttrL *)
      intros.
      destruct n as [|n]; try discriminate.
      rewrite eval_S in H. simplify_option_eq.
      apply eval_le with (m := S n) in Heqo. 2: lia.
      apply IHHctx in Heqo as [m He].
      exists (S (n `max` m)).
      rewrite eval_S. simplify_option_eq.
      by rewrite eval_le with (n := m) (v' := H0) by lia || done.
    + intros.
      destruct n as [|n]; try discriminate.
      rewrite eval_S in H. simplify_option_eq.
      apply eval_le with (m := S n) in H. 2: lia.
      apply IHHctx in H as [m He].
      exists (S (n `max` m)).
      rewrite eval_S; simplify_option_eq.
      apply eval_le with (n := m) (v' := v''); lia || done.
    + intros. simplify_option_eq.
      destruct n as [|n]; try discriminate.
      rewrite eval_S in H. simplify_option_eq.
      apply map_mapM_Some_L in Heqo.
      destruct (map_Forall2_destruct _ _ _ _ _ Heqo)
        as [v' [m2' [Hkm2' HeqH0]]]. simplify_option_eq.
      apply map_Forall2_insert_inv in Heqo as [Hinterp HForall2]; try done.
      apply eval_le with (m := S n) in Hinterp; try lia.
      apply IHHctx in Hinterp as [m Hinterp].
      exists (S (n `max` m)).
      rewrite eval_S. simplify_option_eq.
      apply bind_Some. exists (<[x := v']> m2'). split; try done.
      apply map_mapM_Some_L.
      apply map_Forall2_insert_weak.
      * apply eval_le with (n := m); lia || done.
      * apply map_Forall2_impl_L
        with (R1 := λ x y, eval n true x = Some y); try done.
        intros u v Hjuv. by apply eval_le with (n := n); try lia.
Qed.

Lemma eval_step e e' v'' n :
  e --> e' →
  eval n false e' = Some v'' →
  ∃ m, eval m false e = Some v''.
Proof.
 intros. inv H.
 apply (eval_step_ctx e1 e2 E false uf_int n v'' H1 H2 H0).
Qed.

Theorem eval_complete e (v' : value) :
  e -->* v' → ∃ n, eval n false e = Some v'.
Proof.
  intros [steps Hsteps] % rtc_nsteps. revert e v' Hsteps.
  induction steps; intros e e' Hsteps; inv Hsteps.
  - exists 1. apply eval_value. lia.
  - destruct (IHsteps y e') as [n Hn]; try done.
    clear IHsteps. by apply eval_step with (e := e) in Hn.
Qed.
