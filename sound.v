Require Import Coq.Strings.String.
From stdpp Require Import base gmap relations tactics.
From mininix Require Import
  binop expr interpreter maptools matching relations sem.

Lemma strong_value_stuck sv : ¬ ∃ e, expr_from_strong_value sv --> e.
Proof.
  intros []. destruct sv; inv H; inv H1;
    simplify_option_eq; (try inv H2); inv H.
Qed.

Lemma strong_value_stuck_rtc sv e:
  expr_from_strong_value sv -->* e →
  e = expr_from_strong_value sv.
Proof.
  intros. inv H.
  - reflexivity.
  - exfalso. apply strong_value_stuck with (sv := sv). by exists y.
Qed.

Lemma force__strong_value (e : expr) (v : value) :
  X_Force e -->* v →
  ∃ sv, v = value_from_strong_value sv.
Proof.
  intros [n Hsteps] % rtc_nsteps.
  revert e v Hsteps.
  induction n; intros e v Hsteps; inv Hsteps.
  inv H0. inv H2; simplify_eq/=.
  - inv H3.
    exists sv.
    apply rtc_nsteps_2 in H1.
    apply strong_value_stuck_rtc in H1.
    unfold expr_from_strong_value, compose in H1.
    congruence.
  - inv H0.
    destruct (IHn _ _ H1) as [sv Hsv].
    by exists sv.
Qed.

Lemma forall2_force__strong_values es (vs : gmap string value) :
  map_Forall2 (λ e v', X_Force e -->* X_V v') es vs →
  ∃ svs, vs = value_from_strong_value <$> svs.
Proof.
  revert vs.
  induction es using map_ind; intros vs HForall2.
  - apply map_Forall2_empty_l_L in HForall2. by exists ∅.
  - destruct (map_Forall2_destruct _ _ _ _ _ HForall2)
    as [v [m2' [Him2' Heqvs]]]. simplify_eq/=.
    apply map_Forall2_insert_inv_strict in HForall2
    as [Hstep HForall2]; try done.
    apply IHes in HForall2 as [svs Hsvs]. simplify_eq/=.
    apply force__strong_value in Hstep as [sv Hsv]. simplify_eq/=.
    exists (<[i := sv]>svs). by rewrite fmap_insert.
Qed.

Lemma force_strong_value_forall2_impl es (svs : gmap string strong_value) :
  map_Forall2 (λ e v', X_Force e -->* X_V v')
          es (value_from_strong_value <$> svs) →
  map_Forall2 (λ e sv', X_Force e -->* expr_from_strong_value sv') es svs.
Proof. apply map_Forall2_fmap_r_L. Qed.

Lemma force_map_fmap_union_insert (sws : gmap string strong_value) es k e sv :
  X_Force e -->* expr_from_strong_value sv →
  X_Force (X_V (V_Attrset (<[k := e]>es ∪
    (expr_from_strong_value <$> sws)))) -->*
  X_Force (X_V (V_Attrset (<[k := expr_from_strong_value sv]>es ∪
    (expr_from_strong_value <$> sws)))).
Proof.
  intros [n Hsteps] % rtc_nsteps.
  revert sws es k e Hsteps.
  induction n; intros sws es k e Hsteps.
  - inv Hsteps.
  - inv Hsteps.
    inv H0.
    inv H2.
    + inv H3. inv H1.
      * simplify_option_eq. unfold expr_from_strong_value, compose.
        by rewrite H4.
      * edestruct strong_value_stuck. exists y. done.
    + inv H0. simplify_option_eq.
      apply rtc_transitive
      with (y := X_Force (X_V (V_Attrset (<[k:=E2 e2]> es ∪
        (expr_from_strong_value <$> sws))))).
      * do 2 rewrite <-insert_union_l.
        apply rtc_once.
        eapply E_Ctx
        with (E := λ e, X_Force (X_V (V_Attrset (<[k := E2 e]>(es ∪
          (expr_from_strong_value <$> sws)))))).
        -- eapply IsCtx_Compose.
           ++ constructor.
           ++ eapply IsCtx_Compose
              with (E1 := (λ e, X_V (V_Attrset (<[k := e]>(es ∪
                (expr_from_strong_value <$> sws)))))).
              ** constructor.
              ** done.
        -- done.
      * by apply IHn.
Qed.

Lemma insert_union_fmap__union_fmap_insert {A B} (f : A → B) i x
  (m1 : gmap string B) (m2 : gmap string A) :
    m1 !! i = None →
    <[i := f x]>m1 ∪ (f <$> m2) = m1 ∪ (f <$> <[i := x]>m2).
Proof.
  intros Him1.
  rewrite fmap_insert.
  rewrite <-insert_union_l.
  by rewrite <-insert_union_r.
Qed.

Lemma fmap_insert_union__fmap_union_insert {A B} (f : A → B) i x
  (m1 : gmap string A) (m2 : gmap string A) :
    m1 !! i = None →
    f <$> <[i := x]>m1 ∪ m2 = f <$> m1 ∪ <[i := x]>m2.
Proof.
  intros Him1.
  do 2 rewrite map_fmap_union.
  rewrite 2 fmap_insert.
  rewrite <-insert_union_l.
  rewrite <-insert_union_r; try done.
  rewrite lookup_fmap.
  by rewrite Him1.
Qed.

Lemma force_map_fmap_union (sws svs : gmap string strong_value) es :
  map_Forall2 (λ e sv, X_Force e -->* expr_from_strong_value sv) es svs →
  X_Force (X_V (V_Attrset (es ∪ (expr_from_strong_value <$> sws)))) -->*
  X_Force (X_V (V_Attrset (expr_from_strong_value <$> svs ∪ sws))).
Proof.
  revert sws svs.
  induction es using map_ind; intros sws svs HForall2.
  - apply map_Forall2_empty_l_L in HForall2.
    subst. by do 2 rewrite map_empty_union.
  - apply map_Forall2_destruct in HForall2 as HForall2'.
    destruct HForall2' as [sv [svs' [Him2' Heqm2']]]. subst.
    apply map_Forall2_insert_inv_strict
    in HForall2 as [HForall21 HForall22]; try done.
    apply rtc_transitive with (X_Force
      (X_V (V_Attrset (<[i := expr_from_strong_value sv]> m ∪
                       (expr_from_strong_value <$> sws))))).
    + by apply force_map_fmap_union_insert.
    + rewrite insert_union_fmap__union_fmap_insert by done.
      rewrite fmap_insert_union__fmap_union_insert by done.
      by apply IHes.
Qed.

(* See 194+2024-0525-2305 for proof sketch *)
Lemma force_map_fmap (svs : gmap string strong_value) (es : gmap string expr) :
  map_Forall2 (λ e sv, X_Force e -->* expr_from_strong_value sv) es svs →
  X_Force (X_V (V_Attrset es)) -->*
  X_Force (X_V (V_Attrset (expr_from_strong_value <$> svs))).
Proof.
  pose proof (force_map_fmap_union ∅ svs es).
  rewrite fmap_empty in H. by do 2 rewrite map_union_empty in H.
Qed.

Lemma id_compose_l {A B} (f : A → B) : id ∘ f = f.
Proof. done. Qed.

Lemma is_ctx_trans uf_ext uf_aux uf_int E1 E2 :
  is_ctx uf_ext uf_aux E1 →
  is_ctx uf_aux uf_int E2 →
  is_ctx uf_ext uf_int (E1 ∘ E2).
Proof.
  intros.
  induction H.
  - induction H0.
    + apply IsCtx_Id.
    + rewrite id_compose_l.
      by apply IsCtx_Compose with uf_aux.
  - apply IHis_ctx in H0.
    replace (E1 ∘ E0 ∘ E2) with (E1 ∘ (E0 ∘ E2)) by done.
    by apply IsCtx_Compose with uf_aux.
Qed.

Lemma ctx_mstep e e' E :
  e -->* e' → is_ctx false false E → E e -->* E e'.
Proof.
  intros.
  induction H.
  - apply rtc_refl.
  - inv H.
    pose proof (is_ctx_trans false false uf_int E E0 H0 H2).
    eapply rtc_l.
    + replace (E (E0 e1)) with ((E ∘ E0) e1) by done.
      eapply E_Ctx; [apply H | apply H3].
    + assumption.
Qed.

Definition is_nonempty_ctx (uf_ext uf_int : bool) (E : expr → expr) :=
  ∃ E1 E2 uf_aux,
    is_ctx_item uf_ext uf_aux E1 ∧
    is_ctx uf_aux uf_int E2 ∧ E = E1 ∘ E2.

Lemma nonempty_ctx_mstep e e' uf_int E :
  e -->* e' → is_nonempty_ctx false uf_int E → E e -->* E e'.
Proof.
  intros Hmstep Hctx.
  destruct Hctx as [E1 [E2 [uf_aux [Hctx1 [Hctx2 Hctx3]]]]].
  simplify_option_eq.
  induction Hmstep.
  + apply rtc_refl.
  + apply rtc_l with (y := (E1 ∘ E2) y).
    * inv H.
      destruct (is_ctx_uf_false_impl_true E uf_int0 H0).
      +++ apply E_Ctx with (E := E1 ∘ (E2 ∘ E)) (uf_int := uf_int0).
          ++ eapply IsCtx_Compose.
             ** apply Hctx1.
             ** eapply is_ctx_trans.
                --- apply Hctx2.
                --- destruct uf_int; assumption.
          ++ assumption.
      +++ apply E_Ctx with (E := E1 ∘ (E2 ∘ E)) (uf_int := uf_int).
          ++ eapply IsCtx_Compose.
             ** apply Hctx1.
             ** eapply is_ctx_trans; simplify_option_eq.
                --- apply Hctx2.
                --- constructor.
          ++ assumption.
    * apply IHHmstep.
Qed.

Lemma force_strong_value (sv : strong_value) :
  X_Force sv -->* sv.
Proof.
  destruct sv using strong_value_ind';
    apply rtc_once; eapply E_Ctx with (E := id); constructor.
Qed.

Lemma id_compose_r {A B} (f : A → B) : f ∘ id = f.
Proof. done. Qed.

Lemma force_idempotent e (v' : value) :
  X_Force e -->* v' →
  X_Force (X_Force e) -->* v'.
Proof.
  intros H.
  destruct (force__strong_value _ _ H) as [sv Hsv]. subst.
  apply rtc_transitive with (y := X_Force sv).
  * eapply nonempty_ctx_mstep; try assumption.
    rewrite <-id_compose_r.
    exists X_Force, id, true.
    repeat (split || constructor || done).
  * apply force_strong_value.
Qed.

(* Conditional force *)
Definition cforce (uf : bool) e := if uf then X_Force e else e.

Lemma cforce_strong_value uf (sv : strong_value) :
  cforce uf sv -->* sv.
Proof. destruct uf; try done. apply force_strong_value. Qed.

Theorem eval_sound_strong n uf e v' :
   eval n uf e = Some v' →
   cforce uf e -->* v'.
Proof.
  revert uf e v'.
  induction n; intros uf e v' Heval.
  - discriminate.
  - destruct e; rewrite eval_S in Heval; simplify_option_eq; try done.
    + (* X_V *)
      case_match; simplify_option_eq.
      * (* V_Bool *)
        replace (V_Bool p) with (value_from_strong_value (SV_Bool p)) by done.
        apply cforce_strong_value.
      * (* V_Null *)
        replace V_Null with (value_from_strong_value SV_Null) by done.
        apply cforce_strong_value.
      * (* V_Int *)
        replace (V_Int n0) with (value_from_strong_value (SV_Int n0)) by done.
        apply cforce_strong_value.
      * (* V_Str *)
        replace (V_Str s) with (value_from_strong_value (SV_Str s)) by done.
        apply cforce_strong_value.
      * (* V_Fn *)
        replace (V_Fn x e) with (value_from_strong_value (SV_Fn x e)) by done.
        apply cforce_strong_value.
      * (* V_AttrsetFn *)
        replace (V_AttrsetFn m e)
        with (value_from_strong_value (SV_AttrsetFn m e)) by done.
        apply cforce_strong_value.
      * (* V_Attrset *)
        case_match; simplify_option_eq; try done.
        apply map_mapM_Some_L in Heqo. simplify_option_eq.
        eapply map_Forall2_impl_L in Heqo. 2: { intros a b. apply IHn. }
        destruct (forall2_force__strong_values _ _ Heqo). subst.
        apply force_strong_value_forall2_impl in Heqo.
        rewrite <-map_fmap_compose. fold expr_from_strong_value.
        apply force_map_fmap in Heqo.
        apply rtc_transitive
        with (y := X_Force (X_V (V_Attrset (expr_from_strong_value <$> x))));
          try done.
        apply rtc_once.
        eapply E_Ctx with (E := id); [constructor|].
        replace (X_V (V_Attrset (expr_from_strong_value <$> x)))
         with (expr_from_strong_value (SV_Attrset x)) by reflexivity.
        apply E_Force.
    + (* X_Attrset *)
      apply IHn in Heval.
      apply rtc_transitive with (y := cforce uf (V_Attrset (rec_subst bs)));
        [|done].
      destruct uf; simplify_eq/=.
      -- eapply nonempty_ctx_mstep with (E := X_Force).
         ++ by eapply rtc_once, E_Ctx with (E := id).
         ++ by exists X_Force, id, true.
      -- apply rtc_once. by eapply E_Ctx with (E := id).
    + (* X_LetBinding *)
      apply IHn in Heval.
      apply rtc_transitive
      with (y := cforce uf (subst (closed (rec_subst bs)) e)); [|done].
      destruct uf; simplify_eq/=.
      -- eapply nonempty_ctx_mstep with (E := X_Force).
         ++ by eapply rtc_once, E_Ctx with (E := id).
         ++ by exists X_Force, id, true.
      -- apply rtc_once. by eapply E_Ctx with (E := id).
    + (* X_Select *)
      case_match. simplify_option_eq.
      apply IHn in Heqo. simplify_eq/=.
      apply rtc_transitive with (y := cforce uf
        (X_Select (V_Attrset H0) (Ne_Cons head tail))).
      -- apply ctx_mstep
         with (E := cforce uf ∘ (λ e, X_Select e (Ne_Cons head tail))).
         ++ done.
         ++ destruct uf; simplify_option_eq.
            ** eapply IsCtx_Compose; [constructor | by apply is_ctx_once].
            ** apply is_ctx_once. unfold compose. by simpl.
      -- case_match; apply IHn in Heval.
         ++ apply rtc_transitive with (y := cforce uf H); [|done].
            apply rtc_once.
            eapply E_Ctx.
            ** destruct uf; [by apply is_ctx_once | done].
            ** by replace H0 with (<[head := H]>H0); [|apply insert_id].
         ++ apply rtc_transitive
            with (y := cforce uf (X_Select H (Ne_Cons s l))); [|done].
            ** eapply rtc_l.
               --- eapply E_Ctx.
                   +++ destruct uf; [by apply is_ctx_once | done].
                   +++ replace (Ne_Cons head (s :: l))
                       with (nonempty_cons head (Ne_Cons s l)) by done.
                       apply E_MSelect.
               --- eapply rtc_once.
                   eapply E_Ctx
                   with (E := cforce uf ∘ (λ e, X_Select e (Ne_Cons s l))).
                   +++ destruct uf.
                       *** eapply IsCtx_Compose; [done | by apply is_ctx_once].
                       *** apply is_ctx_once. unfold compose. by simpl.
                   +++ by replace H0
                          with (<[head := H]>H0); [|apply insert_id].
    + (* X_SelectOr *)
      case_match. simplify_option_eq.
      apply IHn in Heqo. simplify_eq/=.
      apply rtc_transitive
      with (y := cforce uf (X_SelectOr (V_Attrset H0) (Ne_Cons head tail) e2)).
      -- apply ctx_mstep
         with (E := cforce uf ∘ (λ e, X_SelectOr e (Ne_Cons head tail) e2)).
         ++ done.
         ++ destruct uf; simplify_option_eq.
            ** eapply IsCtx_Compose; [constructor | by apply is_ctx_once].
            ** apply is_ctx_once. unfold compose. by simpl.
      -- case_match; try case_match; apply IHn in Heval.
         ++ apply rtc_transitive with (y := cforce uf e); [|done].
            eapply rtc_l.
            ** eapply E_Ctx.
               --- destruct uf; [by apply is_ctx_once | done].
               --- replace (Ne_Cons head []) with (nonempty_singleton head)
                   by done. constructor.
            ** eapply rtc_l.
               --- eapply E_Ctx with (E := cforce uf ∘ (λ e1, X_Cond e1 _ _)).
                   +++ destruct uf; simplify_option_eq.
                       *** eapply IsCtx_Compose;
                             [constructor | by apply is_ctx_once].
                       *** apply is_ctx_once. unfold compose. by simpl.
                   +++ by apply E_OpHasAttrTrue.
               --- simplify_eq/=.
                   eapply rtc_l.
                   +++ eapply E_Ctx with (E := cforce uf).
                       *** destruct uf; [by apply is_ctx_once | done].
                       *** apply E_IfTrue.
                   +++ eapply rtc_once.
                       eapply E_Ctx with (E := cforce uf).
                       *** destruct uf; [by apply is_ctx_once | done].
                       *** by replace H0 with (<[head := e]>H0);
                             [|apply insert_id].
         ++ apply rtc_transitive
            with (y := cforce uf (X_SelectOr e (Ne_Cons s l) e2)); [|done].
            eapply rtc_l.
            ** eapply E_Ctx.
               --- destruct uf; [by apply is_ctx_once | done].
               --- replace (Ne_Cons head (s :: l))
                   with (nonempty_cons head (Ne_Cons s l)) by done.
                   constructor.
            ** eapply rtc_l.
               --- eapply E_Ctx with (E := cforce uf ∘ (λ e1, X_Cond e1 _ _)).
                   +++ destruct uf; simplify_option_eq.
                       *** eapply IsCtx_Compose;
                             [constructor | by apply is_ctx_once].
                       *** apply is_ctx_once. unfold compose. by simpl.
                   +++ by apply E_OpHasAttrTrue.
               --- simplify_eq/=.
                   eapply rtc_l.
                   +++ eapply E_Ctx with (E := cforce uf).
                       *** destruct uf; [by apply is_ctx_once | done].
                       *** apply E_IfTrue.
                   +++ eapply rtc_once.
                       eapply E_Ctx
                       with (E := cforce uf ∘ λ e1,
                         X_SelectOr e1 (Ne_Cons s l) e2).
                       *** destruct uf; simplify_option_eq.
                           ---- eapply IsCtx_Compose;
                                  [constructor | by apply is_ctx_once].
                           ---- apply is_ctx_once. unfold compose. by simpl.
                       *** by replace H0 with (<[head := e]>H0);
                             [|apply insert_id].
         ++ apply rtc_transitive with (y := cforce uf e2); [|done].
            destruct tail.
            ** eapply rtc_l.
               --- eapply E_Ctx.
                   +++ destruct uf; [by apply is_ctx_once | done].
                   +++ replace (Ne_Cons head [])
                       with (nonempty_singleton head) by done.
                       constructor.
               --- eapply rtc_l.
                   +++ eapply E_Ctx
                       with (E := cforce uf ∘ (λ e1, X_Cond e1 _ _)).
                       *** destruct uf; simplify_option_eq.
                           ---- eapply IsCtx_Compose;
                                  [constructor | by apply is_ctx_once].
                           ---- apply is_ctx_once. unfold compose. by simpl.
                       *** by apply E_OpHasAttrFalse.
                   +++ simplify_eq/=.
                       eapply rtc_once.
                       eapply E_Ctx with (E := cforce uf).
                       *** destruct uf; [by apply is_ctx_once | done].
                       *** apply E_IfFalse.
            ** eapply rtc_l.
               --- eapply E_Ctx.
                   +++ destruct uf; [by apply is_ctx_once | done].
                   +++ replace (Ne_Cons head (s :: tail))
                       with (nonempty_cons head (Ne_Cons s tail)) by done.
                       constructor.
               --- eapply rtc_l.
                   +++ eapply E_Ctx
                       with (E := cforce uf ∘ (λ e1, X_Cond e1 _ _)).
                       *** destruct uf; simplify_option_eq.
                           ---- eapply IsCtx_Compose;
                                  [constructor | by apply is_ctx_once].
                           ---- apply is_ctx_once. unfold compose. by simpl.
                       *** by apply E_OpHasAttrFalse.
                   +++ simplify_eq/=.
                       eapply rtc_once.
                       eapply E_Ctx with (E := cforce uf).
                       *** destruct uf; [by apply is_ctx_once | done].
                       *** apply E_IfFalse.
    + (* X_Apply *)
      case_match; simplify_option_eq; apply IHn in Heqo, Heval.
      * (* Basic lambda abstraction *)
        apply rtc_transitive with (y := cforce uf (X_Apply (V_Fn x e) e2)).
        -- apply ctx_mstep with (E := cforce uf ∘ λ e1, X_Apply e1 e2);
             [done|].
           destruct uf.
           ++ by eapply IsCtx_Compose; [|apply is_ctx_once].
           ++ apply is_ctx_once. unfold compose. by simpl.
        -- apply rtc_transitive
           with (y := cforce uf (subst {[x := X_Closed e2]} e)); [|done].
           eapply rtc_once.
           eapply E_Ctx.
           ++ destruct uf; [by apply is_ctx_once | done].
           ++ by constructor.
      * (* Pattern-matching function *)
        apply rtc_transitive
        with (y := cforce uf (X_Apply (V_AttrsetFn m e) e2)).
        -- apply ctx_mstep with (E := cforce uf ∘ λ e1, X_Apply e1 e2);
             [done|].
           destruct uf.
           ++ by eapply IsCtx_Compose; [|apply is_ctx_once].
           ++ apply is_ctx_once. unfold compose. by simpl.
        -- apply rtc_transitive
           with (y := cforce uf (X_Apply (V_AttrsetFn m e) (V_Attrset H0))).
           ++ apply ctx_mstep
              with (E := cforce uf ∘ λ e2, X_Apply (V_AttrsetFn m e) e2).
              ** by apply IHn in Heqo0.
              ** destruct uf.
                 --- by eapply IsCtx_Compose; [|apply is_ctx_once].
                 --- apply is_ctx_once. unfold compose. by simpl.
           ++ apply rtc_transitive with (y := cforce uf (X_LetBinding H e));
                [|done].
              eapply rtc_once.
              eapply E_Ctx.
              ** destruct uf; [by apply is_ctx_once | done].
              ** apply matches_sound in Heqo1. by constructor.
      * (* __functor *)
        apply rtc_transitive with (y := cforce uf (X_Apply (V_Attrset bs) e2)).
        -- apply ctx_mstep with (E := cforce uf ∘ λ e1, X_Apply e1 e2);
             [done|].
           destruct uf.
           ++ by eapply IsCtx_Compose; [|apply is_ctx_once].
           ++ apply is_ctx_once. unfold compose. by simpl.
        -- apply rtc_transitive
           with (y := cforce uf (X_Apply (X_Apply H (V_Attrset bs)) e2));
             [|done].
           eapply rtc_once.
           eapply E_Ctx.
           ++ destruct uf; [by apply is_ctx_once | done].
           ++ by replace bs with (<["__functor" := H]>bs); [|apply insert_id].
    + (* X_Cond *)
      simplify_option_eq.
      apply IHn in Heqo, Heval.
      apply rtc_transitive with (y := cforce uf (X_Cond (V_Bool H0) e2 e3)).
      * apply ctx_mstep with (E := cforce uf ∘ λ e1, X_Cond e1 e2 e3); [done|].
        destruct uf.
        -- by eapply IsCtx_Compose; [|apply is_ctx_once].
        -- apply is_ctx_once. unfold compose. by simpl.
      * destruct H0; eapply rtc_l; try done; eapply E_Ctx; try done;
          by destruct uf; [apply is_ctx_once|].
    + (* X_Incl *)
      apply IHn in Heqo.
      apply rtc_transitive with (y := cforce uf (X_Incl H e2)).
      * apply ctx_mstep with (E := cforce uf ∘ λ e1, X_Incl e1 e2).
        -- done.
        -- destruct uf.
           ++ eapply IsCtx_Compose; [done | by apply is_ctx_once].
           ++ unfold compose. apply is_ctx_once. by simpl.
      * destruct (decide (attrset H)).
        -- destruct H; inv a. simplify_option_eq. apply IHn in Heval.
           eapply rtc_l; [|done].
           eapply E_Ctx.
           ++ destruct uf; [by apply is_ctx_once | done].
           ++ apply E_With.
        -- destruct H;
              try (eapply rtc_l;
                   [ eapply E_Ctx;
                     [ destruct uf; [by apply is_ctx_once | done]
                     | by apply E_WithNoAttrset ]
                   | by apply IHn in Heval ]).
           destruct n0. by exists bs.
    + (* X_Assert *)
      apply IHn in Heqo.
      apply rtc_transitive with (y := cforce uf (X_Assert H e2)).
      * apply ctx_mstep with (E := cforce uf ∘ λ e1, X_Assert e1 e2); [done|].
        destruct uf.
        -- by eapply IsCtx_Compose; [|apply is_ctx_once].
        -- unfold compose. apply is_ctx_once. by simpl.
      * destruct H; try discriminate. destruct p; try discriminate.
        apply IHn in Heval. eapply rtc_l; [|done].
        eapply E_Ctx; [|done].
        by destruct uf; [apply is_ctx_once|].
    + (* X_Binop *)
      apply IHn in Heqo, Heqo0.
      apply rtc_transitive with (y := cforce uf (X_Op op (X_V H) e2)).
      * apply ctx_mstep with (E := cforce uf ∘ λ e1, X_Op op e1 e2).
        -- done.
        -- destruct uf.
           ++ eapply IsCtx_Compose; [done | by apply is_ctx_once].
           ++ unfold compose. apply is_ctx_once. by simpl.
      * apply rtc_transitive with (y := cforce uf (X_Op op (X_V H) (X_V H0))).
        -- apply ctx_mstep with (E := cforce uf ∘ λ e2, X_Op op (X_V H) e2).
           ++ done.
           ++ destruct uf.
              ** eapply IsCtx_Compose; [done | by apply is_ctx_once].
              ** unfold compose. apply is_ctx_once. by simpl.
        -- eapply rtc_l.
           ++ eapply E_Ctx with (E := cforce uf).
              ** destruct uf; [by apply is_ctx_once | done].
              ** apply E_Op. by apply binop_eval_sound.
           ++ by apply IHn.
    + (* X_HasAttr *)
      apply IHn in Heqo.
      apply rtc_transitive with (y := cforce uf (X_HasAttr H x)).
      * apply ctx_mstep with (E := cforce uf ∘ λ e, X_HasAttr e x); [done|].
        destruct uf.
        -- by eapply IsCtx_Compose; [|apply is_ctx_once].
        -- unfold compose. apply is_ctx_once. by simpl.
      * destruct (decide (attrset H)).
        -- case_match; inv a. simplify_option_eq.
           apply rtc_transitive
           with (y := cforce uf (bool_decide (is_Some (x0 !! x)))).
           ++ apply rtc_once. eapply E_Ctx.
              ** destruct uf; [by apply is_ctx_once | done].
              ** destruct (decide (is_Some (x0 !! x))).
                 --- rewrite bool_decide_true by done. by constructor.
                 --- rewrite bool_decide_false by done. constructor.
                     by apply eq_None_not_Some in n0.
           ++ destruct uf; [|done].
              apply rtc_once. simpl.
              replace (V_Bool (bool_decide (is_Some (x0 !! x))))
              with (value_from_strong_value
                (SV_Bool (bool_decide (is_Some (x0 !! x)))))
              by done.
              by eapply E_Ctx with (E := id).
        -- apply rtc_transitive with (y := cforce uf false).
           ++ apply rtc_once. eapply E_Ctx.
              ** destruct uf; [by apply is_ctx_once | done].
              ** by constructor.
           ++ assert (Hforce : cforce true false -->* false).
                { apply rtc_once.
                  simpl.
                  replace (V_Bool false)
                  with (value_from_strong_value (SV_Bool false)) by done.
                  eapply E_Ctx with (E := id); done. }
              destruct H; try (by destruct uf; [apply Hforce | done]).
              exfalso. apply n0. by exists bs.
    + (* X_Force *)
      apply IHn in Heval. clear IHn n.
      destruct uf; try done. simplify_eq/=.
      by apply force_idempotent.
    + (* X_Closed *)
      apply IHn in Heval.
      eapply rtc_l; [|done].
      eapply E_Ctx; [|done].
      * by destruct uf; [apply is_ctx_once|].
    + (* X_Placeholder *)
      apply IHn in Heval. clear IHn n.
      destruct uf; simplify_eq/=; eapply rtc_l; try done.
      -- eapply E_Ctx with (E := X_Force); [by apply is_ctx_once | done].
      -- by eapply E_Ctx with (E := id).
Qed.

Lemma value_stuck v : ¬ ∃ e', X_V v --> e'.
Proof.
  induction v; intros [e' He']; inversion He';
    subst; (inv H0; [inv H1 | inv H2]).
Qed.

Theorem eval_sound_weak e v' n : eval n false e = Some v' → is_nf_of step e v'.
Proof.
  intros Heval.
  pose proof (eval_sound_strong _ _ _ _ Heval).
  split; [done | apply value_stuck].
Qed.
