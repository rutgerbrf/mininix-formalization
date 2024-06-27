Require Import Coq.Strings.String.
From stdpp Require Import gmap option tactics.
From mininix Require Import binop expr maptools matching relations sem.

Lemma ctx_item_inj E uf_ext uf_int :
  is_ctx_item uf_ext uf_int E →
  Inj (=) (=) E.
Proof.
  intros Hctx.
  destruct Hctx; intros e1' e2' Hinj; try congruence.
  injection Hinj as Hinj.
  by apply map_insert_rev_1_L in Hinj.
Qed.

Global Instance id_inj {A} : Inj (=) (=) (@id A).
Proof. by unfold Inj. Qed.

Lemma ctx_inj E uf_ext uf_int :
  is_ctx uf_ext uf_int E →
  Inj (=) (=) E.
Proof.
  intros Hctx.
  induction Hctx.
  - apply id_inj.
  - apply ctx_item_inj in H.
    by apply compose_inj with (=).
Qed.

Lemma base_step_deterministic : deterministic base_step.
Proof.
  unfold deterministic.
  intros e0 e1 e2 H1 H2.
  inv H1; inv H2; try done.
  - destruct ys, ys0. by simplify_eq/=.
  - destruct ys. by simplify_eq/=.
  - destruct ys. by simplify_eq/=.
  - apply map_insert_inv in H0. by destruct H0.
  - destruct ys. by simplify_eq/=.
  - destruct ys. by simplify_eq/=.
  - destruct ys, ys0. by simplify_eq/=.
  - exfalso. apply H3. by exists bs.
  - exfalso. apply H. by exists bs.
  - f_equal. by eapply matches_deterministic.
  - apply map_insert_inv in H0 as [H01 H02].
    by simplify_eq/=.
  - f_equal. by eapply binop_deterministic.
  - rewrite H4 in H. by apply is_Some_None in H.
  - exfalso. apply H4. by exists bs.
  - rewrite H in H4. by apply is_Some_None in H4.
  - exfalso. apply H. by exists bs.
Qed.

Reserved Notation "e '-/' uf '/->' e'" (right associativity, at level 55).

Inductive fstep : bool → expr → expr → Prop :=
  | F_Ctx e1 e2 E uf_ext uf_int :
      is_ctx uf_ext uf_int E →
      e1 -->base e2 →
      E e1 -/uf_ext/-> E e2
where "e -/ uf /-> e'" := (fstep uf e e').

Hint Constructors fstep : core.

Lemma ufstep e e' : e -/false/-> e' ↔ e --> e'.
Proof. split; intros; inv H; by econstructor. Qed.

Lemma fstep_strongly_confluent_aux x uf y1 y2 :
  x -/uf/-> y1 →
  x -/uf/-> y2 →
  y1 = y2 ∨ ∃ z, y1 -/uf/-> z ∧ y2 -/uf/-> z.
Proof.
  intros Hstep1 Hstep2.
  inv Hstep1 as [b11 b12 E1 uf_int uf_int1 Hctx1 Hbase1].
  inv Hstep2 as [b21 b22 E2 uf_int uf_int2 Hctx2 Hbase2].
  revert b11 b12 b21 b22 E2 Hbase1 Hbase2 Hctx2 H0.
  induction Hctx1 as [|E1 E0];
    intros b11 b12 b21 b22 E2 Hbase1 Hbase2 Hctx2 H2; inv Hctx2.
  - (* L: id, R: id *) left. by eapply base_step_deterministic.
  - (* L: id, R: ∘ *) simplify_eq/=.
    inv H; try inv select (_ -->base b12);
      (inv select (is_ctx _ _ _);
         [inv select (b21 -->base b22)
         |inv select (is_ctx_item _ _ _)]).
    simplify_option_eq.
    destruct sv; try discriminate.
    exfalso. clear uf. simplify_option_eq.
    apply fmap_insert_lookup in H1. simplify_option_eq.
    revert bs0 x H H1 Heqo.
    induction H2; intros bs0 x H' H1 Heqo; [inv Hbase2|].
    simplify_option_eq.
    inv H. destruct H'; try discriminate.
    inv H1. apply fmap_insert_lookup in H0. simplify_option_eq.
    by eapply IHis_ctx.
  - (* L: ∘, R: id *) simplify_eq/=.
    inv H; try inv select (_ -->base b22);
      (inv select (is_ctx _ _ _);
         [inv select (b11 -->base b12)
         |inv select (is_ctx_item _ _ _)]).
    clear IHHctx1.
    simplify_option_eq.
    destruct sv; try discriminate.
    exfalso. simplify_option_eq.
    apply fmap_insert_lookup in H0. simplify_option_eq.
    revert bs0 x H H0 Heqo.
    induction H1; intros bs0 x H' H0 Heqo; [inv Hbase1|].
    simplify_option_eq.
    inv H. destruct H'; try discriminate.
    inv H0. apply fmap_insert_lookup in H2. simplify_option_eq.
    by eapply IHis_ctx.
  - (* L: ∘, R: ∘ *)
    simplify_option_eq.
    inv H; inv H0.
    + destruct (IHHctx1 _ _ _ _ E4 Hbase1 Hbase2 H1 H2)
        as [IH | [z [IHz1 IHz2]]].
      * left. congruence.
      * right. exists (X_Select z xs).
        split; [inv IHz1 | inv IHz2];
           eapply F_Ctx with (E := (λ e, X_Select e xs) ∘ E); try done;
           by eapply IsCtx_Compose.
    + destruct (IHHctx1 _ _ _ _ E4 Hbase1 Hbase2 H1 H2)
        as [IH | [z [IHz1 IHz2]]].
      * left. congruence.
      * right. exists (X_SelectOr z xs e2).
        split; [inv IHz1 | inv IHz2];
           eapply F_Ctx with (E := (λ e1, X_SelectOr e1 xs e2) ∘ E); try done;
           by eapply IsCtx_Compose.
    + destruct (IHHctx1 _ _ _ _ E4 Hbase1 Hbase2 H1 H2)
        as [IH | [z [IHz1 IHz2]]].
      * left. congruence.
      * right. exists (X_Incl z e2).
        split; [inv IHz1 | inv IHz2];
           eapply F_Ctx with (E := (λ e1, X_Incl e1 e2) ∘ E); try done;
           by eapply IsCtx_Compose.
    + destruct (IHHctx1 _ _ _ _ E4 Hbase1 Hbase2 H1 H2)
        as [IH | [z [IHz1 IHz2]]].
      * left. congruence.
      * right. exists (X_Apply z e2).
        split; [inv IHz1 | inv IHz2];
           eapply F_Ctx with (E := (λ e1, X_Apply e1 e2) ∘ E); try done;
           by eapply IsCtx_Compose.
    + inv Hctx1; simplify_option_eq.
      * inv Hbase1.
      * inv H.
    + inv H1; simplify_option_eq.
      * inv Hbase2.
      * inv H.
    + destruct (IHHctx1 _ _ _ _ E4 Hbase1 Hbase2 H1 H0)
        as [IH | [z [IHz1 IHz2]]].
      * left. congruence.
      * right. exists (X_Apply (V_AttrsetFn m e1) z).
        split; [inv IHz1 | inv IHz2];
           eapply F_Ctx with (E := (λ e2, X_Apply (V_AttrsetFn m e1) e2) ∘ E);
             try done;
           by eapply IsCtx_Compose.
    + destruct (IHHctx1 _ _ _ _ E4 Hbase1 Hbase2 H1 H2)
        as [IH | [z [IHz1 IHz2]]].
      * left. congruence.
      * right. exists (X_Cond z e2 e3).
        split; [inv IHz1 | inv IHz2];
           eapply F_Ctx with (E := (λ e1, X_Cond e1 e2 e3) ∘ E); try done;
           by eapply IsCtx_Compose.
    + destruct (IHHctx1 _ _ _ _ E4 Hbase1 Hbase2 H1 H2)
        as [IH | [z [IHz1 IHz2]]].
      * left. congruence.
      * right. exists (X_Assert z e2).
        split; [inv IHz1 | inv IHz2];
           eapply F_Ctx with (E := (λ e1, X_Assert e1 e2) ∘ E); try done;
           by eapply IsCtx_Compose.
    + destruct (IHHctx1 _ _ _ _ E4 Hbase1 Hbase2 H1 H)
        as [IH | [z [IHz1 IHz2]]].
      * left. congruence.
      * right. exists (X_Op op z e2).
        split; [inv IHz1 | inv IHz2];
           eapply F_Ctx with (E := (λ e1, X_Op op e1 e2) ∘ E); try done;
           by eapply IsCtx_Compose.
    + inv Hctx1; simplify_option_eq.
      * inv Hbase1.
      * inv H0.
    + inv H1; simplify_option_eq.
      * inv Hbase2.
      * inv H0.
    + destruct (IHHctx1 _ _ _ _ E4 Hbase1 Hbase2 H1 H0)
        as [IH | [z [IHz1 IHz2]]].
      * left. congruence.
      * right. exists (X_Op op v1 z).
        split; [inv IHz1 | inv IHz2];
           eapply F_Ctx with (E := (λ e2, X_Op op v1 e2) ∘ E); try done;
           by eapply IsCtx_Compose.
    + destruct (IHHctx1 _ _ _ _ E4 Hbase1 Hbase2 H1 H2)
        as [IH | [z [IHz1 IHz2]]].
      * left. congruence.
      * right. exists (X_HasAttr z x).
        split; [inv IHz1 | inv IHz2];
           eapply F_Ctx with (E := (λ e, X_HasAttr e x) ∘ E); try done;
           by eapply IsCtx_Compose.
    + destruct (IHHctx1 _ _ _ _ E4 Hbase1 Hbase2 H1 H2)
        as [IH | [z [IHz1 IHz2]]].
      * left. congruence.
      * right. exists (X_Force z).
        split.
        -- inv IHz1.
           (* apply is_ctx_uf_false_impl_true in H0 as []. *)
           eapply F_Ctx with (E := X_Force ∘ E); try done;
           by eapply IsCtx_Compose.
        -- inv IHz2.
           eapply F_Ctx with (E := X_Force ∘ E); try done;
           by eapply IsCtx_Compose.
    + destruct (decide (x0 = x)).
      * simplify_option_eq.
        apply map_insert_rev_L in H2 as [H21 H22].
        destruct (IHHctx1 _ _ _ _ E4 Hbase1 Hbase2 H1 H21)
          as [IH | [z [IHz1 IHz2]]].
        -- left. rewrite IH. do 2 f_equal.
           by apply map_insert_L.
        -- right. exists (V_Attrset (<[x := z]>bs)).
           split.
           ++ inv IHz1.
              eapply F_Ctx
              with (E := (λ e, X_V $ V_Attrset (<[x := e]>bs)) ∘ E); try done.
              by eapply IsCtx_Compose.
           ++ inv IHz2.
              rewrite (map_insert_L _ _ _ _ _ (eq_refl (E e1)) H22).
              eapply F_Ctx
              with (E := (λ e, X_V $ V_Attrset (<[x := e]>bs)) ∘ E); try done.
              by eapply IsCtx_Compose.
      * simplify_option_eq.
        right. exists (V_Attrset (<[x := E0 b12]>(<[x0 := E4 b22]>bs))).
        split.
        -- apply map_insert_ne_inv in H2 as H3; try done.
           destruct H3.
           replace bs with (<[x0 := E4 b21]>bs) at 1; try by rewrite insert_id.
           setoid_rewrite insert_commute; try by congruence.
           eapply F_Ctx
           with (E := (λ e, X_V $ V_Attrset
             (<[x0 := e]>(<[x := E0 b12]> bs))) ∘ E4).
           ++ by eapply IsCtx_Compose.
           ++ done.
        -- apply map_insert_ne_inv in H2 as H3; try done.
           destruct H3 as [H31 [H32 H33]].
           replace bs0 with (<[x := E0 b11]>bs0) at 1;
            try by rewrite insert_id.
           rewrite insert_commute; try by congruence.
           replace (<[x:=E0 b11]> (<[x0:=E4 b22]> bs0))
           with (<[x:=E0 b11]> (<[x0:=E4 b22]> bs)).
           2: {
             rewrite <-insert_delete_insert.
             setoid_rewrite <-insert_delete_insert at 2.
             rewrite delete_insert_ne by congruence.
             rewrite delete_commute. rewrite <-H33.
             rewrite insert_delete_insert.
             rewrite <-delete_insert_ne by congruence.
             by rewrite insert_delete_insert.
           }
           eapply F_Ctx with (E := (λ e, X_V $ V_Attrset
             (<[x := e]>(<[x0 := E4 b22]>bs))) ∘ E0).
           ++ by eapply IsCtx_Compose.
           ++ done.
Qed.

Lemma step_strongly_confluent_aux x y1 y2 :
  x --> y1 →
  x --> y2 →
  y1 = y2 ∨ ∃ z, y1 --> z ∧ y2 --> z.
Proof.
  intros Hstep1 Hstep2.
  apply ufstep in Hstep1, Hstep2.
  destruct (fstep_strongly_confluent_aux _ _ _ _ Hstep1 Hstep2) as [|[?[]]].
  - by left.
  - right. exists x0. split; by apply ufstep.
Qed.

Theorem step_strongly_confluent : strongly_confluent step.
Proof.
  intros x y1 y2 Hy1 Hy2.
  destruct (step_strongly_confluent_aux x y1 y2 Hy1 Hy2) as [|[z [Hz1 Hz2]]].
  - exists y1. by subst.
  - exists z. split.
    + by apply rtc_once.
    + by apply rc_once.
Qed.

Lemma step_semi_confluent : semi_confluent step.
Proof. apply strong__semi_confluence. apply step_strongly_confluent. Qed.

Lemma step_cr : cr step.
Proof. apply semi_confluence__cr. apply step_semi_confluent. Qed.

Theorem step_confluent : confluent step.
Proof. apply confluent_alt. apply step_cr. Qed.
