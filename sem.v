Require Import Coq.Strings.String.
From stdpp Require Import gmap.
From mininix Require Import binop expr matching relations.

Definition attrset := is_Some ∘ maybe V_Attrset.

Reserved Infix "-->base" (right associativity, at level 55).

Inductive base_step : expr → expr → Prop :=
  | E_Force (sv : strong_value) :
      X_Force sv -->base sv
  | E_Closed e :
      X_Closed e -->base e
  | E_Placeholder x e :
      X_Placeholder x e -->base e
  | E_MSelect bs x ys :
      X_Select (V_Attrset bs) (nonempty_cons x ys) -->base
      X_Select (X_Select (V_Attrset bs) (nonempty_singleton x)) ys
  | E_Select e bs x :
      X_Select (V_Attrset (<[x := e]>bs)) (nonempty_singleton x) -->base e
  | E_SelectOr bs x e :
      X_SelectOr (V_Attrset bs) (nonempty_singleton x) e -->base
        X_Cond (X_HasAttr (V_Attrset bs) x)
               (* if true *)
               (X_Select (V_Attrset bs) (nonempty_singleton x))
               (* if false *)
               e
  | E_MSelectOr bs x ys e :
      X_SelectOr (V_Attrset bs) (nonempty_cons x ys) e -->base
        X_Cond (X_HasAttr (V_Attrset bs) x)
               (* if true *)
               (X_SelectOr
                 (X_Select (V_Attrset bs) (nonempty_singleton x))
                 ys e)
               (* if false *)
               e
  | E_Rec bs :
      X_Attrset bs -->base V_Attrset (rec_subst bs)
  | E_Let e bs :
      X_LetBinding bs e -->base subst (closed (rec_subst bs)) e
  | E_With e bs :
      X_Incl (V_Attrset bs) e -->base subst (placeholders bs) e
  | E_WithNoAttrset v1 e2 :
      ¬ attrset v1 →
      X_Incl v1 e2 -->base e2
  | E_ApplySimple x e1 e2 :
      X_Apply (V_Fn x e1) e2 -->base subst {[x := X_Closed e2]} e1
  | E_ApplyAttrset m e bs bs' :
      bs ~ m ~> bs' →
      X_Apply (V_AttrsetFn m e) (V_Attrset bs) -->base
      X_LetBinding bs' e
  | E_ApplyFunctor e1 e2 bs :
      X_Apply (V_Attrset (<["__functor" := e2]>bs)) e1 -->base
      X_Apply (X_Apply e2 (V_Attrset (<["__functor" := e2]>bs))) e1
  | E_IfTrue e2 e3 :
      X_Cond true e2 e3 -->base e2
  | E_IfFalse e2 e3 :
      X_Cond false e2 e3 -->base e3
  | E_Op op v1 v2 u :
      v1 ⟦op⟧ v2 -⊚-> u →
      X_Op op v1 v2 -->base u
  | E_OpHasAttrTrue bs x :
      is_Some (bs !! x) →
      X_HasAttr (V_Attrset bs) x -->base true
  | E_OpHasAttrFalse bs x :
      bs !! x = None →
      X_HasAttr (V_Attrset bs) x -->base false
  | E_OpHasAttrNoAttrset v x :
      ¬ attrset v →
      X_HasAttr v x -->base false
  | E_Assert e2 :
      X_Assert true e2 -->base e2
where "e -->base e'" := (base_step e e').

Notation "e '-->base*' e'" := (rtc base_step e e')
                              (right associativity, at level 55).

Hint Constructors base_step : core.

Variant is_ctx_item : bool → bool → (expr → expr) → Prop :=
  | IsCtxItem_Select uf_ext xs :
      is_ctx_item uf_ext false (λ e1, X_Select e1 xs)
  | IsCtxItem_SelectOr uf_ext xs e2 :
      is_ctx_item uf_ext false (λ e1, X_SelectOr e1 xs e2)
  | IsCtxItem_Incl uf_ext e2 :
      is_ctx_item uf_ext false (λ e1, X_Incl e1 e2)
  | IsCtxItem_ApplyL uf_ext e2 :
      is_ctx_item uf_ext false (λ e1, X_Apply e1 e2)
  | IsCtxItem_ApplyAttrsetR uf_ext m e1 :
      is_ctx_item uf_ext false (λ e2, X_Apply (V_AttrsetFn m e1) e2)
  | IsCtxItem_CondL uf_ext e2 e3 :
      is_ctx_item uf_ext false (λ e1, X_Cond e1 e2 e3)
  | IsCtxItem_AssertL uf_ext e2 :
      is_ctx_item uf_ext false (λ e1, X_Assert e1 e2)
  | IsCtxItem_OpL uf_ext op e2 :
      is_ctx_item uf_ext false (λ e1, X_Op op e1 e2)
  | IsCtxItem_OpR uf_ext op v1 :
      is_ctx_item uf_ext false (λ e2, X_Op op (X_V v1) e2)
  | IsCtxItem_OpHasAttrL uf_ext x :
      is_ctx_item uf_ext false (λ e, X_HasAttr e x)
  | IsCtxItem_Force uf_ext :
      is_ctx_item uf_ext true (λ e, X_Force e)
  | IsCtxItem_ForceAttrset bs x :
      is_ctx_item true true (λ e, X_V (V_Attrset (<[x := e]>bs))).

Hint Constructors is_ctx_item : core.

Inductive is_ctx : bool → bool → (expr → expr) → Prop :=
  | IsCtx_Id uf : is_ctx uf uf id
  | IsCtx_Compose E1 E2 uf_int uf_aux uf_ext :
      is_ctx_item uf_ext uf_aux E1 →
      is_ctx uf_aux uf_int E2 →
      is_ctx uf_ext uf_int (E1 ∘ E2).

Hint Constructors is_ctx : core.

(* /--> This is required because the standard library definition of "-->"
   |    (in Coq.Classes.Morphisms, for `respectful`) defines that this operator
   |    uses right associativity. Our definition must match exactly, as Coq
   |    will give an error otherwise.
   \-------------------------------------\
                     |                   | *)
Reserved Infix "-->" (right associativity, at level 55).

Variant step : expr → expr → Prop :=
  E_Ctx e1 e2 E uf_int :
    is_ctx false uf_int E →
    e1 -->base e2 →
    E e1 --> E e2
where "e --> e'" := (step e e').

Hint Constructors step : core.

Notation "e '-->*' e'" := (rtc step e e') (right associativity, at level 55).

(** Theories for contexts *)

Lemma is_ctx_once uf_ext uf_int E :
  is_ctx_item uf_ext uf_int E → is_ctx uf_ext uf_int E.
Proof. intros. eapply IsCtx_Compose; [done | constructor]. Qed.

Lemma is_ctx_item_ext_imp E uf_int :
  is_ctx_item false uf_int E → is_ctx_item true uf_int E.
Proof. intros H. inv H; constructor. Qed.

Lemma is_ctx_ext_imp E1 E2 uf_aux uf_int :
  is_ctx_item false uf_aux E1 →
  is_ctx uf_aux uf_int E2 →
  is_ctx true uf_int (E1 ∘ E2).
Proof.
  intros H1 H2.
  revert E1 H1.
  induction H2; intros.
  - inv H1; eapply IsCtx_Compose; constructor.
  - eapply IsCtx_Compose.
    + by apply is_ctx_item_ext_imp in H1.
    + by eapply IsCtx_Compose.
Qed.

Lemma is_ctx_uf_false_impl_true E uf_int :
  is_ctx false uf_int E →
  is_ctx true uf_int E ∨ E = id.
Proof.
  intros Hctx. inv Hctx.
  - by right.
  - left. eapply is_ctx_ext_imp; [apply H | apply H0].
Qed.
