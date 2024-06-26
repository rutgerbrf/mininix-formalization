Require Import Coq.Strings.String.
From stdpp Require Import gmap.

(* The Nix Expression Language *)

(** Selected operators from Dolsta and Löh, 2008. Newer definitions at
    https://nixos.org/manual/nix/stable/language/operators *)
Variant op : Type :=
  | O_Eq    (* = *)
  | O_Lt    (* < *)
  | O_Plus  (* + *)
  | O_Min   (* - *)
  | O_Div   (* / *)
  | O_Upd.  (* // *)

Hint Constructors op : core.

Variant nonempty A := Ne_Cons (head : A) (tail : list A).
Arguments Ne_Cons {A} _ _.
Hint Constructors nonempty : core.

Inductive expr : Type :=
  | X_V (v : value)                                                   (* v *)
  | X_Id (x : string)                                                 (* x *)
  | X_Attrset (bs : gmap string b_rhs)                          (* { bᵣ* } *)
  | X_LetBinding (bs : gmap string b_rhs) (e : expr)       (* let bᵣ* in e *)
  | X_Select (e : expr) (xs : nonempty string)                     (* e.xs *)
  | X_SelectOr (e : expr) (xs : nonempty string) (or : expr)  (* e.xs or e *)
  | X_Apply (e1 e2 : expr)                                        (* e1 e2 *)
  | X_Cond (e1 e2 e3 : expr)                      (* if e1 then e2 else e3 *)
  | X_Incl (e1 e2 : expr)                                   (* with e1; e2 *)
  | X_Assert (e1 e2 : expr)                               (* assert e1; e2 *)
  | X_Op (op : op) (e1 e2 : expr)                            (* e1 <op> e2 *)
  | X_HasAttr (e1 : expr) (x : string)                            (* e ? x *)
  | X_Force (e : expr)                                          (* force e *)
  | X_Closed (e : expr)                                       (* closed(e) *)
  | X_Placeholder (x : string) (e : expr)               (* placeholderₓ(e) *)
with b_rhs :=
  | B_Rec (e : expr)     (* :=  e *)
  | B_Nonrec (e : expr)  (* :=ᵣ e *)
with matcher :=
  | M_Matcher (ms : gmap string m_rhs) (strict : bool)
with m_rhs :=
  | M_Mandatory
  | M_Optional (e : expr)  (* ? e *)
with value :=
  | V_Bool (p : bool) : value                 (* true | false *)
  | V_Null : value                                    (* null *)
  | V_Int (n : Z) : value                                (* n *)
  | V_Str (s : string) : value                           (* s *)
  | V_Fn (x : string) (e : expr) : value              (* x: e *)
  | V_AttrsetFn (m : matcher) (e : expr) : value  (* { m }: e *)
  | V_Attrset (bs : gmap string expr) : value.      (* { b* } *)

Hint Constructors expr : core.

Instance Maybe_X_Attrset : Maybe X_Attrset := λ e,
  match e with
  | X_Attrset bs => Some bs
  | _ => None
  end.

Instance Maybe_B_Nonrec : Maybe B_Nonrec := λ rhs,
  match rhs with
  | B_Nonrec e => Some e
  | _ => None
  end.

Instance Maybe_B_Rec : Maybe B_Rec := λ rhs,
  match rhs with
  | B_Rec e => Some e
  | _ => None
  end.

Lemma maybe_b_rhs_excl b :
  is_Some (maybe B_Nonrec b) → is_Some (maybe B_Rec b) → False.
Proof. intros [e2 Hnonrec] [e1 Hrec]. simplify_option_eq. Qed.

Lemma no_b_nonrec__b_rec b :
  ¬ is_Some (maybe B_Nonrec b) → is_Some (maybe B_Rec b).
Proof.
  destruct b; try by eauto.
  simplify_eq/=. intros contra. apply is_Some_alt. eauto.
Qed.

Lemma no_b_rec__b_nonrec b :
  ¬ is_Some (maybe B_Rec b) → is_Some (maybe B_Nonrec b).
Proof.
  destruct b; try by eauto.
  simplify_eq/=. intros contra. apply is_Some_alt. eauto.
Qed.

Instance Maybe_V_Attrset : Maybe V_Attrset := λ e,
  match e with
  | V_Attrset bs => Some bs
  | _ => None
  end.

Instance Maybe_V_Bool : Maybe V_Bool := λ e,
  match e with
  | V_Bool p => Some p
  | _ => None
  end.

Global Instance B_Nonrec_inj : Inj (=) (=) B_Nonrec.
Proof. intros [] [] ?; by simplify_eq. Qed.

Definition matcher_keys (m : matcher) : gset string :=
  match m with M_Matcher ms _ => dom ms end.

Definition matcher_map (f : expr → expr) (m : matcher) : matcher :=
  let map_m_rhs := λ rhs,
    match rhs with
    | M_Optional e => M_Optional (f e)
    | _ => rhs
    end in
  match m with
  | M_Matcher ms strict => M_Matcher (map_m_rhs <$> ms) strict
  end.

Local Definition map_delete_all {K V} `{Countable K}
  (ks : gset K) (m : gmap K V) : gmap K V :=
    set_fold (λ k m', map_delete k m') m ks.

Local Definition b_rhs_map (f g : expr → expr) (rhs : b_rhs) : b_rhs :=
  match rhs with
  | B_Rec e => B_Rec (f e)
  | B_Nonrec e => B_Nonrec (g e)
  end.

(* See Dolstra (2006), §4.3.3 and fig. 4.6 (p. 75, PDF: p. 83) *)
Fixpoint subst (subs : gmap string expr) (e : expr) : expr :=
  let msubst subs' := b_rhs_map (subst subs') (subst subs) in
  match e with
  | X_V V_Null | X_V (V_Bool _) | X_V (V_Str _) | X_V (V_Int _) => e
  | X_Id x | X_Placeholder x _ => default e (subs !! x)
  | X_Attrset bs =>
      let subs' := map_delete_all (dom bs) subs in
      X_Attrset (msubst subs' <$> bs)
  | X_V (V_Attrset bs) =>
      X_V (V_Attrset (subst subs <$> bs))
  | X_LetBinding bs e' =>
      let subs' := map_delete_all (dom bs) subs in
      X_LetBinding (msubst subs' <$> bs) (subst subs' e')
  | X_Select e' x => X_Select (subst subs e') x
  | X_SelectOr e' x or => X_SelectOr (subst subs e') x (subst subs or)
  | X_V (V_Fn x e') =>
      let subs' := map_delete x subs in
      X_V (V_Fn x (subst subs' e'))
  | X_V (V_AttrsetFn (M_Matcher ms _ as m) e') =>
      let subs' := map_delete_all (matcher_keys m) subs in
      X_V (V_AttrsetFn (matcher_map (subst subs') m) (subst subs' e'))
  | X_Apply e1 e2 => X_Apply (subst subs e1) (subst subs e2)
  | X_Cond e1 e2 e3 => X_Cond (subst subs e1) (subst subs e2) (subst subs e3)
  | X_Incl e1 e2 => X_Incl (subst subs e1) (subst subs e2)
  | X_Op op e1 e2 => X_Op op (subst subs e1) (subst subs e2)
  | X_HasAttr e x => X_HasAttr (subst subs e) x
  | X_Assert e1 e2 => X_Assert (subst subs e1) (subst subs e2)
  | X_Closed e => X_Closed e
  | X_Force e => X_Force (subst subs e)
  end.

Definition closed (bs : gmap string expr) : gmap string expr :=
  X_Closed <$> bs.

Definition placeholders (bs : gmap string expr) : gmap string expr :=
  map_imap (λ (x : string) (e : expr), Some (X_Placeholder x e)) bs.

Definition nonempty_singleton {A} (a : A): nonempty A := Ne_Cons a nil.

Definition nonempty_cons {A} (a : A) (l : nonempty A) : nonempty A :=
  match l with Ne_Cons head tail => Ne_Cons a (head :: tail) end.

Definition indirect (bs : gmap string b_rhs) : gmap string expr :=
  map_imap (λ (x : string) (rhs : b_rhs),
    Some (X_Select (X_Attrset bs) (nonempty_singleton x))) bs.

Definition rec_subst (bs : gmap string b_rhs) : gmap string expr :=
  let subs := indirect bs
  in (λ b, match b with
           | B_Rec e => subst (closed subs) e
           | B_Nonrec e => e
           end) <$> bs.

Inductive strong_value : Type :=
  | SV_Bool (b : bool)
  | SV_Null
  | SV_Int (n : Z)
  | SV_Str (s : string)
  | SV_Fn (x : string) (e : expr)
  | SV_AttrsetFn (m : matcher) (e : expr)
  | SV_Attrset (bs : gmap string strong_value).

Fixpoint value_from_strong_value (sv : strong_value) : value :=
  match sv with
  | SV_Null => V_Null
  | SV_Bool b => V_Bool b
  | SV_Int n => V_Int n
  | SV_Str s => V_Str s
  | SV_Fn x e => V_Fn x e
  | SV_AttrsetFn m e => V_AttrsetFn m e
  | SV_Attrset bs => V_Attrset (X_V ∘ value_from_strong_value <$> bs)
  end.

Global Instance X_V_inj : Inj (=) (=) X_V.
Proof. intros [] [] ?; by simplify_eq. Qed.

Definition expr_from_strong_value : strong_value → expr :=
  X_V ∘ value_from_strong_value.

(* Based on the fin_maps test from stdpp *)
Fixpoint sv_size (sv : strong_value) : nat :=
  match sv with
  | SV_Null | SV_Bool _ | SV_Int _ | SV_Str _
  | SV_Fn _ _ | SV_AttrsetFn _ _ => 1
  | SV_Attrset bs => S (map_fold (λ _ sv', plus (sv_size sv')) 0 bs)
  end.

(* Based on the fin_maps test from stdpp *)
Lemma strong_value_ind' :
  ∀ P : strong_value → Prop,
    P SV_Null →
    (∀ b : bool, P (SV_Bool b)) →
    (∀ n : Z, P (SV_Int n)) →
    (∀ s : string, P (SV_Str s)) →
    (∀ (x : string) (e : expr), P (SV_Fn x e)) →
    (∀ (m : matcher) (e : expr), P (SV_AttrsetFn m e)) →
    (∀ bs : gmap string strong_value,
      map_Forall (λ i, P) bs → P (SV_Attrset bs)) →
    ∀ s : strong_value, P s.
Proof.
  intros P PNull PBool PInt PStr PFn PAttrsetFn PAttrset sv.
  remember (sv_size sv) as n eqn:Hn. revert sv Hn.
  induction (lt_wf n) as [n _ IH]; intros [| | | | | | bs] ->; simpl in *; try done.
  apply PAttrset. revert bs IH.
  apply (map_fold_ind (λ r bs, (∀ n', n' < S r → _) → map_Forall (λ _, P) bs)).
  - intros IH. apply map_Forall_empty.
  - intros k sv bs r ? IHbs IHsv. apply map_Forall_insert; [done|]. split.
    + eapply IHsv; [|done]; lia.
    + eapply IHbs. intros; eapply IHsv; [|done]; lia.
Qed.

Coercion X_Id : string >-> expr.
Coercion V_Int : Z >-> value.
(* Leaving this out for now: would conflict with X_Id and
   therefore cause ambiguity *)
(* Coercion X_StrVal : string >-> expr. *)
Coercion V_Bool : bool >-> value.
Coercion X_V : value >-> expr.
Coercion value_from_strong_value : strong_value >-> value.
