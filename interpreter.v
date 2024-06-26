Require Import Coq.Strings.String.
From stdpp Require Import fin_maps.
From mininix Require Import binop expr maptools matching.

Open Scope string_scope.

Definition eval1 (go : bool → expr → option value)
  (uf : bool) (d : expr) : option value :=
    match d with
    | X_Id _ => None
    | X_Force e => go true e
    | X_Closed e => go uf e
    | X_Placeholder x e => go uf e
    | X_V (V_Attrset bs) =>
        if uf
        then vs' ← map_mapM (go true) bs;
             Some (V_Attrset (X_V <$> vs'))
        else Some (V_Attrset bs)
    | X_V v => Some v
    | X_Attrset bs => go uf (V_Attrset (rec_subst bs))
    | X_LetBinding bs e =>
      let e' := subst (closed (rec_subst bs)) e
      in go uf e'
    | X_Select e (Ne_Cons x ys) =>
      v' ← go false e;
      bs ← maybe V_Attrset v';
      e'' ← bs !! x;
      match ys with
      | [] => go uf e''
      | y :: ys => go uf (X_Select e'' (Ne_Cons y ys))
      end
    | X_SelectOr e (Ne_Cons x ys) or =>
      v' ← go false e;
      bs ← maybe V_Attrset v';
      match bs !! x with
      | Some e'' =>
          match ys with
          | [] => go uf e''
          | y :: ys => go uf (X_SelectOr e'' (Ne_Cons y ys) or)
          end
      | None => go uf or
      end
    | X_Apply e1 e2 =>
      v1' ← go false e1;
      match v1' with
      | V_Fn x e =>
          let e' := subst {[x := X_Closed e2]} e
          in go uf e'
      | V_AttrsetFn m e =>
          v2' ← go false e2;
          bs ← maybe V_Attrset v2';
          bs' ← matches m bs;
          go uf (X_LetBinding bs' e)
      | V_Attrset bs =>
          f ← bs !! "__functor";
          go uf (X_Apply (X_Apply f (V_Attrset bs)) e2)
      | _ => None
      end
    | X_Cond e1 e2 e3 =>
      v1' ← go false e1;
      b ← maybe V_Bool v1';
      go uf (if b : bool then e2 else e3)
    | X_Incl e1 e2 =>
      v1' ← go false e1;
      match v1' with
      | V_Attrset bs => go uf (subst (placeholders bs) e2)
      | _ => go uf e2
      end
    | X_Op op e1 e2 =>
      e1' ← go false e1;
      e2' ← go false e2;
      v' ← binop_eval op e1' e2';
      go uf (X_V v')
    | X_HasAttr e x =>
      v' ← go false e;
      Some $ V_Bool $
        match v' with
        | V_Attrset bs =>
            bool_decide (is_Some (bs !! x))
        | _ => false
        end
    | X_Assert e1 e2 =>
      v1' ← go false e1;
      match v1' with
      | V_Bool true => go uf e2
      | _ => None
      end
    end.

Fixpoint eval (n : nat) (uf : bool) (e : expr) : option value :=
  match n with
  | O => None
  | S n => eval1 (eval n) uf e
  end.

(* Don't automatically 'simplify' eval: this can lead to very complicated
   assumptions and goals. Instead, we define our own lemma which can be used
   to unfold eval once. This allows us to write proofs in a much more
   controlled manner, and we can still leverage tactics like simplify_option_eq
   without everything blowing up uncontrollably *)
Global Opaque eval.
Lemma eval_S n : eval (S n) = eval1 (eval n).
Proof. done. Qed.
