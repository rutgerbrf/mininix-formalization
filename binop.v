Require Import Coq.NArith.BinNat.
Require Import Coq.Strings.Ascii.
Require Import Coq.Strings.String.
From stdpp Require Import fin_sets gmap option.
From mininix Require Import expr maptools shared.

Open Scope string_scope.
Open Scope N_scope.
Open Scope Z_scope.
Open Scope nat_scope.

Definition right_union {A} (bs1 bs2 : gmap string A) : gmap string A :=
  bs2 ∪ bs1.

Variant binop_r : op → value → value → value → Prop :=
  | Bo_PlusInt n1 n2 : binop_r O_Plus (V_Int n1) (V_Int n2) (V_Int (n1 + n2))
  | Bo_PlusStr s1 s2 : binop_r O_Plus (V_Str s1) (V_Str s2) (V_Str (s1 ++ s2))
  | Bo_MinInt n1 n2 : binop_r O_Min (V_Int n1) (V_Int n2) (V_Int (n1 - n2))
  | Bo_UpdAttrset bs1 bs2 :
      binop_r O_Upd (V_Attrset bs1) (V_Attrset bs2)
        (V_Attrset (right_union bs1 bs2))
  | Bo_Eq v1 v2 : binop_r O_Eq v1 v2 (expr_eq v1 v2)
  | Bo_DivInt (n1 n2 : Z) : n2 ≠ 0%Z → binop_r O_Div n1 n2 (n1 / n2)%Z
  | Bo_LtInt (n1 n2 : Z) : binop_r O_Lt n1 n2 (bool_decide (n1 < n2)%Z)
  | Bo_LtStr s1 s2 : binop_r O_Lt (V_Str s1) (V_Str s2) (string_lt s1 s2).

Notation "u1 '⟦' op '⟧' u2 '-⊚->' v" := (binop_r op u1 u2 v) (at level 55).

Definition binop_eval (op : op) (v1 v2 : value) : option value :=
  match op with
  | O_Plus =>
      match v1, v2 with
      | V_Int n1, V_Int n2 => Some (V_Int (n1 + n2))
      | V_Str s1, V_Str s2 => Some (V_Str (s1 ++ s2))
      | _, _ => None
      end
  | O_Min =>
      match v1, v2 with
      | V_Int n1, V_Int n2 => Some (V_Int (n1 - n2))
      | _, _ => None
      end
  | O_Upd =>
      match v1, v2 with
      | V_Attrset bs1, V_Attrset bs2 =>
          Some (V_Attrset (right_union bs1 bs2))
      | _, _ => None
      end
  | O_Eq => Some (V_Bool (expr_eq (X_V v1) (X_V v2)))
  | O_Div =>
      match v1, v2 with
      | V_Int n1, V_Int n2 =>
          if decide (n2 = 0)%Z
          then None
          else Some (V_Int (n1 / n2)%Z)
      | _, _ => None
      end
  | O_Lt =>
      match v1, v2 with
      | V_Int n1, V_Int n2 => Some (V_Bool (bool_decide (n1 < n2)%Z))
      | V_Str s1, V_Str s2 => Some (V_Bool (string_lt s1 s2))
      | _, _ => None
      end
  end.

Theorem binop_eval_sound op u1 u2 v :
  binop_eval op u1 u2 = Some v → binop_r op u1 u2 v.
Proof.
  intros Heval.
  destruct op, u1, u2; try discriminate; simplify_eq/=; try constructor.
  destruct (decide (n0 = 0)%Z); try discriminate.
  simplify_eq/=. by constructor.
Qed.

Theorem binop_eval_complete op u1 u2 v :
  binop_r op u1 u2 v → binop_eval op u1 u2 = Some v.
Proof.
  intros Heval. inv Heval; try done.
  unfold binop_eval. by apply decide_False.
Qed.

Theorem binop_deterministic op u1 u2 v1 v2 :
  u1 ⟦op⟧ u2 -⊚-> v1 → u1 ⟦op⟧ u2 -⊚-> v2 → v1 = v2.
Proof.
  intros Heval1 Heval2.
  apply binop_eval_complete in Heval1, Heval2.
  congruence.
Qed.
