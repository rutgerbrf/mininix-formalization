Require Import Coq.NArith.BinNat.
Require Import Coq.Strings.Ascii.
Require Import Coq.Strings.String.
From stdpp Require Import fin_sets gmap option.
From mininix Require Import expr maptools.

Open Scope string_scope.
Open Scope N_scope.
Open Scope Z_scope.
Open Scope nat_scope.

Definition nonrecs : gmap string b_rhs → gmap string expr :=
  omap (λ b, match b with B_Nonrec e => Some e | _ => None end).

Lemma nonrecs_nonrec_fmap bs : nonrecs (B_Nonrec <$> bs) = bs.
Proof.
  induction bs using map_ind.
  - done.
  - unfold nonrecs.
    rewrite fmap_insert.
    rewrite omap_insert_Some with (y := x); try done.
    by f_equal.
Qed.

Lemma rec_subst_nonrec_fmap bs : rec_subst (B_Nonrec <$> bs) = bs.
Proof.
  unfold rec_subst.
  rewrite <-map_fmap_compose.
  unfold compose.
  by rewrite map_fmap_id.
Qed.

Definition ascii_ltb (c1 c2 : ascii) : bool :=
  bool_decide (N_of_ascii c1 < N_of_ascii c2)%N.

Fixpoint string_lt (s1 s2 : string) : bool :=
  match s1, s2 with
  | _, EmptyString => false
  | EmptyString, String _ _ => true
  | String c1 s1', String c2 s2' => ascii_ltb c1 c2 || string_lt s1' s2'
  end.

Fixpoint expr_eq (e1 e2 : expr) : bool :=
  match e1, e2 with
  | V_Null, V_Null => false
  | V_Bool b1, V_Bool b2 => bool_decide (b1 = b2)
  | V_Int n1, V_Int n2 => bool_decide (n1 = n2)
  | V_Str s1, V_Str s2 => bool_decide (s1 = s2)
  | V_Attrset bs1, V_Attrset bs2 => bool_decide (dom bs1 = dom bs2) &&
      map_fold (λ x e1' acc, match bs2 !! x with
                             | None => false
                             | Some e2' => acc && expr_eq e1' e2'
                             end) true bs1
  | _, _ => false
  end.

Definition prelude : gmap string expr :=
  {[ "true"  := X_V true;
     "false" := X_V false;
     "null"  := X_V V_Null;
     "builtins" := X_Attrset
       {[ "true"  := B_Nonrec true;
          "false" := B_Nonrec false;
          "null"  := B_Nonrec V_Null
       ]}
  ]}.
