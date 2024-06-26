Require Import Coq.Strings.String.
From stdpp Require Import gmap.
From mininix Require Import
  expr relations sem interpreter complete sound shared.

Theorem correct e v' : (∃ n, eval n false e = Some v') ↔ e -->* v'.
Proof.
  split.
  - intros [n Heval]. by apply (eval_sound_strong n false).
  - intros Heval. by apply eval_complete.
Qed.

(* Top-level program reduction/evaluation:
     we make the prelude available here. *)

Definition with_prelude (e : expr) : expr :=
  subst (closed prelude) e.

Definition tl_reds (e e' : expr) :=
  with_prelude e -->* e'.

Definition tl_eval (n : nat) (e : expr) : option value :=
  eval n false (subst (closed prelude) e).

Definition tl_evals e e' := ∃ n, tl_eval n e = Some e'.

(* Macros *)

Definition μ_neq e1 e2 := X_Cond (X_Op O_Eq e1 e2) false true.
Definition μ_or e1 e2 := X_Cond e1 true e2.
Definition μ_and e1 e2 := X_Cond e1 e2 false.
Definition μ_impl e1 e2 := X_Cond e1 e2 true.
Definition μ_neg e := X_Cond e false true.

Definition μ_le n m := μ_or (X_Op O_Eq n m) (X_Op O_Lt n m).
Definition μ_gt n m := X_Op O_Lt m n.
Definition μ_ge n m := μ_or (X_Op O_Eq n m) (μ_gt n m).

(* Tests/examples *)

Definition ex1 := X_LetBinding {[ "a" := B_Rec 1%Z ]} "a".

(* [let a = 1; in a] gives 1 *)
Theorem ex1_step : tl_reds ex1 1%Z.
Proof.
  unfold ex1.
  eapply rtc_l.
  - by eapply E_Ctx with (E := id).
  - simplify_option_eq.
    eapply rtc_once.
    by eapply E_Ctx with (E := id).
Qed.

Example ex1_eval : tl_evals ex1 (V_Int 1).
Proof. by exists 3. Qed.

(* Definition ex2 := <{ let a = 1 in with { a = 2 }; a }>. *)
Definition ex2 := X_LetBinding {[ "a" := B_Rec 1%Z ]}
  (X_Incl (V_Attrset {[ "a" := X_V 2%Z ]}) "a").

(* [let a = 1; in with { a = 2; }; a] gives 1 *)
Theorem ex2_step : tl_reds ex2 1%Z.
Proof.
  unfold ex2.
  eapply rtc_l.
  - by eapply E_Ctx with (E := id).
  - simplify_option_eq.
    eapply rtc_l.
    + by eapply E_Ctx with (E := id).
    + simpl. eapply rtc_once.
      by eapply E_Ctx with (E := id).
Qed.

Example ex2_eval : tl_evals ex2 (V_Int 1).
Proof. by exists 4. Qed.

(* [with { a = 1; }; with { a = 2; }; a] gives 2 *)
Definition ex3 :=
  X_Incl (V_Attrset {[ "a" := X_V 1%Z ]})
    (X_Incl (V_Attrset {[ "a" := X_V 2%Z ]}) "a").

Theorem ex3_step : tl_reds ex3 2%Z.
Proof.
  unfold ex3.
  eapply rtc_l.
  - eapply E_Ctx with (E := id); [done | apply E_With].
  - simpl. eapply rtc_l.
    + by eapply E_Ctx with (E := id).
    + simplify_option_eq.
      eapply rtc_once.
      by eapply E_Ctx with (E := id).
Qed.

Example ex3_eval : tl_evals ex3 (V_Int 2).
Proof. by exists 4. Qed.

(* [({ x, y ? x } : y) { x = 1; }] gives 1 *)
Definition ex4 :=
  X_Apply
    (V_AttrsetFn
       (M_Matcher
          {[ "x" := M_Mandatory;
             "y" := M_Optional "x"
          ]}
          true)
       "y")
    (V_Attrset {[ "x" := X_V 1%Z ]}).

Example ex4_eval : tl_evals ex4 (V_Int 1).
Proof. by exists 7. Qed.

(* [({ x ? y, y ? x } : y) { x = 1; }] gives 1 *)
Definition ex5 :=
  X_Apply
    (V_AttrsetFn
       (M_Matcher
          {[ "x" := M_Optional "y";
             "y" := M_Optional "x"
          ]}
          true)
       "y")
    (V_Attrset {[ "x" := X_V 1%Z ]}).

Example ex5_eval : tl_evals ex5 (V_Int 1).
Proof. by exists 7. Qed.

(* [let binToString = n:
          if n == 0
          then "0"
          else if n == 1
               then "1"
               else binToString (n / 2) + (if isEven n then "0" else "1");
        isEven = n: n != 1 && (n = 0 || isEven (n - 2));
        test = { x, y ? attrs.x, ... } @ attrs:
          "x: " + x + ", y: " + y + ", z: " + attrs.z or "(no z)"
    in test { x = binToString 6; }] gives "x: 110, y: 110, z: (no z)" *)
Definition ex6 :=
  X_LetBinding
    {[ "binToString" := B_Rec $ V_Fn "n" $
         X_Cond
           (X_Op O_Eq "n" 0%Z)
           (V_Str "0")
           (X_Cond
             (X_Op O_Eq "n" 1%Z)
             (V_Str "1")
             (X_Op O_Plus
               (X_Apply
                 "binToString"
                 (X_Op O_Div "n" 2%Z))
               (X_Cond
                 (X_Apply "isEven" "n")
                 (V_Str "0")
                 (V_Str "1"))));
       "isEven" := B_Rec $ V_Fn "n" $
         μ_and
           (μ_neq "n" 1%Z)
           (μ_or
             (X_Op O_Eq "n" 0%Z)
             (X_Apply "isEven" (X_Op O_Min "n" 2%Z)));
       "test" := B_Rec $ V_Fn "attrs" $
         X_Apply
           (V_AttrsetFn
             (M_Matcher
               {[ "x" := M_Mandatory;
                  "y" := M_Optional
                    (X_Select "attrs"
                    (nonempty_singleton "x"))
               ]} false)
             (X_Op O_Plus
               (X_Op O_Plus
                 (X_Op O_Plus
                   (X_Op O_Plus
                     (X_Op O_Plus
                       (V_Str "x: ")
                       "x")
                     (V_Str ", y: "))
                   "y")
                 (V_Str ", z: "))
               (X_SelectOr
                 "attrs"
                 (nonempty_singleton "z")
                 (V_Str "(no z)"))))
           "attrs"
    ]}
    (X_Apply "test" $ V_Attrset
       {[ "x" := X_Apply "binToString" 6%Z ]}).

Example ex6_eval : tl_evals ex6 (V_Str "x: 110, y: 110, z: (no z)").
Proof. by exists 37. Qed.

(* Important check of if placeholders work correctly:
   [with { x = 1; }; let foo = y: let x = 2; in y; foo x]
   gives 1 *)
Definition ex7 := X_Incl
  (V_Attrset {[ "x" := X_V 1%Z ]})
  (X_LetBinding
    {[ "foo" := B_Rec $ V_Fn "y" $
         X_LetBinding {[ "x" := B_Rec 2%Z ]} "y"
    ]}
    (X_Apply "foo" "x")).

Example ex7_eval : tl_evals ex7 (V_Int 1).
Proof. by exists 7. Qed.

Definition ex8 :=
  X_LetBinding
    {[ "divide" := B_Rec $ V_Fn "a" $ V_Fn "b" $
         X_Assert
           (μ_and (μ_ge "a" 0%Z) (μ_gt "b" 0%Z))
           (X_Cond
             (X_Op O_Lt "a" "b")
             0
             (X_Op
               O_Plus
               (X_Apply
                 (X_Apply
                   "divide"
                   (X_Op O_Min "a" "b"))
                 "b")
               1));
       "divider" := B_Rec $ X_Attrset
         {[ "__functor" := B_Nonrec $ V_Fn "self" $ V_Fn "x" $
              X_Op
                O_Upd
                "self"
                (X_Attrset
                  {[ "value" := B_Nonrec $
                       X_Apply
                         (X_Apply
                           "divide"
                           (X_Select "self" $ nonempty_singleton "value"))
                         "x"
                  ]})
         ]};
       "mkDivider" := B_Rec $ V_Fn "value" $
         X_Op
           O_Upd
           "divider"
           (X_Attrset {[ "value" := B_Nonrec "value" ]})
    ]}%Z
    (X_Select
      (X_Apply (X_Apply (X_Apply "mkDivider" 100) 5) 4)
      (nonempty_singleton "value"))%Z.

Example ex8_eval : tl_evals ex8 (V_Int 5).
Proof. by exists 170. Qed.

Example ex9 :=
  X_Apply
    (X_Apply
       (V_Attrset
         {[ "__functor" := X_V $ V_Fn "self" $ V_Fn "f" $
              X_Apply "f" (X_Apply "self" "f")
         ]})
       (V_Fn "go" $ V_Fn "n" $
         X_Cond
           (μ_le "n" 1)
           "n"
           (X_Op
             O_Plus
             (X_Apply "go" (X_Op O_Min "n" 1))
             (X_Apply "go" (X_Op O_Min "n" 2)))))%Z
    15%Z.

Example ex9_eval : tl_evals ex9 (V_Int 610).
Proof. by exists 78. Qed.

Example ex10 :=
  X_LetBinding
    {[ "true" := B_Rec 42 ]}%Z
    (X_Op O_Eq "true" 42)%Z.

Example ex10_eval : tl_evals ex10 (V_Bool true).
Proof. by exists 4. Qed.

Definition ex11 :=
  X_LetBinding
    {[ "x" := B_Rec "y" ]}%Z
    (X_LetBinding {[ "y" := B_Rec 10 ]} "x")%Z.

Example ex11_eval : tl_eval 1000 ex11 = None.
Proof. done. Qed.

Definition ex12 :=
  X_LetBinding
    {[ "pkgs" := B_Rec $ V_Attrset
          {[ "x" := X_Incl (V_Attrset {[ "y" := X_V 1%Z ]}) "y" ]}
    ]}
    (X_Select
      (X_Attrset
        {[ "x" := B_Rec $ X_Select "pkgs" (nonempty_singleton "x");
           "y" := B_Rec 3%Z
        ]})
      (nonempty_singleton "x")).

Example ex12_eval : tl_eval 1000 ex12 = Some (V_Int 1).
Proof. done. Qed.

(* Aio, quantitas magna frumentorum est. *)
