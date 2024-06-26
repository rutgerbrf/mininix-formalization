(** This files contains definitions for determinism, strong confluence,
 * semi-confluence, the Church-Rosser property and proofs about relationships
 * of these properties. We use definitions and proofs from 'Term Rewriting and
 * All That' by Franz Baader and Tobias Nipkow (1998). *)
From stdpp Require Import relations.

Definition deterministic {A} (R : relation A) :=
  ∀ x y1 y2, R x y1 → R x y2 → y1 = y2.

(** Baader and Nipkow (1998), p. 9:
 *   y is a normal form of x if x -->* y and y is in normal form. *)
Definition is_nf_of `(R : relation A) x y := (rtc R x y) ∧ nf R y.

(** The reflexive closure. *)
Inductive rc {A} (R : relation A) : relation A :=
  | rc_refl x : rc R x x
  | rc_once x y : R x y → rc R x y.

Hint Constructors rc : core.

(** Baader and Nipkow, Definition 2.7.3. *)
Definition strongly_confluent {A} (R : relation A) :=
  ∀ x y1 y2, R x y1 → R x y2 → ∃ z, rtc R y1 z ∧ rc R y2 z.

(** Baader and Nipkow, Definition 2.1.4. *)
Definition semi_confluent {A} (R : relation A) :=
  ∀ x y1 y2, R x y1 → rtc R x y2 → ∃ z, rtc R y1 z ∧ rtc R y2 z.

(** Lemma 2.7.4 from Baader and Nipkow *)
Lemma strong__semi_confluence {A} (R : relation A) :
  strongly_confluent R → semi_confluent R.
Proof.
  intros Hstrc.
  unfold strongly_confluent in Hstrc.
  unfold semi_confluent.
  intros x1 y1 xn Hxy1 [steps Hsteps] % rtc_nsteps.
  revert x1 y1 xn Hxy1 Hsteps.
  induction steps; intros x1 y1 xn Hxy1 Hsteps.
  - inv Hsteps. exists y1.
    split.
    + apply rtc_refl.
    + by apply rtc_once.
  - inv Hsteps as [|? ? x2 ? Hx1x2 Hsteps'].
    destruct (Hstrc x1 y1 x2 Hxy1 Hx1x2) as [y2 [Hy21 Hy22]].
    inv Hy22.
    + exists xn. split; [|done].
      apply rtc_transitive with (y := y2); [done|].
      rewrite rtc_nsteps. by exists steps.
    + destruct (IHsteps x2 y2 xn H Hsteps') as [yn [Hy2yn Hxnyn]].
      exists yn. split; [|done].
      by apply rtc_transitive with (y := y2).
Qed.

(** Baader and Nipkow, Definition 2.1.3. 
 * Copied from stdpp v1.10.0 (confluent_alt). *)
Definition cr {A} (R : relation A) :=
  ∀ x y, rtsc R x y → ∃ z, rtc R x z ∧ rtc R y z.

(** Part of Lemma 2.1.5 from Baader and Nipkow (1998) *)
Lemma semi_confluence__cr {A} (R : relation A) :
  semi_confluent R → cr R.
Proof.
  intros Hsc.
  unfold semi_confluent in Hsc.
  unfold cr.
  intros x y [steps Hsteps] % rtc_nsteps.
  revert x y Hsteps.
  induction steps; intros x y Hsteps.
  - inv Hsteps. by exists y.
  - inv Hsteps. rename x into y', y into x, y0 into y.
    apply IHsteps in H1 as H1'. destruct H1' as [z [Hz1 Hz2]].
    destruct H0.
    + exists z. split; [|done].
      by apply rtc_l with (y := y).
    + destruct (Hsc y y' z H Hz1) as [z' [Hz'1 Hz'2]].
      exists z'. split; [done|].
      by apply rtc_transitive with (y := z).
Qed.
