From stdpp Require Import gmap base relations tactics.
From iris Require Import prelude.
From semantics.ts.stlc Require Import lang notation.

(** Exercise 2 (LN Exercise 1): Deterministic Operational Semantics *)

Lemma val_no_step e e':
  step e e' → is_val e → False.
Proof.
  by destruct 1.
Qed.
(* Note how the above lemma is another way to phrase the statement "values
 * cannot step" that doesn't need inversion. It can also be used to prove the
 * phrasing we had to use inversion for in the lecture: *)
Lemma val_no_step' (v : val) (e : expr) :
  step v e -> False.
Proof.
  intros H. eapply val_no_step; first eassumption.
  apply is_val_val.
Qed.


(* You might find the following tactic useful,
   which derives a contradiction when you have a [step e1 e2] assumption and
   [e1] is a value.

   Example:
   H1: step e e'
   H2: is_val e
   =====================
   ???

   Then [val_no_step.] will solve the goal by applying the [val_no_step] lemma.

   (We neither expect you to understand how exactly the tactic does this nor to
   be able to write such a tactic yourself. Where useful, we will always
   provide you with custom tactics and explain in a comment what they do.) *)
Ltac val_no_step :=
  match goal with
  | [H: step ?e1 ?e2 |- _] =>
    solve [exfalso; eapply (val_no_step _ _ H); done]
  end.

Lemma step_det e e' e'':
  step e e' → step e e'' → e' = e''.
Proof.
  (* TODO: exercise *)
Admitted.


(** Exercise 3 (LN Exercise 2): Call-by-name Semantics *)
Inductive cbn_step : expr → expr → Prop :=
  | CBNStepBeta x e e'  :
      cbn_step (App (Lam x e) e') (subst' x e' e)
      (* TODO: add more constructors *)
.

(* We make the eauto tactic aware of the constructors of cbn_step *)
#[global] Hint Constructors cbn_step : core.

Lemma different_results :
  ∃ (e: expr) (e1 e2: expr), rtc cbn_step e e1 ∧ rtc step e e2 ∧ is_val e1 ∧ is_val e2 ∧ e1 ≠ e2.
Proof.
  (* TODO: exercise *)
Admitted.


Lemma val_no_cbn_step e e':
  cbn_step e e' → is_val e →  False.
Proof.
  (* TODO: exercise *)
Admitted.


(* Same tactic as [val_no_step] but for cbn_step.*)
Ltac val_no_cbn_step :=
  match goal with
  | [H: cbn_step ?e1 ?e2 |- _] =>
    solve [exfalso; eapply (val_no_cbn_step _ _ H); done]
  end.

Lemma cbn_step_det e e' e'':
  cbn_step e e' → cbn_step e e'' → e' = e''.
Proof.
  (* TODO: exercise *)
Admitted.



(** Exercise 4 (LN Exercise 3): Reflexive Transitive Closure *)
Section rtc.
  Context {X : Type}.

  Inductive rtc (R : X → X → Prop) : X → X → Prop :=
    | rtc_base x : rtc R x x
    | rtc_step x y z : R x y → rtc R y z → rtc R x z.

  Lemma rtc_reflexive R : Reflexive (rtc R).
  Proof.
    unfold Reflexive.
    (* TODO: exercise *)
  Admitted.

  Lemma rtc_transitive R : Transitive (rtc R).
  Proof.
    unfold Transitive.
    (* TODO: exercise *)
  Admitted.


  Lemma rtc_subrel (R: X → X → Prop) (x y : X): R x y → rtc R x y.
  Proof.
    (* TODO: exercise *)
  Admitted.


  Section typeclass.
    (* We can use Coq's typeclass mechanism to enable the use of the [transitivity] and [reflexivity] tactics on our goals.
       Typeclasses enable easy extensions of existing mechanisms -- in this case, by telling Coq to use the knowledge about our definition of [rtc].
     *)
    (* [Transitive] is a typeclass. With [Instance] we provide an instance of it. *)
    Global Instance rtc_transitive_inst R : Transitive (rtc R).
  Proof.
    apply rtc_transitive.
  Qed.
  Global Instance rtc_reflexive_inst R : Reflexive (rtc R).
  Proof.
    apply rtc_reflexive.
  Qed.
  End typeclass.
End rtc.
 
(* Let's put this to the test! *)
Goal rtc step (LitInt 42) (LitInt 42).
Proof.
  (* this uses the [rtc_reflexive_inst] instance we registered. *)
  reflexivity.
Qed.
Goal rtc step (LitInt 32 + (LitInt 5 + LitInt 5)%E)%E (LitInt 42).
Proof.
  (* this uses the [rtc_transitive_inst] instance we registered. *)
  etransitivity.
  + eapply rtc_step; eauto. reflexivity.
  + eapply rtc_step; eauto. reflexivity.
Qed.

Section stdpp.
  (* In fact, [rtc] is so common that it is already provided by the [stdpp] library! *)
  Import stdpp.relations.
  Print rtc.

  (* The typeclass instances are also already registered. *)
  Goal rtc step (LitInt 42) (LitInt 42).
  Proof. reflexivity. Qed.
End stdpp.

(* Start by proving these lemmas. Understand why they are useful. *)
Lemma plus_right e1 e2 e2':
  rtc step e2 e2' → rtc step (Plus e1 e2) (Plus e1 e2').
Proof.
  (* TODO: exercise *)
Admitted.


Lemma plus_left e1 e1' n:
  rtc step e1 e1' → rtc step (Plus e1 (LitInt n)) (Plus e1' (LitInt n)).
Proof.
  (* TODO: exercise *)
Admitted.


(* The exercise: *)
Lemma plus_to_consts e1 e2 n m:
  rtc step e1 (LitInt n) → rtc step e2 (LitInt m) → rtc step (e1 + e2)%E (LitInt (n + m)%Z).
Proof.
  (* TODO: exercise *)
Admitted.




(* Now that you have an understanding of how rtc works, we can make eauto aware of it. *)
#[local] Hint Constructors rtc : core.

(* See its power here: *)
Lemma plus_right_eauto e1 e2 e2':
  rtc step e2 e2' → rtc step (Plus e1 e2) (Plus e1 e2').
Proof.
  induction 1; eauto.
Abort.

(** Exercise 5 (LN Exercise 4): Big-step vs small-step semantics *)


Lemma big_step_steps e v :
  big_step e v → rtc step e (of_val v).
Proof.
  (* TODO: exercise *)
Admitted.



Lemma steps_big_step e (v: val):
  rtc step e v → big_step e v.
Proof.
  (* Note how there is a coercion (automatic conversion) hidden in the
   * statement of this lemma: *)
  Set Printing Coercions.
  (* It is sometimes very useful to temporarily print coercions if rewrites or
   * destructs do not behave as expected. *)
  Unset Printing Coercions.
  (* TODO: exercise *)
Admitted.



(** Exercise 6 (LN Exercise 5): left-to-right evaluation *)
Inductive ltr_step : expr → expr → Prop := .

#[global] Hint Constructors ltr_step : core.

Lemma different_steps_ltr_step :
  ∃ (e: expr) (e1 e2: expr), ltr_step e e1 ∧ step e e2 ∧ e1 ≠ e2.
Proof.
  (* TODO: exercise *)
Admitted.




Lemma big_step_ltr_steps e v :
  big_step e v → rtc ltr_step e (of_val v).
Proof.
  (* TODO: exercise *)
Admitted.




Lemma ltr_steps_big_step e (v: val):
  rtc ltr_step e v → big_step e v.
Proof.
  (* TODO: exercise *)
Admitted.

