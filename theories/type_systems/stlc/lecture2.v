(** * This file was shown during the lecture on 26.10.2023.
    * It contrains duplicated code that is copy-pasted from e.g. lang.v
    *)

From stdpp Require Export binders strings.
From stdpp Require Import options.
From semantics.lib Require Import maps.

(** * Simply Typed Lambda Calculus *)

(** ** Expressions and values. *)
(** [Z] is Coq's version of the integers.
    All the standard operations, like [+], are defined on it.

    The type [binder] is defined as [x ::= BNamed (s: string) | BAnon]
    where BAnon can be used if we don't want to use the variable in
    the function.
*)
Inductive expr :=
  (* Base lambda calculus *)
  | Var (x : string)
  | Lam (x : binder) (e : expr)
  | App (e1 e2 : expr)
  (* Base types and their operations *)
  | LitInt (n: Z)
  | Plus (e1 e2 : expr).

Inductive val :=
  | LitIntV (n: Z)
  | LamV (x : binder) (e : expr).

(* Injections into expr *)
Definition of_val (v : val) : expr :=
  match v with
  | LitIntV n => LitInt n
  | LamV x e => Lam x e
  end.

(* try to make an expr into a val *)
Definition to_val (e : expr) : option val :=
  match e with
  | LitInt n => Some (LitIntV n)
  | Lam x e => Some (LamV x e)
  | _ => None
  end.

Lemma to_of_val v : to_val (of_val v) = Some v.
Proof.
  destruct v; simpl; reflexivity.
Qed.

Lemma of_to_val e v : to_val e = Some v -> of_val v = e.
Proof.
  destruct e; simpl; try congruence.
  all: injection 1 as <-; simpl; reflexivity.
Qed.

(* Inj is a type class for injective functions.
   It is defined as:
    [Inj R S f := ∀ x y, S (f x) (f y) -> R x y]
*)
#[export] Instance of_val_inj : Inj (=) (=) of_val.
Proof. by intros ?? Hv; apply (inj Some); rewrite <-!to_of_val, Hv. Qed.

(* A predicate which holds true whenever an
   expression is a value. *)
Definition is_val (e : expr) : Prop :=
  match e with
  | LitInt n => True
  | Lam x e => True
  | _ => False
  end.
Lemma is_val_spec e : is_val e ↔ ∃ v, to_val e = Some v.
Proof.
  destruct e; simpl.
  (* naive_solver is an automation tactic like intuition, firstorder, auto, ...
     It is provided by the stdpp library. *)
  all: naive_solver.
Qed.

Lemma is_val_of_val v : is_val (of_val v).
Proof.
  apply is_val_spec. rewrite to_of_val. eauto.
Qed.

(* A small tactic that simplifies handling values. *)
Ltac simplify_val :=
  repeat match goal with
  | H: to_val (of_val ?v) = ?o |- _ => rewrite to_of_val in H
  | H: is_val ?e |- _ => destruct (proj1 (is_val_spec e) H) as (? & ?); clear H
  end.

(* values are values *)
Lemma is_val_val (v: val): is_val (of_val v).
Proof.
  destruct v; simpl; done.
Qed.

(* we tell eauto to use the lemma is_val_val *)
#[global]
Hint Immediate is_val_val : core.


(** ** Operational Semantics *)

(** *** Substitution *)
Fixpoint subst (x : string) (es : expr) (e : expr)  : expr :=
  match e with
  | LitInt n => LitInt n
  (* The function [decide] can be used to decide propositions.
    [decide P] is of type {P} + {¬ P}.
    It can only be applied to propositions for which, by type class inference,
    it can be determined that the proposition is decidable. *)
  | Var y => if decide (x = y) then es else Var y
  | Lam y e =>
      Lam y $ if decide (BNamed x = y) then e else subst x es e
  | App e1 e2 => App (subst x es e1) (subst x es e2)
  | Plus e1 e2 => Plus (subst x es e1) (subst x es e2)
  end.

(* We lift substitution to binders. *)
Definition subst' (mx : binder) (es : expr) : expr -> expr :=
  match mx with BNamed x => subst x es | BAnon => id end.


(** *** Small-Step Semantics *)
(* We use right-to-left evaluation order,
   which means in a binary term (e.g., e1 + e2),
   the left side can only be reduced once the right
   side is fully evaluated (i.e., is a value). *)
Inductive step : expr -> expr -> Prop :=
  | StepBeta x e e'  :
      is_val e' ->
      step (App (Lam x e) e') (subst' x e' e)
  | StepAppL e1 e1' e2 :
    is_val e2 ->
    step e1 e1' ->
    step (App e1 e2) (App e1' e2)
  | StepAppR e1 e2 e2' :
    step e2 e2' ->
    step (App e1 e2) (App e1 e2')
  | StepPlusRed (n1 n2 n3: Z) :
    (n1 + n2)%Z = n3 ->
    step (Plus (LitInt n1) (LitInt n2)) (LitInt n3)
  | StepPlusL e1 e1' e2 :
    is_val e2 ->
    step e1 e1' ->
    step (Plus e1 e2) (Plus e1' e2)
  | StepPlusR e1 e2 e2' :
    step e2 e2' ->
    step (Plus e1 e2) (Plus e1 e2').

(* We make the tactic eauto aware of the constructors of [step].
   Then it can automatically solve goals where we want to prove a step. *)
#[global] Hint Constructors step : core.


(* A term is reducible, if it can take a step. *)
Definition reducible (e : expr) :=
  ∃ e', step e e'.


(** *** Big-Step Semantics *)
Inductive big_step : expr -> val -> Prop :=
  | bs_lit (n : Z) :
      big_step (LitInt n) (LitIntV n)
  | bs_lam (x : binder) (e : expr) :
      big_step (Lam x e) (LamV x e)
  | bs_add e1 e2 (z1 z2 : Z) :
      big_step e1 (LitIntV z1) ->
      big_step e2 (LitIntV z2) ->
      big_step (Plus e1 e2) (LitIntV (z1 + z2))%Z
  | bs_app e1 e2 x e v2 v :
      big_step e1 (@LamV x e) ->
      big_step e2 v2 ->
      big_step (subst' x (of_val v2) e) v ->
      big_step (App e1 e2) v
    .
#[export] Hint Constructors big_step : core.


Lemma big_step_vals (v: val): big_step (of_val v) v.
Proof.
  induction v; econstructor.
Qed.






(*** Inversion ***)



(* We might want to show the following lemma about small step semantics: *)
Lemma val_no_step (v : val) (e : expr) :
  step (of_val v) e -> False.
Proof.
  (* destructing doesn't work: the different cases don't have enough information *)
  destruct 1.
  - admit.
  - admit.
    Restart.
  remember (of_val v) as e' eqn:Heq.
  destruct 1.
  - (* Aha! Coq remembered that we had a value on the left-hand sidde of the
       step *)
    destruct v; discriminate.
  - destruct v; discriminate.
  - destruct v; discriminate.
  - destruct v; discriminate.
  - destruct v; discriminate.
  - destruct v; discriminate.
  Restart.
  (* there's a tactic that does this for us: inversion *)
  inversion 1.
  all: destruct v; discriminate.
Qed.


(* The (non-recursive) eliminator for step in Coq *)
Lemma step_elim (P : expr -> expr -> Prop) :
           (∀ (x : binder) (e1 e2 : expr), is_val e2 ->               
                                             P (App (Lam x e1) e2) (subst' x e2 e1))
         -> (∀ e1 e1' e2 : expr,           is_val e2 -> step e1 e1' -> 
                                             P (App e1 e2) (App e1' e2))
         -> (∀ e1 e2 e2' : expr,           step e2 e2' -> 
                                             P (App e1 e2) (App e1 e2'))
         -> (∀ n1 n2 n3 : Z,               (n1 + n2)%Z = n3 ->        
                                             P (Plus (LitInt n1) (LitInt n2)) (LitInt n3))
         -> (∀ e1 e1' e2 : expr,           is_val e2 -> step e1 e1' -> 
                                             P (Plus e1 e2) (Plus e1' e2))
         -> (∀ e1 e2 e2' : expr,           step e2 e2' -> P (Plus e1 e2) (Plus e1 e2'))
         
  
         -> ∀ e e' : expr, step e e' -> P e e'.
Proof.
  destruct 7; eauto.
Qed.


(* An inversion operator for step in Coq *)
Lemma step_inversion (P : expr -> expr -> Prop) (e e' : expr) :
           (∀ (x : binder) (e1 e2 : expr), e = App (Lam x e1) e2 -> e' = subst' x e2 e1 -> 
                                             is_val e2 ->               
                                             P (App (Lam x e1) e2) (subst' x e2 e1))
         -> (∀ e1 e1' e2 : expr,           e = App e1 e2 -> e' = App e1' e2 -> 
                                             is_val e2 -> step e1 e1' -> 
                                             P (App e1 e2) (App e1' e2))
         -> (∀ e1 e2 e2' : expr,           e = App e1 e2 -> e' = App e1 e2' ->
                                             step e2 e2' -> 
                                             P (App e1 e2) (App e1 e2'))
         -> (∀ n1 n2 n3 : Z,               e = Plus (LitInt n1) (LitInt n2) -> e' = LitInt n3 -> 
                                             (n1 + n2)%Z = n3 ->        
                                             P (Plus (LitInt n1) (LitInt n2)) (LitInt n3))
         -> (∀ e1 e1' e2 : expr,           e = Plus e1 e2 -> e' = Plus e1' e2 ->
                                             is_val e2 -> step e1 e1' -> 
                                             P (Plus e1 e2) (Plus e1' e2))
         -> (∀ e1 e2 e2' : expr,           e = Plus e1 e2 -> e' = Plus e1 e2' -> 
                                             step e2 e2' -> 
                                             P (Plus e1 e2) (Plus e1 e2'))
         -> step e e' -> P e e'.
Proof.
  intros H1 H2 H3 H4 H5 H6.
  destruct 1.
  { eapply H1. all: easy. }
  { eapply H2. all: easy. }
  (* All the other cases are similar. *)
  all: eauto.
Qed.


(* We can use the inversion operator to show that values cannot step. *)
Lemma val_no_step' (v : val) (e : expr) :
  step (of_val v) e -> False.
Proof.
  intros H. eapply step_inversion. 7: eauto.
  all: intros; destruct v; discriminate.
Qed.



(* The following is another kind of inversion operator, as taught in the ICL lecture. *)
Definition step_inv (e e' : expr) :  step e e' -> 
  (match e with
   | App e1 e2 => 
       (∃ x f, e1 = (Lam x f) ∧ e' = subst' x e2 f) ∨ 
       (∃ e1', is_val e2 ∧ step e1 e1') ∨ 
       (∃ e2', step e2 e2')
   | Plus e1 e2 => 
       (∃ n1 n2, e1 = LitInt n1 ∧ e2 = LitInt n2 ∧ LitInt (n1 + n2) = e') ∨ 
       (∃ e1', is_val e2 ∧ step e1 e1') ∨ 
       (∃ e2', step e2 e2')
   | _ => False
                                        end).
Proof.
  intros H. destruct H; naive_solver.
Qed.
