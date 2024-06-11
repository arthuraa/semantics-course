(* Throughout the course, we will be using the [stdpp] library to provide
   some useful and common features.
   We will introduce you to its features as we need them.
 *)
From stdpp Require Import base tactics numbers strings.
From stdpp Require relations.
From semantics.lib Require Import maps.

(** * Exercise sheet 0 *)

(* We are using Coq's notion of integers, [Z].
   All the standard operations, like [+] and [*], are defined on it.
 *)
Inductive expr :=
  | Const (z : Z)
  | Plus (e1 e2 : expr)
  | Mul (e1 e2 : expr).

(** Exercise 1: Arithmetics *)
Fixpoint expr_eval (e : expr) : Z :=
  (* TODO: write the function *)
  0.

(** Now let's define some notation to make it look nice! *)
(* We declare a so-called notation scope, so that we can still use the nice notations for addition on natural numbers [nat] and integers [Z]. *)
Declare Scope expr.
Delimit Scope expr with E.
Notation "e1 + e2" := (Plus e1%Z e2%Z) : expr.
Notation "e1 * e2" := (Mul e1%Z e2%Z) : expr.

 (* We can use our nice notation to write expressions!
    (note the [%E] to tell Coq to parse this as an arithmetical expression with the
    notations we just defined).
  *)
 Check (Const 5 + Const 5)%E.
 (* The notation also still works for [Z] and [nat]: *)
 Check (5 + 5)%Z.
 Check (5 + 5).

 (* As an exercise, rephrase the following lemmas using the newly defined notation *)

Lemma expr_eval_test: expr_eval (Plus (Const (-4)) (Const 5)) = 1%Z.
Proof.
  (* should be solved by:  simpl. lia. *)
  (* TODO: exercise *)
Admitted.


Lemma plus_eval_comm e1 e2 :
  expr_eval (Plus e1 e2) = expr_eval (Plus e2 e1).
Proof.
  (* TODO: exercise *)
Admitted.

Lemma plus_syntax_not_comm :
  Plus (Const 0) (Const 1) ≠ Plus (Const 1) (Const 0).
Proof.
  (* TODO: exercise *)
Admitted.


(** Exercise 2: Open arithmetical expressions *)

(* Finally, we introduce variables into our arithmetic expressions.
   Variables are of Coq's [string] type.
 *)
Inductive expr' :=
  | Var (x: string)
  | Const' (z : Z)
  | Plus' (e1 e2 : expr')
  | Mul' (e1 e2 : expr').

(* We call an expression closed under the list X,
  if it only contains variables in X *)
Fixpoint is_closed (X: list string) (e: expr') : bool :=
  match e with
    | Var x => bool_decide (x ∈ X)
    | Const' z => true
    | Plus' e1 e2 => is_closed X e1 && is_closed X e2
    | Mul' e1 e2 => is_closed X e1 && is_closed X e2
  end.

Definition closed X e := is_closed X e = true.


(* Some examples of closed terms. *)
Lemma example_no_vars_closed:
  closed [] (Plus' (Const' 3) (Const' 5)).
Proof.
  unfold closed. simpl. done.
Qed.


Lemma example_some_vars_closed:
  closed ["x"; "y"] (Plus' (Var "x") (Var "y")).
Proof.
  unfold closed. simpl. done.
Qed.

Lemma example_not_closed:
  ¬ closed ["x"] (Plus' (Var "x") (Var "y")).
Proof.
  unfold closed. simpl. done.
Qed.

Lemma closed_mono X Y e:
  X ⊆ Y → closed X e → closed Y e.
Proof.
  unfold closed. intros Hsub; induction e as [ x | z | e1 IHe1 e2 IHe2 | e1 IHe1 e2 IHe2]; simpl.
  - (* bool_decide is an stdpp function, which can be used to decide simple decidable propositions.
      Make a search for it to find the right lemmas to complete this subgoal. *)
    (* Search bool_decide. *)
    admit.
  - done.
  - (* Locate the notation for && by typing: Locate "&&". Then search for the right lemmas.*)
    admit.
  - admit.
Admitted.

(* we define a substitution operation on open expressions *)
Fixpoint subst (e: expr') (x: string) (e': expr') : expr' :=
  match e with
  | Var y => if (bool_decide (x = y)) then e' else Var y
  | Const' z => Const' z
  | Plus' e1 e2 => Plus' (subst e1 x e') (subst e2 x e')
  | Mul' e1 e2 => Mul' (subst e1 x e') (subst e2 x e')
  end.

Lemma subst_closed e e' x X:
  closed X e → ¬ (x ∈ X) → subst e x e' = e.
Proof.
  (* TODO: exercise *)
Admitted.


(* To evaluate an arithmetic expression, we define an evaluation function [expr_eval], which maps them to integers.
   Since our expressions contain variables, we pass a finite map as the argument, which is used to look up variables.
   The type of finite maps that we use is called [gmap].
 *)
Fixpoint expr_eval' (m: gmap string Z) (e : expr') : Z :=
  match e with
  | Var x => default 0%Z (m !! x) (* this is the lookup operation on gmaps *)
  | Const' z => z
  | Plus' e1 e2 => (expr_eval' m e1) + (expr_eval' m e2)
  | Mul' e1 e2 => (expr_eval' m e1) * (expr_eval' m e2)
  end.

(* Prove the following lemma which explains how substitution interacts with evaluation *)
Lemma eval_subst_extend (m: gmap string Z) e x e':
  expr_eval' m (subst e x e') = expr_eval' (<[x := expr_eval' m e']> m) e.
Proof.
  (* TODO: exercise *)
Admitted.

