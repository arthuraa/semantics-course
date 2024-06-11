From stdpp Require Import gmap base relations.
From iris Require Import prelude.
From semantics.ts.systemf Require Import lang notation parallel_subst types logrel tactics.

(** Exercise 1 (LN Exercise 19): De Bruijn Terms *)
Module dbterm.
  (** Your type of expressions only needs to encompass the operations of our base lambda calculus. *)
  Inductive expr :=
    | Lit (l : base_lit)
    | Var (n : nat)
    | Lam (e : expr)
    | Plus (e1 e2 : expr)
    | App (e1 e2 : expr)
  .

  (** Formalize substitutions and renamings as functions. *)
  Definition subt := nat → expr.
  Definition rent := nat → nat.

  Implicit Types
    (σ : subt)
    (δ : rent)
    (n x : nat)
    (e : expr).

  Fixpoint subst σ e :=
    (* FIXME *) e.

  

  Goal (subst
    (λ n, match n with
          | 0 => Lit (LitInt 42)
          | 1 => Var 0
          | _ => Var n
          end)
    (Lam (Plus (Plus (Var 2) (Var 1)) (Var 0)))) = 
    Lam (Plus (Plus (Var 1) (Lit 42%Z)) (Var 0)).
  Proof.
    cbn. 
    (* Should be by reflexivity. *)
    (* TODO: exercise *)
  Admitted.


End dbterm.

Section church_encodings.
  (** Exercise 2 (LN Exercise 24): Church encoding, sum types *)
  (* a) Define your encoding *)
  Definition sum_type (A B : type) : type := #0 (* FIXME *).
    

  (* b) Implement inj1, inj2, case *)
  Definition injl_val (v : val) : val := #0 (* FIXME *).
  Definition injl_expr (e : expr) : expr := #0 (* FIXME *).
  Definition injr_val (v : val) : val := #0 (* FIXME *).
  Definition injr_expr (e : expr) : expr := #0 (* FIXME *).

  (* You may want to use the variables x1, x2 for the match arms to fit the typing statements below. *)
  Definition match_expr (e : expr) (e1 e2 : expr) : expr := #0. (* FIXME *)
    

  (* c) Reduction behavior *)
  (* Some lemmas about substitutions might be useful. Look near the end of the lang.v file! *)
  Lemma match_expr_red_injl e e1 e2 (vl v' : val) :
    is_closed [] vl →
    is_closed ["x1"] e1 →
    big_step e (injl_val vl) →
    big_step (subst' "x1" vl e1) v' →
    big_step (match_expr e e1 e2) v'.
  Proof.
    (* TODO: exercise *)
  Admitted.


  Lemma match_expr_red_injr e e1 e2 (vl v' : val) :
    is_closed [] vl →
    big_step e (injr_val vl) →
    big_step (subst' "x2" vl e2) v' →
    big_step (match_expr e e1 e2) v'.
  Proof.
    intros. bs_step_det.
    (* TODO: exercise *)
  Admitted.


  Lemma injr_expr_red e v :
    big_step e v →
    big_step (injr_expr e) (injr_val v).
  Proof.
    intros. bs_step_det.
    (* TODO: exercise *)
  Admitted.


  Lemma injl_expr_red e v :
    big_step e v →
    big_step (injl_expr e) (injl_val v).
  Proof.
    intros. bs_step_det.
    (* TODO: exercise *)
  Admitted.



  (* d) Typing rules *)
  Lemma sum_injl_typed n Γ (e : expr) A B :
    type_wf n B →
    type_wf n A →
    TY n; Γ ⊢ e : A →
    TY n; Γ ⊢ injl_expr e : sum_type A B.
  Proof.
    intros. solve_typing.
    (* TODO: exercise *)
  Admitted.


  Lemma sum_injr_typed n Γ e A B :
    type_wf n B →
    type_wf n A →
    TY n; Γ ⊢ e : B →
    TY n; Γ ⊢ injr_expr e : sum_type A B.
  Proof.
    intros. solve_typing.
    (* TODO: exercise *)
  Admitted.


  Lemma sum_match_typed n Γ A B C e e1 e2 :
    type_wf n A →
    type_wf n B →
    type_wf n C →
    TY n; Γ ⊢ e : sum_type A B →
    TY n; <["x1" := A]> Γ ⊢ e1 : C →
    TY n; <["x2" := B]> Γ ⊢ e2 : C →
    TY n; Γ ⊢ match_expr e e1 e2 : C.
  Proof.
    intros. solve_typing.
    (* TODO: exercise *)
  Admitted.



  (** Exercise 3 (LN Exercise 25): church encoding, list types *)

  (* a) translate the type of lists into De Bruijn. *)
  Definition list_type (A : type) : type := #0 (* FIXME *).
    

  (* b) Implement nil and cons. *)
  Definition nil_val : val := #0 (* FIXME *).
  Definition cons_val (v1 v2 : val) : val := #0 (* FIXME *).
  Definition cons_expr (e1 e2 : expr) : expr := #0 (* FIXME *).

  (* c) Define typing rules and prove them *)
  Lemma nil_typed n Γ A :
    type_wf n A →
    TY n; Γ ⊢ nil_val : list_type A.
  Proof.
    intros. solve_typing.
    (* TODO: exercise *)
  Admitted.


  Lemma cons_typed n Γ (e1 e2 : expr) A :
    type_wf n A →
    TY n; Γ ⊢ e2 : list_type A →
    TY n; Γ ⊢ e1 : A →
    TY n; Γ ⊢ cons_expr e1 e2 : list_type A.
  Proof.
    intros. repeat solve_typing.
    (* TODO: exercise *)
  Admitted.


  (* d) Define a function head of type list A → A + 1 *)
  Definition head : val := #0 (* FIXME *).
    

  Lemma head_typed n Γ A :
    type_wf n A →
    TY n; Γ ⊢ head: (list_type A → (A + Unit)).
  Proof.
    intros. solve_typing.
    (* TODO: exercise *)
  Admitted.


  (* e) Define a function [tail] of type list A → list A *)
  
  Definition tail : val := #0 (* FIXME *).
    

  Lemma tail_typed n Γ A :
    type_wf n A →
    TY n; Γ ⊢ tail: (list_type A → list_type A).
  Proof.
    intros. repeat solve_typing.
    (* TODO: exercise *)
  Admitted.


End church_encodings.

Section free_theorems.

  (** Exercise 4 (LN Exercise 27): Free Theorems I *)
  (* a) State a free theorem for the type ∀ α, β. α → β → α × β *)
  Lemma free_thm_1 :
    ∀ f : val,
    TY 0; ∅ ⊢ f : (∀: ∀: #1 → #0 → #1 × #0) →
    True (* FIXME state your theorem *).
  Proof.
    (* TODO: exercise *)
  Admitted.


  (* b) State a free theorem for the type ∀ α, β. α × β → α *)
  Lemma free_thm_2 :
    ∀ f : val,
    TY 0; ∅ ⊢ f : (∀: ∀: #1 × #0 → #1) →
    True (* FIXME state your theorem *).
  Proof.
    (* TODO: exercise *)
  Admitted.


  (* c) State a free theorem for the type ∀ α, β. α → β *)
  Lemma free_thm_3 :
    ∀ f : val,
    TY 0; ∅ ⊢ f : (∀: ∀: #1 → #0) →
    True (* FIXME state your theorem *).
  Proof.
    (* TODO: exercise *)
  Admitted.



  (** Exercise 5 (LN Exercise 28): Free Theorems II *)
  Lemma free_theorem_either :
    ∀ f : val,
    TY 0; ∅ ⊢ f : (∀: #0 → #0 → #0) →
    ∀ (v1 v2 : val), is_closed [] v1 → is_closed [] v2 →
      big_step (f <> v1 v2) v1 ∨ big_step (f <> v1 v2) v2.
  Proof.
    (* TODO: exercise *)
  Admitted.


  (** Exercise 6 (LN Exercise 29): Free Theorems III *)
  (* Hint: you might want to use the fact that our reduction is deterministic. *)
  Lemma big_step_det e v1 v2 :
    big_step e v1 → big_step e v2 → v1 = v2.
  Proof.
    induction 1 in v2 |-*; inversion 1; subst; eauto 2.
    all: naive_solver.
  Qed.

  Lemma free_theorems_magic :
    ∀ (A A1 A2 : type) (f g : val),
    type_wf 0 A → type_wf 0 A1 → type_wf 0 A2 →
    is_closed [] f → is_closed [] g →
    TY 0; ∅ ⊢ f : (∀: (A1 → A2 → #0) → #0) →
    TY 0; ∅ ⊢ g : (A1 → A2 → A) →
    ∀ v, big_step (f <> g) v →
    ∃ (v1 v2 : val), big_step (g v1 v2) v.
  Proof.
    (* Hint: you may find the following lemmas useful:
        - [sem_val_rel_cons]
        - [type_wf_closed]
        - [val_rel_is_closed]
        - [big_step_preserve_closed]
    *)
    (* TODO: exercise *)
  Admitted.


End free_theorems.
