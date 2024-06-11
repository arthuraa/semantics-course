From stdpp Require Import gmap base relations.
From iris Require Import prelude.
From semantics.ts.systemf Require Import lang notation types tactics.

(** Exercise 3 (LN Exercise 22): Universal Fun *)

Definition fun_comp : val :=
  #0 (* TODO *).
Definition fun_comp_type : type :=
  #0 (* TODO *).
Lemma fun_comp_typed :
  TY 0; ∅ ⊢ fun_comp : fun_comp_type.
Proof. 
  (* should be solved by solve_typing. *)
  (* TODO: exercise *)
Admitted.


Definition swap_args : val :=
  #0 (* TODO *).
Definition swap_args_type : type :=
  #0 (* TODO *).
Lemma swap_args_typed :
  TY 0; ∅ ⊢ swap_args : swap_args_type.
Proof. 
  (* should be solved by solve_typing. *)
  (* TODO: exercise *)
Admitted.


Definition lift_prod : val :=
  #0 (* TODO *).
Definition lift_prod_type : type :=
  #0 (* TODO *).
Lemma lift_prod_typed :
  TY 0; ∅ ⊢ lift_prod : lift_prod_type.
Proof. 
  (* should be solved by solve_typing. *)
  (* TODO: exercise *)
Admitted.


Definition lift_sum : val :=
  #0 (* TODO *).
Definition lift_sum_type : type :=
  #0 (* TODO *).
Lemma lift_sum_typed :
  TY 0; ∅ ⊢ lift_sum : lift_sum_type.
Proof. 
  (* should be solved by solve_typing. *)
  (* TODO: exercise *)
Admitted.


(** Exercise 5 (LN Exercise 18): Named to De Bruijn *)
Inductive ptype : Type :=
  | PTVar : string → ptype
  | PInt
  | PBool
  | PTForall : string → ptype → ptype
  | PTExists : string → ptype → ptype
  | PFun (A B : ptype).

Declare Scope PType_scope.
Delimit Scope PType_scope with pty.
Bind Scope PType_scope with ptype.
Coercion PTVar: string >-> ptype.
Infix "→" := PFun : PType_scope.
Notation "∀:  x , τ" :=
    (PTForall x τ%pty)
    (at level 100, τ at level 200) : PType_scope.
Notation "∃:  x , τ" :=
    (PTExists x τ%pty)
    (at level 100, τ at level 200) : PType_scope.

Fixpoint debruijn (m: gmap string nat) (A: ptype) : option type :=
  None (* FIXME *). 

(* Example *)
Goal debruijn ∅ (∀: "x", ∀: "y", "x" → "y")%pty = Some (∀: ∀: #1 → #0)%ty.
Proof.
  (* Should be solved by reflexivity. *)
  (* TODO: exercise *)
Admitted.


Goal debruijn ∅ (∀: "x", "x" → ∀: "y", "y")%pty = Some (∀: #0 → ∀: #0)%ty.
Proof.
  (* Should be solved by reflexivity. *)
  (* TODO: exercise *)
Admitted.


Goal debruijn ∅ (∀: "x", "x" → ∀: "y", "x")%pty = Some (∀: #0 → ∀: #1)%ty.
Proof.
  (* Should be solved by reflexivity. *)
  (* TODO: exercise *)
Admitted.


