From stdpp Require Import gmap base relations.
From iris Require Import prelude.
From semantics.ts.systemf Require Import lang notation parallel_subst types tactics.
From semantics.ts.systemf Require logrel binary_logrel existential_invariants.

(** * Exercise Sheet 5 *)

Implicit Types
  (e : expr)
  (v : val)
  (A B : type)
.

(** ** Exercise 3 (LN Exercise 23): Existential Fun *)
Section existential.
  (** Since extending our language with records would be tedious,
    we encode records using nested pairs.

   For instance, we would represent the record type
   { add : Int → Int → Int; sub : Int → Int → Int; neg : Int → Int }
   as (Int → Int → Int) × (Int → Int → Int) × (Int → Int).

   Similarly, we would represent the record value
   { add := λ: "x" "y", "x" + "y";
     sub := λ: "x" "y", "x" - "y";
     neg := λ: "x", #0 - "x"
   }
  as the nested pair
  ((λ: "x" "y", "x" + "y",    (* add *)
    λ: "x" "y", "x" - "y"),   (* sub *)
    λ: "x", #0 - "x").        (* neg *)

  *)

  (** We will also assume a recursion combinator. We have not formally added it to our language, but we could do so. *)
  Context (Fix : string → string → expr → val).
  Notation "'fix:' f x := e" := (Fix f x e)%E
    (at level 200, f, x at level 1, e at level 200,
     format "'[' 'fix:'  f  x   :=  '/  ' e ']'") : val_scope.
  Notation "'fix:' f x := e" := (Fix f x e)%E
    (at level 200, f, x at level 1, e at level 200,
     format "'[' 'fix:'  f  x   :=  '/  ' e ']'") : expr_scope.
  Context (fix_typing : ∀ n Γ (f x: string) (A B: type) (e: expr),
    type_wf n A →
    type_wf n B →
    f ≠ x →
    TY n; <[x := A]> (<[f := (A → B)%ty]> Γ) ⊢ e : B →
    TY n; Γ ⊢ (fix: f x := e) : (A → B)).

  Definition ISET : type :=#0. (* TODO: your definition *)

  (* We represent sets as functions of type ((Int → Bool) × Int × Int),
    storing the mapping, the minimum value, and the maximum value. *)
  

  Definition iset : val :=#0. (* TODO: your definition *)

  Lemma iset_typed n Γ : TY n; Γ ⊢ iset : ISET.
  Proof.
    (* HINT: use repeated solve_typing with an explicit apply fix_typing inbetween *)
    (* TODO: exercise *)
  Admitted.


  Definition ISETE : type :=#0. (* TODO: your definition *)

  Definition add_equality : val :=#0. (* TODO: your definition *)

  Lemma add_equality_typed n Γ : TY n; Γ ⊢ add_equality : (ISET → ISETE)%ty.
  Proof.
    repeat solve_typing.
  (* Qed. *)
    (* TODO: exercise *)
  Admitted.


End existential.

Section ex4.
Import logrel existential_invariants.
(** ** Exercise 4 (LN Exercise 30): Evenness *)
(* Consider the following existential type: *)
Definition even_type : type :=
  ∃: (#0 ×              (* zero *)
      (#0 → #0) ×       (* add2 *)
      (#0 → Int)        (* toint *)
  )%ty.

(* and consider the following implementation of [even_type]: *)
Definition even_impl : val :=
  pack (#0,
        λ: "z", #2 + "z",
        λ: "z", "z"
       ).
(* We want to prove that [toint] will only every yield even numbers. *)
(* For that purpose, assume that we have a function [even] that decides even parity available: *)
Context (even_dec : val).
Context (even_dec_typed : ∀ n Γ, TY n; Γ ⊢ even_dec : (Int → Bool)).

(* a) Change [even_impl] to [even_impl_instrumented] such that [toint] asserts evenness of the argument before returned.
You may use the [assert] expression defined in existential_invariants.v.
*)

Definition even_impl_instrumented : val :=#0. (* TODO: your definition *)

(* b) Prove that [even_impl_instrumented] is safe. You may assume that even works as intended,
  but be sure to state this here. *)


Lemma even_impl_instrumented_safe δ:
  𝒱 even_type δ even_impl_instrumented.
Proof.
  (* TODO: exercise *)
Admitted.

End ex4.

(** ** Exercise 5 (LN Exercise 31): Abstract sums *)
Section ex5.
Import logrel existential_invariants.
Definition sum_ex_type (A B : type) : type :=
  ∃: ((A.[ren (+1)] → #0) ×
      (B.[ren (+1)] → #0) ×
      (∀: #1 → (A.[ren (+2)] → #0) → (B.[ren (+2)] → #0) → #0)
     )%ty.

Definition sum_ex_impl : val :=
  pack (λ: "x", (#1, "x"),
        λ: "x", (#2, "x"),
        Λ, λ: "x" "f1" "f2", if: Fst "x" = #1 then "f1" (Snd "x") else "f2" (Snd "x")
       ).

Lemma sum_ex_safe A B δ:
  𝒱 (sum_ex_type A B) δ sum_ex_impl.
Proof.
  (* TODO: exercise *)
Admitted.

End ex5.

(** For Exercise 6 and 7, see binary_logrel.v *)

(** ** Exercise 8 (LN Exercise 35): Contextual equivalence *)
Section ex8.
Import binary_logrel.
Definition sum_ex_impl' : val :=
  pack ((λ: "x", InjL "x"),
        (λ: "x", InjR "x"),
        (Λ, λ: "x" "f1" "f2", Case "x" "f1" "f2")
       ).

Lemma sum_ex_impl'_typed n Γ A B :
  type_wf n A →
  type_wf n B →
  TY n; Γ ⊢ sum_ex_impl' : sum_ex_type A B.
Proof.
  intros.
  eapply (typed_pack _ _ _ (A + B)%ty).
  all: asimpl; solve_typing.
Qed.

Lemma sum_ex_impl_equiv n Γ A B :
  ctx_equiv n Γ sum_ex_impl' sum_ex_impl (sum_ex_type A B).
Proof.
  (* TODO: exercise *)
Admitted.


End ex8.
