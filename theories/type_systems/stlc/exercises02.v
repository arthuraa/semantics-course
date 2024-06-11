From stdpp Require Import gmap base relations tactics.
From iris Require Import prelude.
From semantics.ts.stlc Require Import lang notation.
From semantics.ts.stlc Require untyped types.


(** README: Please also download the assigment sheet as a *.pdf from here:
            https://cms.sic.saarland/semantics_ws2324/materials/
            It contains additional explanation and excercises. **)

(** ** Exercise 1: Prove that the structural and contextual semantics are equivalent. *)
(** You will find it very helpful to separately derive the structural rules of the
  structural semantics for the contextual semantics. *)

Lemma contextual_step_beta x e e':
  is_val e' → contextual_step ((λ: x, e) e') (subst' x e' e).
Proof.
  (* TODO: exercise *)
Admitted.


Lemma contextual_step_app_r (e1 e2 e2': expr) :
  contextual_step e2 e2' →
  contextual_step (e1 e2) (e1 e2').
Proof.
  (* TODO: exercise *)
Admitted.


Lemma contextual_step_app_l (e1 e1' e2: expr) :
  is_val e2 →
  contextual_step e1 e1' →
  contextual_step (e1 e2) (e1' e2).
Proof.
  (* TODO: exercise *)
Admitted.


Lemma contextual_step_plus_red (n1 n2 n3: Z) :
  (n1 + n2)%Z = n3 →
  contextual_step (n1 + n2)%E n3.
Proof.
  (* TODO: exercise *)
Admitted.


Lemma contextual_step_plus_r e1 e2 e2' :
  contextual_step e2 e2' →
  contextual_step (Plus e1 e2) (Plus e1 e2').
Proof.
  (* TODO: exercise *)
Admitted.


Lemma contextual_step_plus_l e1 e1' e2 :
  is_val e2 →
  contextual_step e1 e1' →
  contextual_step (Plus e1 e2) (Plus e1' e2).
Proof.
  (* TODO: exercise *)
Admitted.


(** We register these lemmas as hints for [eauto]. *)
#[global]
Hint Resolve contextual_step_beta contextual_step_app_l contextual_step_app_r contextual_step_plus_red contextual_step_plus_l contextual_step_plus_r : core.

Lemma step_contextual_step e1 e2: step e1 e2 → contextual_step e1 e2.
Proof.
  (* TODO: exercise *)
Admitted.


(** Now the other direction. *)
(* You may find it helpful to introduce intermediate lemmas. *)


Lemma contextual_step_step e1 e2:
  contextual_step e1 e2 → step e1 e2.
Proof.
  (* TODO: exercise *)
Admitted.



(** ** Exercise 2: Scott encodings *)
Section scott.
  (* take a look at untyped.v for usefull lemmas and definitions *)
  Import semantics.ts.stlc.untyped.

  (** Scott encoding of Booleans *)
  Definition true_scott : val := 0(* TODO *).
  Definition false_scott : val := 0(* TODO *).

  Lemma true_red (v1 v2 : val) :
    closed [] v1 →
    closed [] v2 →
    rtc step (true_scott v1 v2) v1.
  Proof.
    (* TODO: exercise *)
  Admitted.


  Lemma false_red (v1 v2 : val) :
    closed [] v1 →
    closed [] v2 →
    rtc step (false_scott v1 v2) v2.
  Proof.
    (* TODO: exercise *)
  Admitted.


  (** Scott encoding of Pairs *)
  Definition pair_scott : val := 0(* TODO *).

  Definition fst_scott : val := 0(* TODO *).
  Definition snd_scott : val := 0(* TODO *).

  Lemma fst_red (v1 v2 : val) :
    is_closed [] v1 →
    is_closed [] v2 →
    rtc step (fst_scott (pair_scott v1 v2)) v1.
  Proof.
    (* TODO: exercise *)
  Admitted.


  Lemma snd_red (v1 v2 : val) :
    is_closed [] v1 →
    is_closed [] v2 →
    rtc step (snd_scott (pair_scott v1 v2)) v2.
  Proof.
    (* TODO: exercise *)
  Admitted.


End scott.

Import semantics.ts.stlc.types.

(** ** Exercise 3: type erasure *)
(** Source terms *)
Inductive src_expr :=
| ELitInt (n: Z)
(* Base lambda calculus *)
| EVar (x : string)
| ELam (x : binder) (A: type) (e : src_expr)
| EApp (e1 e2 : src_expr)
(* Base types and their operations *)
| EPlus (e1 e2 : src_expr).

(** The erasure function *)
Fixpoint erase (E: src_expr) : expr :=
0 (* TODO *).

Reserved Notation "Γ '⊢S' e : A" (at level 74, e, A at next level).
Inductive src_typed : typing_context → src_expr → type → Prop :=
| src_typed_var Γ x A :
    Γ !! x = Some A →
    Γ ⊢S (EVar x) : A
| src_typed_lam Γ x E A B :
    (<[ x := A]> Γ) ⊢S E : B →
    Γ ⊢S (ELam (BNamed x) A E) : (A → B)
| src_typed_int Γ z :
    Γ ⊢S (ELitInt z) : Int
| src_typed_app Γ E1 E2 A B :
    Γ ⊢S E1 : (A → B) →
    Γ ⊢S E2 : A →
    Γ ⊢S EApp E1 E2 : B
| src_typed_add Γ E1 E2 :
    Γ ⊢S E1 : Int →
    Γ ⊢S E2 : Int →
    Γ ⊢S EPlus E1 E2 : Int
where "Γ '⊢S' E : A" := (src_typed Γ E%E A%ty) : FType_scope.
#[export] Hint Constructors src_typed : core.

Lemma type_erasure_correctness Γ E A:
  (Γ ⊢S E : A)%ty → (Γ ⊢ erase E : A)%ty.
Proof.
  (* TODO: exercise *)
Admitted.


(** ** Exercise 4: Unique Typing *)
Lemma src_typing_unique Γ E A B:
  (Γ ⊢S E : A)%ty → (Γ ⊢S E : B)%ty → A = B.
Proof.
  (* TODO: exercise *)
Admitted.


(** TODO: Is runtime typing (Curry-style) also unique? Prove it or give a counterexample. *)


(** ** Exercise 5: Type Inference *)

Fixpoint type_eq A B :=
  match A, B with
  | Int, Int => true
  | Fun A B, Fun A' B' => type_eq A A' && type_eq B B'
  | _, _ => false
  end.

Lemma type_eq_iff A B: type_eq A B ↔ A = B.
Proof.
  induction A in B |-*; destruct B; simpl; naive_solver.
Qed.

Notation ctx := (gmap string type).
Fixpoint infer_type (Γ: ctx) E :=
  match E with
  | EVar x => Γ !! x
  | ELam (BNamed x) A E =>
    match infer_type (<[x := A]> Γ) E with
    | Some B => Some (Fun A B)
    | None => None
    end
  (* TODO: complete the definition for the remaining cases *)
  | ELitInt l => None (* TODO *)
  | EApp E1 E2 => None (* TODO *)
  | EPlus E1 E2 => None (* TODO *)
  | ELam BAnon A E => None
  end.

(** Prove both directions of the correctness theorem. *)
Lemma infer_type_typing Γ E A:
  infer_type Γ E = Some A → (Γ ⊢S E : A)%ty.
Proof.
  (* TODO: exercise *)
Admitted.


Lemma typing_infer_type Γ E A:
  (Γ ⊢S E : A)%ty → infer_type Γ E = Some A.
Proof.
  (* TODO: exercise *)
Admitted.



(** ** Exercise 6: untypable, safe term *)

(* The exercise asks you to:
  "Give one example if there is such an expression, otherwise prove their non-existence."
  So either finish one section or the other.
*)

Section give_example.
  Definition ust : expr := 0 (* TODO *).

  Lemma ust_safe e':
    rtc step ust e' → is_val e' ∨ reducible e'.
  Proof.
    (* TODO: exercise *)
  Admitted.


  Lemma ust_no_type Γ A:
    ¬ (Γ ⊢ ust : A)%ty.
  Proof.
    (* TODO: exercise *)
  Admitted.

End give_example.

Section prove_non_existence.
  Lemma no_ust :
  ∀ e, (∀ e', rtc step e e' → is_val e' ∨ reducible e') → ∃ A, (∅ ⊢ e : A)%ty.
  Proof.
    (* TODO: exercise *)
  Admitted.

End prove_non_existence.