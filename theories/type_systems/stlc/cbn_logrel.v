From stdpp Require Import base relations.
From iris Require Import prelude.
From semantics.lib Require Import sets maps.
From semantics.ts.stlc Require Import lang notation types parallel_subst.
From Equations Require Import Equations.

Implicit Types
  (Γ : typing_context)
  (v : val)
  (e : expr)
  (A : type).

(** *** Big-Step Semantics for cbn *)
Inductive big_step : expr → val → Prop :=
  | bs_lit (n : Z) :
      big_step (LitInt n) (LitIntV n)
  | bs_lam (x : binder) (e : expr) :
      big_step (Lam x e) (LamV x e)
  | bs_add e1 e2 (z1 z2 : Z) :
      big_step e1 (LitIntV z1) →
      big_step e2 (LitIntV z2) →
      big_step (Plus e1 e2) (LitIntV (z1 + z2))%Z
  | bs_app e1 e2 x e v2 v :
      big_step e1 (@LamV x e) →
      big_step (subst' x e2 e) v →
      big_step (App e1 e2) v
    .
#[export] Hint Constructors big_step : core.


Lemma big_step_vals (v: val): big_step (of_val v) v.
Proof.
  induction v; econstructor.
Qed.

Lemma big_step_inv_vals (v w: val): big_step (of_val v) w → v = w.
Proof.
  destruct v; inversion 1; eauto.
Qed.



(* *** Definition of the logical relation. *)
(* We reuse most of these definitions. *)
Inductive val_or_expr : Type :=
| inj_val : val → val_or_expr
| inj_expr : expr → val_or_expr.

(* Note that we're using a slightly modified termination argument here. *)
Equations type_size (t : type) : nat :=
  type_size Int := 1;
  type_size (Fun A B) := type_size A + type_size B + 2.
Equations mut_measure (ve : val_or_expr) (t : type) : nat :=
  mut_measure (inj_val _) t := type_size t;
  mut_measure (inj_expr _) t := 1 + type_size t.

Equations type_interp (ve : val_or_expr) (t : type) : Prop by wf (mut_measure ve t) := {
  type_interp (inj_val v) Int =>
    ∃ z : Z, v = z ;
  type_interp (inj_val v) (A → B) =>
    ∃ x e, v = @LamV x e ∧ closed (x :b: nil) e ∧
      ∀ e',
        type_interp (inj_expr e') A →
        type_interp (inj_expr (subst' x e' e)) B;

  type_interp (inj_expr e) t =>
    (* we now need to explicitly require that expressions here are closed so
       that we can apply them to lambdas directly. *)
    ∃ v, big_step e v ∧ closed [] e ∧ type_interp (inj_val v) t
}.
Next Obligation.
  repeat simp mut_measure; simp type_size; lia.
Qed.
Next Obligation.
  simp mut_measure. simp type_size.
  destruct A; repeat simp mut_measure; repeat simp type_size; lia.
Qed.

(* We derive the expression/value relation. *)
Notation sem_val_rel t v := (type_interp (inj_val v) t).
Notation sem_expr_rel t e := (type_interp (inj_expr e) t).

Notation 𝒱 t v := (sem_val_rel t v).
Notation ℰ t v := (sem_expr_rel t v).


(* *** Semantic typing of contexts *)
Implicit Types
  (θ : gmap string expr).

Inductive sem_context_rel : typing_context → (gmap string expr) → Prop :=
  | sem_context_rel_empty : sem_context_rel ∅ ∅
  (* contexts may now contain arbitrary (semantically well-typed) expressions
     as opposed to just values. *)
  | sem_context_rel_insert Γ θ e x A :
    ℰ A e →
    sem_context_rel Γ θ →
    sem_context_rel (<[x := A]> Γ) (<[x := e]> θ).

Notation 𝒢 := sem_context_rel.

(* The semantic typing judgement. Note that we require e to be closed under Γ. *)
Definition sem_typed Γ e A :=
  closed (elements (dom Γ)) e ∧
  ∀ θ, 𝒢 Γ θ → ℰ A (subst_map θ e).
Notation "Γ ⊨ e : A" := (sem_typed Γ e A) (at level 74, e, A at next level).


(* We start by proving a couple of helper lemmas that will be useful later. *)

Lemma sem_expr_rel_of_val A v:
  ℰ A v → 𝒱 A v.
Proof.
  simp type_interp.
  intros (v' & ->%big_step_inv_vals & Hv').
  apply Hv'.
Qed.



Lemma val_rel_closed v A:
  𝒱 A v → closed [] v.
Proof.
  induction A; simp type_interp.
  - intros [z ->]. done.
  - intros (x & e & -> & Hcl & _). done.
Qed.
Lemma val_inclusion A v:
  𝒱 A v → ℰ A v.
Proof.
  intros H. simp type_interp. eauto using big_step_vals, val_rel_closed.
Qed.
Lemma expr_rel_closed e A :
  ℰ A e → closed [] e.
Proof.
  simp type_interp. intros (v & ? & ? & ?). done.
Qed.
Lemma sem_context_rel_closed Γ θ:
  𝒢 Γ θ → subst_closed [] θ.
Proof.
  induction 1; rewrite /subst_closed.
  - naive_solver.
  - intros y e'. rewrite lookup_insert_Some.
    intros [[-> <-]|[Hne Hlook]].
    + by eapply expr_rel_closed.
    + eapply IHsem_context_rel; last done.
Qed.


(* This is essentially an inversion lemma for 𝒢 *)
Lemma sem_context_rel_exprs Γ θ x A :
  sem_context_rel Γ θ →
  Γ !! x = Some A →
  ∃ e, θ !! x = Some e ∧ ℰ A e.
Proof.
  induction 1 as [|Γ θ e y B Hvals Hctx IH].
  - naive_solver.
  - rewrite lookup_insert_Some. intros [[-> ->]|[Hne Hlook]].
    + eexists; first by rewrite lookup_insert.
    + eapply IH in Hlook as (e' & Hlook & He).
      eexists; split; first by rewrite lookup_insert_ne.
      done.
Qed.

Lemma sem_context_rel_dom Γ θ :
  𝒢 Γ θ → dom Γ = dom θ.
Proof.
  induction 1.
  - by rewrite !dom_empty.
  - rewrite !dom_insert. congruence.
Qed.




Lemma termination e A :
  (∅ ⊢ e : A)%ty →
  ∃ v, big_step e v.
Proof.
  (* You may want to add suitable intermediate lemmas, like we did for the cbv
     logical relation as seen in the lecture. *)
  (* TODO: exercise *)
Admitted.

