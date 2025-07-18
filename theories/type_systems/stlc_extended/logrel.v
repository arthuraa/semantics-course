From stdpp Require Import gmap base relations.
From iris Require Import prelude.
From semantics.ts.stlc_extended Require Import lang notation parallel_subst types bigstep.
From semantics.ts.stlc_extended Require Import lang notation parallel_subst types bigstep.
From Equations Require Export Equations.



(** * Logical relation for the extended STLC *)

Implicit Types
  (Γ : typing_context)
  (v : val)
  (e : expr)
  (A : type).


(* *** Definition of the logical relation. *)

Inductive val_or_expr : Type :=
| inj_val : val → val_or_expr
| inj_expr : expr → val_or_expr.

Equations type_size (A : type) : nat :=
  type_size Int := 1;
  type_size (A → B) := type_size A + type_size B + 1;
  type_size (A × B) := type_size A + type_size B + 1;
  type_size (A + B) := max (type_size A) (type_size B) + 1.
Equations mut_measure (ve : val_or_expr) (t : type) : nat :=
  mut_measure (inj_val _) t := type_size t;
  mut_measure (inj_expr _) t := 1 + type_size t.


Equations type_interp (ve : val_or_expr) (t : type) : Prop by wf (mut_measure ve t) := {
  type_interp (inj_val v) Int =>
    ∃ z : Z, v = #z ;
  type_interp (inj_val v) (A × B) =>
    (* TODO: add type interpretation *) 
    False;
  type_interp (inj_val v) (A + B) =>
    (* TODO: add type interpretation *)
    False;
  type_interp (inj_val v) (A → B) =>
    ∃ x e, v = @LamV x e ∧ closed (x :b: nil) e ∧
      ∀ v',
        type_interp (inj_val v') A →
        type_interp (inj_expr (subst' x v' e)) B;

  type_interp (inj_expr e) t =>
    ∃ v, big_step e v ∧ type_interp (inj_val v) t
}.
Next Obligation.
  repeat simp mut_measure; simp type_size; lia.
Qed.
Next Obligation.
  simp mut_measure. simp type_size.
  destruct A; repeat simp mut_measure; repeat simp type_size; lia.
Qed.
(* Uncomment the following once you have amended the type interpretation to
   solve the new obligations: *)
(*
Next Obligation. repeat simp mut_measure; simp type_size; lia. Qed.
Next Obligation. repeat simp mut_measure; simp type_size; lia. Qed.
Next Obligation. repeat simp mut_measure; simp type_size; lia. Qed.
Next Obligation. repeat simp mut_measure; simp type_size; lia. Qed.
*)


Notation sem_val_rel t v := (type_interp (inj_val v) t).
Notation sem_expr_rel t e := (type_interp (inj_expr e) t).

Notation 𝒱 t v := (sem_val_rel t v).
Notation ℰ t v := (sem_expr_rel t v).


(* *** Semantic typing of contexts *)
Implicit Types
  (θ : gmap string expr).

Inductive sem_context_rel : typing_context → (gmap string expr) → Prop :=
  | sem_context_rel_empty : sem_context_rel ∅ ∅
  | sem_context_rel_insert Γ θ v x A :
    𝒱 A v →
    sem_context_rel Γ θ →
    sem_context_rel (<[x := A]> Γ) (<[x := of_val v]> θ).

Notation 𝒢 := sem_context_rel.

Definition sem_typed Γ e A :=
  closed (elements (dom Γ)) e ∧
  ∀ θ, 𝒢 Γ θ → ℰ A (subst_map θ e).
Notation "Γ ⊨ e : A" := (sem_typed Γ e A) (at level 74, e, A at next level).


(* We start by proving a couple of helper lemmas that will be useful later. *)

Lemma sem_expr_rel_of_val A v:
  ℰ A v → 𝒱 A v.
Proof.
  simp type_interp.
  intros (v' & ->%big_step_val & Hv').
  apply Hv'.
Qed.
Lemma val_inclusion A v:
  𝒱 A v → ℰ A v.
Proof.
  intros H. simp type_interp. eauto using big_step_of_val.
Qed.



Lemma val_rel_closed v A:
  𝒱 A v → closed [] v.
Proof.
  induction A in v |-*; simp type_interp.
  - intros [z ->]. done.
  - intros (x & e & -> & Hcl & _). done.
  (* TODO: exercise *)
Admitted.

Lemma sem_context_rel_closed Γ θ:
  𝒢 Γ θ → subst_closed [] θ.
Proof.
  induction 1; rewrite /subst_closed.
  - naive_solver.
  - intros y e. rewrite lookup_insert_Some.
    intros [[-> <-]|[Hne Hlook]].
    + by eapply val_rel_closed.
    + eapply IHsem_context_rel; last done.
Qed.


(* This is essentially an inversion lemma for 𝒢 *)
Lemma sem_context_rel_vals Γ θ x A :
  𝒢 Γ θ →
  Γ !! x = Some A →
  ∃ e v, θ !! x = Some e ∧ to_val e = Some v ∧ 𝒱 A v.
Proof.
  induction 1 as [|Γ θ v y B Hvals Hctx IH].
  - naive_solver.
  - rewrite lookup_insert_Some. intros [[-> ->]|[Hne Hlook]].
    + do 2 eexists. split; first by rewrite lookup_insert_eq.
      split; first by eapply to_of_val. done.
    + eapply IH in Hlook as (e & w & Hlook & He & Hval).
      do 2 eexists; split; first by rewrite lookup_insert_ne.
      split; first done. done.
Qed.

Lemma sem_context_rel_dom Γ θ :
  𝒢 Γ θ → dom Γ = dom θ.
Proof.
  induction 1.
  - by rewrite !dom_empty.
  - rewrite !dom_insert. congruence.
Qed.


(* *** Compatibility lemmas *)
Lemma compat_int Γ z : Γ ⊨ (LitInt z) : Int.
Proof.
  split; first done.
  intros θ _. simp type_interp.
  exists #z. split; simpl.
  - constructor.
  - simp type_interp. eauto.
Qed.

Lemma compat_var Γ x A :
  Γ !! x = Some A →
  Γ ⊨ (Var x) : A.
Proof.
  intros Hx. split.
  { eapply bool_decide_pack, elem_of_elements, elem_of_dom_2, Hx. }
  intros θ Hctx; simpl.
  eapply sem_context_rel_vals in Hx as (e & v & He & Heq & Hv); last done.
  rewrite He. simp type_interp. exists v. split; last done.
  rewrite -(of_to_val _ _ Heq).
  by apply big_step_of_val.
Qed.

Lemma compat_app Γ e1 e2 A B :
  Γ ⊨ e1 : (A → B) →
  Γ ⊨ e2 : A →
  Γ ⊨ (e1 e2) : B.
Proof.
  intros [Hfuncl Hfun] [Hargcl Harg]. split.
  { unfold closed. simpl. eauto. }
  intros θ Hctx; simpl.
  specialize (Hfun _ Hctx). simp type_interp in Hfun. destruct Hfun as (v1 & Hbs1 & Hv1).
  simp type_interp in Hv1. destruct Hv1 as (x & e & -> & Hcl & Hv1).
  specialize (Harg _ Hctx). simp type_interp in Harg.
  destruct Harg as (v2 & Hbs2 & Hv2).

  apply Hv1 in Hv2.
  simp type_interp in Hv2. destruct Hv2 as (v & Hbsv & Hv).

  simp type_interp.
  exists v. split; last done.
  eauto.
Qed.


(* Compatibility for [lam] unfortunately needs a very technical helper lemma. *)
Lemma lam_closed Γ θ (x : string) A e :
  closed (elements (dom (<[x:=A]> Γ))) e → 
  𝒢 Γ θ → 
  closed [] (Lam x (subst_map (delete x θ) e)).
Proof.
  intros Hcl Hctxt.
  eapply subst_map_closed'_2.
  - eapply is_closed_weaken; first done.
    rewrite dom_delete dom_insert (sem_context_rel_dom Γ θ) //.
    intros y. destruct (decide (x = y)); set_solver.
  - eapply subst_closed_weaken, sem_context_rel_closed; last done.
    + set_solver.
    + apply map_delete_subseteq.
Qed.
Lemma compat_lam Γ x e A B :
  (<[ x := A ]> Γ) ⊨ e : B →
  Γ ⊨ (Lam (BNamed x) e) : (A → B).
Proof.
  intros [Hbodycl Hbody]. split.
  { unfold closed in *. cbn in *. eapply is_closed_weaken; first eassumption.
    set_solver. }
  intros θ Hctxt. simpl. simp type_interp.
  eexists.
  split; first by eauto.
  simp type_interp.
  eexists x, _. split; first reflexivity.
  split; first by eapply lam_closed.
  intros v' Hv'.
  specialize (Hbody (<[ x := of_val v']> θ)).
  simpl. rewrite subst_subst_map; last by eapply sem_context_rel_closed.
  apply Hbody.
  apply sem_context_rel_insert; done.
Qed.
Lemma compat_lam_anon Γ e A B :
  Γ ⊨ e : B →
  Γ ⊨ (Lam BAnon e) : (A → B).
Proof.
  intros [Hbodycl Hbody]. split; first done.
  intros θ Hctxt. simpl. simp type_interp.
  eexists.
  split; first by eauto.
  simp type_interp.
  eexists _, _. split; first reflexivity.
  split.
  { simpl. eapply subst_map_closed'_2; simpl.
    - by erewrite <-sem_context_rel_dom.
    - by eapply sem_context_rel_closed. }
  naive_solver.
Qed.

Lemma compat_add Γ e1 e2 :
  Γ ⊨ e1 : Int →
  Γ ⊨ e2 : Int →
  Γ ⊨ (e1 + e2) : Int.
Proof.
  intros [Hcl1 He1] [Hcl2 He2]. split.
  { unfold closed in *. naive_solver. }
  intros θ Hctx.
  simp type_interp.
  specialize (He1 _ Hctx). specialize (He2 _ Hctx).
  simp type_interp in He1. simp type_interp in He2.

  destruct He1 as (v1 & Hb1 & Hv1).
  destruct He2 as (v2 & Hb2 & Hv2).
  simp type_interp in Hv1, Hv2.
  destruct Hv1 as (z1 & ->). destruct Hv2 as (z2 & ->).

  exists #(z1 + z2). split.
  - constructor; done.
  - exists (z1 + z2)%Z. done.

Qed.




Lemma sem_soundness Γ e A :
  (Γ ⊢ e : A)%ty →
  Γ ⊨ e : A.
Proof.
  induction 1.
  - by apply compat_var.
  - by apply compat_lam.
  - by apply compat_lam_anon.
  - apply compat_int.
  - by eapply compat_app.
  - by apply compat_add.
  (* add compatibility lemmas for the new rules here. *)
  (* TODO: exercise *)
Admitted.


Lemma termination e A :
  (∅ ⊢ e : A)%ty →
  ∃ v, big_step e v.
Proof.
  intros [Hsemcl Hsem]%sem_soundness.
  specialize (Hsem ∅).
  simp type_interp in Hsem.
  rewrite subst_map_empty in Hsem.
  destruct Hsem as (v & Hbs & _); last eauto.
  constructor.
Qed.

