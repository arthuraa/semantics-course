From stdpp Require Import gmap base relations.
From iris Require Import prelude.
From semantics.lib Require Export facts.
From semantics.ts.systemf Require Import lang notation parallel_subst types bigstep tactics binary_logrel.
From semantics.ts.systemf Require church_encodings.

Import church_encodings.


(* we first prove some helpful lemmas *)

Lemma big_step_bind e v w K:
  big_step e v → big_step (fill K v) w → big_step (fill K e) w.
Proof.
  intros Hbs; induction K in w |-*; simpl.
  { intros ->%big_step_val. done. }
  all: inversion 1; subst; by econstructor; eauto.
Qed.

Lemma big_step_bind_inv e w K:
  big_step (fill K e) w → ∃ v, big_step e v ∧ big_step (fill K v) w.
Proof.
  induction K in w |-*; simpl.
  { intros ?; eexists _; split; first done. by eapply big_step_of_val. }
  all: inversion 1; subst; edestruct IHK as [? [? ?]]; eauto.
Qed.


Lemma big_step_det e v w:
  big_step e v → big_step e w → v = w.
Proof.
  induction 1 in w |-*; inversion 1; subst; eauto 2.
  all: naive_solver.
Qed.


Lemma closure_under_reduction e1 e2 v1 v2 δ A:
  big_step e1 v1 →
  big_step e2 v2 →
  𝒱 A δ v1 v2 →
  ℰ A δ e1 e2.
Proof. simp type_interp. eauto. Qed.


Lemma closure_under_partial_reduction e1 e2 v1 v2 K1 K2 δ A:
  big_step e1 v1 →
  big_step e2 v2 →
  ℰ A δ (fill K1 v1) (fill K2 v2) →
  ℰ A δ (fill K1 e1) (fill K2 e2).
Proof.
  simp type_interp. intros Hbs1 Hbs2 (v3 & v4 & Hbs3 & Hbs4 & Hty).
  eexists _, _. eauto using big_step_bind.
Qed.


Lemma closure_under_expansion e1 e2 v1 v2 K1 K2 δ A:
  big_step e1 v1 →
  big_step e2 v2 →
  ℰ A δ (fill K1 e1) (fill K2 e2) →
  ℰ A δ (fill K1 v1) (fill K2 v2).
Proof.
  simp type_interp. intros Hbs1 Hbs2 (v3 & v4 & Hbs3 & Hbs4 & Hty).
  eapply big_step_bind_inv in Hbs3 as [? [Hr1 Hbs3]].
  eapply big_step_bind_inv in Hbs4 as [? [Hr2 Hbs4]].
  eapply big_step_det in Hr1; last apply Hbs1.
  eapply big_step_det in Hr2; last apply Hbs2.
  subst. eauto.
Qed.

Lemma tforall_expand (v1 v2 v3 v4 : val) δ A:
  (∀ τ, ℰ A (τ.:δ) (v1 <>) (v2 <>)) →
  𝒱 (∀: A) δ v1 v3 →
  𝒱 (∀: A) δ v2 v4 →
  𝒱 (∀: A) δ v1 v2.
Proof.
  simp type_interp.
  intros Hty (e1 & e2 & -> & -> & Hc1 & Hc2 & Hty2) (e3 & e4 & -> & -> & Hc3 & Hc4 & Hty3).
  eexists _, _. split_and!; eauto. intros τ. specialize (Hty τ).
  revert Hty. simp type_interp.
  intros (v1 & v2 & Hbs1 & Hbs2 & Hty).
  inversion Hbs1; subst. inversion Hbs2; subst. inversion H0; subst. inversion H2; subst.
  eexists _, _. split_and!; done.
Qed.

Lemma tforall_reduce v1 v2 δ A τ:
  𝒱 (∀: A) δ v1 v2 →
  ℰ A (τ.:δ) (v1 <>) (v2 <>).
Proof.
  simp type_interp. intros (? & ? & -> & -> & ? & ? & Hty).
  specialize (Hty τ). revert Hty.
  simp type_interp. intros (? & ? & ? & ? & Hval).
  eexists _, _. split_and!; eauto using big_step.
Qed.


Lemma fun_expand (e1 e2 e3 e4 : expr) δ A B:
  (∀ v w, 𝒱 A δ v w → ℰ B δ (e1 v) (e2 w)) →
  ℰ (A → B) δ e1 e3 →
  ℰ (A → B) δ e4 e2 →
  ℰ (A → B) δ e1 e2.
Proof.
  simp type_interp.
  intros Hty (v1 & v3 & Hbs1 & Hbs3 & Hty13) (v2 & v4 & Hbs2 & Hbs4 & Hty24).
  simp type_interp in Hty13. simp type_interp in Hty24.
  destruct Hty13 as (x1 & x3 & e1' & e3' & -> & -> & Hc1 & Hc3 & _),
           Hty24 as (x2 & x4 & e2' & e4' & -> & -> & Hc2 & Hc4 & _).
  eexists _, _. split_and!; eauto. simp type_interp.
  eexists _, _, _, _. split_and!; eauto.

  intros v' w' Hty'. specialize (Hty _ _ Hty').
  simp type_interp. simp type_interp in Hty.
  destruct Hty as (v1 & v2 & Hbs1' & Hbs2' & Hval).
  eexists _, _. split_and!; last done.
  - eapply big_step_bind_inv with (K := AppLCtx HoleCtx v') in Hbs1' as [u1 [Hu1 Hu2]].
    eapply big_step_det in Hu1; last by apply Hbs1.
    subst u1. simpl in Hu2. inversion Hu2; subst. eapply big_step_val in H2. inversion H1; subst.
    done.
  - eapply big_step_bind_inv with (K := AppLCtx HoleCtx w') in Hbs2' as [u1 [Hu1 Hu2]].
    eapply big_step_det in Hu1; last by apply Hbs4.
    subst u1. simpl in Hu2. inversion Hu2; subst. eapply big_step_val in H2. inversion H1; subst.
    done.
Qed.


Lemma fun_reduce e1 e2 δ A B:
  ℰ (A → B) δ e1 e2 →
  (∀ v w, 𝒱 A δ v w → ℰ B δ (e1 v) (e2 w)).
Proof.
  simp type_interp. intros (? & ? & Hbs1 & Hbs2 & Hty) v w Hval.
  simp type_interp in Hty. destruct Hty as (? & ? & e1' & e3' & -> & -> & ? & ? & Hrest).
  specialize (Hrest  _ _ Hval).
  simp type_interp in Hrest.
  destruct Hrest as (v' & w' & ? & ? & Hval').
  simp type_interp. eexists _, _; split_and!; eauto using big_step, big_step_of_val.
Qed.


Lemma bind e1 e2 K1 K2 δ δ' A B:
  ℰ A δ e1 e2 →
  (∀ v w, 𝒱 A δ v w → ℰ B δ' (fill K1 v) (fill K2 w)) →
  ℰ B δ' (fill K1 e1) (fill K2 e2).
Proof.
  simp type_interp. intros (v & w & Hbs1 & Hbs2 & Hty) Hcont.
  specialize (Hcont v w Hty). simp type_interp in Hcont.
  destruct Hcont as (v' & w' & Hbs1' & Hbs2' & Hcont).
  eexists _, _. split_and!; eauto using big_step_bind.
Qed.

(* faithfulness of bool *)

Definition eta_bool (e: expr) : expr :=
  e <> bool_true bool_false.


Lemma bool_type_full (v w f g : val) δ :
  closed [] v →
  closed [] w →
  type_interp (inj_val f g) bool_type δ →
  ∃ b, (b = v ∨ b = w) ∧ (big_step (f <> v w) b ∧ big_step (g <> v w) b).
Proof.
  intros Hc1 Hc2.
  rewrite /bool_type. simp type_interp.
  intros (e1 & e2 & -> & -> & Hcl1 & Hcl2 & Hty).
  specialize_sem_type Hty with (λ u1 u2, (u1 = u2 ∧ u2 = v) ∨ (u1 = u2 ∧ u2 = w)) as B.
  { intros u1 u2 [[-> ->]|[-> ->]]; split; done. }
  simp type_interp in Hty. destruct Hty as (u3 & u4 & Hbs1 & Hbs2 & Hu34).
  simp type_interp in Hu34. destruct Hu34 as (x1 & x1' & e3 & e3' & -> & -> & ? & ? & Hty).
  opose proof* (Hty v v) as Hty; first simp type_interp; simpl; eauto.

  simp type_interp in Hty. destruct Hty as (u5 & u6 & Hbs3 & Hbs4 & Hu56).
  simp type_interp in Hu56. destruct Hu56 as (x2 & x2' & e4 & e4' & -> & -> & ? & ? & Hty).
  opose proof* (Hty w w) as Hty; first simp type_interp; simpl; eauto.

  simp type_interp in Hty. destruct Hty as (u7 & u8 & Hbs5 & Hbs6 & Hu78).
  simp type_interp in Hu78. simpl in Hu78. destruct Hu78 as [[-> ->] | [-> ->]].
  - exists v. split; first naive_solver.
    split; repeat econstructor; eauto using big_step_of_val.
  - exists w. split; first naive_solver.
    split; repeat econstructor; eauto using big_step_of_val.
Qed.


Lemma bool_true_sem_bool δ: 𝒱 bool_type δ bool_true bool_true.
Proof.
  assert (TY 0; ∅ ⊢ bool_true: bool_type) as Hty by solve_typing.
  eapply sem_soundness in Hty as (Htycl1 & Htycl2 & Hty).
  opose proof* (Hty ∅ ∅ δ) as Hty; first constructor.
  by eapply sem_expr_rel_of_val.
Qed.

Lemma bool_false_sem_bool δ: 𝒱 bool_type δ bool_false bool_false.
Proof.
  assert (TY 0; ∅ ⊢ bool_false: bool_type) as Hty by solve_typing.
  eapply sem_soundness in Hty as (Htycl1 & Htycl2 & Hty).
  opose proof* (Hty ∅ ∅ δ) as Hty; first constructor.
  by eapply sem_expr_rel_of_val.
Qed.


Lemma bool_faithful Δ Γ e:
  TY Δ; Γ ⊢ e: bool_type → ctx_equiv Δ Γ e (eta_bool e) bool_type.
Proof.
  intros Hty. eapply soundness_wrt_ctx_equiv; [solve_typing..].
  split_and!. 1-2: apply syn_typed_closed in Hty; naive_solver.
  intros θ1 θ2 δ Hctx. eapply sem_soundness in Hty as (Htycl1 & Htycl2 & Hty).
  specialize (Hty θ1 θ2 δ Hctx). simp type_interp in Hty.
  replace (subst_map θ2 (eta_bool e)) with (eta_bool (subst_map θ2 e)); last first.
  { simpl; rewrite lookup_delete_ne //= !lookup_delete //. }
  destruct Hty as (v1 & v2 & Hbs1 & Hbs2 & Hty).
  eapply closure_under_partial_reduction with (K1 := HoleCtx) (K2:= (AppLCtx (AppLCtx (TAppCtx HoleCtx) bool_true) bool_false)); eauto.
  simpl; change (v2 <> _ _)%E with (eta_bool v2). clear Hctx Hbs1 Hbs2.


  generalize Hty=> Hfull.
  eapply (bool_type_full bool_true bool_false) in Hfull; [|done..].
  destruct Hfull as (b & Hopt & Hv1b & Hv2b).
  eapply closure_under_reduction; eauto using big_step_of_val.

  assert (𝒱 bool_type δ b b) as Hb.
  { destruct Hopt; subst; eauto using bool_true_sem_bool, bool_false_sem_bool. }

  eapply tforall_expand; eauto.

  intros R. generalize Hty=>Hty'.

  (* we have to evaluate these assumptions along the way *)
  rewrite /bool_type in Hb, Hty'.
  eapply tforall_reduce with (τ := R) in Hb.
  eapply tforall_reduce with (τ := R) in Hty'.

  eapply fun_expand; eauto.
  intros a1 a2 Ha12.
  eapply fun_reduce in Hb; last done.
  eapply fun_reduce in Hty'; last done.

  eapply fun_expand; eauto.
  intros b1 b2 Hb12.
  simp type_interp in Ha12; simpl in Ha12.
  simp type_interp in Hb12; simpl in Hb12.
  clear Hb Hty'.

  eapply closure_under_expansion with
  (K1:= (AppLCtx (AppLCtx (TAppCtx HoleCtx) a1) b1))
  (K2:= (AppLCtx (AppLCtx (TAppCtx HoleCtx) a2) b2));
  [by eapply big_step_of_val | eapply Hv2b|]; cbn [fill].

  pose_sem_type (λ v w, (v = a1 ∧ w = bool_true) ∨ (v = b1 ∧ w = bool_false)) as τ.
  { apply sem_type_closed_val in Ha12, Hb12. naive_solver. }

  eapply bind with
    (K1 := HoleCtx)
    (K2 := AppLCtx (AppLCtx (TAppCtx HoleCtx) a2) b2)
    (A := (#0)%ty)
    (δ := τ.:δ).
  { eapply fun_reduce.
    eapply fun_reduce.
    eapply tforall_reduce.
    exact Hty.
    - simp type_interp. simpl. auto.
    - simp type_interp. simpl. auto. }
  simpl. intros v w Hty'. simp type_interp in Hty'. simpl in Hty'. 
  destruct Hty' as [[-> ->]|[-> ->]].
  - simp type_interp. exists a1, a2. split_and!.
    + by apply big_step_of_val.
    + simpl. bs_step_det.
      rewrite subst_is_closed_nil; first by apply big_step_of_val.
      apply sem_type_closed_val in Ha12. naive_solver.
    + simp type_interp.
  - simp type_interp. exists b1, b2. split_and!.
    + by apply big_step_of_val.
    + simpl. bs_step_det. by apply big_step_of_val.
    + simp type_interp.
Qed.
