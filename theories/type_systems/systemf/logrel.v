From stdpp Require Import gmap base relations.
From iris Require Import prelude.
From semantics.lib Require Export facts.
From semantics.ts.systemf Require Import lang notation parallel_subst types bigstep.
From Equations Require Export Equations.


(** * Logical relation for SystemF *)

Implicit Types
  (Δ : nat)
  (Γ : typing_context)
  (v : val)
  (α : var)
  (e : expr)
  (A : type).

(* *** Definition of the logical relation. *)
(* In Rocq, we need to make argument why the logical relation is well-defined
   precise: 
   In particular, we need to show that the mutual recursion between the value
   relation and the expression relation, which are defined in terms of each
   other, terminates. We therefore define a termination measure [mut_measure]
   that makes sure that for each recursive call, we either decrease the size of
   the type or switch from the expression case to the value case.

   We use the Equations package to define the logical relation, as it's tedious
   to make the termination argument work with Rocq's built-in support for
   recursive functions---but under the hood, Equations also just encodes it as
   a Rocq Fixpoint.
 *)
Inductive val_or_expr : Type :=
| inj_val : val → val_or_expr
| inj_expr : expr → val_or_expr.

(* The [type_size] function essentially computes the size of the "type tree". *)
(* Note that we have added some additional primitives to make our (still
   simple) language more expressive. *)
Equations type_size (A : type) : nat :=
  type_size Int := 1;
  type_size Bool := 1;
  type_size Unit := 1;
  type_size (A → B) := type_size A + type_size B + 1;
  type_size (#α) := 1;
  type_size (∀: A) := type_size A + 2;
  type_size (∃: A) := type_size A + 2;
  type_size (A × B) := type_size A + type_size B + 1;
  type_size (A + B) := max (type_size A) (type_size B) + 1.
(* The definition of the expression relation uses the value relation -- therefore, it needs to be larger, and we add [1]. *)
Equations mut_measure (ve : val_or_expr) (t : type) : nat :=
  mut_measure (inj_val _) t := type_size t;
  mut_measure (inj_expr _) t := 1 + type_size t.

(** A semantic type consists of a value-predicate and a proof of closedness *)
Record sem_type := mk_ST {
  sem_type_car :> val → Prop;
  sem_type_closed_val v : sem_type_car v → is_closed [] (of_val v);
  }.
(** Two tactics we will use later on.
  [pose_sem_type P as N] defines a semantic type at name [N] with the value predicate [P].
  [specialize_sem_type S with P as N] specializes a universal quantifier over sem types in [S] with
    a semantic type with predicate [P], giving it the name [N].
 *)
(* slightly complicated formulation to make the proof term [p] opaque and prevent it from polluting the context *)
Tactic Notation "pose_sem_type" uconstr(P) "as" ident(N) :=
  let p := fresh "__p" in
  unshelve refine ((λ p, let N := (mk_ST P p) in _) _); first (simpl in p); cycle 1.
Tactic Notation "specialize_sem_type" constr(S) "with" uconstr(P) "as" ident(N) :=
  pose_sem_type P as N; last specialize (S N).

(** We represent type variable assignments [δ] as lists of semantic types.
  The variable #n (in De Bruijn representation) is mapped to the [n]-th element of the list.
 *)
Definition tyvar_interp := nat → sem_type.
Implicit Types
  (δ : tyvar_interp)
  (τ : sem_type).

(** The logical relation *)
Equations type_interp (c : val_or_expr) (t : type) δ : Prop by wf (mut_measure c t) := {
  type_interp (inj_val v) Int δ =>
    ∃ z : Z, v = #z ;
  type_interp (inj_val v) Bool δ =>
    ∃ b : bool, v = #b ;
  type_interp (inj_val v) Unit δ =>
    v = #LitUnit ;
  type_interp (inj_val v) (A × B) δ =>
    ∃ v1 v2 : val, v = (v1, v2)%V ∧ type_interp (inj_val v1) A δ ∧ type_interp (inj_val v2) B δ;
  type_interp (inj_val v) (A + B) δ =>
    (∃ v' : val, v = InjLV v' ∧ type_interp (inj_val v') A δ) ∨
    (∃ v' : val, v = InjRV v' ∧ type_interp (inj_val v') B δ);
  type_interp (inj_val v) (A → B) δ =>
    ∃ x e, v = LamV x e ∧ is_closed (x :b: nil) e ∧
      ∀ v',
        type_interp (inj_val v') A δ →
        type_interp (inj_expr (subst' x (of_val v') e)) B δ;
  (** Type variable case *)
  type_interp (inj_val v) (#α) δ =>
    (δ α).(sem_type_car) v;
  (** ∀ case *)
  type_interp (inj_val v) (∀: A) δ =>
    ∃ e, v = TLamV e ∧ is_closed [] e ∧
      ∀ τ, type_interp (inj_expr e) A (τ .: δ);
  (** ∃ case *)
  type_interp (inj_val v) (∃: A) δ =>
    ∃ v', v = PackV v' ∧
      ∃ τ : sem_type, type_interp (inj_val v') A (τ .: δ);

  type_interp (inj_expr e) t δ =>
    ∃ v, big_step e v ∧ type_interp (inj_val v) t δ
}.
Next Obligation. repeat simp mut_measure; simp type_size; lia. Qed.
Next Obligation. repeat simp mut_measure; simp type_size; lia. Qed.
Next Obligation. repeat simp mut_measure; simp type_size; lia. Qed.
Next Obligation.
  simp mut_measure. simp type_size.
  destruct A; repeat simp mut_measure; repeat simp type_size; lia.
Qed.
Next Obligation. repeat simp mut_measure; simp type_size; lia. Qed.
Next Obligation. repeat simp mut_measure; simp type_size; lia. Qed.
Next Obligation. repeat simp mut_measure; simp type_size; lia. Qed.
Next Obligation. repeat simp mut_measure; simp type_size; lia. Qed.

(** Value relation and expression relation *)
Notation sem_val_rel A δ v := (type_interp (inj_val v) A δ).
Notation sem_expr_rel A δ e := (type_interp (inj_expr e) A δ).

Notation 𝒱 A δ v := (sem_val_rel A δ v).
Notation ℰ A δ v := (sem_expr_rel A δ v).


(* *** Semantic typing of contexts *)
Implicit Types
  (θ : gmap string expr).
Inductive sem_context_rel (δ : tyvar_interp) : typing_context → (gmap string expr) → Prop :=
  | sem_context_rel_empty : sem_context_rel δ ∅ ∅
  | sem_context_rel_insert Γ θ v x A :
    𝒱 A δ v →
    sem_context_rel δ Γ θ →
    sem_context_rel δ (<[x := A]> Γ) (<[x := of_val v]> θ).

Notation 𝒢 := sem_context_rel.



(* Semantic typing judgement *)
Definition sem_typed Δ Γ e A :=
  is_closed (elements (dom Γ)) e ∧
  ∀ θ δ, 𝒢 δ Γ θ → ℰ A δ (subst_map θ e).
Notation "'TY' Δ ; Γ ⊨ e : A" := (sem_typed Δ Γ e A) (at level 74, e, A at next level).


Lemma val_rel_closed v δ A:
  𝒱 A δ v → is_closed [] (of_val v).
Proof.
  induction A as [ | | | | | A IHA | | A IH1 B IH2 | A IH1 B IH2] in v, δ |-*; simp type_interp.
  - eapply sem_type_closed_val.
  - intros [z ->]. done.
  - intros [b ->]. done.
  - intros ->. done.
  - intros (e & -> & ? & _). done.
  - intros (v' & -> & (τ & Hinterp)). simpl. by eapply IHA.
  - intros (x & e & -> & ? & _). done.
  - intros (v1 & v2 & -> & ? & ?). simpl. apply andb_True. eauto.
  - intros [(v' & -> & ?) | (v' & -> & ?)]; simpl; eauto.
Qed.

(** Interpret a syntactic type *)
Program Definition interp_type A δ : sem_type := {|
  sem_type_car := fun v => 𝒱 A δ v;
|}.
Next Obligation. by eapply val_rel_closed. Qed.


(* We start by proving a couple of helper lemmas that will be useful later. *)

Lemma sem_expr_rel_of_val A δ v :
  ℰ A δ (of_val v) → 𝒱 A δ v.
Proof.
  simp type_interp.
  intros (v' & ->%big_step_val & Hv').
  apply Hv'.
Qed.
Lemma val_inclusion A δ v:
  𝒱 A δ v → ℰ A δ v.
Proof.
  intros H. simp type_interp. eauto using big_step_of_val.
Qed.


Lemma sem_context_rel_closed δ Γ θ:
  𝒢 δ Γ θ → subst_is_closed [] θ.
Proof.
  induction 1.
  - done.
  - intros y e. rewrite lookup_insert_Some.
    intros [[-> <-]|[Hne Hlook]].
    + by eapply val_rel_closed.
    + eapply IHsem_context_rel; last done.
Qed.


(* This is essentially an inversion lemma for 𝒢 *)
Lemma sem_context_rel_vals δ Γ θ x A :
  𝒢 δ Γ θ →
  Γ !! x = Some A →
  ∃ e v, θ !! x = Some e ∧ to_val e = Some v ∧ 𝒱 A δ v.
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

Lemma sem_context_rel_dom δ Γ θ :
  𝒢 δ Γ θ → dom Γ = dom θ.
Proof.
  induction 1.
  - by rewrite !dom_empty.
  - rewrite !dom_insert. congruence.
Qed.


Section boring_lemmas.
  (** The lemmas in this section are all quite boring and expected statements,
    but are quite technical to prove due to De Bruijn binders.
    We encourage you to skip over the proofs of these lemmas.
  *)

  Lemma sem_val_rel_ext B δ δ' v :
    (∀ n v, δ n v ↔ δ' n v) →
    𝒱 B δ v ↔ 𝒱 B δ' v.
  Proof.
    induction B in δ, δ', v |-*; simpl; simp type_interp; eauto; intros Hiff.
    - f_equiv; intros e. f_equiv. f_equiv.
      eapply forall_proper; intros τ.
      simp type_interp. f_equiv. intros w.
      f_equiv. etransitivity; last apply IHB; first done.
      intros [|m] ?; simpl; eauto.
    - f_equiv; intros w. f_equiv. f_equiv. intros τ.
      etransitivity; last apply IHB; first done.
      intros [|m] ?; simpl; eauto.
    - f_equiv. intros ?. f_equiv. intros ?.
      f_equiv. f_equiv. eapply forall_proper. intros x.
      eapply if_iff; first eauto.
      simp type_interp. f_equiv. intros ?. f_equiv.
      eauto.
    - f_equiv. intros ?. f_equiv. intros ?.
      f_equiv. f_equiv; eauto.
    - f_equiv; f_equiv; intros ?; f_equiv; eauto.
  Qed.


  Lemma sem_val_rel_move_ren B δ σ v :
     𝒱 B (λ n, δ (σ n)) v ↔ 𝒱 (rename σ B) δ v.
  Proof.
    induction B in σ, δ, v |-*; simpl; simp type_interp; eauto.
    - f_equiv; intros e. f_equiv. f_equiv.
      eapply forall_proper; intros τ.
      simp type_interp. f_equiv. intros w.
      f_equiv. etransitivity; last apply IHB.
      eapply sem_val_rel_ext; intros [|n] u; asimpl; done.
    - f_equiv; intros w. f_equiv. f_equiv. intros τ.
      etransitivity; last apply IHB.
      eapply sem_val_rel_ext; intros [|n] u.
      +  simp type_interp. done.
      + simpl. rewrite /up. simpl. done.
    - f_equiv. intros ?. f_equiv. intros ?.
      f_equiv. f_equiv. eapply forall_proper. intros x.
      eapply if_iff; first done.
      simp type_interp. f_equiv. intros ?. f_equiv.
      done.
    - f_equiv. intros ?. f_equiv. intros ?.
      f_equiv. f_equiv; done.
    - f_equiv; f_equiv; intros ?; f_equiv; done.
  Qed.


  Lemma sem_val_rel_move_subst B δ σ v :
    𝒱 B (λ n, interp_type (σ n) δ) v ↔ 𝒱 (B.[σ]) δ v.
  Proof.
    induction B in σ, δ, v |-*; simpl; simp type_interp; eauto.
    - f_equiv; intros e. f_equiv. f_equiv.
      eapply forall_proper; intros τ.
      simp type_interp. f_equiv. intros w.
      f_equiv. etransitivity; last apply IHB.
      eapply sem_val_rel_ext; intros [|n] u.
      +  simp type_interp. done.
      + simpl. rewrite /up. simpl.
        etransitivity; last eapply sem_val_rel_move_ren.
        simpl. done.
    - f_equiv; intros w. f_equiv. f_equiv. intros τ.
      etransitivity; last apply IHB.
      eapply sem_val_rel_ext; intros [|n] u.
      +  simp type_interp. done.
      + simpl. rewrite /up. simpl.
        etransitivity; last eapply sem_val_rel_move_ren.
        simpl. done.
    - f_equiv. intros ?. f_equiv. intros ?.
      f_equiv. f_equiv. eapply forall_proper. intros x.
      eapply if_iff; first done.
      simp type_interp. f_equiv. intros ?. f_equiv.
      done.
    - f_equiv. intros ?. f_equiv. intros ?.
      f_equiv. f_equiv; done.
    - f_equiv; f_equiv; intros ?; f_equiv; done.
  Qed.

  Lemma sem_val_rel_move_single_subst A B δ v :
    𝒱 B (interp_type A δ .: δ) v ↔ 𝒱 (B.[A/]) δ v.
  Proof.
    rewrite -sem_val_rel_move_subst. eapply sem_val_rel_ext.
    intros [| n] w; simpl; done.
  Qed.

  Lemma sem_val_rel_cons A δ v τ :
    𝒱 A δ v ↔ 𝒱  A.[ren (+1)] (τ .: δ) v.
  Proof.
    rewrite -sem_val_rel_move_subst; simpl.
    eapply sem_val_rel_ext; done.
  Qed.

  Lemma sem_context_rel_cons Γ δ θ τ :
    𝒢 δ Γ θ →
    𝒢 (τ .: δ) (⤉ Γ) θ.
  Proof.
    induction 1 as [ | Γ θ v x A Hv Hctx IH]; simpl.
    - rewrite fmap_empty. constructor.
    - rewrite fmap_insert. constructor; last done.
      rewrite -sem_val_rel_cons. done.
  Qed.
End boring_lemmas.

(** ** Compatibility lemmas *)

Lemma compat_int Δ Γ z : TY Δ; Γ ⊨ (Lit $ LitInt z) : Int.
Proof.
  split; first done. 
  intros θ δ _. simp type_interp.
  exists #z. split. { simpl. constructor. }
  simp type_interp. eauto.
Qed.

Lemma compat_bool Δ Γ b : TY Δ; Γ ⊨ (Lit $ LitBool b) : Bool.
Proof.
  split; first done. 
  intros θ δ _. simp type_interp.
  exists #b. split. { simpl. constructor. }
  simp type_interp. eauto.
Qed.

Lemma compat_unit Δ Γ : TY Δ; Γ ⊨ (Lit $ LitUnit) : Unit.
Proof.
  split; first done. 
  intros θ δ _. simp type_interp.
  exists #LitUnit. split. { simpl. constructor. }
  simp type_interp. eauto.
Qed.

Lemma compat_var Δ Γ x A :
  Γ !! x = Some A →
  TY Δ; Γ ⊨ (Var x) : A.
Proof.
  intros Hx. split.
  { eapply bool_decide_pack, elem_of_elements, elem_of_dom_2, Hx. }
  intros θ δ Hctx; simpl.
  eapply sem_context_rel_vals in Hx as (e & v & He & Heq & Hv); last done.
  rewrite He. simp type_interp. exists v. split; last done.
  rewrite -(of_to_val _ _ Heq).
  by apply big_step_of_val.
Qed.

Lemma compat_app Δ Γ e1 e2 A B :
  TY Δ; Γ ⊨ e1 : (A → B) →
  TY Δ; Γ ⊨ e2 : A →
  TY Δ; Γ ⊨ (e1 e2) : B.
Proof.
  intros [Hfuncl Hfun] [Hargcl Harg]. split.
  { simpl. eauto. }
  intros θ δ Hctx; simpl.

  specialize (Hfun _ _ Hctx). simp type_interp in Hfun. destruct Hfun as (v1 & Hbs1 & Hv1).
  simp type_interp in Hv1. destruct Hv1 as (x & e & -> & Hv1).
  specialize (Harg _ _ Hctx). simp type_interp in Harg.
  destruct Harg as (v2 & Hbs2  & Hv2).

  apply Hv1 in Hv2.
  simp type_interp in Hv2. destruct Hv2 as (v & Hbsv & Hv).

  simp type_interp.
  exists v. split; last done.
  eauto.
Qed.

(* Compatibility for [lam] unfortunately needs a very technical helper lemma. *)
Lemma lam_closed δ Γ θ (x : string) A e :
  closed (elements (dom (<[x:=A]> Γ))) e → 
  𝒢 δ Γ θ → 
  closed [] (Lam x (subst_map (delete x θ) e)).
Proof.
  intros Hcl Hctxt.
  eapply subst_map_closed.
  - eapply is_closed_weaken; first done.
    rewrite dom_delete dom_insert (sem_context_rel_dom δ Γ θ) //.
    intros y. destruct (decide (x = y)); set_solver.
  - intros x' e' Hx.
    eapply (is_closed_weaken []); last set_solver.
    eapply sem_context_rel_closed; first eassumption.
    eapply map_subseteq_spec; last done.
    apply map_delete_subseteq.
Qed.
Lemma compat_lam Δ Γ x e A B :
  TY Δ; (<[ x := A ]> Γ) ⊨ e : B →
  TY Δ; Γ ⊨ (Lam (BNamed x) e) : (A → B).
Proof.
  intros [Hbodycl Hbody]. split.
  { simpl. eapply is_closed_weaken; first eassumption. set_solver. }
  intros θ Hctxt. simpl. simp type_interp.
  eexists.
  split; first by eauto.
  simp type_interp.
  eexists _, _. split; first reflexivity.
  split; first by eapply lam_closed.
  intros v' Hv'.
  specialize (Hbody (<[ x := of_val v']> θ)).
  simpl. rewrite subst_subst_map; last by eapply sem_context_rel_closed.
  apply Hbody.
  apply sem_context_rel_insert; done.
Qed.

Lemma compat_lam_anon Δ Γ e A B :
  TY Δ; Γ ⊨ e : B →
  TY Δ; Γ ⊨ (Lam BAnon e) : (A → B).
Proof.
  intros [Hbodycl Hbody]. split; first done.
  intros θ Hctxt. simpl. simp type_interp.
  eexists.
  split; first by eauto.
  simp type_interp.
  eexists _, _. split; first reflexivity.
  split.
  { simpl. eapply subst_map_closed; simpl.
    - by erewrite <-sem_context_rel_dom.
    - by eapply sem_context_rel_closed. }
  naive_solver.
Qed.

Lemma compat_int_binop Δ Γ op e1 e2 :
  bin_op_typed op Int Int Int →
  TY Δ; Γ ⊨ e1 : Int →
  TY Δ; Γ ⊨ e2 : Int →
  TY Δ; Γ ⊨ (BinOp op e1 e2) : Int.
Proof.
  intros Hop [He1cl He1] [He2cl He2].
  split; first naive_solver.

  intros θ δ Hctx. simpl.
  simp type_interp.
  specialize (He1 _ _ Hctx). specialize (He2 _ _ Hctx).
  simp type_interp in He1. simp type_interp in He2.

  destruct He1 as (v1 & Hb1 & Hv1).
  destruct He2 as (v2 & Hb2 & Hv2).
  simp type_interp in Hv1, Hv2.
  destruct Hv1 as (z1 & ->). destruct Hv2 as (z2 & ->).

  inversion Hop; subst op.
  + exists #(z1 + z2)%Z. split.
    - econstructor; done.
    - exists (z1 + z2)%Z. done.
  + exists #(z1 - z2)%Z. split.
    - econstructor; done.
    - exists (z1 - z2)%Z. done.
  + exists #(z1 * z2)%Z. split.
    - econstructor; done.
    - exists (z1 * z2)%Z. done.
Qed.

Lemma compat_int_bool_binop Δ Γ op e1 e2 :
  bin_op_typed op Int Int Bool →
  TY Δ; Γ ⊨ e1 : Int →
  TY Δ; Γ ⊨ e2 : Int →
  TY Δ; Γ ⊨ (BinOp op e1 e2) : Bool.
Proof.
  intros Hop [He1cl He1] [He2cl He2].
  split; first naive_solver.

  intros θ δ Hctx. simpl.
  simp type_interp.
  specialize (He1 _ _ Hctx). specialize (He2 _ _ Hctx).
  simp type_interp in He1. simp type_interp in He2.

  destruct He1 as (v1 & Hb1 & Hv1).
  destruct He2 as (v2 & Hb2 & Hv2).
  simp type_interp in Hv1, Hv2.
  destruct Hv1 as (z1 & ->). destruct Hv2 as (z2 & ->).

  inversion Hop; subst op.
  + exists #(bool_decide (z1 < z2))%Z. split.
    - econstructor; done.
    - by eexists _.
  + exists #(bool_decide (z1 ≤ z2))%Z. split.
    - econstructor; done.
    - by eexists _.
  + exists #(bool_decide (z1 = z2))%Z. split.
    - econstructor; done.
    - eexists _. done.
Qed.

Lemma compat_unop Δ Γ op A B e :
  un_op_typed op A B →
  TY Δ; Γ ⊨ e : A →
  TY Δ; Γ ⊨ (UnOp op e) : B.
Proof.
  intros Hop [Hecl He].
  split; first naive_solver.
  intros θ δ Hctx. simpl.
  simp type_interp. specialize (He _ _ Hctx).
  simp type_interp in He.

  destruct He as (v & Hb & Hv).
  inversion Hop; subst; simp type_interp in Hv.
  - destruct Hv as (b & ->).
    exists #(negb b). split.
    + econstructor; done.
    + by eexists _.
  - destruct Hv as (z & ->).
    exists #(-z)%Z. split.
    + econstructor; done.
    + by eexists _.
Qed.

Lemma compat_tlam Δ Γ e A :
  TY S Δ; (⤉ Γ) ⊨ e : A →
  TY Δ; Γ ⊨ (Λ, e) : (∀: A).
Proof.
  intros [Hecl He]. split.
  { simpl. by erewrite <-dom_fmap. }
  intros θ δ Hctx. simpl.
  simp type_interp.
  exists (Λ, subst_map θ e)%V.
  split; first constructor.

  simp type_interp.
  eexists _. split_and!; first done.
  { simpl. eapply subst_map_closed; simpl.
    - erewrite <-sem_context_rel_dom; last eassumption. 
      by erewrite <-dom_fmap.
    - by eapply sem_context_rel_closed. }
  intros τ. eapply He.
  by eapply sem_context_rel_cons.
Qed.

Lemma compat_tapp Δ Γ e A B :
  type_wf Δ B →
  TY Δ; Γ ⊨ e : (∀: A) →
  TY Δ; Γ ⊨ (e <>) : (A.[B/]).
Proof.
  (* TODO: exercise *)
Admitted.


Lemma compat_pack Δ Γ e n A B :
  type_wf n B →
  type_wf (S n) A →
  TY n; Γ ⊨ e : A.[B/] →
  TY n; Γ ⊨ (pack e) : (∃: A).
Proof.
  (* This will be an exercise for you next week :) *)
  (* TODO: exercise *)
Admitted.


Lemma compat_unpack n Γ A B e e' x :
  type_wf n B →
  TY n; Γ ⊨ e : (∃: A) →
  TY S n; <[x:=A]> (⤉Γ) ⊨ e' : B.[ren (+1)] →
  TY n; Γ ⊨ (unpack e as BNamed x in e') : B.
Proof.
  (* This will be an exercise for you next week :) *)
  (* TODO: exercise *)
Admitted.


Lemma compat_if n Γ e0 e1 e2 A :
  TY n; Γ ⊨ e0 : Bool →
  TY n; Γ ⊨ e1 : A →
  TY n; Γ ⊨ e2 : A →
  TY n; Γ ⊨ (if: e0 then e1 else e2) : A.
Proof.
  intros [He0cl He0] [He1cl He1] [He2cl He2].
  split; first naive_solver.
  intros θ δ Hctx. simpl.
  simp type_interp.
  specialize (He0 _ _ Hctx). simp type_interp in He0.
  specialize (He1 _ _ Hctx). simp type_interp in He1.
  specialize (He2 _ _ Hctx). simp type_interp in He2.

  destruct He0 as (v0 & Hb0 & Hv0). simp type_interp in Hv0. destruct Hv0 as (b & ->).
  destruct He1 as (v1 & Hb1 & Hv1).
  destruct He2 as (v2 & Hb2 & Hv2).

  destruct b.
  - exists v1. split; first by repeat econstructor. done.
  - exists v2. split; first by repeat econstructor. done.
Qed.

Lemma compat_pair Δ Γ e1 e2 A B :
  TY Δ; Γ ⊨ e1 : A →
  TY Δ; Γ ⊨ e2 : B →
  TY Δ; Γ ⊨ (e1, e2) : A × B.
Proof.
  intros [He1cl He1] [He2cl He2].
  split; first naive_solver.
  intros θ δ Hctx. simpl.
  simp type_interp.
  specialize (He1 _ _ Hctx). simp type_interp in He1.
  destruct He1 as (v1 & Hb1 & Hv1).
  specialize (He2 _ _ Hctx). simp type_interp in He2.
  destruct He2 as (v2 & Hb2 & Hv2).
  exists (v1, v2)%V. split; first eauto.
  simp type_interp. exists v1, v2. done.
Qed.

Lemma compat_fst Δ Γ e A B :
  TY Δ; Γ ⊨ e : A × B →
  TY Δ; Γ ⊨ Fst e : A.
Proof.
  intros [Hecl He]. split; first naive_solver.
  intros θ δ Hctx. simpl.
  simp type_interp.
  specialize (He _ _ Hctx). simp type_interp in He.
  destruct He as (v & Hb & Hv).
  simp type_interp in Hv. destruct Hv as (v1 & v2 & -> & Hv1 & Hv2).
  exists v1. split; first eauto. done.
Qed.

Lemma compat_snd Δ Γ e A B :
  TY Δ; Γ ⊨ e : A × B →
  TY Δ; Γ ⊨ Snd e : B.
Proof.
  intros [Hecl He]. split; first naive_solver.
  intros θ δ Hctx. simpl.
  simp type_interp.
  specialize (He _ _ Hctx). simp type_interp in He.
  destruct He as (v & Hb & Hv).
  simp type_interp in Hv. destruct Hv as (v1 & v2 & -> & Hv1 & Hv2).
  exists v2. split; first eauto. done.
Qed.

Lemma compat_injl Δ Γ e A B :
  TY Δ; Γ ⊨ e : A →
  TY Δ; Γ ⊨ InjL e : A + B.
Proof.
  intros [Hecl He]. split; first naive_solver.
  intros θ δ Hctx. simpl.
  simp type_interp.
  specialize (He _ _ Hctx). simp type_interp in He.
  destruct He as (v & Hb & Hv).
  exists (InjLV v). split; first eauto.
  simp type_interp. eauto.
Qed.

Lemma compat_injr Δ Γ e A B :
  TY Δ; Γ ⊨ e : B →
  TY Δ; Γ ⊨ InjR e : A + B.
Proof.
  intros [Hecl He]. split; first naive_solver.
  intros θ δ Hctx. simpl.
  simp type_interp.
  specialize (He _ _ Hctx). simp type_interp in He.
  destruct He as (v & Hb & Hv).
  exists (InjRV v). split; first eauto.
  simp type_interp. eauto.
Qed.

Lemma compat_case Δ Γ e e1 e2 A B C :
  TY Δ; Γ ⊨ e : B + C →
  TY Δ; Γ ⊨ e1 : (B → A) →
  TY Δ; Γ ⊨ e2 : (C → A) →
  TY Δ; Γ ⊨ Case e e1 e2 : A.
Proof.
  intros [Hecl He] [He1cl He1] [He2cl He2].
  split; first naive_solver.
  intros θ δ Hctx. simpl.
  simp type_interp.
  specialize (He _ _ Hctx). simp type_interp in He.
  destruct He as (v & Hb & Hv).
  simp type_interp in Hv. destruct Hv as [(v' & -> & Hv') | (v' & -> & Hv')].
  - specialize (He1 _ _ Hctx). simp type_interp in He1.
    destruct He1 as (v & Hb' & Hv).
    simp type_interp in Hv. destruct Hv as (x & e' & -> & Cl & Hv).
    apply Hv in Hv'. simp type_interp in Hv'. destruct Hv' as (v & Hb'' & Hv'').
    exists v. split; last done.
    econstructor; first done.
    econstructor; [done | apply big_step_of_val; done | done].
  - specialize (He2 _ _ Hctx). simp type_interp in He2.
    destruct He2 as (v & Hb' & Hv).
    simp type_interp in Hv. destruct Hv as (x & e' & -> & Cl & Hv).
    apply Hv in Hv'. simp type_interp in Hv'. destruct Hv' as (v & Hb'' & Hv'').
    exists v. split; last done.
    econstructor; first done.
    econstructor; [done | apply big_step_of_val; done | done].
Qed.

Lemma sem_soundness Δ Γ e A :
  TY Δ; Γ ⊢ e : A →
  TY Δ; Γ ⊨ e : A.
Proof.
  induction 1 as [ | | | | | | | |  | | | | n Γ e1 e2 op A B C Hop ? ? ? ? | | | | | | | ].
  - by apply compat_var.
  - by apply compat_lam.
  - by apply compat_lam_anon.
  - by apply compat_tlam.
  - apply compat_tapp; done.
  - eapply compat_pack; done.
  - eapply compat_unpack; done.
  - apply compat_int.
  - by eapply compat_bool.
  - by eapply compat_unit.
  - by eapply compat_if.
  - by eapply compat_app.
  - inversion Hop; subst.
    1-3: by apply compat_int_binop.
    1-3: by apply compat_int_bool_binop.
  - by eapply compat_unop.
  - by apply compat_pair.
  - by eapply compat_fst.
  - by eapply compat_snd.
  - by eapply compat_injl.
  - by eapply compat_injr.
  - by eapply compat_case.
Qed.

(* dummy delta which we can use if we don't care *)
Program Definition any_type : sem_type := {| sem_type_car := λ v, is_closed [] v |}.
Definition δ_any : var → sem_type := λ _, any_type.

Lemma termination e A :
  (TY 0; ∅ ⊢ e : A)%ty →
  ∃ v, big_step e v.
Proof.
  intros [Hsemcl Hsem]%sem_soundness.
  specialize (Hsem ∅ δ_any).
  simp type_interp in Hsem.
  rewrite subst_map_empty in Hsem.
  destruct Hsem as (v & Hbs & _); last eauto.
  constructor.
Qed.
