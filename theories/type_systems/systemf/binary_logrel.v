(* NOTE: import order matters here.
   stdpp and Equations both set different default obligation tactics,
   and the one from Equations is much better at solving the Equations goals. *)
From stdpp Require Import gmap base relations.
From iris Require Import prelude.
From semantics.lib Require Export facts.
From semantics.ts.systemf Require Import lang notation parallel_subst types bigstep tactics.
From Equations Require Export Equations.

(** * Logical relation for SystemF *)

Implicit Types
  (Δ : nat)
  (Γ : typing_context)
  (v : val)
  (α : var)
  (e : expr)
  (A : type).

(** ** Definition of the logrel *)
(**
  In Rocq, we need to make argument why the logical relation is well-defined precise:
  This holds true in particular for the mutual recursion between the value relation and the expression relation.
  We therefore define a termination measure [mut_measure] that makes sure that for each recursive call, we either
   - decrease the size of the type
   - or switch from the expression case to the value case.

  We use the Equations package to define the logical relation, as it's tedious to make the termination
   argument work with Rocq's built-in support for recursive functions.
 *)
Inductive val_or_expr : Type :=
| inj_val : val → val → val_or_expr
| inj_expr : expr → expr → val_or_expr.

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
  mut_measure (inj_val _ _) t := type_size t;
  mut_measure (inj_expr _ _) t := 1 + type_size t.

(** A semantic type consists of a value-relation and a proof of closedness *)
Record sem_type := mk_ST {
  sem_type_car :> val → val → Prop;
  sem_type_closed_val v w : sem_type_car v w → is_closed [] (of_val v) ∧ is_closed [] (of_val w);
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
  (τ : sem_type)
.

(** The logical relation *)
Equations type_interp (c : val_or_expr) (t : type) δ : Prop by wf (mut_measure c t) := {
  type_interp (inj_val v w) Int δ =>
    ∃ z : Z, v = #z ∧ w = #z;
  type_interp (inj_val v w) Bool δ =>
    ∃ b : bool, v = #b ∧ w = #b;
  type_interp (inj_val v w) Unit δ =>
    v = #LitUnit ∧ w = #LitUnit ;
  type_interp (inj_val v w) (A × B) δ =>
    ∃ v1 v2 w1 w2 : val, v = (v1, v2)%V ∧ w = (w1, w2)%V ∧ type_interp (inj_val v1 w1) A δ ∧ type_interp (inj_val v2 w2) B δ;
  type_interp (inj_val v w) (A + B) δ =>
    (∃ v' w' : val, v = InjLV v' ∧ w = InjLV w' ∧ type_interp (inj_val v' w') A δ) ∨
    (∃ v' w' : val, v = InjRV v' ∧ w = InjRV w' ∧ type_interp (inj_val v' w') B δ);
  type_interp (inj_val v w) (A → B) δ =>
    ∃ x y e1 e2, v = LamV x e1 ∧ w = LamV y e2 ∧ is_closed (x :b: nil) e1 ∧ is_closed (y :b: nil) e2 ∧
      ∀ v' w',
        type_interp (inj_val v' w') A δ →
        type_interp (inj_expr (subst' x (of_val v') e1) (subst' y (of_val w') e2)) B δ;
  (** Type variable case *)
  type_interp (inj_val v w) (#α) δ =>
    (δ α).(sem_type_car) v w;
  (** ∀ case *)
  type_interp (inj_val v w) (∀: A) δ =>
    ∃ e1 e2, v = TLamV e1 ∧  w = TLamV e2 ∧ is_closed [] e1 ∧ is_closed [] e2 ∧
      ∀ τ, type_interp (inj_expr e1 e2) A (τ .: δ);
  (** ∃ case *)
  type_interp (inj_val v w) (∃: A) δ =>
    ∃ v' w', v = PackV v' ∧ w = PackV w' ∧
      ∃ τ : sem_type, type_interp (inj_val v' w') A (τ .: δ);

  type_interp (inj_expr e1 e2) t δ =>
    ∃ v1 v2, big_step e1 v1 ∧ big_step e2 v2 ∧ type_interp (inj_val v1 v2) t δ
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
Notation sem_val_rel A δ v w := (type_interp (inj_val v w) A δ).
Notation sem_expr_rel A δ e1 e2 := (type_interp (inj_expr e1 e2) A δ).

Notation 𝒱 A δ v w := (sem_val_rel A δ v w).
Notation ℰ A δ e1 e2 := (sem_expr_rel A δ e1 e2).


Lemma val_rel_is_closed v w δ A:
  𝒱 A δ v w → is_closed [] (of_val v) ∧ is_closed [] (of_val w).
Proof.
  induction A as [ | | | | | A IHA | | A IH1 B IH2 | A IH1 B IH2] in v, w, δ |-*; simp type_interp.
  - by eapply sem_type_closed_val.
  - intros [z [-> ->]]. done.
  - intros [b [-> ->]]. done.
  - intros [-> ->]. done.
  - intros (e1 & e2 & -> & -> & ? & ? & _). done.
  - intros (v' & w' & -> & -> & (τ & Hinterp)). simpl. by eapply IHA.
  - intros (x & y & e1 & e2 & -> & -> & ? & ? & _). done.
  - intros (v1 & v2 & w1 & w2 & -> & -> & ? & ?). simpl. split; apply andb_True; split; naive_solver.
  - intros [(v' & w' & -> & -> & ?) | (v' & w' & -> & -> & ?)]; simpl; eauto.
Qed.

(** Interpret a syntactic type *)
Program Definition interp_type A δ : sem_type := {|
  sem_type_car := fun v w => 𝒱 A δ v w;
|}.
Next Obligation. by eapply val_rel_is_closed. Qed.

(* Semantic typing of contexts *)
Implicit Types
  (θ : gmap string expr).

(** Context relation *)
Inductive sem_context_rel (δ : tyvar_interp) : typing_context → (gmap string expr) → (gmap string expr) → Prop :=
  | sem_context_rel_empty : sem_context_rel δ ∅ ∅ ∅
  | sem_context_rel_insert Γ θ1 θ2 v w x A :
    𝒱 A δ v w →
    sem_context_rel δ Γ θ1 θ2 →
    sem_context_rel δ (<[x := A]> Γ) (<[x := of_val v]> θ1) (<[x := of_val w]> θ2).

Notation 𝒢 := sem_context_rel.

(** Semantic typing judgment *)
Definition sem_typed Δ Γ e1 e2 A :=
  is_closed (elements (dom Γ)) e1 ∧ is_closed (elements (dom Γ)) e2 ∧
  ∀ θ1 θ2 δ, 𝒢 δ Γ θ1 θ2 → ℰ A δ (subst_map θ1 e1) (subst_map θ2 e2).
Notation "'TY' Δ ;  Γ ⊨ e1 ≈ e2 : A" := (sem_typed Δ Γ e1 e2 A) (at level 74, e1, e2, A at next level).

Lemma sem_expr_rel_of_val A δ v w :
  ℰ A δ (of_val v) (of_val w) → 𝒱 A δ v w.
Proof.
  simp type_interp.
  intros (v' & w' & ->%big_step_val & ->%big_step_val & Hv').
  apply Hv'.
Qed.

Lemma sem_context_rel_vals {δ Γ θ1 θ2 x A} :
  sem_context_rel δ Γ θ1 θ2 →
  Γ !! x = Some A →
  ∃ e1 e2 v1 v2, θ1 !! x = Some e1 ∧ θ2 !! x = Some e2 ∧ to_val e1 = Some v1 ∧ to_val e2 = Some v2 ∧ 𝒱 A δ v1 v2.
Proof.
  induction 1 as [|Γ θ1 θ2 v w y B Hvals Hctx IH].
  - naive_solver.
  - rewrite lookup_insert_Some. intros [[-> ->]|[Hne Hlook]].
    + do 4 eexists.
      split; first by rewrite lookup_insert_eq.
      split; first by rewrite lookup_insert_eq.
      split; first by eapply to_of_val.
      split; first by eapply to_of_val.
      done.
    + eapply IH in Hlook as (e1 & e2 & w1 & w2 & Hlook1 & Hlook2 & He1 & He2 & Hval).
      do 4 eexists.
      split; first by rewrite lookup_insert_ne.
      split; first by rewrite lookup_insert_ne.
      repeat split; done.
Qed.

Lemma sem_context_rel_subset δ Γ θ1 θ2 :
  𝒢 δ Γ θ1 θ2 → dom Γ ⊆ dom θ1 ∧ dom Γ ⊆ dom θ2.
Proof.
  intros Hctx. split; apply elem_of_subseteq; intros x (A & Hlook)%elem_of_dom.
  all: eapply sem_context_rel_vals in Hlook as (e1 & e2 & v1 & v2 & Hlook1 & Hlook2 & Heq1 & Heq2 & Hval); last done.
  all: eapply elem_of_dom; eauto.
Qed.


Lemma sem_context_rel_closed δ Γ θ1 θ2:
  𝒢 δ Γ θ1 θ2 → subst_is_closed [] θ1 ∧ subst_is_closed [] θ2.
Proof.
  induction 1 as [ | Γ θ1 θ2 v w x A Hv Hctx [IH1 IH2]]; rewrite /subst_is_closed.
  - naive_solver.
  - split; intros y e; rewrite lookup_insert_Some.
    all: intros [[-> <-]|[Hne Hlook]].
    + eapply val_rel_is_closed in Hv. naive_solver.
    + eapply IH1; last done.
    + eapply val_rel_is_closed in Hv. naive_solver.
    + eapply IH2; last done.
Qed.
Lemma sem_context_rel_dom δ Γ θ1 θ2 :
  𝒢 δ Γ θ1 θ2 → dom Γ = dom θ1 /\ dom Γ = dom θ2.
Proof.
  induction 1.
  - by rewrite !dom_empty.
  - rewrite !dom_insert. set_solver.
Qed.


Section boring_lemmas.
  (** The lemmas in this section are all quite boring and expected statements,
    but are quite technical to prove due to De Bruijn binders.
    We encourage to skip over the proofs of these lemmas.
  *)

  Lemma sem_val_rel_ext B δ δ' v w :
    (∀ n v w, δ n v w ↔ δ' n v w) →
    𝒱 B δ v w ↔ 𝒱 B δ' v w.
  Proof.
    induction B in δ, δ', v, w |-*; simpl; simp type_interp; eauto; intros Hiff.
    - f_equiv; intros e1. f_equiv; intros e2. do 4 f_equiv.
      eapply forall_proper; intros τ.
      simp type_interp. f_equiv. intros v1. f_equiv. intros v2.
      do 2 f_equiv. etransitivity; last apply IHB; first done.
      intros [|m] ?; simpl; eauto.
    - f_equiv. intros v1. f_equiv. intros v2. do 3 f_equiv. intros τ.
      etransitivity; last apply IHB; first done.
      intros [|m] ?; simpl; eauto.
    - do 4 (f_equiv; intros ?).
      do 4 f_equiv.
      eapply forall_proper; intros v1.
      eapply forall_proper; intros v2.
      eapply if_iff; first eauto.
      simp type_interp. f_equiv. intros v3.
      f_equiv. intros v4.
      do 2 f_equiv.
      eauto.
    - do 4 (f_equiv; intros ?).
      do 3 f_equiv; eauto.
    - f_equiv; f_equiv; intros ?; f_equiv; intros ?.
      all: do 2 f_equiv; eauto.
  Qed.


  Lemma sem_val_rel_move_ren B δ σ v w:
     𝒱 B (λ n, δ (σ n)) v w ↔ 𝒱 (rename σ B) δ v w.
  Proof.
    induction B in σ, δ, v, w |-*; simpl; simp type_interp; eauto.
    - f_equiv; intros e1. f_equiv; intros e2. do 4 f_equiv.
      eapply forall_proper; intros τ.
      simp type_interp. f_equiv. intros v1. f_equiv. intros v2.
      do 2 f_equiv. etransitivity; last apply IHB.
      eapply sem_val_rel_ext; intros [|n] u; asimpl; done.
    - f_equiv. intros v1. f_equiv. intros v2. do 3 f_equiv. intros τ.
      etransitivity; last apply IHB.
      eapply sem_val_rel_ext; intros [|n] u.
      +  simp type_interp. done.
      + simpl. rewrite /up. simpl. done.
    - do 4 (f_equiv; intros ?).
      do 4 f_equiv.
      eapply forall_proper; intros v1.
      eapply forall_proper; intros v2.
      eapply if_iff; first eauto.
      simp type_interp. f_equiv. intros v3.
      f_equiv. intros v4.
      do 2 f_equiv.
      eauto.
    - do 4 (f_equiv; intros ?).
      do 3 f_equiv; eauto.
    - f_equiv; f_equiv; intros ?; f_equiv; intros ?.
      all: do 2 f_equiv; eauto.
  Qed.


  Lemma sem_val_rel_move_subst B δ σ v w :
    𝒱 B (λ n, interp_type (σ n) δ) v w ↔ 𝒱 (B.[σ]) δ v w.
  Proof.
    induction B in σ, δ, v, w |-*; simpl; simp type_interp; eauto.
    - f_equiv; intros e1. f_equiv; intros e2. do 4 f_equiv.
      eapply forall_proper; intros τ.
      simp type_interp. f_equiv. intros v1. f_equiv. intros v2.
      do 2 f_equiv. etransitivity; last apply IHB.
      eapply sem_val_rel_ext; intros [|n] u.
      +  simp type_interp. done.
      + simpl. rewrite /up. simpl.
        etransitivity; last eapply sem_val_rel_move_ren.
        simpl. done.
    - f_equiv. intros v1. f_equiv. intros v2. do 3 f_equiv. intros τ.
      etransitivity; last apply IHB.
      eapply sem_val_rel_ext; intros [|n] u.
      +  simp type_interp. done.
      + simpl. rewrite /up. simpl.
      etransitivity; last eapply sem_val_rel_move_ren.
      simpl. done.
    - do 4 (f_equiv; intros ?).
      do 4 f_equiv.
      eapply forall_proper; intros v1.
      eapply forall_proper; intros v2.
      eapply if_iff; first eauto.
      simp type_interp. f_equiv. intros v3.
      f_equiv. intros v4.
      do 2 f_equiv.
      eauto.
    - do 4 (f_equiv; intros ?).
      do 3 f_equiv; eauto.
    - f_equiv; f_equiv; intros ?; f_equiv; intros ?.
      all: do 2 f_equiv; eauto.
  Qed.

  Lemma sem_val_rel_move_single_subst A B δ v w :
    𝒱 B (interp_type A δ .: δ) v w ↔ 𝒱 (B.[A/]) δ v w.
  Proof.
    rewrite -sem_val_rel_move_subst. eapply sem_val_rel_ext.
    intros [| n] w1 w2; simpl; done.
  Qed.

  Lemma sem_val_rel_cons A δ v w τ :
    𝒱 A δ v w ↔ 𝒱  A.[ren (+1)] (τ .: δ) v w.
  Proof.
    rewrite -sem_val_rel_move_subst; simpl.
    eapply sem_val_rel_ext; done.
  Qed.

  Lemma sem_context_rel_cons Γ δ θ1 θ2 τ :
    𝒢 δ Γ θ1 θ2 →
    𝒢 (τ .: δ) (⤉ Γ) θ1 θ2.
  Proof.
    induction 1 as [ | Γ θ1 θ2 v w x A Hv Hctx IH]; simpl.
    - rewrite fmap_empty. constructor.
    - rewrite fmap_insert. constructor; last done.
      rewrite -sem_val_rel_cons. done.
  Qed.
End boring_lemmas.

(** ** Compatibility lemmas *)

Lemma compat_int Δ Γ z : TY Δ; Γ ⊨ (Lit $ LitInt z) ≈ (Lit $ LitInt z) : Int.
Proof.
  do 2 (split; first done).
  intros θ1 θ2 δ _. simp type_interp.
  exists #z, #z.
  split; first by constructor.
  split; first by constructor.
  simp type_interp. eauto.
Qed.

Lemma compat_bool Δ Γ b : TY Δ; Γ ⊨ (Lit $ LitBool b) ≈ (Lit $ LitBool b) : Bool.
Proof.
  do 2 (split; first done).
  intros θ1 θ2 δ _. simp type_interp.
  exists #b, #b.
  split; first by constructor.
  split; first by constructor.
  simp type_interp. eauto.
Qed.

Lemma compat_unit Δ Γ : TY Δ; Γ ⊨ (Lit $ LitUnit) ≈ (Lit $ LitUnit) : Unit.
Proof.
  do 2 (split; first done).
  intros θ1 θ2 δ _. simp type_interp.
  exists #LitUnit, #LitUnit.
  split; first by constructor.
  split; first by constructor.
  simp type_interp. split; eauto.
Qed.

Lemma compat_var Δ Γ x A :
  Γ !! x = Some A →
  TY Δ; Γ ⊨ (Var x) ≈ (Var x) : A.
Proof.
  intros Hx.
  do 2 (split; first eapply bool_decide_pack, elem_of_elements, elem_of_dom_2, Hx).
  intros θ1 θ2 δ Hctx; simpl.

  (* TODO: exercise *)
Admitted.


Lemma compat_app Δ Γ e1 e1' e2 e2' A B :
  TY Δ; Γ ⊨ e1 ≈ e1': (A → B) →
  TY Δ; Γ ⊨ e2 ≈ e2' : A →
  TY Δ; Γ ⊨ (e1 e2) ≈ (e1' e2') : B.
Proof.
  intros (Hfuncl & Hfuncl' & Hfun) (Hargcl & Hargcl' & Harg).
  do 2 (split; first naive_solver).
  intros θ1 θ2 δ Hctx; simpl.

  specialize (Hfun _ _ _ Hctx). simp type_interp in Hfun. destruct Hfun as (v1 & v2 & Hbs1 & Hbs2 & Hv12).
  simp type_interp in Hv12. destruct Hv12 as (x & y & e1'' & e2'' & -> & -> & ? & ? & Hv12).
  specialize (Harg _ _ _ Hctx). simp type_interp in Harg.
  destruct Harg as (v3 & v4 & Hbs3 & Hbs4 & Hv34).

  apply Hv12 in Hv34.
  simp type_interp in Hv34.
  destruct Hv34 as (v5 & v6 & Hbs5 & Hbs6 & Hv56).

  simp type_interp.
  exists v5, v6. eauto.
Qed.



(* Compatibility for [lam] unfortunately needs a very technical helper lemma. *)
Lemma lam_closed Γ θ (x : string) A e :
  dom Γ = dom θ →
  subst_is_closed [] θ →
  closed (elements (dom (<[x:=A]> Γ))) e → 
  closed [] (Lam x (subst_map (delete x θ) e)).
Proof.
  intros Hdom Hsubstcl Hcl.
  eapply subst_map_closed.
  - eapply is_closed_weaken; first done.
    rewrite dom_delete dom_insert Hdom //.
    intros y. destruct (decide (x = y)); set_solver.
  - intros x' e' Hx.
    eapply (is_closed_weaken []); last set_solver.
    eapply Hsubstcl.
    eapply map_subseteq_spec; last done.
    apply map_delete_subseteq.
Qed.
(** Lambdas need to be closed by the context *)
Lemma compat_lam_named Δ Γ x e1 e2 A B :
  TY Δ; (<[ x := A ]> Γ) ⊨ e1 ≈ e2 : B →
  TY Δ; Γ ⊨ (Lam (BNamed x) e1) ≈ (Lam (BNamed x) e2): (A → B).
Proof.
  intros (Hbodycl & Hbodycl' & Hbody).
  do 2 (split; first (simpl; eapply is_closed_weaken; set_solver)).
  intros θ1 θ2 δ Hctx. simpl.
  simp type_interp.

  exists ((λ: x, subst_map (delete x θ1) e1))%V, ((λ: x, subst_map (delete x θ2) e2))%V.
  split; first by eauto.
  split; first by eauto.
  simp type_interp.

  opose proof* sem_context_rel_dom as []; first done.
  opose proof* sem_context_rel_closed as []; first done.
  eexists (BNamed x), (BNamed x), _, _. split_and!.
  1-2: reflexivity.
  1-2: eapply lam_closed; eauto.
  intros v' w' Hvw'.
  specialize (Hbody (<[ x := of_val v']> θ1) (<[ x := of_val w']> θ2)).
  simpl. generalize Hctx=>Hctx'.
  eapply sem_context_rel_closed in Hctx' as Hclosed.
  rewrite !subst_subst_map; [|naive_solver..].
  apply Hbody. apply sem_context_rel_insert; done.
Qed.


Lemma compat_lam_anon Δ Γ e1 e2 A B :
  TY Δ; Γ ⊨ e1 ≈ e2 : B →
  TY Δ; Γ ⊨ (Lam BAnon e1) ≈ (Lam BAnon e2) : (A → B).
Proof.
  intros (Hbodycl & Hbodycl' & Hbody).
  do 2 (split; first done).
  intros θ1 θ2 δ Hctx. simpl.
  simp type_interp.

  exists (λ: <>, subst_map θ1 e1)%V, (λ: <>, subst_map θ2 e2)%V.
  split; first by eauto.
  split; first by eauto.
  simp type_interp.
  eexists BAnon, BAnon, _, _. split_and!; try reflexivity.
  - simpl. eapply subst_map_closed; simpl.
    + replace (dom θ1) with (dom Γ); first done.
      eapply sem_context_rel_dom in Hctx. naive_solver.
    + apply sem_context_rel_closed in Hctx. naive_solver.
  - simpl. eapply subst_map_closed; simpl.
    + replace (dom θ2) with (dom Γ); first done.
      eapply sem_context_rel_dom in Hctx. naive_solver.
    + apply sem_context_rel_closed in Hctx. naive_solver.
  - intros v' w' Hvw'.
    specialize (Hbody θ1 θ2).
    simpl. apply Hbody; done.
Qed.

Lemma compat_int_binop Δ Γ op e1 e1' e2 e2' :
  bin_op_typed op Int Int Int →
  TY Δ; Γ ⊨ e1 ≈ e1' : Int →
  TY Δ; Γ ⊨ e2 ≈ e2' : Int →
  TY Δ; Γ ⊨ (BinOp op e1 e2) ≈ (BinOp op e1' e2') : Int.
Proof.
  intros Hop (He1cl & He1cl' & He1) (He2cl & He2cl' & He2).
  do 2 (split; first naive_solver).
  intros θ1 θ2 δ Hctx. simpl.
  simp type_interp.
  specialize (He1 _ _ _ Hctx). specialize (He2 _ _ _ Hctx).
  simp type_interp in He1. simp type_interp in He2.

  destruct He1 as (v1 & v1' & Hb1 & Hb1' & Hv1).
  destruct He2 as (v2 & v2' & Hb2 & Hb2' & Hv2).
  simp type_interp in Hv1, Hv2.
  destruct Hv1 as (z1 & -> & ->).
  destruct Hv2 as (z2 & -> & ->).

  inversion Hop; subst op.
  + exists #(z1 + z2)%Z, #(z1 + z2)%Z. split_and!.
    - econstructor; done.
    - econstructor; done.
    - exists (z1 + z2)%Z. done.
  + exists #(z1 - z2)%Z, #(z1 - z2)%Z. split_and!.
    - econstructor; done.
    - econstructor; done.
    - exists (z1 - z2)%Z. done.
  + exists #(z1 * z2)%Z, #(z1 * z2)%Z. split_and!.
    - econstructor; done.
    - econstructor; done.
    - exists (z1 * z2)%Z. done.
Qed.

Lemma compat_int_bool_binop Δ Γ op e1 e1' e2 e2' :
  bin_op_typed op Int Int Bool →
  TY Δ; Γ ⊨ e1 ≈ e1' : Int →
  TY Δ; Γ ⊨ e2 ≈ e2' : Int →
  TY Δ; Γ ⊨ (BinOp op e1 e2) ≈ (BinOp op e1' e2')  : Bool.
Proof.
  intros Hop (He1cl & He1cl' & He1) (He2cl & He2cl' & He2).
  do 2 (split; first naive_solver).
  intros θ1 θ2 δ Hctx. simpl.

  simp type_interp.
  specialize (He1 _ _ _ Hctx). specialize (He2 _ _ _ Hctx).
  simp type_interp in He1. simp type_interp in He2.

  destruct He1 as (v1 & v1' & Hb1 & Hb1' & Hv1).
  destruct He2 as (v2 & v2' & Hb2 & Hb2' & Hv2).
  simp type_interp in Hv1, Hv2.
  destruct Hv1 as (z1 & -> & ->).
  destruct Hv2 as (z2 & -> & ->).

  inversion Hop; subst op.
  + exists #(bool_decide (z1 < z2))%Z, #(bool_decide (z1 < z2))%Z. split_and!.
    - econstructor; done.
    - econstructor; done.
    - by eexists _.
  + exists #(bool_decide (z1 ≤ z2))%Z, #(bool_decide (z1 ≤ z2))%Z. split_and!.
    - econstructor; done.
    - econstructor; done.
    - by eexists _.
  + exists #(bool_decide (z1 = z2))%Z, #(bool_decide (z1 = z2))%Z. split_and!.
    - econstructor; done.
    - econstructor; done.
    - eexists _. done.
Qed.

Lemma compat_unop Δ Γ op A B e e' :
  un_op_typed op A B →
  TY Δ; Γ ⊨ e ≈ e' : A →
  TY Δ; Γ ⊨ (UnOp op e) ≈ (UnOp op e') : B.
Proof.
  intros Hop (Hecl & Hecl' & He).
  do 2 (split; first naive_solver).
  intros θ1 θ2 δ Hctx. simpl.

  simp type_interp. specialize (He _ _ _ Hctx).
  simp type_interp in He.

  destruct He as (v & v' & Hb & Hb' & Hv).
  inversion Hop; subst; simp type_interp in Hv.
  - destruct Hv as (b & -> & ->).
    exists #(negb b), #(negb b). split_and!.
    + econstructor; done.
    + econstructor; done.
    + by eexists _.
  - destruct Hv as (z & -> & ->).
    exists #(-z)%Z, #(-z)%Z. split_and!.
    + econstructor; done.
    + econstructor; done.
    + by eexists _.
Qed.


Lemma compat_tlam Δ Γ e1 e2 A :
  TY S Δ; (⤉ Γ) ⊨ e1 ≈ e2 : A →
  TY Δ; Γ ⊨ (Λ, e1) ≈ (Λ, e2) : (∀: A).
Proof.
  intros (Hcl & Hcl' & He).
  do 2 (split; first (simpl; by erewrite <-dom_fmap)).

  intros θ1 θ2 δ Hctx. simpl.
  simp type_interp.
  exists (Λ, subst_map θ1 e1)%V, (Λ, subst_map θ2 e2)%V.
  split; first constructor.
  split; first constructor.

  simp type_interp.
  eexists _, _. split_and!; try done.
  - simpl. eapply subst_map_closed; simpl.
    + replace (dom θ1) with (dom Γ).
      * by erewrite <-dom_fmap.
      * apply sem_context_rel_dom in Hctx. naive_solver.
    + apply sem_context_rel_closed in Hctx. naive_solver.
  - simpl. eapply subst_map_closed; simpl.
    + replace (dom θ2) with (dom Γ).
      * by erewrite <-dom_fmap.
      * apply sem_context_rel_dom in Hctx. naive_solver.
    + apply sem_context_rel_closed in Hctx. naive_solver.
  - intros τ. eapply He.
    by eapply sem_context_rel_cons.
Qed.

Lemma compat_tapp Δ Γ e e' A B :
  type_wf Δ B →
  TY Δ; Γ ⊨ e ≈ e' : (∀: A) →
  TY Δ; Γ ⊨ (e <>) ≈ (e' <>) : (A.[B/]).
Proof.
  intros Hwf (Hecl & Hecl' & He).
  do 2 (split; first naive_solver).
  intros θ1 θ2 δ Hctx. simpl.

  (* TODO: exercise *)
Admitted.


Lemma compat_pack Δ Γ e e' n A B :
  type_wf n B →
  type_wf (S n) A →
  TY n; Γ ⊨ e ≈ e': A.[B/] →
  TY n; Γ ⊨ (pack e) ≈ (pack e') : (∃: A).
Proof.
  intros Hwf Hwf' (Hecl & Hecl' & He).
  do 2 (split; first naive_solver).
  intros θ1 θ2 δ Hctx. simpl.

  (* TODO: exercise *)
Admitted.


Lemma compat_unpack n Γ A B e1 e1' e2 e2' x :
  type_wf n B →
  TY n; Γ ⊨ e1 ≈ e2 : (∃: A) →
  TY S n; <[x:=A]> (⤉Γ) ⊨ e1' ≈ e2' : B.[ren (+1)] →
  TY n; Γ ⊨ (unpack e1 as BNamed x in e1') ≈ (unpack e2 as BNamed x in e2') : B.
Proof.
  intros Hwf (Hecl & Hecl' & He) (He'cl & He'cl' & He').
  split. { simpl. apply andb_True. split; first done.
    eapply is_closed_weaken; set_solver. }
  split. { simpl. apply andb_True. split; first done.
    eapply is_closed_weaken; set_solver. }
  intros θ1 θ2 δ Hctx. simpl. 

  (* TODO: exercise *)
Admitted.


Lemma compat_if n Γ e0 e0' e1 e1' e2 e2' A :
  TY n; Γ ⊨ e0 ≈ e0' : Bool →
  TY n; Γ ⊨ e1 ≈ e1' : A →
  TY n; Γ ⊨ e2 ≈ e2' : A →
  TY n; Γ ⊨ (if: e0 then e1 else e2) ≈ (if: e0' then e1' else e2') : A.
Proof.
  intros (He0cl & He0cl' & He0) (He1cl & He1cl' & He1) (He2cl & He2cl' & He2).
  do 2 (split; first naive_solver).
  intros θ1 θ2 δ Hctx. simpl.
  simp type_interp.

  specialize (He0 _ _ _ Hctx). simp type_interp in He0.
  specialize (He1 _ _ _ Hctx). simp type_interp in He1.
  specialize (He2 _ _ _ Hctx). simp type_interp in He2.

  destruct He0 as (v0 & v0' & Hb0 & Hb0' & Hv0). simp type_interp in Hv0.
  destruct Hv0 as (b & -> & ->).
  destruct He1 as (v1 & w1 & Hb1 & Hb1' & Hv1).
  destruct He2 as (v2 & w2 & Hb2 & Hb2' & Hv2).

  destruct b.
  - exists v1, w1. split_and!; try by repeat econstructor.
  - exists v2, w2. split_and!; try by repeat econstructor.
Qed.

Lemma compat_pair Δ Γ e1 e1' e2 e2' A B :
  TY Δ; Γ ⊨ e1 ≈ e1' : A →
  TY Δ; Γ ⊨ e2 ≈ e2' : B →
  TY Δ; Γ ⊨ (e1, e2) ≈ (e1', e2') : A × B.
Proof.
  intros (He1cl & He1cl' & He1) (He2cl & He2cl' & He2).
  do 2 (split; first naive_solver).
  intros θ1 θ2 δ Hctx. simpl.
  simp type_interp.
  
  specialize (He1 _ _ _ Hctx). specialize (He2 _ _ _ Hctx).
  simp type_interp in He1. simp type_interp in He2.

  destruct He1 as (v1 & v1' & Hb1 & Hb1' & Hv1).
  destruct He2 as (v2 & v2' & Hb2 & Hb2' & Hv2).
  simp type_interp in Hv1, Hv2.
  eexists _, _. split_and!; try by econstructor.
  simp type_interp. eexists _, _, _, _.
  split_and!; eauto.
Qed.

Lemma compat_fst Δ Γ e e' A B :
  TY Δ; Γ ⊨ e ≈ e' : A × B →
  TY Δ; Γ ⊨ Fst e ≈ Fst e' : A.
Proof.
  intros (Hecl & Hecl' & He).
  do 2 (split; first naive_solver).
  intros θ1 θ2 δ Hctx. simpl.
  simp type_interp.

  specialize (He _ _ _ Hctx). simp type_interp in He.
  destruct He as (v & v' & Hb & Hb' & Hv).
  simp type_interp in Hv.
  destruct Hv as (v1 & v2 & w1 & w2 & -> & -> & Hv & Hw).
  eexists _, _.
  split_and!; eauto.
Qed.

Lemma compat_snd Δ Γ e e' A B :
  TY Δ; Γ ⊨ e ≈ e' : A × B →
  TY Δ; Γ ⊨ Snd e ≈ Snd e' : B.
Proof.
  intros (Hecl & Hecl' & He).
  do 2 (split; first naive_solver).
  intros θ1 θ2 δ Hctx. simpl.
  simp type_interp.

  specialize (He _ _ _ Hctx). simp type_interp in He.
  destruct He as (v & v' & Hb & Hb' & Hv).
  simp type_interp in Hv.
  destruct Hv as (v1 & v2 & w1 & w2 & -> & -> & Hv & Hw).
  eexists _, _.
  split_and!; eauto.
Qed.

Lemma compat_injl Δ Γ e e' A B :
  TY Δ; Γ ⊨ e ≈ e' : A →
  TY Δ; Γ ⊨ InjL e ≈ InjL e' : A + B.
Proof.
  intros (Hecl & Hecl' & He).
  do 2 (split; first naive_solver).
  intros θ1 θ2 δ Hctx. simpl.
  simp type_interp.

  specialize (He _ _ _ Hctx). simp type_interp in He.
  destruct He as (v & v' & Hb & Hb' & Hv).
  simp type_interp in Hv.
  eexists _, _.
  split_and!; eauto.
  simp type_interp.
  left. eexists _, _. split_and!; eauto.
Qed.

Lemma compat_injr Δ Γ e e' A B :
  TY Δ; Γ ⊨ e ≈ e' : B →
  TY Δ; Γ ⊨ InjR e ≈ InjR e' : A + B.
Proof.
  intros (Hecl & Hecl' & He).
  do 2 (split; first naive_solver).
  intros θ1 θ2 δ Hctx. simpl.
  simp type_interp.

  specialize (He _ _ _ Hctx). simp type_interp in He.
  destruct He as (v & v' & Hb & Hb' & Hv).
  simp type_interp in Hv.
  eexists _, _.
  split_and!; eauto.
  simp type_interp.
  right. eexists _, _. split_and!; eauto.
Qed.

Lemma compat_case Δ Γ e e' e1 e1' e2 e2' A B C :
  TY Δ; Γ ⊨ e ≈ e' : B + C →
  TY Δ; Γ ⊨ e1 ≈ e1' : (B → A) →
  TY Δ; Γ ⊨ e2 ≈ e2' : (C → A) →
  TY Δ; Γ ⊨ Case e e1 e2 ≈ Case e' e1' e2' : A.
Proof.
  intros (He0cl & He0cl' & He0) (He1cl & He1cl' & He1) (He2cl & He2cl' & He2).
  do 2 (split; first naive_solver).
  intros θ1 θ2 δ Hctx. simpl.
  simp type_interp.

  specialize (He0 _ _ _ Hctx). simp type_interp in He0.
  specialize (He1 _ _ _ Hctx). simp type_interp in He1.
  specialize (He2 _ _ _ Hctx). simp type_interp in He2.

  destruct He0 as (v0 & v0' & Hb0 & Hb0' & Hv0). simp type_interp in Hv0.
  destruct He1 as (v1 & w1 & Hb1 & Hb1' & Hv1).
  destruct He2 as (v2 & w2 & Hb2 & Hb2' & Hv2).

  destruct Hv0 as [(v' & w' & -> & -> & Hv)|(v' & w' & -> & -> & Hv)].
  - simp type_interp in Hv1. destruct Hv1 as (x & y & e'' & e''' & -> & -> & Cl & Cl' & Hv1).
    apply Hv1 in Hv. simp type_interp in Hv. destruct Hv as (v & w & Hb''' & Hb'''' & Hv'').
    eexists _, _. split_and!; eauto using big_step, big_step_of_val.
  - simp type_interp in Hv2. destruct Hv2 as (x & y & e'' & e''' & -> & -> & Cl & Cl' & Hv2).
    apply Hv2 in Hv. simp type_interp in Hv. destruct Hv as (v & w & Hb''' & Hb'''' & Hv'').
    eexists _, _. split_and!; eauto using big_step, big_step_of_val.
Qed.



(* we register the compatibility lemmas with eauto *)
Local Hint Resolve
  compat_var compat_lam_named compat_lam_anon
  compat_tlam compat_tapp compat_pack compat_unpack
  compat_int compat_bool compat_unit compat_if
  compat_app compat_int_binop compat_int_bool_binop
  compat_unop compat_pair compat_fst compat_snd
  compat_injl compat_injr compat_case : core.





Lemma sem_soundness Δ Γ e A :
  TY Δ; Γ ⊢ e : A →
  TY Δ; Γ ⊨ e ≈ e : A.
Proof.
  induction 1 as [ | Δ Γ x e A B Hsyn IH | Δ Γ e A B Hsyn IH| Δ Γ e A Hsyn IH| | | | |  | | | | n Γ e1 e2 op A B C [] ? ? ? ? | | | | | | | ]; eauto.
Qed.


Program Definition any_type : sem_type := {| sem_type_car := λ v w, is_closed [] v ∧ is_closed [] w |}.
Definition δ_any : var → sem_type := λ _, any_type.



(* Contextual Equivalence *)
Inductive pctx :=
  | HolePCtx
  | AppLPCtx (C: pctx) (e2 : expr)
  | AppRPCtx (e1 : expr) (C: pctx)
  | TAppPCtx (C: pctx)
  | PackPCtx (C: pctx)
  | UnpackLPCtx (x : binder)(C: pctx) (e2 : expr)
  | UnpackRPCtx (x : binder) (e1 : expr) (C: pctx)
  | UnOpPCtx (op : un_op) (C: pctx)
  | BinOpLPCtx (op : bin_op) (C: pctx) (e2 : expr)
  | BinOpRPCtx (op : bin_op) (e1 : expr) (C: pctx)
  | IfPCtx (C: pctx) (e1 e2 : expr)
  | IfTPCtx (e: expr) (C: pctx) (e2 : expr)
  | IfEPCtx (e e1: expr) (C: pctx)
  | PairLPCtx (C: pctx) (e2 : expr)
  | PairRPCtx (e1 : expr) (C: pctx)
  | FstPCtx (C: pctx)
  | SndPCtx (C: pctx)
  | InjLPCtx (C: pctx)
  | InjRPCtx (C: pctx)
  | CasePCtx (C: pctx) (e1 e2 : expr)
  | CaseTPCtx (e: expr) (C: pctx) (e2 : expr)
  | CaseEPCtx (e e1: expr) (C: pctx)
  | LamPCtx (x: binder) (C: pctx)
  | TLamPCtx (C: pctx).

Fixpoint pfill (C : pctx) (e : expr) : expr :=
  match C with
  | HolePCtx => e
  | AppLPCtx K e2 => App (pfill K e) e2
  | AppRPCtx e1 K => App e1 (pfill K e)
  | TAppPCtx K => TApp (pfill K e)
  | PackPCtx K => Pack (pfill K e)
  | UnpackLPCtx x K e2 => Unpack x (pfill K e) e2
  | UnpackRPCtx x e1 K => Unpack x e1 (pfill K e)
  | UnOpPCtx op K => UnOp op (pfill K e)
  | BinOpLPCtx op K e2 => BinOp op (pfill K e) e2
  | BinOpRPCtx op e1 K => BinOp op e1 (pfill K e)
  | IfPCtx K e1 e2 => If (pfill K e) e1 e2
  | IfTPCtx e' K e2 => If e' (pfill K e) e2
  | IfEPCtx e' e1 K => If e' e1 (pfill K e)
  | PairLPCtx K e2 => Pair (pfill K e) e2
  | PairRPCtx e1 K => Pair e1 (pfill K e)
  | FstPCtx K => Fst (pfill K e)
  | SndPCtx K => Snd (pfill K e)
  | InjLPCtx K => InjL (pfill K e)
  | InjRPCtx K => InjR (pfill K e)
  | CasePCtx K e1 e2 => Case (pfill K e) e1 e2
  | CaseTPCtx e' K e2 => Case e' (pfill K e) e2
  | CaseEPCtx e' e1 K => Case e' e1 (pfill K e)
  | LamPCtx x C => Lam x (pfill C e)
  | TLamPCtx C => TLam (pfill C e)
  end.


Inductive pctx_typed (Δ: nat) (Γ: typing_context) (A: type): pctx → nat → typing_context → type → Prop :=
  | pctx_typed_HolePCtx : pctx_typed Δ Γ A HolePCtx Δ Γ A
  | pctx_typed_AppLPCtx K e2 B C Δ' Γ':
    pctx_typed Δ Γ A K Δ' Γ' (B → C) →
    TY Δ'; Γ' ⊢ e2 : B →
    pctx_typed Δ Γ A (AppLPCtx K e2) Δ' Γ' C
  | pctx_typed_AppRPCtx e1 K B C Δ' Γ':
    (TY Δ'; Γ' ⊢ e1 : Fun B C) →
    pctx_typed Δ Γ A K Δ' Γ' B →
    pctx_typed Δ Γ A (AppRPCtx e1 K) Δ' Γ' C
  | pctx_typed_TLamPCtx K B Δ' Γ':
    pctx_typed Δ Γ A K (S Δ') (⤉ Γ') B →
    pctx_typed Δ Γ A (TLamPCtx K) Δ' Γ' (∀: B)
  | pctx_typed_TAppPCtx K B C Δ' Γ':
    type_wf Δ' C →
    pctx_typed Δ Γ A K Δ' Γ' (∀: B) →
    pctx_typed Δ Γ A (TAppPCtx K) Δ' Γ' (B.[C/])
  | pctx_typed_PackPCtx K B C Δ' Γ':
      type_wf Δ' C →
      type_wf (S Δ') B →
      pctx_typed Δ Γ A K Δ' Γ' (B.[C/]) →
      pctx_typed Δ Γ A (PackPCtx K) Δ' Γ' (∃: B)
  | pctx_typed_UnpackLPCtx (x: string) K e2 B C Δ' Γ' :
      type_wf Δ' C →
      pctx_typed Δ Γ A K Δ' Γ' (∃: B) →
      (TY S Δ'; (<[x := B]> (⤉ Γ')) ⊢ e2 : C.[ren (+1)]) →
      pctx_typed Δ Γ A (UnpackLPCtx x K e2) Δ' Γ' C
  | pctx_typed_UnpackRPCtx (x: string) e1 K B C Δ' Γ' :
      type_wf Δ' C →
      (TY Δ'; Γ' ⊢ e1 : (∃: B)) →
      (pctx_typed Δ Γ A K (S Δ') (<[x := B]> (⤉ Γ')) (C.[ren (+1)])) →
      pctx_typed Δ Γ A (UnpackRPCtx x e1 K) Δ' Γ' C
  | pctx_typed_UnOpPCtx op K Δ' Γ' B C:
    un_op_typed op B C →
    pctx_typed Δ Γ A K Δ' Γ' B →
    pctx_typed Δ Γ A (UnOpPCtx op K) Δ' Γ' C
  | pctx_typed_BinOpLPCtx op K e2 B1 B2 C Δ' Γ' :
    bin_op_typed op B1 B2 C →
    pctx_typed Δ Γ A K Δ' Γ' B1 →
    TY Δ'; Γ' ⊢ e2 : B2 →
    pctx_typed Δ Γ A (BinOpLPCtx op K e2) Δ' Γ' C
  | pctx_typed_BinOpRPCtx op K e1 B1 B2 C Δ' Γ' :
    bin_op_typed op B1 B2 C →
    TY Δ'; Γ' ⊢ e1 : B1 →
    pctx_typed Δ Γ A K Δ' Γ' B2 →
    pctx_typed Δ Γ A (BinOpRPCtx op e1 K) Δ' Γ' C
  | pctx_typed_IfPCtx K e1 e2 B Δ' Γ' :
    pctx_typed Δ Γ A K Δ' Γ' Bool →
    TY Δ'; Γ' ⊢ e1 : B →
    TY Δ'; Γ' ⊢ e2 : B →
    pctx_typed Δ Γ A (IfPCtx K e1 e2) Δ' Γ' B
  | pctx_typed_IfTPCtx K e e2 B Δ' Γ' :
    TY Δ'; Γ' ⊢ e : Bool →
    pctx_typed Δ Γ A K Δ' Γ' B →
    TY Δ'; Γ' ⊢ e2 : B →
    pctx_typed Δ Γ A (IfTPCtx e K e2) Δ' Γ' B
  | pctx_typed_IfEPCtx K e e1 B Δ' Γ' :
    TY Δ'; Γ' ⊢ e : Bool →
    TY Δ'; Γ' ⊢ e1 : B →
    pctx_typed Δ Γ A K Δ' Γ' B →
    pctx_typed Δ Γ A (IfEPCtx e e1 K) Δ' Γ' B
  | pctx_typed_PairLPCtx K e2 B1 B2 Δ' Γ' :
    pctx_typed Δ Γ A K Δ' Γ' B1 →
    TY Δ'; Γ' ⊢ e2 : B2 →
    pctx_typed Δ Γ A (PairLPCtx K e2) Δ' Γ' (Prod B1 B2)
  | pctx_typed_PairRPCtx K e1 B1 B2 Δ' Γ' :
    TY Δ'; Γ' ⊢ e1 : B1 →
    pctx_typed Δ Γ A K Δ' Γ' B2 →
    pctx_typed Δ Γ A (PairRPCtx e1 K) Δ' Γ' (Prod B1 B2)
  | pctx_typed_FstPCtx K Δ' Γ' B C:
    pctx_typed Δ Γ A K Δ' Γ' (Prod B C) →
    pctx_typed Δ Γ A (FstPCtx K) Δ' Γ' B
  | pctx_typed_SndPCtx K Δ' Γ' B C:
    pctx_typed Δ Γ A K Δ' Γ' (Prod B C) →
    pctx_typed Δ Γ A (SndPCtx K) Δ' Γ' C
  | pctx_typed_InjLPCtx K Δ' Γ' B C:
    type_wf Δ' C →
    pctx_typed Δ Γ A K Δ' Γ' B →
    pctx_typed Δ Γ A (InjLPCtx K) Δ' Γ' (Sum B C)
  | pctx_typed_InjRPCtx K Δ' Γ' B C:
    type_wf Δ' B →
    pctx_typed Δ Γ A K Δ' Γ' C →
    pctx_typed Δ Γ A (InjRPCtx K) Δ' Γ' (Sum B C)
  | pctx_typed_CasePCtx K e1 e2 B C D Δ' Γ' :
    pctx_typed Δ Γ A K Δ' Γ' (Sum B C) →
    TY Δ'; Γ' ⊢ e1 : (Fun B D) →
    TY Δ'; Γ' ⊢ e2 : (Fun C D) →
    pctx_typed Δ Γ A (CasePCtx K e1 e2) Δ' Γ' D
  | pctx_typed_CaseTPCtx K e e2 B C D Δ' Γ' :
    TY Δ'; Γ' ⊢ e : (Sum B C) →
    pctx_typed Δ Γ A K Δ' Γ' (Fun B D) →
    TY Δ'; Γ' ⊢ e2 : (Fun C D) →
    pctx_typed Δ Γ A (CaseTPCtx e K e2) Δ' Γ' D
  | pctx_typed_CaseEPCtx K e e1 B C D Δ' Γ' :
    TY Δ'; Γ' ⊢ e : (Sum B C) →
    TY Δ'; Γ' ⊢ e1 : (Fun B D) →
    pctx_typed Δ Γ A K Δ' Γ' (Fun C D) →
    pctx_typed Δ Γ A (CaseEPCtx e e1 K) Δ' Γ' D
  | pctx_typed_named_LamPCtx (x: string) K B C Γ' Δ' :
    type_wf Δ' B →
    pctx_typed Δ Γ A K Δ' (<[x := B]> Γ') C →
    pctx_typed Δ Γ A (LamPCtx x K) Δ' Γ' (Fun B C)
  | pctx_typed_anon_LamPCtx K B C Γ' Δ' :
    type_wf Δ' B →
    pctx_typed Δ Γ A K Δ' Γ' C →
    pctx_typed Δ Γ A (LamPCtx BAnon K) Δ' Γ' (Fun B C)
  .


Lemma pfill_typed C Δ Δ' Γ Γ' e A B:
  pctx_typed Δ Γ A C Δ' Γ' B → TY Δ; Γ ⊢ e : A → TY Δ'; Γ' ⊢ pfill C e : B.
Proof.
  induction 1 in |-*; simpl; eauto using pctx_typed.
Qed.


Lemma syn_typed_closed Δ Γ A e:
  TY Δ; Γ ⊢ e : A →
  is_closed (elements (dom Γ)) e.
Proof.
  intros Hty; eapply syn_typed_closed; eauto.
  intros x Hx. by eapply elem_of_elements.
Qed.

Lemma pctx_typed_fill_closed Δ Δ' Γ Γ' A B K e:
  is_closed (elements (dom Γ)) e →
  pctx_typed Δ Γ A K Δ' Γ' B →
  is_closed (elements (dom Γ')) (pfill K e).
Proof.
  intros Hcl. induction 1; simplify_closed; eauto using syn_typed_closed.
  - eapply is_closed_weaken; first by eapply syn_typed_closed.
    rewrite dom_insert.
    intros y Hin. destruct (decide (x = y)); subst; first set_solver.
    eapply elem_of_elements in Hin. eapply elem_of_union in Hin as [].
    + set_solver.
    + rewrite dom_fmap in H2. eapply list_elem_of_further.
      by eapply elem_of_elements.
  - rewrite dom_insert.
    intros y Hin. destruct (decide (x = y)); subst; first set_solver.
    eapply elem_of_elements in Hin. eapply elem_of_union in Hin as [].
    + set_solver.
    + rewrite dom_fmap in H2. eapply list_elem_of_further.
      by eapply elem_of_elements.
  - rewrite dom_insert.
    intros y Hin. destruct (decide (x = y)); subst; first set_solver.
    eapply elem_of_elements in Hin. eapply elem_of_union in Hin as [].
    + set_solver.
    + eapply list_elem_of_further.
      by eapply elem_of_elements.
Qed.


Lemma sem_typed_congruence Δ Δ' Γ Γ' e1 e2 C A B  :
  closed (elements (dom Γ)) e1 →
  closed (elements (dom Γ)) e2 →
  TY Δ; Γ ⊨ e1 ≈ e2 : A →
  pctx_typed Δ Γ A C Δ' Γ' B →
  TY Δ'; Γ' ⊨ pfill C e1 ≈ pfill C e2 : B.
Proof.
  intros ???.
  induction 1; simpl; eauto using sem_soundness.
  - inversion H2; subst; eauto using sem_soundness.
  - inversion H2; subst; eauto using sem_soundness.
Qed.

Lemma adequacy δ e1 e2: ℰ Int δ e1 e2 → ∃ n, big_step e1 n ∧ big_step e2 n.
Proof.
  simp type_interp. intros (? & ? & ? & ? & Hty).
  simp type_interp  in Hty. naive_solver.
Qed.


Definition ctx_equiv Δ Γ e1 e2 A :=
  ∀ K, pctx_typed Δ Γ A K 0 ∅ Int → ∃ n: Z, big_step (pfill K e1) #n ∧ big_step (pfill K e2) #n.


Lemma sem_typing_ctx_equiv Δ Γ e1 e2 A :
  (* the closedness assumptions could be replaced by typing assumptions *)
  closed (elements (dom Γ)) e1 →
  closed (elements (dom Γ)) e2 →
  TY Δ; Γ ⊨ e1 ≈ e2 : A → ctx_equiv Δ Γ e1 e2 A.
Proof.
  intros Hcl Hcl' Hsem C Hty. eapply sem_typed_congruence in Hty as (Htycl & Htycl' & Hty); last done.
  all: try done.
  opose proof* (Hty ∅ ∅ δ_any) as He; first constructor.
  revert He. rewrite !subst_map_empty.
  simp type_interp. destruct 1 as (v1 & v2 & Hbs1 & Hbs2 & Hv).
  simp type_interp in Hv. destruct Hv as (z & -> & ->). eauto.
Qed.

Lemma soundness_wrt_ctx_equiv Δ Γ e1 e2 A :
  TY Δ; Γ ⊢ e1 : A →
  TY Δ; Γ ⊢ e2 : A →
  TY Δ; Γ ⊨ e1 ≈ e2 : A →
  ctx_equiv Δ Γ e1 e2 A.
Proof.
  intros ???; eapply sem_typing_ctx_equiv; eauto.
  all: by eapply syn_typed_closed.
Qed.
