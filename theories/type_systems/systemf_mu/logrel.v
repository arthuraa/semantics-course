From stdpp Require Import gmap base relations.
From iris Require Import prelude.
From semantics.lib Require Export facts.
From semantics.ts.systemf_mu Require Import lang notation types tactics pure parallel_subst.
From Equations Require Export Equations.

(** * Logical relation for SystemF + recursive types *)

Implicit Types
  (Δ : nat)
  (Γ : typing_context)
  (v : val)
  (α : var)
  (e : expr)
  (A : type).


(** ** Definition of the logrel *)
(** A semantic type consists of a value-predicate parameterized over a step-index,
   a proof of closedness, and a proof of downwards-closure wrt step-indices. *)
Record sem_type := mk_ST {
  sem_type_car :> nat → val → Prop;
  sem_type_closed_val k v : sem_type_car k v → is_closed [] v;
  sem_type_mono : ∀ k k' v, sem_type_car k v → k' ≤ k → sem_type_car k' v
  }.

(** Two tactics we will use later on.
  [pose_sem_type P as N] defines a semantic type at name [N] with the value predicate [P].
 *)
(* slightly complicated formulation to make the proof term [p] opaque and prevent it from polluting the context *)
Tactic Notation "pose_sem_type" uconstr(P) "as" ident(N) :=
  let p := fresh "__p" in
  let p2 := fresh "__p2" in
  unshelve refine ((λ p p2, let N := (mk_ST P p p2) in _) _ _); first (simpl in p, p2); cycle 1.
Tactic Notation "specialize_sem_type" constr(S) "with" uconstr(P) "as" ident(N) :=
  pose_sem_type P as N; last specialize (S N).

(** We represent type variable assignments [δ] as functions [f] into semantic types.
  The variable [#n] (in De Bruijn representation) is mapped to [f n].
 *)
Definition tyvar_interp := var → sem_type.
Implicit Types
  (δ : tyvar_interp)
  (τ : sem_type)
.

(**
  In Rocq, we need to make argument why the logical relation is well-defined precise:
  (for Rocq, that means: we need to show that the recursion is terminating).

  Adding in the recursion over step-indices makes the termination argument slightly more complicated:
    we now have a mutual recursion over types, step-indices, and the case of the logrel (the expression relation is defined in terms of the value relation).

  To make this formal, we define a well-founded relation that allows to either decrease the step-index, the type, or switch from the expression case to the value case for recursive calls.
  We define size measures for for all three of these things, and then combine them into a big lexicographic ordering [term_rel].
 *)
Equations type_size (A : type) : nat :=
  type_size Int := 1;
  type_size Bool := 1;
  type_size Unit := 1;
  type_size (A → B) := type_size A + type_size B + 1;
  type_size (#α) := 1;
  type_size (∀: A) := type_size A + 2;
  type_size (∃: A) := type_size A + 2;
  type_size (A × B) := type_size A + type_size B + 1;
  type_size (A + B) := max (type_size A) (type_size B) + 1;
  type_size (μ: A) := type_size A + 2
.
(* [ltof A R] defines a well-founded measure on type [A] by using a mapping [R] from [A] to [nat]
  (it lifts the < relation on natural numbers to [A]) *)
Definition type_lt := ltof type type_size.
#[local] Instance type_lt_wf : WellFounded type_lt.
Proof. apply well_founded_ltof. Qed.

Inductive val_or_expr : Type :=
| inj_val : val → val_or_expr
| inj_expr : expr → val_or_expr.

Definition val_or_expr_size (ve : val_or_expr) : nat :=
  match ve with | inj_val _ => 0 | inj_expr _ => 1 end.
Definition val_or_expr_lt := ltof val_or_expr val_or_expr_size.
#[local] Instance val_or_expr_lt_wf : WellFounded val_or_expr_lt.
Proof. apply well_founded_ltof. Qed.

Definition term_rel := Subterm.lexprod nat (type * val_or_expr) lt (Subterm.lexprod type val_or_expr type_lt val_or_expr_lt).
#[local] Instance term_rel_wf : WellFounded term_rel. apply _. Qed.

(** *** The logical relation *)
(** Since the relation is step-indexed now, and the argument that the case for recursive types is well-formed
  fundamentally requires decreasing the step-index, we also need to convince Equations that this definition is well-formed!
   We do this by providing a well-founded termination relation [term_rel] that decreases for each recursive call.
 *)
Equations type_interp (ve : val_or_expr) (t : type) δ (k : nat) : Prop
  by wf (k, (t, ve)) term_rel := {

  type_interp (inj_val v) Int δ k =>
    ∃ z : Z, v = #z ;
  type_interp (inj_val v) Bool δ k =>
    ∃ b : bool, v = #b ;
  type_interp (inj_val v) Unit δ k =>
    v = #LitUnit ;
  type_interp (inj_val v) (A × B) δ k =>
    ∃ v1 v2 : val, v = (v1, v2)%V ∧ type_interp (inj_val v1) A δ k ∧ type_interp (inj_val v2) B δ k;
  type_interp (inj_val v) (A + B) δ k =>
    (∃ v' : val, v = InjLV v' ∧ type_interp (inj_val v') A δ k) ∨
    (∃ v' : val, v = InjRV v' ∧ type_interp (inj_val v') B δ k);

  type_interp (inj_val v) (A → B) δ k =>
    ∃ x e, v = LamV x e ∧ is_closed (x :b: nil) e ∧
      (* We write ∀ (H:k' ≤ k), .. instead of k' ≤ k → .. due to a longstanding Rocq quirk, see
               https://coq.zulipchat.com/#narrow/stream/237977-Rocq-users/topic/.60Program.60.20and.20variable.20names/near/404824378 *)
      ∀ v' k' (H:k' ≤ k),
        type_interp (inj_val v') A δ k' →
        type_interp (inj_expr (subst' x (of_val v') e)) B δ k' ;
  type_interp (inj_val v) (#α) δ k =>
    (δ α).(sem_type_car) k v;
  type_interp (inj_val v) (∀: A) δ k =>
    ∃ e, v = TLamV e ∧ is_closed [] e ∧
      ∀ τ, type_interp (inj_expr e) A (τ .: δ) k;
  type_interp (inj_val v) (∃: A) δ k =>
    ∃ v', v = PackV v' ∧
      ∃ τ : sem_type, type_interp (inj_val v') A (τ .: δ) k;
  (** Recursive type case *)
  type_interp (inj_val v) (μ: A) δ k =>
    ∃ v', v = (roll v')%V ∧ is_closed [] v' ∧ ∀ k' (H:k' < k), type_interp (inj_val v') (A.[μ: A/]%ty) δ k';

  type_interp (inj_expr e) t δ k =>
    ∀ e' n, n < k → red_nsteps n e e' → ∃ v, to_val e' = Some v ∧ type_interp (inj_val v) t δ (k - n)
}.

(** Proving that the arguments are decreasing for recursive calls is a bit more messy now, but it's mostly systematic.
  Therefore we provide a simple automation tactic that will also become useful a few times below.
*)
Ltac dsimpl :=
  repeat match goal with
  | |- term_rel (?k, _) (?k, _) =>
      (* step-index is not decreasing, go right *)
      right
  | |- term_rel (?k1, _) (?k2, _) =>
      (* use [lia] to decide where to go *)
      destruct (decide (k1 < k2)) as [ ? | ?]; [left; lia | assert (k1 = k2) as -> by lia; right]
  | |- Subterm.lexprod type val_or_expr _ _ (?t, _) (?t, _) =>
      (* type is not decreasing, go right *)
      right
  | |- Subterm.lexprod type val_or_expr _ _ (_, ?a) (_, ?a) =>
      (* type case is not decreasing, go left *)
      left
  | |- term_rel (_, _) (_, _) =>
      (* branch non-deterministically and try to solve the remaining goal *)
      first [left; solve [dsimpl] | right; solve [dsimpl]]
  | |- Subterm.lexprod type val_or_expr  _ _ _ _ =>
      (* branch non-deterministically *)
      first [left; solve [dsimpl] | right; solve [dsimpl]]
  | _ =>
      (* try to solve a leaf, i.e. a [type_lt], [val_or_expr_lt] or [lt] goal *)
      unfold val_or_expr_lt, type_lt, ltof; simp type_size; simpl; try lia
  end.
(** The tactic solves all of Equations' obligations for showing that the argument decreases. *)
Solve Obligations with (intros; dsimpl).

(** *** Value relation and expression relation *)
Notation sem_val_rel A δ k v := (type_interp (inj_val v) A δ k).
Notation sem_expr_rel A δ k e := (type_interp (inj_expr e) A δ k).

Notation 𝒱 A δ k v := (sem_val_rel A δ k v).
Notation ℰ A δ k v := (sem_expr_rel A δ k v).

Lemma val_rel_is_closed v δ k A:
  𝒱 A δ k v → is_closed [] (of_val v).
Proof.
  induction A as [ | | | | | A IHA | | A IH1 B IH2 | A IH1 B IH2 | A IHA] in k, v, δ |-*; simp type_interp.
  - by eapply sem_type_closed_val.
  - intros [z ->]. done.
  - intros [b ->]. done.
  - intros ->. done.
  - intros (e & -> & ? & _). done.
  - intros (v' & -> & (τ & Hinterp)). simpl. by eapply IHA.
  - intros (x & e & -> & ? & _). done.
  - intros (v1 & v2 & -> & ? & ?). simpl; apply andb_True; split; eauto.
  - intros [(v' & -> & ?) | (v' & -> & ?)]; simpl; eauto.
  - intros (v' & -> & ? & Ha); done.
Qed.


(** This is the Value Inclusion lemma from the lecture notes *)
Lemma sem_val_expr_rel A δ k v :
  𝒱 A δ k v → ℰ A δ k (of_val v).
Proof.
  simp type_interp. intros Hv e' n Hn [-> ->]%nsteps_val_inv.
  rewrite to_of_val. eexists; split; first done.
  replace (k - 0) with k by lia. done.
Qed.
Lemma sem_val_expr_rel' A δ k v e:
  to_val e = Some v →
  𝒱 A δ k v → ℰ A δ k e.
Proof.
  intros <-%of_to_val. apply sem_val_expr_rel.
Qed.

Lemma sem_expr_rel_zero_trivial A δ e :
  ℰ A δ 0 e.
Proof.
  simp type_interp. intros ???. lia.
Qed.

Lemma sem_expr_rel_of_val A δ k v :
  k > 0 → ℰ A δ k (of_val v) → 𝒱 A δ k v.
Proof.
  simp type_interp.
  intros Hk He. destruct (He (of_val v) 0 ltac:(lia)) as (v' & Hv & Hvr).
  { split; first constructor. apply val_irreducible. rewrite to_of_val. eauto. }
  rewrite to_of_val in Hv. injection Hv as [= <-].
  replace k with (k - 0) by lia. done.
Qed.


(** *** Downwards closure wrt step-index *)
(** Formally proving that the expression and value relations are downwards-closed wrt the step-index
    (see the lemmas [val_rel_mono] and [expr_rel_mono] below) is slightly involved:
    Intuitively, we'd like to do an inductive argument, since the "base cases" (Int, Bool, etc.) of the
    relation are trivially downwards-closed and the other cases inductively preserve this fact.
    However, since the relation is defined via recursion on both types and the step-index, we need to
    do an induction on both simultaneously.

    For that, we do a well-founded induction with the termination relation [term_rel_wf] we gave to prove
    well-formedness of the logical relation.
    We can use the inductive hypothesis whenever either the type or the step-index decreases, or we switch from
    the expression case to the value case.
 *)
Lemma type_interp_mono : ∀ '(k, (A, ve)) δ k', k' ≤ k → type_interp ve A δ k → type_interp ve A δ k'.
Proof.
  eapply (well_founded_ind (R := term_rel) term_rel_wf).
  intros (k & A & []) IH δ k'; first last.
  { (* expression rel *)
    intros Hk He. simp type_interp in He. simp type_interp. intros e' n Hn Hred.
    destruct (He e' n ltac:(lia) Hred) as (v & Hval & Hv).
    exists v. split; first done.
    eapply (IH (k-n, (A, inj_val v))); [ | lia | done].
    (* show that the induction is decreasing *)
    dsimpl.
  }
  intros Hk Hv.
  destruct A as [x | | | | A | A | A B | A B | A B | A ]; simp type_interp; simp type_interp in Hv.
  - (* var case *)
    by eapply sem_type_mono.
  - (* universal case *)
    destruct Hv as (e & -> & ? & Hv).
    exists e. split_and!; [done.. | ]. intros τ.
    eapply (IH (k, (A, inj_expr e))); [ dsimpl | done | done].
  - (* existential case *)
    destruct Hv as (v' & -> & (τ & Hv)). exists v'. split; first done.
    exists τ. eapply (IH (k, (A, _))); [ dsimpl | done..].
  - (* fun case *)
    destruct Hv as (x & e & -> & ? & Hv). exists x, e. split_and!; [done..| ].
    intros v' k'' Hk'' Hv'.
    apply Hv, Hv'. lia.
  - (* pair case *)
    destruct Hv as (v1 & v2 & -> & Hv1 & Hv2).
    exists v1, v2. split_and!; first done.
    all: eapply (IH (k, (_, _))); [ dsimpl | done..].
  - (* sum case *)
    destruct Hv as [(v' & -> & Hv) | (v' & -> & Hv)]; [ left | right].
    all: exists v'; split; first done.
    all: eapply (IH (k, (_, _))); [ dsimpl | done..].
  - (* rec case *)
    destruct Hv as (v' & -> & ? & Hv).
    exists v'. split_and!; [ done.. | ].
    intros k'' Hk''. apply Hv. lia.
Qed.

(** We can now derive the two desired lemmas *)
Lemma val_rel_mono A δ k k' v : k' ≤ k → 𝒱 A δ k v → 𝒱 A δ k' v.
Proof. apply (type_interp_mono (k, (A, inj_val v))). Qed.
Lemma expr_rel_mono A δ k k' e : k' ≤ k → ℰ A δ k e → ℰ A δ k' e.
Proof. apply (type_interp_mono (k, (A, inj_expr e))). Qed.


(** Interpret a syntactic type *)
Program Definition interp_type A δ : sem_type := {|
  sem_type_car := fun k v => 𝒱 A δ k v;
|}.
Next Obligation. by eapply val_rel_is_closed. Qed.
Next Obligation. by eapply val_rel_mono. Qed.

(** Semantic typing of contexts *)
Implicit Types
  (θ : gmap string expr).

(** Context relation *)
Inductive sem_context_rel (δ : tyvar_interp) (k : nat) : typing_context → (gmap string expr) → Prop :=
  | sem_context_rel_empty : sem_context_rel δ k ∅ ∅
  | sem_context_rel_insert Γ θ v x A :
    𝒱 A δ k v →
    sem_context_rel δ k Γ θ →
    sem_context_rel δ k (<[x := A]> Γ) (<[x := of_val v]> θ).

Notation 𝒢 := sem_context_rel.


(** *** Semantic typing judgment *)
Definition sem_typed Δ Γ e A :=
  is_closed (elements (dom Γ)) e ∧
  ∀ θ δ k, 𝒢 δ k Γ θ → ℰ A δ k (subst_map θ e).
Notation "'TY' Δ ;  Γ ⊨ e : A" := (sem_typed Δ Γ e A) (at level 74, e, A at next level).


Lemma sem_context_rel_vals {δ k Γ θ x A} :
  sem_context_rel δ k Γ θ →
  Γ !! x = Some A →
  ∃ e v, θ !! x = Some e ∧ to_val e = Some v ∧ 𝒱 A δ k v.
Proof.
  induction 1 as [|Γ θ v y B Hvals Hctx IH].
  - naive_solver.
  - rewrite lookup_insert_Some. intros [[-> ->]|[Hne Hlook]].
    + do 2 eexists. split; first by rewrite lookup_insert.
      split; first by eapply to_of_val. done.
    + eapply IH in Hlook as (e & w & Hlook & He & Hval).
      do 2 eexists; split; first by rewrite lookup_insert_ne.
      split; first done. done.
Qed.

Lemma sem_context_rel_dom δ k Γ θ :
  𝒢 δ k Γ θ → dom Γ = dom θ.
Proof.
  induction 1.
  - by rewrite !dom_empty.
  - rewrite !dom_insert. congruence.
Qed.

Lemma sem_context_rel_dom_eq δ k Γ θ :
  𝒢 δ k Γ θ → dom Γ = dom θ.
Proof.
  induction 1 as [ | ??????? IH].
  - rewrite !dom_empty //.
  - rewrite !dom_insert IH //.
Qed.

Lemma sem_context_rel_closed δ k Γ θ:
  𝒢 δ k Γ θ → subst_is_closed [] θ.
Proof.
  induction 1 as [ | Γ θ v x A Hv Hctx IH]; rewrite /subst_is_closed.
  - naive_solver.
  - intros y e. rewrite lookup_insert_Some.
    intros [[-> <-]|[Hne Hlook]].
    + by eapply val_rel_is_closed.
    + eapply IH; last done.
Qed.

Lemma sem_context_rel_mono Γ δ k k' θ :
  k' ≤ k → 𝒢 δ k Γ θ → 𝒢 δ k' Γ θ.
Proof.
  intros Hk. induction 1 as [|Γ θ v y B Hvals Hctx IH]; constructor.
  - eapply val_rel_mono; done.
  - apply IH.
Qed.

Section boring_lemmas.
  (** The lemmas in this section are all quite boring and expected statements,
    but are quite technical to prove due to De Bruijn binders.
    We encourage to skip over the proofs of these lemmas.
  *)

  Lemma type_interp_ext  :
    ∀ '(k, (B, ve)), ∀ δ δ',
    (∀ n k v, δ n k v ↔ δ' n k v) →
    type_interp ve B δ k ↔ type_interp ve B δ' k.
  Proof.
    eapply (well_founded_ind (R := term_rel) term_rel_wf).
    intros (k & A & [v|e]) IH δ δ'; first last.
    { (* expression rel *)
      intros Hd. simp type_interp. eapply forall_proper; intros e'.
      eapply forall_proper; intros n. eapply if_iff; first done.
      eapply if_iff; first done. f_equiv. intros v. f_equiv.
      eapply (IH ((k - n), (A, inj_val v))); last done.
      (* show that the induction is decreasing *)
      dsimpl.
    }
    intros Hd. destruct A as [x | | | | A | A | A B | A B | A B | A ]; simp type_interp; eauto.
    - f_equiv; intros e. f_equiv. f_equiv.
      eapply forall_proper; intros τ.
      eapply (IH (_, (_, _))); first dsimpl.
      intros [|m] ?; simpl; eauto.
    - f_equiv; intros w. f_equiv. f_equiv. intros τ.
      eapply (IH (_, (_, _))); first dsimpl.
      intros [|m] ?; simpl; eauto.
    - f_equiv. intros ?. f_equiv. intros ?.
      f_equiv. f_equiv. eapply forall_proper. intros ?.
      eapply forall_proper. intros ?.
      eapply forall_proper. intros ?.
      eapply if_iff; by eapply (IH (_, (_, _))); first dsimpl.
    - f_equiv. intros ?. f_equiv. intros ?.
      f_equiv. f_equiv; by eapply (IH (_, (_, _))); first dsimpl.
    - f_equiv; f_equiv; intros ?; f_equiv; by eapply (IH (_, (_, _))); first dsimpl.
   - f_equiv; intros ?. f_equiv. f_equiv.
      eapply forall_proper; intros ?.
      eapply forall_proper; intros ?.
      by eapply (IH (_, (_, _))); first dsimpl.
  Qed.


  Lemma type_interp_move_ren :
    ∀ '(k, (B, ve)), ∀ δ σ, type_interp ve B (λ n, δ (σ n)) k ↔ type_interp ve (rename σ B) δ k.
  Proof.
    eapply (well_founded_ind (R := term_rel) term_rel_wf).
    intros (k & A & [v|e]) IH δ σ; first last.
    { (* expression rel *)
      simp type_interp. eapply forall_proper; intros e'.
      eapply forall_proper; intros n. eapply if_iff; first done.
      eapply if_iff; first done. f_equiv. intros v. f_equiv.
      eapply (IH (_, (_, _))).
      (* show that the induction is decreasing *)
      dsimpl.
    }
    destruct A as [x | | | | A | A | A B | A B | A B | A ]; simpl; simp type_interp; eauto.
    - f_equiv; intros e. f_equiv. f_equiv.
      eapply forall_proper; intros τ.
      etransitivity; last eapply (IH (_, (_, _))); last dsimpl.
      eapply (type_interp_ext (_, (_, _))).
      intros [|m] ?; simpl; eauto.
    - f_equiv; intros w. f_equiv. f_equiv. intros τ.
      etransitivity; last eapply (IH (_, (_, _))); last dsimpl.
      eapply (type_interp_ext (_, (_, _))).
      intros [|m] ?; simpl; eauto.
    - f_equiv. intros ?. f_equiv. intros ?.
      f_equiv. f_equiv. eapply forall_proper. intros ?.
      eapply forall_proper. intros ?.
      eapply forall_proper. intros ?.
      eapply if_iff; by eapply (IH (_, (_, _))); first dsimpl.
    - f_equiv. intros ?. f_equiv. intros ?.
      f_equiv. f_equiv; by eapply (IH (_, (_, _))); first dsimpl.
    - f_equiv; f_equiv; intros ?; f_equiv; by eapply (IH (_, (_, _))); first dsimpl.
    - f_equiv; intros ?. f_equiv. f_equiv.
      eapply forall_proper; intros ?.
      eapply forall_proper; intros ?.
      etransitivity; first eapply (IH (_, (_, _))); first dsimpl.
      (* NOTE: nice use of asimpl; :-) *)
      asimpl. done.
  Qed.


  Lemma type_interp_move_subst  :
    ∀ '(k, (B, ve)), ∀ δ σ, type_interp ve B (λ n, interp_type (σ n) δ) k ↔ type_interp ve (B.[σ]) δ k.
  Proof.
    eapply (well_founded_ind (R := term_rel) term_rel_wf).
    intros (k & A & [v|e]) IH δ σ; first last.
    { (* expression rel *)
      simp type_interp. eapply forall_proper; intros e'.
      eapply forall_proper; intros n. eapply if_iff; first done.
      eapply if_iff; first done. f_equiv. intros v. f_equiv.
      eapply (IH (_, (_, _))).
      (* show that the induction is decreasing *)
      dsimpl.
    }
    destruct A as [x | | | | A | A | A B | A B | A B | A ]; simpl; simp type_interp; eauto.
    - f_equiv; intros e. f_equiv. f_equiv.
      eapply forall_proper; intros τ.
      etransitivity; last eapply (IH (_, (_, _))); last dsimpl.
      eapply (type_interp_ext (_, (_, _))).
      intros [|m] ? ?; simpl.
      + asimpl. simp type_interp. done.
      + unfold up; simpl. etransitivity;
          last eapply (type_interp_move_ren (_, (_, _))).
        done.
    - f_equiv; intros w. f_equiv. f_equiv. intros τ.
      etransitivity; last eapply (IH (_, (_, _))); last dsimpl.
      eapply (type_interp_ext (_, (_, _))).
      intros [|m] ? ?; simpl.
      + asimpl. simp type_interp. done.
      + unfold up; simpl. etransitivity;
          last eapply (type_interp_move_ren (_, (_, _))).
        done.
    - f_equiv. intros ?. f_equiv. intros ?.
      f_equiv. f_equiv. eapply forall_proper. intros ?.
      eapply forall_proper. intros ?.
      eapply forall_proper. intros ?.
      eapply if_iff; by eapply (IH (_, (_, _))); first dsimpl.
    - f_equiv. intros ?. f_equiv. intros ?.
      f_equiv. f_equiv; by eapply (IH (_, (_, _))); first dsimpl.
    - f_equiv; f_equiv; intros ?; f_equiv; by eapply (IH (_, (_, _))); first dsimpl.
    - f_equiv; intros ?. f_equiv. f_equiv.
      eapply forall_proper; intros ?.
      eapply forall_proper; intros ?.
      etransitivity; first eapply (IH (_, (_, _))); first dsimpl.
      (* NOTE: nice use of asimpl; :-) *)
      asimpl. done.
  Qed.


  Lemma sem_val_rel_move_single_subst A B δ k v :
    𝒱 B (interp_type A δ .: δ) k v ↔ 𝒱 (B.[A/]) δ k v.
  Proof.
    etransitivity; last eapply (type_interp_move_subst (_, (_, _))).
    eapply (type_interp_ext (_, (_, _))).
    intros [| n] ? w; simpl; simp type_interp; done.
  Qed.

  Lemma sem_expr_rel_move_single_subst A B δ k e :
    ℰ B (interp_type A δ .: δ) k e ↔ ℰ (B.[A/]) δ k e.
  Proof.
    etransitivity; last eapply (type_interp_move_subst (_, (_, _))).
    eapply (type_interp_ext (_, (_, _))).
    intros [| n] ? w; simpl; simp type_interp; done.
  Qed.

  Lemma sem_val_rel_cons A δ k v τ :
    𝒱 A δ k v ↔ 𝒱 A.[ren (+1)] (τ .: δ) k v.
  Proof.
    etransitivity; last eapply (type_interp_move_subst (_, (_, _))).
    eapply (type_interp_ext (_, (_, _))).
    intros [| n] ? w; simpl; simp type_interp; done.
  Qed.

  Lemma sem_expr_rel_cons A δ k e τ :
    ℰ A δ k e ↔ ℰ A.[ren (+1)] (τ .: δ) k e.
  Proof.
    etransitivity; last eapply (type_interp_move_subst (_, (_, _))).
    eapply (type_interp_ext (_, (_, _))).
    intros [| n] ? w; simpl; simp type_interp; done.
  Qed.


  Lemma sem_context_rel_cons Γ k δ θ τ :
    𝒢 δ k Γ θ →
    𝒢 (τ .: δ) k (⤉ Γ) θ.
  Proof.
    induction 1 as [ | Γ θ v x A Hv Hctx IH]; simpl.
    - rewrite fmap_empty. constructor.
    - rewrite fmap_insert. constructor; last done.
      rewrite -sem_val_rel_cons. done.
  Qed.
End boring_lemmas.

(** Bind lemma *)
Lemma bind K e k δ A B :
  ℰ A δ k e →
  (∀ j v, j ≤ k → 𝒱 A δ j v → ℰ B δ j (fill K (of_val v))) →
  ℰ B δ k (fill K e).
Proof.
  intros H1 H2. simp type_interp in H1. simp type_interp.
  intros e' n Hn (j & e'' & Hj & Hred1 & Hred2)%red_nsteps_fill.
  specialize (H1 e'' j ltac:(lia) Hred1) as (v & Hev & Hv).
  specialize (H2 (k-j) v ltac:(lia) Hv).
  simp type_interp in H2.
  rewrite (of_to_val _ _ Hev) in H2.
  eapply H2 in Hred2; last lia.
  assert (k - n = k - j - (n - j)) as -> by lia.
  done.
Qed.

(** This is the closure-under-expansion lemma from the lecture notes *)
Lemma expr_det_step_closure e e' A δ k :
  det_step e e' →
  ℰ A δ (k - 1) e' →
  ℰ A δ k e.
Proof.
  simp type_interp. intros Hdet Hexpr e'' n Hn [? Hred]%(det_step_red _ e'); last done.
  destruct (Hexpr e'' (n -1)) as (v & Hev & Hv); [lia | done | ].
  exists v. split; first done. replace (k - n) with (k - 1 - (n - 1)) by lia. done.
Qed.

Lemma expr_det_steps_closure e e' A δ k n :
  nsteps det_step n e e' → ℰ A δ (k - n) e' → ℰ A δ k e.
Proof.
  induction 1 as [ | n e1 e2 e3 Hstep Hsteps IH] in k |-* .
  - replace (k - 0) with k by lia. done.
  - intros He.
    eapply expr_det_step_closure; first done.
    apply IH. replace (k - 1 - n) with (k - (S n)) by lia. done.
Qed.

(** ** Compatibility lemmas *)

Lemma compat_int Δ Γ z : TY Δ; Γ ⊨ (Lit $ LitInt z) : Int.
Proof.
  split; first done. 
  intros θ δ k _.
  eapply (sem_val_expr_rel _ _ _ #z).
  simp type_interp. eauto.
Qed.

Lemma compat_bool Δ Γ b : TY Δ; Γ ⊨ (Lit $ LitBool b) : Bool.
Proof.
  split; first done. 
  intros θ δ k _.
  eapply (sem_val_expr_rel _ _ _ #b). simp type_interp. eauto.
Qed.

Lemma compat_unit Δ Γ : TY Δ; Γ ⊨ (Lit $ LitUnit) : Unit.
Proof.
  split; first done. 
  intros θ δ k _.
  eapply (sem_val_expr_rel _ _ _ #LitUnit). simp type_interp. eauto.
Qed.

Lemma compat_var Δ Γ x A :
  Γ !! x = Some A →
  TY Δ; Γ ⊨ (Var x) : A.
Proof.
  intros Hx. split.
  { eapply bool_decide_pack, elem_of_elements, elem_of_dom_2, Hx. }
  intros θ δ k Hctx; simpl.
  specialize (sem_context_rel_vals Hctx Hx) as (e & v & He & Heq & Hv).
  rewrite He. simp type_interp.
  rewrite -(of_to_val _ _ Heq).
  intros e' n Hn [-> ->]%nsteps_val_inv.
  rewrite to_of_val. eexists; split; first done.
  replace (k -0) with k by lia. done.
Qed.

Lemma compat_app Δ Γ e1 e2 A B :
  TY Δ; Γ ⊨ e1 : (A → B) →
  TY Δ; Γ ⊨ e2 : A →
  TY Δ; Γ ⊨ (e1 e2) : B.
Proof.
  intros [Hfuncl Hfun] [Hargcl Harg]. split.
  { simpl. eauto. }
  intros θ δ k Hctx; simpl.
  specialize (Hfun _ _ _ Hctx).
  specialize (Harg _ _ _ Hctx).

  eapply (bind [AppRCtx _]); first done.
  intros j v Hj Hv. simpl.

  eapply (bind [AppLCtx _ ]).
  { eapply expr_rel_mono; last done. lia. }
  intros j' f Hj' Hf.

  simp type_interp in Hf. destruct Hf as (x & e & -> & Hcl & Hf).
  specialize (Hf v j' (ltac:(lia))).
  eapply expr_det_step_closure.
  { eapply det_step_beta. apply is_val_of_val. }
  eapply expr_rel_mono; last apply Hf; first lia.
  eapply val_rel_mono; last done. lia.
Qed.

Lemma is_closed_subst_map_delete X Γ (x: string) θ A e:
  closed X e →
  subst_is_closed [] θ →
  dom Γ = dom θ →
  (∀ y : string, y ∈ X → y ∈ dom (<[x:=A]> Γ)) →
  is_closed (x :b: []) (subst_map (delete x θ) e).
Proof.
  intros He Hθ Hdom1 Hdom2.
  eapply closed_subst_weaken; [ | | apply He].
  - eapply subst_is_closed_subseteq; last done.
    apply map_delete_subseteq.
  - intros y Hy%Hdom2 Hn. apply elem_of_list_singleton.
    apply not_elem_of_dom in Hn. apply elem_of_dom in Hy.
    destruct (decide (x = y)) as [<- | Hneq]; first done.
    rewrite lookup_delete_ne in Hn; last done.
    rewrite lookup_insert_ne in Hy; last done.
    move : Hn Hy. rewrite -elem_of_dom -not_elem_of_dom.
    rewrite Hdom1. done.
Qed.

(** Lambdas need to be closed by the context *)
Lemma compat_lam_named Δ Γ x e A B :
  TY Δ; (<[ x := A ]> Γ) ⊨ e : B →
  TY Δ; Γ ⊨ (Lam (BNamed x) e) : (A → B).
Proof.
  intros [Hbodycl Hbody]. split.
  { simpl. eapply is_closed_weaken; first eassumption. set_solver. }
  intros θ δ k Hctxt. simpl.
  eapply (sem_val_expr_rel _ _ _ (LamV x _)).
  simp type_interp.
  eexists (BNamed x), _. split_and!; [done| | ].
  { eapply is_closed_subst_map_delete; eauto.
    + eapply sem_context_rel_closed in Hctxt. naive_solver.
    + by eapply sem_context_rel_dom.
    + apply elem_of_elements.
  }

  intros v' k' Hk' Hv'.
  specialize (Hbody (<[ x := of_val v']> θ) δ k').
  simpl. rewrite subst_subst_map.
  2: { by eapply sem_context_rel_closed. }
  apply Hbody.
  apply sem_context_rel_insert; first done.
  eapply sem_context_rel_mono; last done. lia.
Qed.

Lemma is_closed_subst_map_anon X Γ θ e:
  closed X e →
  subst_is_closed [] θ →
  dom Γ = dom θ →
  (∀ y, y ∈ X → y ∈ dom Γ) →
  is_closed [] (subst_map θ e).
Proof.
  intros He Hθ Hdom1 Hdom2.
  eapply closed_subst_weaken; [ | | apply He].
  - eapply subst_is_closed_subseteq; done.
  - intros y Hy%Hdom2 Hn.
    apply not_elem_of_dom in Hn. apply elem_of_dom in Hy.
    move : Hn Hy. rewrite -elem_of_dom -not_elem_of_dom.
    rewrite Hdom1. done.
Qed.

Lemma compat_lam_anon Δ Γ e A B :
  TY Δ; Γ ⊨ e : B →
  TY Δ; Γ ⊨ (Lam BAnon e) : (A → B).
Proof.
  intros [Hbodycl Hbody]. split; first done.
  intros θ δ k Hctxt. simpl.
  eapply (sem_val_expr_rel _ _ _ (LamV BAnon _)).
  simp type_interp.
  eexists BAnon, _. split_and!; [done| | ].
  { eapply is_closed_subst_map_anon; eauto.
    + eapply sem_context_rel_closed in Hctxt. naive_solver.
    + by eapply sem_context_rel_dom.
    + apply elem_of_elements.
  }

  intros v' k' Hk' Hv'.
  apply (Hbody θ δ k').
  eapply sem_context_rel_mono; last done. lia.
Qed.

Lemma compat_int_binop Δ Γ op e1 e2 :
  bin_op_typed op Int Int Int →
  TY Δ; Γ ⊨ e1 : Int →
  TY Δ; Γ ⊨ e2 : Int →
  TY Δ; Γ ⊨ (BinOp op e1 e2) : Int.
Proof.
  intros Hop [He1cl He1] [He2cl He2].
  split; first naive_solver.

  intros θ δ k Hctx. simpl.
  specialize (He1 _ _ _ Hctx).
  specialize (He2 _ _ _ Hctx).

  eapply (bind [BinOpRCtx _ _]); first done.
  intros j v2 Hj Hv2. simpl.

  eapply (bind [BinOpLCtx _ _ ]).
  { eapply expr_rel_mono; last done. lia. }
  intros j' v1 Hj' Hv1.

  simp type_interp. intros e' n Hn Hred.
  simp type_interp in Hv1. simp type_interp in Hv2.
  destruct Hv1 as (z1 & ->). destruct Hv2 as (z2 & ->).

  inversion Hop; subst; simpl.
  all: eapply det_step_red in Hred as [ ? Hred]; [ |  eapply det_step_binop; done].
  all: apply nsteps_val_inv in Hred as [? ->].
  all: eexists; simpl; split; first done.
  all: simp type_interp; eauto.
Qed.

Lemma compat_int_bool_binop Δ Γ op e1 e2 :
  bin_op_typed op Int Int Bool →
  TY Δ; Γ ⊨ e1 : Int →
  TY Δ; Γ ⊨ e2 : Int →
  TY Δ; Γ ⊨ (BinOp op e1 e2) : Bool.
Proof.
  intros Hop [He1cl He1] [He2cl He2].
  split; first naive_solver.

  intros θ δ k Hctx. simpl.
  specialize (He1 _ _ _ Hctx).
  specialize (He2 _ _ _ Hctx).

  eapply (bind [BinOpRCtx _ _]); first done.
  intros j v2 Hj Hv2. simpl.

  eapply (bind [BinOpLCtx _ _ ]).
  { eapply expr_rel_mono; last done. lia. }
  intros j' v1 Hj' Hv1.

  simp type_interp. intros e' n Hn Hred.
  simp type_interp in Hv1. simp type_interp in Hv2.
  destruct Hv1 as (z1 & ->). destruct Hv2 as (z2 & ->).

  inversion Hop; subst; simpl.
  all: eapply det_step_red in Hred as [ ? Hred]; [ |  eapply det_step_binop; done].
  all: apply nsteps_val_inv in Hred as [? ->].
  all: eexists; simpl; split; first done.
  all: simp type_interp; eauto.
Qed.

Lemma compat_unop Δ Γ op A B e :
  un_op_typed op A B →
  TY Δ; Γ ⊨ e : A →
  TY Δ; Γ ⊨ (UnOp op e) : B.
Proof.
  intros Hop [Hecl He].
  split; first naive_solver.

  intros θ δ k Hctx. simpl.
  specialize (He _ _ _ Hctx).

  eapply (bind [UnOpCtx _]); first done.
  intros j v Hj Hv. simpl.

  simp type_interp. intros e' n Hn Hred.
  inversion Hop; subst.
  all: simp type_interp in Hv; destruct Hv as (? & ->).
  all: eapply det_step_red in Hred as [ ? Hred]; [ |  eapply det_step_unop; done].
  all: apply nsteps_val_inv in Hred as [? ->].
  all: eexists; simpl; split; first done.
  all: simp type_interp; eauto.
Qed.

Lemma compat_tlam Δ Γ e A :
  TY S Δ; (⤉ Γ) ⊨ e : A →
  TY Δ; Γ ⊨ (Λ, e) : (∀: A).
Proof.
  intros [Hecl He]. split.
  { simpl. by erewrite <-dom_fmap. }

  intros θ δ k Hctx. simpl.
  simp type_interp.
  intros e' n Hn Hred. eapply nsteps_val_inv' in Hred as [ -> ->]; last done.
  eexists; split; first done.
  simp type_interp.
  eexists _. split_and!; [ done | | ].
  { eapply is_closed_subst_map_anon; eauto.
    + eapply sem_context_rel_closed in Hctx; naive_solver.
    + by eapply sem_context_rel_dom.
    + rewrite dom_fmap. apply elem_of_elements.
  }

  intros τ. eapply He.
  replace (k -0) with k by lia. by eapply sem_context_rel_cons.
Qed.

Lemma compat_tapp Δ Γ e A B :
  type_wf Δ B →
  TY Δ; Γ ⊨ e : (∀: A) →
  TY Δ; Γ ⊨ (e <>) : (A.[B/]).
Proof.
  intros Hwf [Hecl He].
  split; first naive_solver.

  intros θ δ k Hctx. simpl.
  specialize (He _ _ _ Hctx).
  eapply (bind [TAppCtx]); first done.
  intros j v Hj Hv.
  simp type_interp in Hv.
  destruct Hv as (e' & -> & ? & He').

  set (τ := interp_type B δ).
  specialize (He' τ). simpl.
  eapply expr_det_step_closure.
  { apply det_step_tbeta. }
  eapply sem_expr_rel_move_single_subst.
  eapply expr_rel_mono; last done.
  lia.
Qed.

Lemma compat_pack Δ Γ e n A B :
  type_wf n B →
  type_wf (S n) A →
  TY n; Γ ⊨ e : A.[B/] →
  TY n; Γ ⊨ (pack e) : (∃: A).
Proof.
  intros Hwf1 Hwf2 [Hecl He].
  split; first naive_solver.

  intros θ δ k Hctx. simpl.

  specialize (He _ _ _ Hctx).
  eapply (bind [PackCtx]); first done.
  intros j v Hj Hv.
  simpl. eapply (sem_val_expr_rel _ _ _ (PackV v)).
  simp type_interp. exists v; split; first done.
  exists (interp_type B δ).
  apply sem_val_rel_move_single_subst. done.
Qed.

Lemma compat_unpack n Γ A B e e' x :
  type_wf n B →
  TY n; Γ ⊨ e : (∃: A) →
  TY S n; <[x:=A]> (⤉Γ) ⊨ e' : B.[ren (+1)] →
  TY n; Γ ⊨ (unpack e as BNamed x in e') : B.
Proof.
  intros Hwf [Hecl He] [He'cl He']. split.
  { simpl. apply andb_True. split; first done. eapply is_closed_weaken; first eassumption. set_solver. }
  intros θ δ k Hctx. simpl.

  specialize (He _ _ _ Hctx).
  eapply (bind [UnpackCtx _ _]); first done.
  intros j v Hj Hv.
  simp type_interp in Hv. destruct Hv as (v' & -> & τ & Hv').
  simpl.

  eapply expr_det_step_closure.
  { apply det_step_unpack. apply is_val_of_val. }
  simpl. rewrite subst_subst_map; last by eapply sem_context_rel_closed.

  specialize (He' (<[x := of_val v']> θ) (τ.:δ) (j - 1)).
  rewrite <-sem_expr_rel_cons in He'.
  apply He'.
  constructor.
  { eapply val_rel_mono; last done. lia. }
  apply sem_context_rel_cons.
  eapply sem_context_rel_mono; last done. lia.
Qed.

Lemma compat_if n Γ e0 e1 e2 A :
  TY n; Γ ⊨ e0 : Bool →
  TY n; Γ ⊨ e1 : A →
  TY n; Γ ⊨ e2 : A →
  TY n; Γ ⊨ (if: e0 then e1 else e2) : A.
Proof.
  intros [He0cl He0] [He1cl He1] [He2cl He2].
  split; first naive_solver.

  intros θ δ k Hctx. simpl.
  specialize (He0 _ _ _ Hctx).
  specialize (He1 _ _ _ Hctx).
  specialize (He2 _ _ _ Hctx).

  eapply (bind [IfCtx _ _]); first done.
  intros j v Hj Hv.
  simp type_interp in Hv. destruct Hv as (b & ->).
  simpl.

  destruct b.
  - eapply expr_det_step_closure.
    { apply det_step_if_true. }
    eapply expr_rel_mono; last done. lia.
  - eapply expr_det_step_closure.
    { apply det_step_if_false. }
    eapply expr_rel_mono; last done. lia.
Qed.

Lemma compat_pair Δ Γ e1 e2 A B :
  TY Δ; Γ ⊨ e1 : A →
  TY Δ; Γ ⊨ e2 : B →
  TY Δ; Γ ⊨ (e1, e2) : A × B.
Proof.
  intros [He1cl He1] [He2cl He2].
  split; first naive_solver.

  intros θ δ k Hctx. simpl.
  specialize (He1 _ _ _ Hctx).
  specialize (He2 _ _ _ Hctx).

  eapply (bind [PairRCtx _]); first done.
  intros j v2 Hj Hv2.
  eapply (bind [PairLCtx _]).
  { eapply expr_rel_mono; last done. lia. }
  intros j' v1 Hj' Hv1.

  simpl.
  eapply (sem_val_expr_rel _ _ _ (v1, v2)%V).
  simp type_interp. exists v1, v2. split_and!; first done.
  - done.
  - eapply val_rel_mono; last done. lia.
Qed.

Lemma compat_fst Δ Γ e A B :
  TY Δ; Γ ⊨ e : A × B →
  TY Δ; Γ ⊨ Fst e : A.
Proof.
  intros [Hecl He]. split; first naive_solver.

  intros θ δ k Hctx.
  specialize (He _ _ _ Hctx).
  simpl. eapply (bind [FstCtx]); first done.
  intros j v Hj Hv.
  simp type_interp in Hv. destruct Hv as (v1 & v2 & -> & Hv1 & Hv2).

  eapply expr_det_step_closure.
  { simpl. apply det_step_fst; apply is_val_of_val. }
  eapply sem_val_expr_rel. eapply val_rel_mono; last done. lia.
Qed.

Lemma compat_snd Δ Γ e A B :
  TY Δ; Γ ⊨ e : A × B →
  TY Δ; Γ ⊨ Snd e : B.
Proof.
  intros [Hecl He]. split; first naive_solver.

  intros θ δ k Hctx.
  specialize (He _ _ _ Hctx).
  simpl. eapply (bind [SndCtx]); first done.
  intros j v Hj Hv.
  simp type_interp in Hv. destruct Hv as (v1 & v2 & -> & Hv1 & Hv2).

  eapply expr_det_step_closure.
  { simpl. apply det_step_snd; apply is_val_of_val. }
  eapply sem_val_expr_rel. eapply val_rel_mono; last done. lia.
Qed.

Lemma compat_injl Δ Γ e A B :
  TY Δ; Γ ⊨ e : A →
  TY Δ; Γ ⊨ InjL e : A + B.
Proof.
  (* TODO: exercise *)
Admitted.


Lemma compat_injr Δ Γ e A B :
  TY Δ; Γ ⊨ e : B →
  TY Δ; Γ ⊨ InjR e : A + B.
Proof.
  (* TODO: exercise *)
Admitted.


Lemma compat_case Δ Γ e e1 e2 A B C :
  TY Δ; Γ ⊨ e : B + C →
  TY Δ; Γ ⊨ e1 : (B → A) →
  TY Δ; Γ ⊨ e2 : (C → A) →
  TY Δ; Γ ⊨ Case e e1 e2 : A.
Proof.
  (* TODO: exercise *)
Admitted.


Lemma compat_roll n Γ e A :
  TY n; Γ ⊨ e : (A.[(μ: A)%ty/]) →
  TY n; Γ ⊨ (roll e) : (μ: A).
Proof.
  intros [Hecl He]. split; first naive_solver.

  intros θ δ k Hctx. simpl.
  specialize (He _ _ _ Hctx).

  eapply (bind [RollCtx]); first done.
  intros j v Hj Hv.
  eapply (sem_val_expr_rel _ _ _ (RollV v)).

  specialize (val_rel_is_closed _ _ _ _ Hv) as ?.
  simp type_interp.
  exists v. split_and!; [done.. | ].
  intros k' Hk'. eapply val_rel_mono; last done. lia.
Qed.

Lemma compat_unroll n Γ e A :
  TY n; Γ ⊨ e : (μ: A) →
  TY n; Γ ⊨ (unroll e) : (A.[(μ: A)%ty/]).
Proof.
  intros [Hecl He]. split; first naive_solver.

  intros θ δ k Hctx. simpl.
  specialize (He _ _ _ Hctx).

  eapply (bind [UnrollCtx]); first done.
  intros j v Hj Hv.
  destruct j as [ | j]; first by apply sem_expr_rel_zero_trivial.
  simp type_interp in Hv. destruct Hv as (v' & -> & ? & Hv).
  eapply expr_det_step_closure.
  { simpl. apply det_step_unroll. apply is_val_of_val. }
  eapply sem_val_expr_rel. apply Hv. lia.
Qed.

Local Hint Resolve compat_var compat_lam_named compat_lam_anon compat_tlam compat_int compat_bool compat_unit compat_if compat_app compat_tapp compat_pack compat_unpack compat_int_binop compat_int_bool_binop compat_unop compat_pair compat_fst compat_snd compat_injl compat_injr compat_case compat_roll compat_unroll: core.

Lemma sem_soundness Δ Γ e A :
  TY Δ; Γ ⊢ e : A →
  TY Δ; Γ ⊨ e : A.
Proof.
  induction 1 as [ | Δ Γ x e A B Hsyn IH | Δ Γ e A B Hsyn IH| Δ Γ e A Hsyn IH| | | | |  | | | | n Γ e1 e2 op A B C [] ? ? ? ? | | | | | | | | | ]; eauto.
Qed.


(* dummy delta which we can use if we don't care *)
Program Definition any_type : sem_type := {| sem_type_car := λ k v, is_closed [] v |}.
Definition δ_any : var → sem_type := λ _, any_type.


Definition safe e :=
  ∀ e' n, red_nsteps n e e' → is_val e'.

Lemma type_safety e A :
  TY 0; ∅ ⊢ e : A →
  safe e.
Proof.
  intros [Hecl He]%sem_soundness e' n Hred.
  specialize (He ∅ δ_any (S n)). simp type_interp in He.
  rewrite subst_map_empty in He.
  edestruct (He ) as (v & Hv & _); [ | | eassumption | ].
  - constructor.
  - lia.
  - rewrite <- (of_to_val _ _ Hv). apply is_val_of_val.
Qed.


(** Additional lemmas *)
Lemma semantic_app A B δ k e1 e2 :
  ℰ (A → B) δ k e1 →
  ℰ A δ k e2 →
  ℰ B δ k (e1 e2).
Proof.
  intros He1 He2.
  eapply (bind [AppRCtx e1]); first done.
  intros j v Hj Hv. eapply (bind [AppLCtx _]).
  { eapply expr_rel_mono; last done. lia. }
  intros j' v' Hj' Hf.
  simp type_interp in Hf. destruct Hf as (x & e & -> & Hcl & Hf).
  eapply expr_det_step_closure.
  { apply det_step_beta. apply is_val_of_val. }
  apply Hf; first lia.
  eapply val_rel_mono; last done. lia.
Qed.
