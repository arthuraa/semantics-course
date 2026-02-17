From iris.proofmode Require Import proofmode.
From iris.heap_lang Require Import lang notation.
From iris.heap_lang Require Export metatheory.
From semantics.pl.reloc Require Import syntactic notation ghost_state proofmode logrel.
From semantics.pl.heap_lang Require Export proofmode.
From semantics.pl.program_logic Require Export notation.
From Autosubst Require Import Autosubst.
From iris.prelude Require Import options.

Section interp.
Context `{relocGS Σ}.

(** The interpretation into semantic types. This also serves as the value relation. *)
Fixpoint type_interp (A : type) : envO -n> semtypeO :=
  match A with
  | TVar x => var_interp x
  | TUnit => unit_interp
  | TInt => int_interp
  | TBool => bool_interp
  | TFun A B => fun_interp (type_interp A) (type_interp B)
  | TForall A => all_interp (type_interp A)
  | TExists A => exist_interp (type_interp A)
  | TMu A => mu_interp (type_interp A)
  | TRef A => ref_interp (type_interp A)
  | TProd A B => prod_interp (type_interp A) (type_interp B)
  | TSum A B => sum_interp (type_interp A) (type_interp B)
  end.
Notation 𝒱 := type_interp.

Implicit Type (γ : gmap string (val * val)).

(** The context relation *)
Program Definition context_interp Γ γ : envO -n> iPropO Σ :=
  λne δ, ([∗ map] x ↦ A; vs ∈ Γ; γ, 𝒱 A δ (fst vs) (snd vs))%I.
Solve Obligations with solve_proper.
Global Instance context_interp_pers Γ γ δ : Persistent (context_interp Γ γ δ).
Proof. apply _. Qed.
Notation 𝒢 := context_interp.

Lemma context_interp_dom_eq Γ γ δ :
  context_interp Γ γ δ -∗ ⌜dom Γ = dom γ⌝.
Proof. iApply big_sepM2_dom. Qed.

Lemma context_interp_empty δ :
  ⊢ 𝒢 ∅ ∅ δ.
Proof.
  by iApply big_sepM2_empty.
Qed.

Lemma context_interp_insert Γ γ δ A v v' x :
  𝒱 A δ v v' -∗
  𝒢 Γ γ δ -∗
  𝒢 (<[x := A]> Γ) (<[x := (v, v')]> γ) δ.
Proof.
  iIntros "Hv Hγ". iApply (big_sepM2_insert_2 with "[Hv] [Hγ]"); done.
Qed.

Lemma context_interp_lookup' Γ γ δ A x :
  ⌜Γ !! x = Some A⌝ -∗
  𝒢 Γ γ δ -∗
  ∃ v v', ⌜γ !! x = Some (v, v')⌝ ∗ 𝒱 A δ v v'.
Proof.
  iIntros (Hlook) "Hγ".
  iPoseProof (big_sepM2_lookup_l with "Hγ") as ([]) "(% & Ha)"; eauto.
Qed.

Lemma context_interp_lookup Γ γ δ A x :
  ⌜Γ !! x = Some A⌝ -∗
  𝒢 Γ γ δ -∗
  ∃ v v', ⌜(fst <$> γ) !! x = Some v⌝ ∗ ⌜(snd <$> γ) !! x = Some v'⌝ ∗ 𝒱 A δ v v'.
Proof.
  iIntros "Hlook Hγ".
  iPoseProof (context_interp_lookup' with "Hlook Hγ") as "(%v & %v' & %Hlook & Hv)".
  iExists _, _. iFrame. iSplit; by rewrite lookup_fmap Hlook.
Qed.

Notation ℰ := refines.

Implicit Types
  (δ : envO (Σ := Σ))
.
Notation "τ '.::' δ" := (consCtx τ δ) (at level 30).

Section boring_lemmas.
  (* ad-hoc tactic to solve the trivial cases *)
  Ltac try_solve_eq :=
  match goal with
  | |- pointwise_relation _ _ _ _ => intros ?
  | |- mk_semtype _ ≡ mk_semtype _ => intros ? ?; simpl
  | |- ofe_mor_car _ _ (ofe_mor_car _ _ consCtx _) _ ≡ _ => rewrite !consCtx_unfold; intros []; try done
  | |- _ =>
      match goal with
      (* don't [f_equiv] when we should apply the IH *)
      | |- ofe_mor_car _ _ (type_interp _) _ ≡ ofe_mor_car _ _ (type_interp _) _ => idtac
      | |- _ => f_equiv
      end
  end.

  Opaque consCtx.
  Lemma type_interp_ext B δ δ' :
    (∀ n, δ n ≡ δ' n) →
    𝒱 B δ ≡ 𝒱 B δ'.
  Proof.
    intros Hd. induction B; intros ? ?; simpl; f_equiv; eauto.
    all: try apply fixpoint_proper; try solve_proper.
  Qed.

  Lemma type_interp_move_ren B δ s :
    𝒱 B (λne n, δ (s n)) ≡ 𝒱 (rename s B) δ.
  Proof.
    induction B in δ, s |-*; intros ? ?; simpl; eauto; repeat try_solve_eq; try done.
    - (* universal *) rewrite -IHB; f_equiv. repeat try_solve_eq.
    - (* existential *) rewrite -IHB; f_equiv. repeat try_solve_eq.
    - (* recursive *) unfold mu_interp. apply fixpoint_proper. unfold mu_rec.
      intros ?. repeat try_solve_eq. rewrite -IHB.
      f_equiv. rewrite !consCtx_unfold; intros []; done.
  Qed.

  Lemma type_interp_move_subst B δ s :
    𝒱 B (λne n, 𝒱 (s n) δ) ≡ 𝒱 (B.[s]) δ.
  Proof.
    induction B in s, δ |-*; simpl; eauto; repeat try_solve_eq; try done.
    - (* universal *)
      etransitivity; last apply IHB.
      apply type_interp_ext.
      intros []; rewrite !consCtx_unfold; simpl; first done.
      unfold up; simpl. etransitivity; last apply type_interp_move_ren.
      simpl. f_equiv. done.
    - (* existential *)
      etransitivity; last apply IHB.
      apply type_interp_ext. intros []; rewrite !consCtx_unfold; simpl; first done.
      unfold up; simpl. etransitivity; last apply type_interp_move_ren.
      simpl. f_equiv. done.
    - (* recursive *)
      apply fixpoint_proper; intros ?; unfold mu_rec. repeat try_solve_eq.
      rewrite -IHB. f_equiv.
      rewrite !consCtx_unfold. intros []; simpl; first done.
      replace (up s (S n)) with (rename (+1) (s n)) by by asimpl.
      rewrite -type_interp_move_ren. f_equiv. simpl. intros ?; done.
  Qed.

  Lemma type_interp_move_single_subst A B δ v v' :
    𝒱 B ((𝒱 A δ) .:: δ) v v' ⊣⊢ 𝒱 (B.[A/]) δ v v'.
  Proof.
    f_equiv. etransitivity; last apply type_interp_move_subst.
    apply type_interp_ext. intros []; rewrite consCtx_unfold; simpl; done.
  Qed.

  Lemma expr_interp_move_single_subst A B δ e e' :
    ℰ e e' (𝒱 B ((𝒱 A δ) .:: δ)) ⊣⊢ ℰ e e' (𝒱 (B.[A/]) δ).
  Proof.
    f_equiv. intros ? ? -> ? ? ->. apply type_interp_move_single_subst.
  Qed.

  Lemma type_interp_cons A δ v v' τ :
    𝒱 A δ v v' ⊣⊢ 𝒱 A.[ren (+1)] (τ .:: δ) v v'.
  Proof.
    f_equiv. etransitivity; last apply type_interp_move_subst.
    apply type_interp_ext. intros []; rewrite consCtx_unfold; simpl; done.
  Qed.

  Lemma expr_interp_cons A δ e e' τ :
    ℰ e e' (𝒱 A δ) ⊣⊢ ℰ e e' (𝒱 A.[ren (+1)] (τ .:: δ)) .
  Proof.
    f_equiv. intros ? ? -> ?? ->. apply type_interp_cons.
  Qed.

  Lemma context_interp_cons Γ γ δ τ :
    𝒢 Γ γ δ -∗
    𝒢 (⤉ Γ) γ (τ .:: δ).
  Proof.
    iIntros "Hctx".
    iApply big_sepM2_fmap_l.
    iApply (big_sepM2_mono with "Hctx").
    iIntros (k A v HA Hv) "Hv". by rewrite type_interp_cons.
  Qed.
End boring_lemmas.

Definition sem_typed (n : nat) Γ e e' A : Prop :=
  ⊢ ∀ δ γ, 𝒢 Γ γ δ -∗ ℰ (subst_map (fst <$> γ) e) (subst_map (snd <$> γ) e') (𝒱 A δ).
Notation "'TY' Δ ;  Γ ⊨ e ':≤:' e' : A" := (sem_typed Δ Γ e e' A) (at level 74, e, e', A at next level).

Opaque context_interp.

Notation sub := heap_lang.subst.

(** Exercise: Prove the compatibility lemmas. *)
(** You will find the following tactics for source execution useful:
  - [src_bind e] binds a subexpression e in the source
  - [src_alloc l as "Hl"] allocates a location l in the source
  - [src_load] performs a load
  - [src_store] performs a store
 *)

(* The following tactic will be useful for applying bind:
  [smart_wp_bind e e' "Hs" v v' "Hv" He]
  will bind the subexpressions [e] and [e'] (in target and source),
  apply the semantic typing assumption [He] for it,
  and then introduce the resulting values [v] and [v'] (in target and source),
   as well as the interpretation ["Hv"] for [v] and [v'].
 *)
Local Lemma bi_sep_intro {X} (Φ Ψ : X → iProp Σ) (R : iProp Σ) :
  (∀ x : X, Φ x -∗ Ψ x -∗ R) -∗
  ((∃ x : X, Φ x ∗ Ψ x) -∗ R).
Proof.
  iIntros "Ha (%x & HP & HQ)". iApply ("Ha" with "HP HQ").
Qed.
Local Tactic Notation "smart_wp_bind"
    uconstr(e) uconstr(e') constr(Hs) ident(v) ident(v') constr(Hv) uconstr(Hp) :=
  src_bind e;
  wp_bind e;
  let itmp := iFresh in
  iPoseProof (Hp with "[//]") as itmp;
  iSpecialize (itmp with Hs);
  iApply (wp_wand with itmp);
  simpl; iIntros (v);
  iApply bi_sep_intro;
  iIntros (v'); iIntros Hs; iIntros Hv.


Lemma compat_beta Δ Γ e1 e1' e2 e2' A B :
  TY Δ; Γ ⊨ e1 :≤: e1' : (A → B) →
  TY Δ; Γ ⊨ e2 :≤: e2' : A →
  TY Δ; Γ ⊨ (e1 e2) :≤: (e1' e2') : B.
Proof.
  iIntros (He1 He2 δ γ) "#Hctx/=".
  iIntros (K) "Hs".

  smart_wp_bind (subst_map _ _) (subst_map _ _) "Hs" v2 v2' "Hv2" He2.
  (* more explicit: *)
  (*
  src_bind (subst_map _ _).
  wp_bind (subst_map _ _).
  iPoseProof (He2 with "[//] Hs") as "He2".
  iApply (wp_wand with "He2").
  iIntros (v2) "(%v2' & Hs & Hv2)".
   *)
  smart_wp_bind (subst_map _ _) (subst_map _ _) "Hs" v1 v1' "Hv1" He1.
  simpl. iApply ("Hv1" with "Hv2 Hs").
Qed.

Lemma compat_var Δ Γ (x : string) A :
  Γ !! x = Some A →
  TY Δ; Γ ⊨ x :≤: x : A.
Proof.
  (* FIXME exercise *)
Admitted.

Lemma compat_int Δ Γ (z : Z) :
  TY Δ; Γ ⊨ #z :≤: #z : TInt.
Proof.
  (* FIXME exercise *)
Admitted.

Lemma compat_bool Δ Γ (b : bool) :
  TY Δ; Γ ⊨ #b :≤: #b : TBool.
Proof.
  (* FIXME exercise *)
Admitted.


Lemma compat_unit Δ Γ :
  TY Δ; Γ ⊨ #() :≤: #() : TUnit.
Proof.
  (* FIXME exercise *)
Admitted.

Lemma compat_lambda Δ Γ (x : string) e e' A B :
  TY Δ; (<[x := A]> Γ) ⊨ e :≤: e' : B →
  TY Δ; Γ ⊨ (λ: x, e) :≤: (λ: x, e') : (A → B).
Proof.
  (* FIXME exercise *)
Admitted.

Lemma compat_lambda_anon Δ Γ e e' A B :
  TY Δ; Γ ⊨ e :≤: e' : B →
  TY Δ; Γ ⊨ (Lam BAnon e) :≤: (Lam BAnon e') : (A → B).
Proof.
  (* FIXME exercise *)
Admitted.

Lemma compat_binop Δ Γ e1 e1' e2 e2' A1 A2 B op :
  bin_op_typed op A1 A2 B →
  TY Δ; Γ ⊨ e1 :≤: e1' : A1 →
  TY Δ; Γ ⊨ e2 :≤: e2' : A2 →
  TY Δ; Γ ⊨ (BinOp op e1 e2) :≤: (BinOp op e1' e2'): B.
Proof.
  (* FIXME exercise *)
Admitted.

Lemma compat_unop Δ Γ e e' A B op :
  un_op_typed op A B →
  TY Δ; Γ ⊨ e :≤: e' : A →
  TY Δ; Γ ⊨ (UnOp op e) :≤: (UnOp op e') : B.
Proof.
  (* FIXME exercise *)
Admitted.

Lemma compat_tlam Δ Γ e e' A :
  TY S Δ; (⤉ Γ) ⊨ e :≤: e' : A →
  TY Δ; Γ ⊨ (Λ, e) :≤: (Λ, e') : (∀: A).
Proof.
  (* FIXME exercise *)
Admitted.

Lemma compat_tapp Δ Γ e e' A B :
  TY Δ; Γ ⊨ e :≤: e' : (∀: A) →
  TY Δ; Γ ⊨ (TApp e) :≤: (TApp e') : (A.[B/]).
Proof.
  (* FIXME exercise *)
Admitted.

Lemma compat_pack Δ Γ e e' A B :
  TY Δ; Γ ⊨ e :≤: e' : A.[B/] →
  TY Δ; Γ ⊨ (Pack e) :≤: (Pack e') : (∃: A).
Proof.
  (* FIXME exercise *)
Admitted.

Lemma compat_unpack Δ Γ A B e1 e1' e2 e2' x :
  TY Δ; Γ ⊨ e1 :≤: e1' : (∃: A) →
  TY S Δ; <[x:=A]> (⤉Γ) ⊨ e2 :≤: e2' : B.[ren (+1)] →
  TY Δ; Γ ⊨ (unpack e1 as BNamed x in e2) :≤: (unpack e1' as BNamed x in e2') : B.
Proof.
  (* FIXME exercise *)
Admitted.

Lemma compat_if Δ Γ e0 e0' e1 e1' e2 e2' A :
  TY Δ; Γ ⊨ e0 :≤: e0' : TBool →
  TY Δ; Γ ⊨ e1 :≤: e1' : A →
  TY Δ; Γ ⊨ e2 :≤: e2' : A →
  TY Δ; Γ ⊨ (if: e0 then e1 else e2) :≤: (if: e0' then e1' else e2') : A.
Proof.
  (* FIXME exercise *)
Admitted.

Lemma compat_pair Δ Γ e1 e1' e2 e2' A B :
  TY Δ; Γ ⊨ e1 :≤: e1' : A →
  TY Δ; Γ ⊨ e2 :≤: e2' : B →
  TY Δ; Γ ⊨ (e1, e2) :≤: (e1', e2') : A × B.
Proof.
  (* FIXME exercise *)
Admitted.

Lemma compat_fst Δ Γ e e' A B :
  TY Δ; Γ ⊨ e :≤: e' : A × B →
  TY Δ; Γ ⊨ Fst e :≤: Fst e' : A.
Proof.
  (* FIXME exercise *)
Admitted.

Lemma compat_snd Δ Γ e e' A B :
  TY Δ; Γ ⊨ e :≤: e' : A × B →
  TY Δ; Γ ⊨ Snd e :≤: Snd e' : B.
Proof.
  (* FIXME exercise *)
Admitted.

Lemma compat_injl Δ Γ e e' A B :
  TY Δ; Γ ⊨ e :≤: e' : A →
  TY Δ; Γ ⊨ InjL e :≤: InjL e' : A + B.
Proof.
  (* FIXME exercise *)
Admitted.

Lemma compat_injr Δ Γ e e' A B :
  TY Δ; Γ ⊨ e :≤: e' : B →
  TY Δ; Γ ⊨ InjR e :≤: InjR e' : A + B.
Proof.
  (* FIXME exercise *)
Admitted.

Lemma compat_case Δ Γ e e' e1 e1' e2 e2' A B C :
  TY Δ; Γ ⊨ e :≤: e' : B + C →
  TY Δ; Γ ⊨ e1 :≤: e1' : (B → A) →
  TY Δ; Γ ⊨ e2 :≤: e2' : (C → A) →
  TY Δ; Γ ⊨ Case e e1 e2 :≤: Case e' e1' e2' : A.
Proof.
  (* FIXME exercise *)
Admitted.

Lemma compat_roll Δ Γ e e' A :
  TY Δ; Γ ⊨ e :≤: e' : (A.[(μ: A)%ty/]) →
  TY Δ; Γ ⊨ (roll e) :≤: (roll e') : (μ: A).
Proof.
  (* FIXME exercise *)
Admitted.

Lemma compat_unroll Δ Γ e e' A :
  TY Δ; Γ ⊨ e :≤: e' : (μ: A) →
  TY Δ; Γ ⊨ (unroll e) :≤: (unroll e') : (A.[(μ: A)%ty/]).
Proof.
  (* FIXME exercise *)
Admitted.

Lemma compat_new Δ Γ e e' A :
  TY Δ; Γ ⊨ e :≤: e' : A →
  TY Δ; Γ ⊨ ref e :≤: ref e' : (TRef A).
Proof.
  (* FIXME exercise *)
Admitted.

Lemma compat_load Δ Γ e e' A :
  TY Δ; Γ ⊨ e :≤: e' : TRef A →
  TY Δ; Γ ⊨ !e :≤: !e' : A.
Proof.
  (* FIXME exercise *)
Admitted.

Lemma compat_store Δ Γ e1 e1' e2 e2' A :
  TY Δ; Γ ⊨ e1 :≤: e1' : TRef A →
  TY Δ; Γ ⊨ e2 :≤: e2' : A →
  TY Δ; Γ ⊨ (e1 <- e2) :≤: (e1' <- e2') : TUnit.
Proof.
  (* FIXME exercise *)
Admitted.

Local Hint Resolve compat_var compat_lambda compat_lambda_anon compat_tlam compat_int compat_bool compat_unit compat_if compat_beta compat_tapp compat_pack compat_unpack compat_binop compat_unop compat_pair compat_fst compat_snd compat_injl compat_injr compat_case compat_roll compat_unroll compat_new compat_store compat_load: core.

(* We prove reflexivity of the logical relation *)
Lemma fundamental Δ Γ e A :
  (syn_typed Δ Γ e A) →
  (TY Δ; Γ ⊨ e :≤: e : A).
Proof.
  induction 1 as [ | | | | | | | | | | | ? ? ? ? ? ? ? IH1 ? IH2 | | | | | | | | ? ? ?? ??????IH0 ? IH1 ? IH2  | | | | ?????? IH1 ? IH2| ].
  (* for some reason, [eauto] is exceedingly slow on some of these cases... *)
  1-11: eauto.
  { eapply compat_beta; [apply IH1 | apply IH2]. }
  1-7: eauto.
  { eapply compat_case; [apply IH0 | apply IH1 | apply IH2]. }
  1-3: eauto.
  { eapply compat_store; [apply IH1 | apply IH2 ]. }
  all: eauto.
Qed.

End interp.

Notation ℰ := refines.
Notation 𝒢 := context_interp.
Notation 𝒱 := type_interp.
Notation "'TY' Δ ;  Γ ⊨ e ':≤:' e' : A" := (sem_typed Δ Γ e e' A) (at level 74, e, e', A at next level).
