From iris.proofmode Require Import tactics.
From iris.heap_lang Require Import lang notation.
From iris.bi Require Import fractional.
From semantics.pl.heap_lang Require Import primitive_laws proofmode.
From Stdlib.Logic Require FunctionalExtensionality.
From iris.base_logic Require Import own.
From semantics.pl Require Import ra_lib resource_algebras_1.
From iris.prelude Require Import options.

(** ** Lifting to ghost theories *)

(** Iris has a more general mechanism, [cmra], which you will learn more about in a week.
   Thus, we need a bit of boilerplate code to adapt the definitions we've setup above to work with Iris.
  (Essentially, this defines CMRAs from our notion of LRAs. )
 *)
Canonical Structure max_natO := leibnizO max_nat.
Canonical Structure maxnatCR : cmra := cmra_of_lra max_nat max_nat_lra_mixin.

Canonical Structure authO A := leibnizO (auth A).
Canonical Structure authCR (A : ulra) : cmra := cmra_of_lra (auth A) (auth_lra_mixin (A := A)).

Canonical Structure exclO A := leibnizO (excl A).
Canonical Structure exclCR (A : Type) : cmra := cmra_of_lra (excl A) (excl_lra_mixin (A := A)).

Canonical Structure agreeO A `{Countable A} := leibnizO (agree A).
Canonical Structure agreeCR (A : Type) `{Countable A} : cmra := cmra_of_lra (agree A) (agree_lra_mixin (A := A)).

Canonical Structure csumO A B := leibnizO (csum A B).
Canonical Structure csumCR (A B : lra) : cmra := cmra_of_lra (csum A B) (csum_lra_mixin (A := A) (B := B)).

(* Technical note: slightly hacky workaround. There's already a canonical structure declaration for the prod OFE,
  so defining it with Leibniz equality via [leibnizO] will make the [Cmra] smart constructor below fail,
  as it will infer the wrong instance.
  The trick is to just define an alias [prod'] that will not be unfolded by canonical structure inference.
 *)
Definition prod' A B := prod A B.
Canonical Structure prodO A B := leibnizO (prod' A B).
Canonical Structure prodCR (A B : lra) : cmra := cmra_of_lra (prod' A B) (prod_lra_mixin (A := A) (B := B)).


(** The following lemmas are useful for deriving ghost theory laws:
  - [own_alloc]
  - [own_op]
  - [own_core_persistent]

  - [own_valid]
  - [own_valid_2]
  - [own_valid_3]

  - [own_lra_update]
    (This lemma is phrased for our notion of [lra_update]s to directly lift the lemmas we derived above)

  - [own_mono]
  - [own_unit]
 *)

(** Defining the ghost theory for MonoNat *)

(** We need this to register the ghost state we setup with Iris. *)
Class mono_natG Σ :=
  MonoNatG { mono_natG_inG : inG Σ (authCR max_natUR); }.
#[export] Existing Instance mono_natG_inG.
Definition mono_natΣ : gFunctors := #[ GFunctor (authCR max_natUR) ].
Global Instance subG_mono_natΣ Σ : subG mono_natΣ Σ → mono_natG Σ.
Proof. solve_inG. Qed.

Section mono_nat.
  (** We now assume that the mono_nat ghost state we have just defined is registered with Iris. *)
  Context `{mono_natG Σ}.

  Definition mono_nat_own_auth γ n := (own γ (auth_auth (MaxNat n)) ∗ own γ (auth_frag (MaxNat n)))%I.
  Definition mono_nat_own_frag γ n := own γ (auth_frag (MaxNat n)).

  Instance mono_nat_own_frag_pers γ n : Persistent (mono_nat_own_frag γ n).
  Proof.
    apply own_core_persistent.
    unfold CoreId. rewrite auth_frag_pcore max_nat_pcore. done.
  Qed.

  Lemma mono_make_bound γ n :
    mono_nat_own_auth γ n -∗ mono_nat_own_frag γ n.
  Proof.
    iIntros "[_ $]".
  Qed.

  Lemma mono_use_bound γ n m :
    mono_nat_own_auth γ n -∗ mono_nat_own_frag γ m -∗ ⌜n ≥ m⌝.
  Proof.
    iIntros "[Hauth Hfrag1] Hfrag2".
    iDestruct (own_valid_2 with "Hauth Hfrag2") as %Hv.
    iPureIntro. move: Hv.
    rewrite auth_auth_frag_valid.
    rewrite max_nat_included. simpl; lia.
  Qed.

  Lemma mono_increase_val γ n :
    mono_nat_own_auth γ n -∗ |==> mono_nat_own_auth γ (S n).
  Proof.
    unfold mono_nat_own_auth. rewrite -!own_op.
    iApply own_lra_update.
    eapply auth_update. apply local_upd_nat_max.
    lia.
  Qed.

  Lemma mono_new n :
    ⊢ |==> ∃ γ, mono_nat_own_auth γ n.
  Proof.
    unfold mono_nat_own_auth. setoid_rewrite <-own_op.
    iApply own_alloc. rewrite auth_auth_frag_valid. split.
    - apply max_nat_included. lia.
    - apply max_nat_valid.
  Qed.
End mono_nat.

(** ** Exercise: Oneshot *)
Class oneshotG Σ (A : Type) `{Countable A} :=
  OneShotG { oneshotG_inG : inG Σ (csumCR (exclR unit) (agreeR A)); }.
#[export] Existing Instance oneshotG_inG.
Definition oneshotΣ A `{Countable A} : gFunctors := #[ GFunctor (csumCR (exclR unit) (agreeR A)) ].
Global Instance subG_oneshotΣ Σ A `{Countable A} : subG (oneshotΣ A) Σ → oneshotG Σ A.
Proof. solve_inG. Qed.
Section oneshot.
  Context {A : Type}.
  Context `{oneshotG Σ A}.

  Definition os_pending γ := own γ (Cinl (Excl ())).
  Definition os_shot γ (a : A) := own γ (Cinr (to_agree a)).

  Lemma os_pending_alloc :
    ⊢ |==> ∃ γ, os_pending γ.
  Proof.
    (* TODO: exercise *)
  Admitted.


  Lemma os_pending_shoot γ a :
    os_pending γ -∗ |==> os_shot γ a.
  Proof.
    (* TODO: exercise *)
  Admitted.


  Global Instance os_shot_persistent γ a : Persistent (os_shot γ a).
  Proof.
    (* TODO: exercise *)
  Admitted.


  Lemma os_pending_shot_False γ a :
    os_pending γ -∗ os_shot γ a -∗ False.
  Proof.
    (* TODO: exercise *)
  Admitted.


  Lemma os_pending_pending_False γ :
    os_pending γ -∗ os_pending γ -∗ False.
  Proof.
    (* TODO: exercise *)
  Admitted.


  Lemma os_shot_agree γ a b :
    os_shot γ a -∗ os_shot γ b -∗ ⌜a = b⌝.
  Proof.
    (* TODO: exercise *)
  Admitted.


  Global Instance os_shot_timeless γ a : Timeless (os_shot γ a).
  Proof. apply _. Qed.
  Global Instance os_pending_timeless γ : Timeless (os_pending γ).
  Proof. apply _. Qed.
End oneshot.

(** ** Exercise: Synchronized Ghost State *)
Class halvesG Σ (A : Type) :=
  HalvesG { halvesG_inG : inG Σ (authCR (optionUR (exclR A))); }.
#[export] Existing Instance halvesG_inG.
Definition halvesΣ A : gFunctors := #[ GFunctor (authCR (optionUR (exclR A))) ].
Global Instance subG_halvesΣ Σ A : subG (halvesΣ A) Σ → halvesG Σ A.
Proof. solve_inG. Qed.
Section halves.
  Context {A : Type}.
  Context `{halvesG Σ A}.

  Definition gleft γ (a : A) := own γ (auth_auth (Some (Excl a))).
  Definition gright γ (a : A) := own γ (auth_frag (Some (Excl a))).

  Lemma ghalves_alloc a :
    ⊢ |==> ∃ γ, gleft γ a ∗ gright γ a.
  Proof.
    (* TODO: exercise *)
  Admitted.


  Lemma ghalves_agree γ a b :
    gleft γ a -∗ gright γ b -∗ ⌜a = b⌝.
  Proof.
    (* TODO: exercise *)
  Admitted.


  Lemma ghalves_update γ a b c :
    gleft γ a -∗ gright γ b -∗ |==> gleft γ c ∗ gright γ c.
  Proof.
    (* TODO: exercise *)
  Admitted.


  Global Instance gleft_timeless γ a : Timeless (gleft γ a).
  Proof. apply _. Qed.
  Global Instance gright_timeless γ a : Timeless (gright γ a).
  Proof. apply _. Qed.
End halves.

(** ** Exercise: gvar *)
Class gvarG Σ (A : Type) `{Countable A} := GvarG { gvarG_inG : inG Σ (prodCR fracR (agreeR A)); }.
#[export] Existing Instance gvarG_inG.
Definition gvarΣ A `{Countable A} : gFunctors := #[ GFunctor (prodCR fracR (agreeR A)) ].
Global Instance subG_gvarΣ Σ A `{Countable A} : subG (gvarΣ A) Σ → gvarG Σ A.
Proof. solve_inG. Qed.
Section gvar.
  Context {A : Type} `{Countable A}.
  Context `{gvarG Σ A}.

  Definition gvar γ (q : frac) (a : A) := own γ ((q, to_agree a) : prodCR _ _).

  Lemma gvar_alloc a :
    ⊢ |==> ∃ γ, gvar γ 1 a.
  Proof.
    (* TODO: exercise *)
  Admitted.


  Lemma gvar_agree γ q1 q2 a b :
    gvar γ q1 a -∗ gvar γ q2 b -∗ ⌜(q1 + q2 ≤ 1)%Qp⌝ ∗ ⌜a = b⌝.
  Proof.
    (* TODO: exercise *)
  Admitted.



  Lemma gvar_fractional γ q1 q2 a :
    gvar γ q1 a ∗ gvar γ q2 a ⊣⊢ gvar γ (q1 + q2)%Qp a.
  Proof.
    (* TODO: exercise *)
  Admitted.



  (* Note: The following instance can make the IPM aware of the fractionality of the [gvar] assertion,
    meaning that it can automatically split and merge (when framing) in some cases.
    See the proof of [gvar_split_halves] as an example.
   *)
  Global Instance gvar_AsFractional γ q b :
    AsFractional (gvar γ q b) (λ q', gvar γ q' b) q.
  Proof.
    split; first done.
    intros ??. by rewrite gvar_fractional.
  Qed.
  Lemma gvar_split_halves γ a :
    gvar γ 1 a -∗ gvar γ (1/2) a ∗ gvar γ (1/2) a.
  Proof.
    iIntros "[H1 H2]". iFrame.
  Qed.

  Lemma gvar_update γ a b :
    gvar γ 1 a -∗ |==> gvar γ 1 b.
  Proof.
    (* TODO: exercise *)
  Admitted.


  Global Instance gvar_timeless γ q a : Timeless (gvar γ q a).
  Proof. apply _. Qed.
End gvar.

(** Finite functions *)
Section fin_fun.
  Context `{Countable K} {A : lra}.
  Implicit Types m : gmap K A.

  (** The proofs in this section are quite a mouthful, so we recommend to skip over them.
    They are just here for completeness.
    (The lemma statements are more interesting, though: especially the local updates, which you will need to do some of the exercises below!)
   *)

  Local Instance gmap_unit_instance : Unit (gmap K A) := (∅ : gmap K A).
  Local Instance gmap_op_instance : Op (gmap K A) := merge op.
  Local Instance gmap_pcore_instance : PCore (gmap K A) := λ m, Some (omap pcore m).
  Local Instance gmap_valid_instance : Valid (gmap K A) := λ m, ∀ i, ✓ (m !! i).

  Lemma gmap_op m1 m2 : m1 ⋅ m2 = merge op m1 m2.
  Proof. done. Qed.
  Lemma lookup_op m1 m2 i : (m1 ⋅ m2) !! i = m1 !! i ⋅ m2 !! i.
  Proof. rewrite lookup_merge. by destruct (m1 !! i), (m2 !! i). Qed.
  Lemma lookup_core m i : core m !! i = core (m !! i).
  Proof. by apply lookup_omap. Qed.
  Lemma gmap_pcore m : pcore m = Some (omap pcore m).
  Proof. done. Qed.

  Lemma lookup_included (m1 m2 : gmap K A) : m1 ≼ m2 ↔ ∀ i, m1 !! i ≼ m2 !! i.
  Proof.
    split; [by intros [m Hm] i; exists (m !! i); rewrite -lookup_op Hm|].
    revert m2. induction m1 as [|i x m Hi IH] using map_ind=> m2 Hm.
    { exists m2. by rewrite left_id. }
    destruct (IH (delete i m2)) as [m2' Hm2'].
    { intros j. move: (Hm j); destruct (decide (i = j)) as [->|].
      - intros _. rewrite Hi. apply: ulra_unit_least.
      - rewrite lookup_insert_ne // lookup_delete_ne //. }
    destruct (Hm i) as [my Hi']; simplify_map_eq.
    exists (partial_alter (λ _, my) i m2'). apply map_eq => j.
    destruct (decide (i = j)) as [->|].
    - by rewrite Hi' lookup_op lookup_insert lookup_partial_alter.
    - move : Hm2'. rewrite map_eq_iff. intros Hm2'. move : (Hm2' j).
      by rewrite !lookup_op lookup_delete_ne //
        lookup_insert_ne // lookup_partial_alter_ne.
  Qed.

  Lemma gmap_lra_mixin : LRAMixin (gmap K A).
  Proof.
    apply lra_total_mixin.
    - done.
    - intros m1 m2 m3. apply map_eq. intros i. by rewrite !lookup_op assoc.
    - intros m1 m2. apply map_eq. intros i. by rewrite !lookup_op lra_comm.
    - intros m. apply map_eq. intros i. by rewrite lookup_op lookup_core lra_core_l.
    - intros m. apply map_eq. intros i. by rewrite !lookup_core lra_core_idemp.
    - intros m1 m2; rewrite !lookup_included=> Hm i.
      rewrite !lookup_core. by apply lra_core_mono.
    - intros m1 m2 Hm i. apply lra_valid_op_l with (m2 !! i).
      by rewrite -lookup_op.
  Qed.
  Canonical Structure gmapR := Lra (gmap K A) gmap_lra_mixin.

  Lemma gmap_ulra_mixin : ULRAMixin (gmap K A).
  Proof.
    split.
    - intros m. apply map_eq. intros i; by rewrite /= lookup_op lookup_empty (left_id_L None _).
    - by intros i; rewrite lookup_empty.
    - rewrite /pcore /gmap_pcore_instance. f_equiv. apply map_eq. intros i. by rewrite lookup_omap lookup_empty.
  Qed.
  Canonical Structure gmapUR := Ulra (gmap K A) gmap_lra_mixin gmap_ulra_mixin.

  Lemma lookup_valid_Some m i x : ✓ m → m !! i = Some x → ✓ x.
  Proof. move=> Hm Hi. move:(Hm i). by rewrite Hi. Qed.

  Lemma insert_valid m i x : ✓ x → ✓ m → ✓ <[i:=x]>m.
  Proof. by intros ?? j; destruct (decide (i = j)); simplify_map_eq. Qed.
  Lemma singleton_valid i x : ✓ ({[ i := x ]} : gmap K A) ↔ ✓ x.
  Proof.
    split.
    - move=>/(_ i); by simplify_map_eq.
    - intros. apply insert_valid; first done. apply: ulra_unit_valid.
  Qed.
  Lemma delete_valid m i : ✓ m → ✓ (delete i m).
  Proof. intros Hm j; destruct (decide (i = j)); by simplify_map_eq. Qed.

  Lemma insert_singleton_op m i x : m !! i = None → <[i:=x]> m = {[ i := x ]} ⋅ m.
  Proof.
    intros Hi; apply map_eq=> j; destruct (decide (i = j)) as [->|].
    - by rewrite lookup_op lookup_insert lookup_singleton Hi right_id_L.
    - by rewrite lookup_op lookup_insert_ne // lookup_singleton_ne // left_id_L.
  Qed.

  Lemma singleton_core (i : K) (x : A) cx :
    pcore x = Some cx → core {[ i := x ]} =@{gmap K A} {[ i := cx ]}.
  Proof. apply omap_singleton_Some. Qed.
  Lemma singleton_core_total `{!LraTotal A} (i : K) (x : A) :
    core {[ i := x ]} =@{gmap K A} {[ i := core x ]}.
  Proof. apply singleton_core. apply lra_pcore_core. Qed.
  Lemma singleton_op (i : K) (x y : A) :
    {[ i := x ]} ⋅ {[ i := y ]} =@{gmap K A} {[ i := x ⋅ y ]}.
  Proof. by apply (merge_singleton _ _ _ x y). Qed.

  Lemma singleton_included_l m i x :
    {[ i := x ]} ≼ m ↔ ∃ y, m !! i = Some y ∧ Some x ≼ Some y.
  Proof.
    split.
    - move=> [m' ]. rewrite map_eq_iff. intros Heq. specialize (Heq i).
      rewrite lookup_op lookup_singleton in Heq.
      exists (x ⋅? m' !! i). rewrite -Some_op_opM.
      split; first done. apply lra_included_l.
    - intros (y&Hi&[mz Hy]). exists (partial_alter (λ _, mz) i m).
      apply map_eq. intros j; destruct (decide (i = j)) as [->|].
      + by rewrite lookup_op lookup_singleton lookup_partial_alter Hi.
      + by rewrite lookup_op lookup_singleton_ne// lookup_partial_alter_ne// left_id.
  Qed.
  Lemma singleton_included_exclusive_l m i x :
    lra_exclusive x → ✓ m →
    {[ i := x ]} ≼ m ↔ m !! i = Some x.
  Proof.
    intros ? Hm. rewrite singleton_included_l. split.
    - intros (y&?&->%(Some_included_lra_exclusive _)); eauto using lookup_valid_Some.
    - intros ->. exists x. split; first done. reflexivity.
  Qed.
  Lemma singleton_included i x y :
    {[ i := x ]} ≼ ({[ i := y ]} : gmap K A) ↔ x = y ∨ x ≼ y.
  Proof.
    rewrite singleton_included_l. split.
    - intros (y'&Hi&Ha). rewrite lookup_insert in Hi.
      apply Some_included in Ha as (? & [= <-] & ?). naive_solver.
    - intros ?. exists y. rewrite lookup_insert Some_included; eauto.
  Qed.
  Lemma singleton_mono i x y :
    x ≼ y → {[ i := x ]} ≼ ({[ i := y ]} : gmap K A).
  Proof. intros Hincl. apply singleton_included. right. done. Qed.

  Lemma insert_op m1 m2 i x y :
    <[i:=x ⋅ y]>(m1 ⋅ m2) =  <[i:=x]>m1 ⋅ <[i:=y]>m2.
  Proof. by rewrite (insert_merge (⋅) m1 m2 i (x ⋅ y) x y). Qed.

  (** Updates *)
  Lemma insert_updateP (P : A → Prop) (Q : gmap K A → Prop) m i x :
    lra_updateP x P →
    (∀ y, P y → Q (<[i:=y]>m)) →
    lra_updateP (<[i:=x]>m) Q.
  Proof.
    intros Hx%option_updateP' HP; apply lra_total_updateP=> mf Hm.
    destruct (Hx (Some (mf !! i))) as ([y|]&?&?); try done.
    { by generalize (Hm i); rewrite lookup_op; simplify_map_eq. }
    exists (<[i:=y]> m); split; first by auto.
    intros j; move: (Hm j)=>{Hm}; rewrite !lookup_op=>Hm.
    destruct (decide (i = j)); simplify_map_eq/=; auto.
  Qed.
  Lemma insert_updateP' (P : A → Prop) m i x :
    lra_updateP x P → lra_updateP (<[i:=x]>m) (λ m', ∃ y, m' = <[i:=y]>m ∧ P y).
  Proof. eauto using insert_updateP. Qed.
  Lemma insert_update m i x y : lra_update x y → lra_update (<[i:=x]>m) (<[i:=y]>m).
  Proof. rewrite !lra_update_updateP; eauto using insert_updateP with subst. Qed.

  Lemma singleton_updateP (P : A → Prop) (Q : gmap K A → Prop) i x :
    lra_updateP x P → (∀ y, P y → Q {[ i := y ]}) → lra_updateP {[ i := x ]} Q.
  Proof. apply insert_updateP. Qed.
  Lemma singleton_updateP' (P : A → Prop) i x :
    lra_updateP x P → lra_updateP {[ i := x ]} (λ m, ∃ y, m = {[ i := y ]} ∧ P y).
  Proof. apply insert_updateP'. Qed.
  Lemma singleton_update i (x y : A) : lra_update x y → lra_update {[ i := x ]} {[ i := y ]}.
  Proof. apply insert_update. Qed.

  Lemma delete_update m i : lra_update m (delete i m).
  Proof.
    apply lra_total_update=> mf Hm j; destruct (decide (i = j)); subst.
    - move: (Hm j). rewrite !lookup_op lookup_delete left_id.
      apply lra_valid_op_r.
    - move: (Hm j). by rewrite !lookup_op lookup_delete_ne.
  Qed.

  Lemma dom_op m1 m2 : dom (m1 ⋅ m2) = dom m1 ∪ dom m2.
  Proof.
    apply set_eq=> i; rewrite elem_of_union !elem_of_dom.
    unfold is_Some; setoid_rewrite lookup_op.
    destruct (m1 !! i), (m2 !! i); naive_solver.
  Qed.
  Lemma dom_included m1 m2 : m1 ≼ m2 → dom m1 ⊆ dom m2.
  Proof.
    rewrite lookup_included=>Ha i; rewrite !elem_of_dom.
    specialize (Ha i). intros (c & Hc).
    rewrite Hc in Ha. apply Some_included in Ha as (b & -> & _). eauto.
  Qed.

  Section freshness.
    Local Set Default Proof Using "Type*".
    Context `{!Infinite K}.
    Lemma alloc_updateP_strong_dep (Q : gmap K A → Prop) (I : K → Prop) m (f : K → A) :
      pred_infinite I →
      (∀ i, m !! i = None → I i → ✓ (f i)) →
      (∀ i, m !! i = None → I i → Q (<[i:=f i]>m)) →
      lra_updateP m Q.
    Proof.
      move=> /(pred_infinite_set I (C:=gset K)) HP ? HQ.
      apply lra_total_updateP. intros mf Hm.
      destruct (HP (dom (m ⋅ mf))) as [i [Hi1 Hi2]].
      assert (m !! i = None).
      { eapply (not_elem_of_dom). revert Hi2.
        rewrite dom_op not_elem_of_union. naive_solver. }
      exists (<[i:=f i]>m); split.
      - by apply HQ.
      - rewrite insert_singleton_op //.
        rewrite -assoc -insert_singleton_op;
          last by eapply (not_elem_of_dom (D:=gset K)).
      apply insert_valid; auto.
    Qed.
    (** This corresponds to the Alloc axiom shown on paper. *)
    Lemma alloc_updateP_strong (Q : gmap K A → Prop) (I : K → Prop) m x :
      pred_infinite I →
      ✓ x → (∀ i, m !! i = None → I i → Q (<[i:=x]>m)) →
      lra_updateP m Q.
    Proof.
      move=> HP ? HQ. eapply (alloc_updateP_strong_dep _ _ _ (λ _, x)); eauto.
    Qed.
    Lemma alloc_updateP (Q : gmap K A → Prop) m x :
      ✓ x → (∀ i, m !! i = None → Q (<[i:=x]>m)) → lra_updateP m Q.
    Proof.
      move=>??.
      eapply (alloc_updateP_strong _ (λ _, True));
      eauto using pred_infinite_True.
    Qed.
    Lemma alloc_updateP_cofinite (Q : gmap K A → Prop) (J : gset K) m x :
      ✓ x → (∀ i, m !! i = None → i ∉ J → Q (<[i:=x]>m)) → lra_updateP m  Q.
    Proof.
      eapply alloc_updateP_strong.
      apply (pred_infinite_set (C:=gset K)).
      intros E. exists (fresh (J ∪ E)).
      apply not_elem_of_union, is_fresh.
    Qed.
  End freshness.

  Lemma alloc_unit_singleton_updateP (P : A → Prop) (Q : gmap K A → Prop) u i :
    ✓ u → LeftId (=) u (⋅) →
    lra_updateP u P → (∀ y, P y → Q {[ i := y ]}) → lra_updateP ∅ Q.
  Proof.
    intros ?? Hx HQ. apply lra_total_updateP=> gf Hg.
    destruct (Hx (gf !! i)) as (y&?&Hy).
    { move:(Hg i). rewrite !left_id.
      case: (gf !! i)=>[x|]; rewrite /= ?left_id //.
    }
    exists {[ i := y ]}; split; first by auto.
    intros i'; destruct (decide (i' = i)) as [->|].
    - rewrite lookup_op lookup_singleton.
      move:Hy; case: (gf !! i)=>[x|]; rewrite /= ?right_id //.
    - move:(Hg i'). by rewrite !lookup_op lookup_singleton_ne // !left_id.
  Qed.
  Lemma alloc_unit_singleton_updateP' (P: A → Prop) u i :
    ✓ u → LeftId (=) u (⋅) →
    lra_updateP u P → lra_updateP ∅ (λ m, ∃ y, m = {[ i := y ]} ∧ P y).
  Proof. eauto using alloc_unit_singleton_updateP. Qed.
  Lemma alloc_unit_singleton_update (u : A) i (y : A) :
    ✓ u → LeftId (=) u (⋅) → lra_update u y → lra_update (∅:gmap K A) {[ i := y ]}.
  Proof.
    rewrite !lra_update_updateP; eauto using alloc_unit_singleton_updateP with subst.
  Qed.

  (** Local updates *)
  Lemma alloc_local_update m1 m2 i x :
    m1 !! i = None → ✓ x → lra_local_update (m1,m2) (<[i:=x]>m1, <[i:=x]>m2).
  Proof.
    intros Hi ?. apply local_update_unital => mf Hmv; simpl in *.
    rewrite map_eq_iff => Hm.
    split; auto using insert_valid.
    apply (map_eq (<[i := x]> m1)). intros j; destruct (decide (i = j)) as [->|].
    - move: (Hm j); rewrite Hi symmetry_iff lookup_op None_op => -[_ Hj].
      by rewrite lookup_op !lookup_insert Hj.
    - rewrite lookup_insert_ne // !lookup_op lookup_insert_ne //.
      rewrite Hm lookup_op //.
  Qed.

  Lemma alloc_singleton_local_update m i x :
    m !! i = None → ✓ x → lra_local_update (m,∅) (<[i:=x]>m, {[ i:=x ]}).
  Proof. apply alloc_local_update. Qed.

  Lemma insert_local_update m1 m2 i x y x' y' :
    m1 !! i = Some x → m2 !! i = Some y →
    lra_local_update (x, y) (x', y') →
    lra_local_update (m1, m2) (<[i:=x']>m1, <[i:=y']>m2).
  Proof.
    intros Hi1 Hi2 Hup; apply local_update_unital=> mf Hmv. rewrite map_eq_iff => Hm; simpl in *.
    destruct (Hup (mf !! i)) as [? Hx']; simpl in *.
    { move: (Hm i). rewrite lookup_op Hi1 Hi2 Some_op_opM (inj_iff Some).
      intros; split; last done. by eapply lookup_valid_Some.
    }
    split; auto using insert_valid. apply (map_eq (<[i := x']> m1)). intros j.
    destruct (decide (i = j)) as [->|].
    - rewrite lookup_insert lookup_op lookup_insert Some_op_opM. by subst.
    - rewrite lookup_insert_ne // !lookup_op lookup_insert_ne //. rewrite Hm lookup_op//.
  Qed.

  Lemma singleton_local_update_any m i y x' y' :
    (∀ x, m !! i = Some x → lra_local_update (x, y) (x', y')) →
    lra_local_update (m, {[ i := y ]}) (<[i:=x']>m, {[ i := y' ]}).
  Proof.
    intros. rewrite /singletonM /map_singleton -(insert_insert ∅ i y' y).
    apply lra_local_update_total_valid =>_ _ /singleton_included_l [x0 [Hlk0 _]].
    eapply insert_local_update; [|eapply lookup_insert|]; eauto.
  Qed.

  Lemma singleton_local_update m i x y x' y' :
    m !! i = Some x →
    lra_local_update (x, y) (x', y') →
    lra_local_update (m, {[ i := y ]}) (<[i:=x']>m, {[ i := y' ]}).
  Proof.
    intros Hmi ?. apply singleton_local_update_any.
    intros x2. rewrite Hmi=>[=<-]. done.
  Qed.

  Lemma delete_local_update m1 m2 i x :
    lra_exclusive x →
    m2 !! i = Some x → lra_local_update (m1, m2) (delete i m1, delete i m2).
  Proof.
    intros Hexcl Hi. apply local_update_unital=> mf Hmv Hm; simpl in *.
    split; auto using delete_valid.
    rewrite Hm. apply (map_eq (delete i (m2 ⋅ mf))) => j; destruct (decide (i = j)) as [<-|].
    - rewrite lookup_op !lookup_delete left_id symmetry_iff.
      apply eq_None_not_Some=> -[y Hi'].
      move: (Hmv i). rewrite Hm lookup_op Hi Hi' -Some_op. intros []%Hexcl.
    - by rewrite lookup_op !lookup_delete_ne // lookup_op.
  Qed.

  Lemma delete_singleton_local_update m i x :
    lra_exclusive x →
    lra_local_update (m, {[ i := x ]}) (delete i m, ∅).
  Proof.
    rewrite -(delete_singleton i x).
    intros ?. by eapply delete_local_update, lookup_singleton.
  Qed.
End fin_fun.
Global Arguments gmapUR : clear implicits.
Global Arguments gmapUR _ {_ _}.
Global Arguments gmapR : clear implicits.
Global Arguments gmapR _ {_ _}.

(** Agreement maps *)
Definition agmapCR (A B : Type) `{Countable A} `{Countable B} := (authCR (gmapUR A (agreeR B))).
Class agmapG Σ (A B : Type) `{Countable A} `{Countable B} :=
  AgMapG { agmapG_inG : inG Σ (agmapCR A B); }.
#[export] Existing Instance agmapG_inG.
Definition agmapΣ A B `{Countable A} `{Countable B} : gFunctors := #[ GFunctor (agmapCR A B) ].
Global Instance subG_agmapΣ Σ A B `{Countable A} `{Countable B} : subG (agmapΣ A B) Σ → agmapG Σ A B.
Proof. solve_inG. Qed.
Section agmap.
  Context {A B : Type} `{Countable A} `{Countable B}.
  Context `{agmapG Σ A B}.

  Definition to_agmap (m : gmap A B) : gmapUR A (agreeR B) := fmap (λ a, to_agree a) m.

  Definition agmap_auth γ (m : gmap A B) := own γ (auth_auth (to_agmap m)).

  Definition agmap_elem γ (a : A) (b : B) := own γ (auth_frag ({[ a := to_agree b ]})).

    Lemma agmap_alloc_empty :
    ⊢ |==> ∃ γ, agmap_auth γ ∅.
  Proof.
    (* TODO: exercise *)
  Admitted.


  Lemma agmap_insert γ m a b :
    m !! a = None →
    agmap_auth γ m -∗ |==> agmap_auth γ (<[a := b]> m) ∗ agmap_elem γ a b.
  Proof.
    (* TODO: exercise *)
  Admitted.



  Lemma agmap_lookup γ m a b :
    agmap_auth γ m -∗ agmap_elem γ a b -∗ ⌜m !! a = Some b⌝.
  Proof.
    (* TODO: exercise *)
  Admitted.



  Global Instance agmap_elem_persistent γ a b : Persistent (agmap_elem γ a b).
  Proof.
    (* TODO: exercise *)
  Admitted.



  Global Instance agmap_auth_timeless γ m : Timeless (agmap_auth γ m).
  Proof. apply _. Qed.
  Global Instance agmap_elem_timeless γ a b : Timeless (agmap_elem γ a b).
  Proof. apply _. Qed.
End agmap.

(** Updateable maps *)
Definition exmapCR (A B : Type) `{Countable A} := (authCR (gmapUR A (exclR B))).
Class exmapG Σ (A B : Type) `{Countable A} :=
  ExMapG { exmapG_inG : inG Σ (exmapCR A B); }.
#[export] Existing Instance exmapG_inG.
Definition exmapΣ A B `{Countable A} : gFunctors := #[ GFunctor (exmapCR A B) ].
Global Instance subG_exmapΣ Σ A B `{Countable A} : subG (exmapΣ A B) Σ → exmapG Σ A B.
Proof. solve_inG. Qed.
Section exmap.
  Context {A B : Type} `{Countable A}.
  Context `{exmapG Σ A B}.

  Definition to_exmap (m : gmap A B) : gmapUR A (exclR B) := fmap (λ a, Excl (A := B) a) m.

  Definition exmap_auth γ (m : gmap A B) := own γ (auth_auth (to_exmap m)).
  Definition exmap_elem γ (a : A) (b : B) := own γ (auth_frag ({[ a := Excl b ]})).

  Lemma exmap_alloc_empty :
    ⊢ |==> ∃ γ, exmap_auth γ ∅.
  Proof.
    (* TODO: exercise *)
  Admitted.


  Lemma exmap_insert γ m a b :
    m !! a = None →
    exmap_auth γ m -∗ |==> exmap_auth γ (<[a := b]> m) ∗ exmap_elem γ a b.
  Proof.
    (* TODO: exercise *)
  Admitted.



  Lemma exmap_lookup γ m a b :
    exmap_auth γ m -∗ exmap_elem γ a b -∗ ⌜m !! a = Some b⌝.
  Proof.
    (* TODO: exercise *)
  Admitted.


  Lemma exmap_update γ m a b c :
    exmap_auth γ m -∗ exmap_elem γ a b -∗ |==> exmap_auth γ (<[a := c]> m) ∗ exmap_elem γ a c.
  Proof.
    (* TODO: exercise *)
  Admitted.


  Lemma exmap_delete γ m a b :
    exmap_auth γ m -∗ exmap_elem γ a b -∗ |==> exmap_auth γ (delete a m).
  Proof.
    (* TODO: exercise *)
  Admitted.


  Global Instance exmap_auth_timeless γ m : Timeless (exmap_auth γ m).
  Proof. apply _. Qed.
  Global Instance exmap_elem_timeless γ a b : Timeless (exmap_elem γ a b).
  Proof. apply _. Qed.
End exmap.


(** ** Exercise: functions, pointwise *)
Section functions.
  (* TODO: this is an exercise for you *)
  Context {A : Type} {B : ulra}.
  Implicit Types (f g : A → B).

  (* You may assume functional extensionality.
     (Note that in the Iris version of this RA, FE is not needed, due to a more flexible setup of RAs.) *)
  Import FunctionalExtensionality.
  Notation fext := functional_extensionality.

  Local Instance fun_op_instance : Op (A → B) := λ f g, f (* TODO *).
  Local Instance fun_pcore_instance : PCore (A → B) := λ f, None (* TODO *).
  Local Instance fun_valid_instance : Valid (A → B) := λ f,False (* TODO *).
  (* TODO: uncomment if there's a unit *)
  (*Local Instance fun_unit_instance : Unit (A → B) := λ a, (??) .*)

  Lemma fun_included f g :
    f ≼ g → False (* TODO *).
  Proof.
    (* TODO: exercise *)
  Admitted.


  (* You may want to derive additional lemmas about the definition of your operations *)
  

  Lemma fun_lra_mixin : LRAMixin (A → B).
  Proof.
    (** Hint: you may want to use that [B]'s core is total. *)
    (* TODO: exercise *)
  Admitted.

  Canonical Structure funR := Lra (A → B) fun_lra_mixin.

  (* TODO: uncomment if you think that there's a unit *)
  (*
  Lemma fun_ulra_mixin :  ULRAMixin (A → B).
  Proof.
  Admitted.
  (*Qed.*)
  Canonical Structure funUR := Ulra (A → B) fun_lra_mixin fun_ulra_mixin.
   *)

  Lemma fun_exclusive `{Inhabited A} f :
    (∀ a, lra_exclusive (f a)) → lra_exclusive f.
  Proof.
    (* Hint: you may assume that [A] is inhabited, i.e., there's an [inhabitant] of A that you can use. *)
    (* TODO: exercise *)
  Admitted.

End functions.
