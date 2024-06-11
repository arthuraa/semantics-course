From iris.proofmode Require Import tactics.
From iris.heap_lang Require Import lang primitive_laws notation.
From iris.base_logic Require Import invariants.
From semantics.pl.heap_lang Require Import adequacy proofmode primitive_laws_nolater.
From semantics.pl Require Import hoare_lib.
From semantics.pl.program_logic Require Import notation.
From semantics.pl Require Import ipm ipm_persistency.

(** ** Step-indexing *)
Import hoare ipm_persistency.
Implicit Types
  (P Q R: iProp)
  (Φ Ψ : val → iProp)
.

(*Check ent_later_intro.*)
(*Check ent_later_mono.*)
(*Check ent_löb.*)
(*Check ent_later_sep.*)
(*Check ent_later_exists.*)
(*Check ent_later_all.*)
(*Check ent_later_pers.*)

(*Check ent_later_wp_pure_step.*)
(*Check ent_later_wp_new.*)
(*Check ent_later_wp_load.*)
(*Check ent_later_wp_store.*)

(* Exercise: Derive the old rules from the new ones. *)
Lemma ent_wp_pure_step_old e e' Φ :
  pure_step e e' →
  WP e' {{ Φ }} ⊢ WP e {{ Φ }}.
Proof.
  (* TODO: exercise *)
Admitted.

Lemma ent_wp_new_old v Φ :
  (∀ l, l ↦ v -∗ Φ #l) ⊢ WP ref v {{ Φ }}.
Proof.
  (* TODO: exercise *)
Admitted.

Lemma ent_wp_load_old l v Φ :
  l ↦ v ∗ (l ↦ v -∗ Φ v) ⊢ WP !#l {{ Φ }}.
Proof.
  (* TODO: exercise *)
Admitted.

Lemma ent_wp_store_old l v w Φ :
  l ↦ v ∗ (l ↦ w -∗ Φ #()) ⊢ WP #l <- w {{ Φ }}.
Proof.
  (* TODO: exercise *)
Admitted.


Lemma ent_later_and P Q :
  ▷ (P ∧ Q) ⊣⊢ ▷ P ∧ ▷ Q.
Proof.
  (* TODO: exercise *)
Admitted.


Lemma ent_later_or P Q :
  ▷ (P ∨ Q) ⊣⊢ ▷ P ∨ ▷ Q.
Proof.
  (* TODO: exercise *)
Admitted.


Lemma ent_all_pers {X} (Φ : X → iProp) :
  □ (∀ x : X, Φ x) ⊢ ∀ x : X, □ Φ x.
Proof.
  apply ent_all_intro. intros x. apply ent_pers_mono. apply ent_all_elim.
Qed.

Lemma ent_wp_rec' Φ (Ψ : val → val → iProp) e :
  (⊢ ∀ v, {{ Φ v ∗ (∀ u, {{ Φ u }} (rec: "f" "x" := e) u {{ Ψ u }})}} subst "x" v (subst "f" (rec: "f" "x" := e) e) {{ Ψ v }}) →
  (⊢ ∀ v, {{ Φ v }} (rec: "f" "x" := e) v {{ Ψ v }}).
Proof.
  intros Ha. apply ent_löb.
  apply ent_all_intro. intros v.
  etrans. { apply ent_later_mono. apply ent_pers_all. }
  rewrite ent_later_pers. etrans; first apply ent_pers_idemp.
  apply ent_pers_mono.
  apply ent_wand_intro. etrans; last apply ent_wp_pure_steps.
  2: { apply rtc_pure_step_fill with (K := [AppLCtx _]). apply pure_step_val. done. }
  etrans; last apply ent_later_wp_pure_step.
  2: { apply pure_step_beta. }
  (* strip the later *)
  etrans. { apply ent_sep_split; first done. apply ent_later_intro. }
  rewrite -ent_later_pers. rewrite -ent_later_sep. apply ent_later_mono.
  (* use the assumption / get it into the right shape to use the hypothesis *)
  etrans.
  { apply ent_sep_split; last done. apply ent_all_pers. }
  rewrite ent_sep_comm. etrans; first apply ent_sep_true.
  apply ent_wand_elim.
  etrans; last apply ent_pers_elim.
  etrans; first apply Ha.
  apply (ent_all_elim v).
Qed.