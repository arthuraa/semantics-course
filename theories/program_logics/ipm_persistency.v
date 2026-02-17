From iris.proofmode Require Import proofmode.
From iris.heap_lang Require Import lang primitive_laws notation.
From iris.base_logic Require Import invariants.
From semantics.pl.heap_lang Require Import adequacy proofmode primitive_laws_nolater.
From semantics.pl Require Import hoare_lib ipm.
From semantics.pl.program_logic Require Import notation.
Import hoare.


Implicit Types
  (P Q R: iProp)
  (Φ Ψ : val → iProp)
.

(** ** Persistency *)
(*Check ent_pers_dup.*)
(*Check ent_pers_elim.*)
(*Check ent_pers_mono.*)
(*Check ent_pers_pure.*)
(*Check ent_pers_and_sep.*)
(*Check ent_pers_idemp.*)
(*Check ent_pers_all.*)
(*Check ent_pers_exists.*)

Lemma ent_pers_dup' P :
  □ P ⊢ (□ P) ∗ (□ P).
Proof.
(* don't use the IPM *)
  (* TODO: exercise *)
Admitted.



(** Hoare triples, internalized *)
Definition hoare (P : iProp) (e : expr) (Φ : val → iProp) : iProp :=
  □ (P -∗ WP e {{ Φ }}).

Global Notation "{{ P } } e {{ Φ } }" := (hoare P%I e%E Φ%I)
  (at level 20, P, e, Φ at level 200,
  format "{{  P  } }  e  {{  Φ  } }") : stdpp_scope.

Global Notation "{{ P } } e {{ v , Q } }" := (hoare P%I e%E (λ v, Q)%I)
  (at level 20, P, e, Q at level 200,
  format "{{  P  } }  e  {{  v ,  Q  } }") : stdpp_scope.

(** Example: *)
Lemma double_int f :
  {{ True }} f #() {{ v, ∃ z : Z, ⌜v = #z⌝ }} ⊢ {{ True }} f #() + f #() {{ v, ∃ z : Z, ⌜v = #z⌝ }}.
Proof.
  iIntros "#Hf". unfold hoare. iModIntro. iIntros "_".
  Restart.
  (* more concisely: *)
  iIntros "#Hf !> _".

  (* Let's complete the proof *)
  wp_bind (f _). iApply wp_wand.
  { by iApply "Hf". }
  iIntros (v) "(%z & ->)".

  wp_bind (f _). iApply ent_wp_wand'; first last.
  { by iApply "Hf". }
  iIntros (v) "(%z2 & ->)".

  wp_pures. iApply wp_value. eauto.
Qed.

(** Exercise: Magic Wands for Accessors *)
Definition lookup_ll : val :=
  rec: "lookup" "l" "i" :=
    match: "l" with
      NONE => NONE
    | SOME "l" =>
        if: "i" = #0 then SOME "l"
        else
          let: "lv" := !"l" in
          "lookup" (Snd "lv") ("i" - #1)
    end.

(**
  The lookup [!!!] is stdpp's [lookup_total] that, in contrast to [lookup],
  does not return an [option], but rather a default value.
  (It computes well using Rocq's reduction tactics.)
 *)
Lemma lookup_ll_correct xs lv (n : nat) :
  ⊢ {{ is_ll xs lv ∗ ⌜n < length xs⌝ }}
      lookup_ll lv #n
    {{ v, ∃ (l : loc) next, ⌜v = SOMEV #l⌝ ∗ l ↦ (xs !!! n, next) ∗ (∀ w', l ↦ (w', next) -∗ is_ll (<[n := w']> xs) lv) }}.
Proof.
  (* TODO: exercise *)
Admitted.


(* A derived version that does not wrap the result in an option value.
  (thus, at the language level, no case analysis on whether the value actually exists is possible)
*)
Definition lookup_ll_unsafe : val :=
  λ: "l" "i",
    match: lookup_ll "l" "i" with
      SOME "l" => "l"
    | NONE => NONE
    end.
Lemma lookup_ll_unsafe_correct xs lv (n : nat) :
  ⊢ {{ is_ll xs lv ∗ ⌜n < length xs⌝ }}
      lookup_ll_unsafe lv #n
    {{ v, ∃ (l : loc) next, ⌜v = #l⌝ ∗ l ↦ (xs !!! n, next) ∗ (∀ w', l ↦ (w', next) -∗ is_ll (<[n := w']> xs) lv) }}.
Proof.
(* derive this from [lookup_ll_correct] *)
  (* TODO: exercise *)
Admitted.


(** ** Invariants *)
(*Check ent_inv_pers.*)
(*Check ent_inv_alloc.*)

(* The following rule is more comvenient to use *)
(*Check inv_alloc.*)

(** We require a sidecondition here, namely that [F] is "timeless". All propositions we have seen up to now are in fact timeless.
  We will see propositions that do not satisfy this requirement and which need a stronger rule for invariants soon.
*)
(*Check ent_inv_open.*)
(*Check inv_open.*)


(** MyMutBit *)
Definition MyMutBit : expr :=
  let: "x" := ref #0 in
  (λ: "y", "x" <- #1 - !"x",
   λ: "y", #0 < !"x").

Definition MutBit v : iProp :=
  {{ True }} (Fst v) #() {{ w, ⌜w = #()⌝ }} ∗
  {{ True }} (Snd v) #() {{ w, ⌜w = #true⌝ ∨ ⌜w = #false⌝}}.

Definition mutbitN := nroot .@ "mutbit".
Lemma MyMutBit_proof :
  ⊢ {{ True }} MyMutBit {{ v, MutBit v }}.
Proof.
  iIntros "!> _". unfold MyMutBit. wp_alloc l as "Hl". wp_pures.
  iApply (inv_alloc mutbitN (l ↦ #0 ∨ l ↦ #1) with "[Hl]").
  { eauto with iFrame. }
  iIntros "#HInv".
  iApply wp_value. unfold MutBit. iSplit.
  - iIntros "!>_". wp_pures.
    iApply (inv_open with "HInv"); first set_solver.
    iIntros "[Hl | Hl]".
    + wp_load. wp_store. iApply wp_value. eauto with iFrame.
    + wp_load. wp_store. iApply wp_value. eauto with iFrame.
  - iIntros "!> _". wp_pures.
    iApply (inv_open with "HInv"); first set_solver.
    iIntros "[Hl | Hl]".
    + wp_load. wp_pures. iApply wp_value. eauto with iFrame.
    + wp_load. wp_pures. iApply wp_value. eauto with iFrame.
Qed.

Notation "'assert' e" := (if: e%E then #() else #0 #0)%E (at level 40) : expr_scope.
(** Exercise: Counter *)

Definition SafeCounter : expr :=
  let: "c1" := ref #0 in let: "c2" := ref #0 in
  ((* inc *) λ: "_", "c1" <- !"c1" + #1;; "c2" <- !"c2" + #1,
   (* get *) λ: "_", let: "v1" := !"c1" in let: "v2" := !"c2" in assert("v1" = "v2");; "v1").

Definition SafeCounter_safe v : iProp :=
  {{ True }} (Fst v) #() {{ w, True }} ∗
  {{ True }} (Snd v) #() {{ w, True }}.

Definition counterN := nroot .@ "counter".
Lemma SafeCounter_proof :
  ⊢ {{ True }} SafeCounter {{ v, SafeCounter_safe v }}.
Proof.
  (* TODO: exercise *)
Admitted.


(** Exercise: Abstract integers *)
Definition MyInt : expr :=
  λ: "z",
  let: "x" := ref (if: #0 < "z" then (#0, "z") else (-"z", #0)) in
  ((λ: "y", let: "xv" := !"x" in assert (#0 ≤ Fst "xv");; assert (#0 ≤ Snd "xv");; Snd "xv" - Fst "xv"),
   (λ: "y", let: "xv" := !"x" in "x" <- (Snd "xv", Fst "xv"))).

Definition FlipInt v : iProp :=
  {{ True }} (Fst v) #() {{ w, ∃ z : Z, ⌜w = #z⌝ }} ∗
  {{ True }} (Snd v) #() {{ w, ⌜w = #()⌝ }}.

Definition flipintN := nroot .@ "flipint".
Lemma MyInt_proof (z : Z) :
  ⊢ {{ True }} MyInt #z {{ v, FlipInt v }}.
Proof.
  (* TODO: exercise *)
Admitted.

