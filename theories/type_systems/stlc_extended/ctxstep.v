From semantics.ts.stlc_extended Require Export lang.

(** The stepping relation *)

Inductive base_step : expr → expr → Prop :=
  | BetaS x e1 e2 e' :
     is_val e2 →
     e' = subst' x e2 e1 →
     base_step (App (Lam x e1) e2) e'
  | PlusS e1 e2 (n1 n2 n3 : Z):
     e1 = (LitInt n1) →
     e2 = (LitInt n2) →
     (n1 + n2)%Z = n3 →
     base_step (Plus e1 e2) (LitInt n3)
  (* TODO: extend the definition *)
.

#[export] Hint Constructors base_step : core.

(** We define evaluation contexts *)
Inductive ectx :=
  | HoleCtx
  | AppLCtx (K: ectx) (v2 : val)
  | AppRCtx (e1 : expr) (K: ectx)
  | PlusLCtx (K: ectx) (v2 : val)
  | PlusRCtx (e1 : expr) (K: ectx)
  (* TODO: extend the definition *)
.

Fixpoint fill (K : ectx) (e : expr) : expr :=
  match K with
  | HoleCtx => e
  | AppLCtx K v2 => App (fill K e) (of_val v2)
  | AppRCtx e1 K => App e1 (fill K e)
  | PlusLCtx K v2 => Plus (fill K e) (of_val v2)
  | PlusRCtx e1 K => Plus e1 (fill K e)
  (* TODO: extend the definition *)
  end.

Fixpoint comp_ectx (K: ectx) (K' : ectx) : ectx :=
  match K with
  | HoleCtx => K'
  | AppLCtx K v2 => AppLCtx (comp_ectx K K') v2
  | AppRCtx e1 K => AppRCtx e1 (comp_ectx K K')
  | PlusLCtx K v2 => PlusLCtx (comp_ectx K K') v2
  | PlusRCtx e1 K => PlusRCtx e1 (comp_ectx K K')
  (* TODO: extend the definition *)
  end.

(** Contextual steps *)
Inductive contextual_step (e1 : expr) (e2 : expr) : Prop :=
  Ectx_step K e1' e2' :
    e1 = fill K e1' → e2 = fill K e2' →
    base_step e1' e2' → contextual_step e1 e2.

#[export] Hint Constructors contextual_step : core.

Definition reducible (e : expr) :=
  ∃ e', contextual_step e e'.

Definition empty_ectx := HoleCtx.

(** Basic properties about the language *)
Lemma fill_empty e : fill empty_ectx e = e.
Proof. done. Qed.

Lemma fill_comp (K1 K2 : ectx) e : fill K1 (fill K2 e) = fill (comp_ectx K1 K2) e.
Proof. induction K1; simpl; congruence. Qed.

Lemma base_contextual_step e1 e2 :
  base_step e1 e2 → contextual_step e1 e2.
Proof. apply Ectx_step with empty_ectx; by rewrite ?fill_empty. Qed.

Lemma fill_contextual_step K e1 e2 :
  contextual_step e1 e2 → contextual_step (fill K e1) (fill K e2).
Proof.
  destruct 1 as [K' e1' e2' -> ->].
  rewrite !fill_comp. by econstructor.
Qed.

(** We derive a few lemmas about contextual steps:
  these essentially provide rules for structural lifting
   akin to the structural semantics.
 *)
Lemma contextual_step_app_l e1 e1' e2:
  is_val e2 →
  contextual_step e1 e1' →
  contextual_step (App e1 e2) (App e1' e2).
Proof.
  intros [v <-%of_to_val]%is_val_spec Hcontextual.
  by eapply (fill_contextual_step (AppLCtx HoleCtx v)).
Qed.

Lemma contextual_step_app_r e1 e2 e2':
  contextual_step e2 e2' →
  contextual_step (App e1 e2) (App e1 e2').
Proof.
  intros Hcontextual.
  by eapply (fill_contextual_step (AppRCtx e1 HoleCtx)).
Qed.

Lemma contextual_step_plus_l e1 e1' e2:
  is_val e2 →
  contextual_step e1 e1' →
  contextual_step (Plus e1 e2) (Plus e1' e2).
Proof.
  intros [v <-%of_to_val]%is_val_spec Hcontextual.
  by eapply (fill_contextual_step (PlusLCtx HoleCtx v)).
Qed.

Lemma contextual_step_plus_r e1 e2 e2':
  contextual_step e2 e2' →
  contextual_step (Plus e1 e2) (Plus e1 e2').
Proof.
  intros Hcontextual.
  by eapply (fill_contextual_step (PlusRCtx e1 HoleCtx)).
Qed.

Lemma contextual_step_pair_l e1 e1' e2:
  is_val e2 →
  contextual_step e1 e1' →
  contextual_step (Pair e1 e2) (Pair e1' e2).
Proof.
  (* TODO: exercise *)
Admitted.


Lemma contextual_step_pair_r e1 e2 e2':
  contextual_step e2 e2' →
  contextual_step (Pair e1 e2) (Pair e1 e2').
Proof.
  (* TODO: exercise *)
Admitted.


Lemma contextual_step_fst e e':
  contextual_step e e' →
  contextual_step (Fst e) (Fst e').
Proof.
  (* TODO: exercise *)
Admitted.


Lemma contextual_step_snd e e':
  contextual_step e e' →
  contextual_step (Snd e) (Snd e').
Proof.
  (* TODO: exercise *)
Admitted.


Lemma contextual_step_injl e e':
  contextual_step e e' →
  contextual_step (InjL e) (InjL e').
Proof.
  (* TODO: exercise *)
Admitted.


Lemma contextual_step_injr e e':
  contextual_step e e' →
  contextual_step (InjR e) (InjR e').
Proof.
  (* TODO: exercise *)
Admitted.


Lemma contextual_step_case e e' e1 e2:
  contextual_step e e' →
  contextual_step (Case e e1 e2) (Case e' e1 e2).
Proof.
  (* TODO: exercise *)
Admitted.


#[global]
Hint Resolve
  contextual_step_app_l contextual_step_app_r contextual_step_plus_l contextual_step_plus_r
  contextual_step_case contextual_step_fst contextual_step_injl contextual_step_injr
  contextual_step_pair_l contextual_step_pair_r contextual_step_snd : core.
