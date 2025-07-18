From stdpp Require Import prelude.
From iris Require Import prelude.
From semantics.ts.stlc_extended Require Import lang.
From semantics.lib Require Import maps.

Fixpoint subst_map (xs : gmap string expr) (e : expr) : expr :=
  match e with
  | LitInt n => LitInt n
  | Var y => match xs !! y with Some es => es | _ =>  Var y end
  | App e1 e2 => App (subst_map xs e1) (subst_map xs e2)
  | Lam x e => Lam x (subst_map (binder_delete x xs) e)
  | Plus e1 e2 => Plus (subst_map xs e1) (subst_map xs e2)
  | Pair e1 e2 => Pair (subst_map xs e1) (subst_map xs e2)
  | Fst e => Fst (subst_map xs e)
  | Snd e => Snd (subst_map xs e)
  | InjL e => InjL (subst_map xs e)
  | InjR e => InjR (subst_map xs e)
  | Case e e1 e2 => Case (subst_map xs e) (subst_map xs e1) (subst_map xs e2)
  end.


Lemma subst_map_empty e :
  subst_map ∅ e = e.
Proof.
  induction e; simpl; f_equal; eauto.
  destruct x; simpl; [done | by rewrite !delete_empty..].
Qed.



Lemma subst_map_closed X e xs :
  closed X e →
  (∀ x : string, x ∈ dom xs → x ∉ X) →
  subst_map xs e = e.
Proof.
  intros Hclosed Hd.
  induction e in xs, X, Hd, Hclosed |-*; simpl in *;try done.
  { (* Var *)
    apply bool_decide_spec in Hclosed.
    assert (xs !! x = None) as ->; last done.
    destruct (xs !! x) as [s | ] eqn:Helem; last done.
    exfalso; eapply Hd; last apply Hclosed.
    apply elem_of_dom; eauto.
  }
  { (* lambdas *)
    erewrite IHe; [done | done |].
    intros y. destruct x as [ | x]; first apply Hd.
    simpl.
    rewrite dom_delete elem_of_difference not_elem_of_singleton.
    intros [Hnx%Hd Hneq]. rewrite elem_of_cons. intros [? | ?]; done.
  }
  (* all other cases *)
  all: unfold closed in *; simpl in *.
  all: repeat match goal with
  | H : Is_true (_ && _)  |- _ => apply andb_True in H as [ ? ? ]
              end.
  all: repeat match goal with
       | H : ∀ _ _, _ → _ → subst_map _ _ = _ |- _ => erewrite H; clear H
       end; try done.
Qed.

Lemma subst_map_subst map x (e e': expr) :
  closed [] e' →
  subst_map map (subst x e' e) = subst_map (<[x:=e']>map) e.
Proof.
  intros He'; induction e as [y|y e IH | | | | | | | | | ]in map|-*; simpl; try (f_equal; eauto).
  - case_decide.
    + simplify_eq/=. rewrite lookup_insert_eq.
      rewrite (subst_map_closed []); [done | apply He' | ].
      intros ? ?. apply not_elem_of_nil.
    + rewrite lookup_insert_ne; done.
  - destruct y; simpl; first done.
    + case_decide.
      * simplify_eq/=. by rewrite delete_insert_eq.
      * rewrite delete_insert_ne; last by congruence. done.
Qed.

(** We lift the notion of closedness [closed] to substitution maps. *)
Definition subst_closed (X : list string) (map : gmap string expr) :=
  ∀ x e, map !! x = Some e → closed X e.
Lemma subst_closed_subseteq X map1 map2 :
  map1 ⊆ map2 → subst_closed X map2 → subst_closed X map1.
Proof.
  intros Hsub Hclosed2 x e Hl. eapply Hclosed2, map_subseteq_spec; done.
Qed.

Lemma subst_closed_weaken X Y map1 map2 :
  Y ⊆ X → map1 ⊆ map2 → subst_closed Y map2 → subst_closed X map1.
Proof.
  intros Hsub1 Hsub2 Hclosed2 x e Hl.
  eapply is_closed_weaken. 1:eapply Hclosed2, map_subseteq_spec; done. done.
Qed.

(** Lemma about the interaction with "normal" substitution. *)
Lemma subst_subst_map x es map e :
  subst_closed [] map →
  subst x es (subst_map (delete x map) e) =
  subst_map (<[x:=es]> map) e.
Proof.
  revert map es x; induction e; intros map v0 xx Hclosed; simpl;
  try (f_equal; eauto).
  - destruct (decide (xx=x)) as [->|Hne].
    + rewrite lookup_delete_eq // lookup_insert_eq //. simpl.
      rewrite decide_True //.
    + rewrite lookup_delete_ne // lookup_insert_ne //.
      destruct (_ !! x) as [rr|] eqn:Helem.
      * apply Hclosed in Helem.
        by apply subst_is_closed_nil.
      * simpl. rewrite decide_False //.
  - destruct x; simpl; first by auto.
    case_decide.
    + simplify_eq. rewrite delete_delete_eq delete_insert_eq. done.
    + rewrite delete_insert_ne //; last congruence. rewrite delete_delete. apply IHe.
      eapply subst_closed_subseteq; last done.
      apply map_delete_subseteq.
Qed.

Lemma subst'_subst_map b (es : expr) map e :
  subst_closed [] map →
  subst' b es (subst_map (binder_delete b map) e) =
  subst_map (binder_insert b es map) e.
Proof.
  destruct b; first done.
  apply subst_subst_map.
Qed.

Lemma closed_subst_weaken e map X Y :
  subst_closed [] map →
  (∀ x, x ∈ X → x ∉ dom map → x ∈ Y) →
  closed X e →
  closed Y (subst_map map e).
Proof.
  induction e in X, Y, map |-*; simpl; intros Hmclosed Hsub Hcl.
  { (* vars *)
    destruct (map !! x) as [es | ] eqn:Heq.
    + apply is_closed_weaken_nil. by eapply Hmclosed.
    + apply bool_decide_pack. apply Hsub; first by eapply bool_decide_unpack.
      by apply not_elem_of_dom.
  }
  { (* lambdas *)
    eapply IHe; last done.
    + eapply subst_closed_subseteq; last done.
      destruct x; first done. apply map_delete_subseteq.
    + intros y. destruct x as [ | x]; first by apply Hsub.
      rewrite !elem_of_cons. intros [-> | Hy] Hn; first by left.
      destruct (decide (y = x)) as [ -> | Hneq]; first by left.
      right. eapply Hsub; first done. set_solver.
  }
  (* all other cases *)
  all: unfold closed in *; simpl in *.
  all: repeat match goal with
         | H : Is_true (_ && _)  |- _ => apply andb_True in H as [ ? ? ]
              end.
  all: repeat match goal with
         | |- Is_true (_ && _) => apply andb_True; split
              end.
  all: try naive_solver.
Qed.


Lemma subst_map_closed' X Y Θ e:
  closed Y e →
  (∀ x, x ∈ Y → if Θ !! x is (Some e') then closed X e' else x ∈ X) →
  closed X (subst_map Θ e).
Proof.
  induction e in X, Θ, Y |-*; simpl.
  { intros Hel%bool_decide_unpack Hcl.
    eapply Hcl in Hel.
    destruct (Θ !! x); first done.
    simpl. by eapply bool_decide_pack. }
  { intros Hcl Hcl'. destruct x as [|x]; simpl; first naive_solver.
    eapply IHe; first done.
    intros y [|]%elem_of_cons.
    + subst. rewrite lookup_delete_eq. set_solver.
    + destruct (decide (x = y)); first by subst; rewrite lookup_delete_eq; set_solver.
      rewrite lookup_delete_ne //=. eapply Hcl' in H.
      destruct lookup; last set_solver.
      eapply is_closed_weaken; eauto with set_solver. }
  all: unfold closed; simpl; naive_solver.
Qed.

Lemma subst_map_closed'_2 X Θ e:
  closed (X ++ (elements (dom Θ))) e ->
  subst_closed X Θ ->
  closed X (subst_map Θ e).
Proof.
  intros Hcl Hsubst.
  eapply subst_map_closed'; first eassumption.
  intros x Hx.
  destruct (Θ !! x) as [e'|] eqn:Heq.
  - eauto.
  - by eapply elem_of_app in Hx as [H|H%elem_of_elements%not_elem_of_dom].
Qed.
