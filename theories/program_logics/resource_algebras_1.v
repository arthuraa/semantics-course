From iris.proofmode Require Import tactics.
From iris.heap_lang Require Import lang notation.
From iris.bi Require Import fractional.
From semantics.pl.heap_lang Require Import primitive_laws proofmode.
From Stdlib.Logic Require FunctionalExtensionality.
From iris.base_logic Require Import own.
From semantics.pl Require Import ra_lib.
From iris.prelude Require Import options.

(** ** Resource algebras *)

(** Let's first consider the interaction with Iris's [own] connective. *)

(* Allocation ResAlloc *)
(* Note that we use the symbol ✓ for validity *)
(*Check own_alloc.*)

(* Interaction with separating conjunction, ResSep *)
(*Check own_op.*)

(* The core is persistent, ResPers *)
(* (this is formulated slightly differently here: [CoreId a] says that [a] is its own core) *)
(*Check own_core_persistent.*)

(* Resources are valid, ResValid *)
(*Check own_valid.*)

(* Frame-preserving updates, ResUpd *)
(*Check own_update.*)

(* [own] is monotonous wrt inclusion *)
(*Check own_mono.*)

(* We can always own a unit *)
(*Check own_unit.*)

(** Some notes on the setup in Rocq:
  1. The `inG` assumptions you see for these lemmas above require that the given algebra has been registered with Iris, similar to the `mono_natG Σ` assumption you have already seen. We will discuss this later in more detail.

  2. Iris uses a considerably more general notion of resources than the RAs we consider in the lecture for now (it is actually step-indexed, to resolve some issues you will see soon in the lecture.)

    Here's some information on that you may find helpful for understanding this file:
    - Each RA can define its own notion of "equality" via an [Equiv] instance, and the laws (e.g. [ra_comm]) use this notion instead of Rocq's propositional Leibniz equality. (This is to make up for the lack of the ability to quotient via an equivalence relation which is possible in set theory, but not generally available in type theory.)

    - In Iris, you will usually see the type [cmra]. This is a generalization of RAs that allows validity and equality on the algebra to depend on the current step-index.
      We will discuss this later in the course.
      The RAs we saw in the lecture are essentially "discrete" CMRAs (that don't depend on the step-index).
      One can construct a CMRA that does not depend on the step-index by proving some simpler rules ([RAMixin] instead of [CmraMixin] in Iris).

  3. Below, we setup a notion of RAs that closely matches the simplified version shown in the lecture, so you do not need to understand the CMRA setup in Iris in detail for now. It is sufficient to do most things we are interested in for now.
    Our definition essentially matches Iris's notion of RAs (non step-indexed CMRAs), but uses Rocq's propositional (Leibniz) equality instead of allowing to define a setoid via an [Equiv] instance. This reduces the overhead for showing that all our things are proper wrt this notion of equivalence.

  4. You can type the relevant symbols as follows:
   - ✓ (validity): \valid or \checkmark
   - ⋅ (the operator of RAs): \cdot or \mult
   - ≼ (the inclusion on RAs): \incl or \preccurlyeq
 *)

(** ** Setup of our notion of RAs *)
(** Aside: our notion of RA's is defined via Rocq's propositional (Leibniz) equality [=], so we call them "LRA" (Leibniz RA). *)
(** An lra contains a carrier type and the necessary operations:
  - a partial core [pcore]
  - an operation [⋅]
  - a validity predicate [✓]

  In addition, it carries a proof that these operations satisfy the necessary laws [LRAMixin].
 *)
(*Print lra.*)

(** The required laws: this matches what you can find in the lecture notes. *)
(*Print LRAMixin.*)

(** We require a few additional operations:
  - [lra_included] defines the inclusion [≼]
  - [lra_update] defines the notion of frame-preserving updates.
   Here [⋅?] lifts the operation [⋅] to optional right-hand sides: [opMLRA].
  - [lra_exclusive] defines what it means for an element to be exclusive (i.e., not compose with any frame).
 *)
(*Print lra_included.*)
(*Print lra_update.*)
(*Print lra_local_update.*)
(*Print opMLRA.*)
(*Print lra_exclusive.*)

(** We prove some derived lemmas *)

(** Inclusion lemmas *)
Lemma lra_included_l {A : lra} (x y : A) :
  x ≼ x ⋅ y.
Proof.
  by exists y.
Qed.

Lemma lra_included_r {A : lra} (x y : A) :
  x ≼ y ⋅ x.
Proof.
  exists y. by rewrite lra_comm.
Qed.

Global Instance lra_included_trans {A : lra} : Transitive (lra_included (A:=A)).
Proof.
  intros x y z [c1 ->] [c2 ->].
  exists (c1 ⋅ c2). by rewrite assoc.
Qed.

Lemma lra_included_valid {A : lra} (x y : A) :
  x ≼ y → ✓ y → ✓ x.
Proof.
  intros [c ->]. apply lra_valid_op_l.
Qed.

(** Core *)
Lemma lra_pcore_r {A : lra} (x cx : A) :
  pcore x = Some cx → x ⋅ cx = x.
Proof. intros ?. rewrite lra_comm. by apply lra_pcore_l. Qed.

Lemma lra_valid_op_r {A : lra} (x y : A) :
  ✓ (x ⋅ y) → ✓ y.
Proof.
  rewrite comm. apply lra_valid_op_l.
Qed.

(** We can always update exclusive elements, since there is no frame we could disturb. *)
Lemma lra_update_exclusive {A : lra} (x y : A) :
  lra_exclusive x →
  ✓ y →
  lra_update x y.
Proof.
  (* TODO: exercise *)
Admitted.


(** Relation of update and updateP *)
Lemma lra_update_updateP {A : lra} (x y : A) : lra_update x y ↔ lra_updateP x (y =.).
Proof. split=> Hup z ?; eauto. destruct (Hup z) as (?&<-&?); auto. Qed.
Lemma lra_updateP_id {A : lra} (P : A → Prop) x : P x → lra_updateP x P.
Proof. intros ? mz ?; eauto. Qed.
Lemma lra_updateP_compose {A : lra} (P Q : A → Prop) x :
  lra_updateP x P → (∀ y, P y → lra_updateP y Q) → lra_updateP x Q.
Proof. intros Hx Hy mz ?. destruct (Hx mz) as (y&?&?); naive_solver. Qed.

Lemma lra_local_update_valid {A : lra} (x y x' y' : A) :
  (✓ x → ✓ y → x = y ∨ y ≼ x → lra_local_update (x,y) (x',y')) →
  lra_local_update (x,y) (x',y').
Proof.
  intros Hup mz [Hmz1 Hmz2]. simpl in *. apply Hup; auto.
  - rewrite Hmz2 in Hmz1. destruct mz; simpl; eauto using lra_valid_op_l.
  - destruct mz; simpl in *; subst; eauto using lra_included_l.
Qed.

(** In addition, we need a notion of unital RAs (i.e., RAs with a unit). *)
(** In addition to [lra]s, they need to have a unit [ε] (type \varepsilon). *)
(*Print ulra.*)

(** The unit needs to satisfy the following laws: *)
(*Print ULRAMixin.*)

(** Unit: derived laws *)
Global Instance ulra_unit_right_id {A : ulra} : RightId (=) ε (@op A _).
Proof.
  intros x. by rewrite lra_comm left_id.
Qed.
Lemma ulra_unit_included {A : ulra} (x : A) :
  ε ≼ x.
Proof.
  exists x. by rewrite left_id.
Qed.

Global Instance ulra_included_reflexive {A : ulra} : Reflexive (lra_included (A := A)).
Proof.
  intros a. exists ε. rewrite right_id. done.
Qed.

(** Total RAs have a total core *)
(** The operation [core] is usable for total RAs. *)
Class LraTotal (A : lra) := lra_total (x : A) : is_Some (pcore x).
Section total.
  Context `{LraTotal A}.
  Implicit Types (x : A).

  (** Lemmas about total RAs *)
  Lemma lra_pcore_core x : pcore x = Some (core x).
  Proof using Type*.
    rewrite /core. destruct (lra_total x) as [cx ->]. done.
  Qed.
  Lemma lra_core_l x : core x ⋅ x = x.
  Proof using Type*.
    destruct (lra_total x) as [cx Hcx]. by rewrite /core /= Hcx lra_pcore_l.
  Qed.
  Lemma lra_core_r x : x ⋅ core x = x.
  Proof using Type*.
    destruct (lra_total x) as [cx Hcx]. by rewrite /core /= Hcx lra_pcore_r.
  Qed.
  Lemma lra_core_idemp x : core (core x) = core x.
  Proof using Type*.
    destruct (lra_total x) as [cx Hcx]. rewrite /core !Hcx /=. by erewrite lra_pcore_idemp.
  Qed.
  Lemma lra_core_mono x y : x ≼ y → core x ≼ core y.
  Proof using Type*.
    intros; destruct (lra_total x) as [cx Hcx].
    destruct (lra_pcore_mono x y cx) as (cy&Hcy&?); auto.
    by rewrite /core /= Hcx Hcy.
  Qed.

  Lemma lra_total_updateP x (P : A → Prop) :
    lra_updateP x P ↔ ∀ z, ✓ (x ⋅ z) → ∃ y, P y ∧ ✓ (y ⋅ z).
  Proof using Type*.
    split=> Hup; [intros z; apply (Hup (Some z))|].
    intros [z|] ?; simpl; [by apply Hup|].
    destruct (Hup (core x)) as (y&?&?); first by rewrite lra_core_r.
    eauto using lra_valid_op_l.
  Qed.
  Lemma lra_total_update x y : lra_update x y ↔ ∀ z, ✓ (x ⋅ z) → ✓ (y ⋅ z).
  Proof using Type*. rewrite lra_update_updateP lra_total_updateP. naive_solver. Qed.

  Global Instance lra_total_included_refl : Reflexive (lra_included (A := A)).
  Proof using Type*. intros a. exists (core a). by rewrite lra_comm lra_core_l. Qed.

  Lemma lra_local_update_total_valid (x y x' y' : A) :
    (✓ x → ✓ y → y ≼ x → lra_local_update (x,y) (x',y')) → lra_local_update (x,y) (x',y').
  Proof using Type*.
    intros Hup. apply lra_local_update_valid => ?? [Hx|?]; apply Hup; auto.
    by rewrite Hx.
  Qed.
End total.

(** Smart constructor for total RAs *)
Section lra_total.
  Context A `{PCore A, Op A, Valid A}.
  Context (total : ∀ x : A, is_Some (pcore x)).
  Context (op_assoc : Assoc (=) (@op A _)).
  Context (op_comm : Comm (=) (@op A _)).
  Context (core_l : ∀ x : A, core x ⋅ x = x).
  Context (core_idemp : ∀ x : A, core (core x) = core x).
  Context (core_mono : ∀ x y : A, x ≼ y → core x ≼ core y).
  Context (valid_op_l : ∀ (x y : A), ✓ (x ⋅ y) → ✓ x).
  Lemma lra_total_mixin : LRAMixin A.
  Proof using Type*.
    split; auto.
    - intros x y Hx. rewrite -{2}(core_l x). by rewrite /core Hx.
    - intros x cx Hcx.
      move: (core_idemp x). rewrite /core. rewrite Hcx. simpl.
      case (total cx)=>[ccx ->]. naive_solver.
    - intros x y cx Hxy%core_mono Hx. move: Hxy.
      rewrite /core /= Hx /=. case (total y)=> [cy ->]; eauto.
  Qed.
End lra_total.

(** Unital RAs are total: we can always pick the unit *)
Section ulra_total.
  Context {A : ulra}.
  Lemma ulra_unit_least (x : A) : ε ≼ x.
  Proof. by exists x; rewrite left_id. Qed.

  Global Instance lra_unit_lra_total : LraTotal A.
  Proof.
    intros x.
    destruct (lra_pcore_mono ε x ε) as (cx&->&?); [..|by eauto].
    - apply ulra_unit_least.
    - apply ulra_unit_pcore.
  Qed.
End ulra_total.


(** ** Example: the (nat, max) RA *)
Record max_nat := MaxNat { max_nat_car : nat }.
Add Printing Constructor max_nat.
Section max_nat.
  (** We define local typeclass instances for the operations.
    These must not be global (outside the section), since they will be inferred automatically from the
    definition of the full RA below. *)
  Instance max_nat_valid_instance : Valid max_nat := λ x, True.
  Instance max_nat_pcore_instance : PCore max_nat := λ x, Some x.
  Instance max_nat_op_instance : Op max_nat := λ n m, MaxNat (max_nat_car n `max` max_nat_car m).

  Instance max_nat_unit_instance : Unit max_nat := MaxNat 0.

  Lemma max_nat_op x y : MaxNat x ⋅ MaxNat y = MaxNat (x `max` y).
  Proof. reflexivity. Qed.
  Lemma max_nat_pcore (x : max_nat) : pcore x = Some x.
  Proof. done. Qed.
  Lemma max_nat_valid (x : max_nat) : ✓ x.
  Proof. done. Qed.

  Lemma max_nat_included x y : x ≼ y ↔ max_nat_car x ≤ max_nat_car y.
  Proof.
    split.
    - intros [z ->]. simpl. lia.
    - exists y. rewrite /op /max_nat_op_instance. rewrite Nat.max_r; last lia. by destruct y.
  Qed.

  (** We prove that this definition satisfies the RA laws *)
  Lemma max_nat_lra_mixin : LRAMixin max_nat.
  Proof.
    constructor; apply _ || eauto.
    - intros [x] [y] [z]. repeat rewrite max_nat_op. by rewrite Nat.max_assoc.
    - intros [x] [y]. by rewrite max_nat_op Nat.max_comm.
    - intros [x] [cx]. intros [= ->]. by rewrite max_nat_op Nat.max_id.
    - intros [x] [y] [cx].
      intros ([z] & ->). intros [= ->]. rewrite max_nat_op.
      eexists _. split; first done. exists (MaxNat z); by rewrite max_nat_op.
  Qed.
  (** Iris uses the canonical structure mechanism (which is similar to, but different from typeclasses)
     of Rocq to register the RA structure we define for a type.
     This will allow us to use elements of the Rocq type [max_nat] as normal, but when we need the RA operations and laws on it, Rocq will automatically infer them from this declaration.

     You do not need to understand this in detail -- just take this example.
     We usually define the canonical structure by appending a big R to the name of the type on which it is defined.
   *)
  Canonical Structure max_natR : lra := Lra max_nat max_nat_lra_mixin.

  (** Similarly, we define the unital structure *)
  Lemma max_nat_ulra_mixin : ULRAMixin max_nat.
  Proof.
    constructor; try done.
    intros []. rewrite max_nat_op. by f_equiv.
  Qed.
  Canonical Structure max_natUR : ulra := Ulra max_nat max_nat_lra_mixin max_nat_ulra_mixin.

  (** Updates are trivial *)
  Lemma max_nat_update (x y : max_nat) : lra_update x y.
  Proof. done. Qed.
End max_nat.

(** ** Example: The (nat, +) RA *)
Section nat.
  Instance nat_unit_instance : Unit nat := 0.
  Instance nat_valid_instance : Valid nat := λ x, True.
  Instance nat_pcore_instance : PCore nat := λ x, Some 0.
  Instance nat_op_instance : Op nat := λ n m, n + m.

  Lemma nat_op (x y : nat) : x ⋅ y = (x + y).
  Proof. reflexivity. Qed.
  Lemma nat_unit : ε = 0.
  Proof. done. Qed.

  Lemma nat_included x y : x ≼ y ↔ x ≤ y.
  Proof.
    split.
    - intros [z ->]. rewrite nat_op. lia.
    - intros Hle. exists (y - x). rewrite nat_op. lia.
  Qed.

  Lemma nat_lra_mixin : LRAMixin nat.
  Proof.
    constructor; apply _ || eauto.
    - intros x cx. intros [= <-]. done.
    - intros x y cx (z & ->) [= <-]. rewrite nat_op. exists 0. split; first done.
      exists 0. done.
  Qed.
  Canonical Structure natR : lra := Lra nat nat_lra_mixin.

  Lemma nat_ulra_mixin : ULRAMixin nat.
  Proof. constructor; done. Qed.
  Canonical Structure natUR : ulra := Ulra nat nat_lra_mixin nat_ulra_mixin.

  Lemma nat_update (x y : nat) : lra_update x y.
  Proof. done. Qed.
End nat.


(** ** The (Q, +) RA *)
Notation frac := Qp.
Section frac.
  Local Instance frac_valid_instance : Valid frac := λ x, (x ≤ 1)%Qp.
  Local Instance frac_pcore_instance : PCore frac := λ _, None.
  Local Instance frac_op_instance : Op frac := λ x y, (x + y)%Qp.

  Lemma frac_valid p : ✓ p ↔ (p ≤ 1)%Qp.
  Proof. done. Qed.
  Lemma frac_op p q : p ⋅ q = (p + q)%Qp.
  Proof. done. Qed.
  Lemma frac_included p q : p ≼ q ↔ (p < q)%Qp.
  Proof. by rewrite Qp.lt_sum. Qed.

  Corollary frac_included_weak p q : p ≼ q → (p ≤ q)%Qp.
  Proof. rewrite frac_included. apply Qp.lt_le_incl. Qed.

  Definition frac_lra_mixin : LRAMixin frac.
  Proof.
    split; try apply _; try done.
    intros p q. rewrite !frac_valid frac_op=> ?.
    trans (p + q)%Qp; last done. apply Qp.le_add_l.
  Qed.
  Canonical Structure fracR : lra := Lra frac frac_lra_mixin.

  Lemma frac_lra_exclusive_1 :
    lra_exclusive 1%Qp.
  Proof.
    intros f. rewrite frac_valid frac_op.
    apply Qp.not_add_le_l.
  Qed.
End frac.

(** ** Exercise: (Z, +) *)
Section Z.
  (** TODO: This is an exercise for you! *)
  Instance Z_unit_instance : Unit Z := 42 (* TODO *).
  Instance Z_valid_instance : Valid Z := λ x, False (* TODO *).
  Instance Z_pcore_instance : PCore Z := λ x, None (* TODO *).
  Instance Z_op_instance : Op Z := λ n m, n (* TODO *).

  Lemma Z_op (x y : Z) : x ⋅ y = x (* TODO *).
  Proof. reflexivity. Qed.

  Lemma Z_included (x y : Z) : x ≼ y ↔ False (* TODO *).
  Proof.
    (* TODO: exercise *)
  Admitted.


  Lemma Z_lra_mixin : LRAMixin Z.
  Proof.
    constructor; apply _ || eauto.
    (* TODO: exercise *)
  Admitted.


  Canonical Structure ZR : lra := Lra Z Z_lra_mixin.

  Lemma Z_ulra_mixin : ULRAMixin Z.
  Proof.
    (* TODO: exercise *)
  Admitted.


  Canonical Structure ZUR : ulra := Ulra Z Z_lra_mixin Z_ulra_mixin.

  Lemma Z_update (x y : Z) : lra_update x y ↔ False (* TODO *).
  Proof.
    (* TODO: exercise *)
  Admitted.

End Z.

(** ** Exercise: The (nat, min) RA *)
Record min_nat := MinNat { min_nat_car : nat }.
Add Printing Constructor min_nat.
Section min_nat.
  (* TODO: This is an exercise for you. Fix the definitions and statements. *)
  Instance min_nat_valid_instance : Valid min_nat := λ x, False (* TODO *).
  Instance min_nat_pcore_instance : PCore min_nat := λ x, None (* TODO *).
  Instance min_nat_op_instance : Op min_nat := λ n m, n (* TODO *).

  Lemma min_nat_op x y : MinNat x ⋅ MinNat y = MinNat x (* TODO *).
  Proof. reflexivity. Qed.

  Lemma min_nat_included (x y : min_nat) : x ≼ y ↔ False (* TODO *).
  Proof.
    (* TODO: exercise *)
  Admitted.


  Lemma min_nat_lra_mixin : LRAMixin min_nat.
  Proof.
    (* TODO: exercise *)
  Admitted.

  Canonical Structure min_natR : lra := Lra min_nat min_nat_lra_mixin.

  Lemma min_nat_update (x y : min_nat) : lra_update x y ↔ False (* TODO *).
  Proof.
    (* TODO: exercise *)
  Admitted.

End min_nat.

(** ** Options *)
Section option.
  Context {A : lra}.
  Instance option_unit_instance : Unit (option A) := None.
  Instance option_valid_instance : Valid (option A) :=
    λ mx, match mx with
          | None => True
          | Some x => ✓ x
          end.
  Instance option_pcore_instance : PCore (option A) :=
    λ mx, Some (mx ≫= pcore).
  Instance option_op_instance : Op (option A) :=
    λ mx my,
      match mx, my with
      | None, _ => my
      | Some x, Some y => Some (x ⋅ y)
      | _, None => mx
      end.

  Lemma Some_valid a : ✓ Some a ↔ ✓ a.
  Proof. done. Qed.
  Lemma Some_op a b : Some (a ⋅ b) = Some a ⋅ Some b.
  Proof. done. Qed.
  Lemma None_valid : ✓ None.
  Proof. done. Qed.
  Lemma None_op ma mb : ma ⋅ mb = None ↔ ma = None ∧ mb = None.
  Proof. destruct ma, mb; naive_solver. Qed.
  Lemma option_pcore a : pcore a = Some (a ≫= pcore).
  Proof. done. Qed.

  Lemma Some_op_opM a ma : Some a ⋅ ma = Some (a ⋅? ma).
  Proof. by destruct ma. Qed.

  Lemma None_included mb :
    None ≼ mb.
  Proof.
    destruct mb as [ b | ].
    + exists (Some b). done.
    + exists None. done.
  Qed.

   Lemma Some_included a mb :
    Some a ≼ mb ↔ ∃ b, mb = Some b ∧ (a = b ∨ a ≼ b).
  Proof.
    split.
    - intros [mc Hmc].
      destruct mb as [b|]; [exists b|destruct mc; inversion_clear Hmc].
      destruct mc as [c|]; inversion_clear Hmc; split_and?; auto; subst; eauto using lra_included_l.
    - intros (b&->&[Hc|[c Hc]]).
      + subst. exists None; done.
      + exists (Some c). subst b. done.
  Qed.

  Lemma Some_included_lra_exclusive a :
    lra_exclusive a →
    ∀ b, (Some a ≼ Some b) → ✓ b → a = b.
  Proof.
    intros Hexcl b. intros (c & [= <-] & Hor)%Some_included.
    destruct Hor as [ | [c ->]]; first done.
    intros []%Hexcl.
  Qed.

  Lemma option_included ma mb :
    ma ≼ mb ↔ ma = None ∨ ∃ a b, ma = Some a ∧ mb = Some b ∧ (a = b ∨ a ≼ b).
  Proof.
    destruct ma.
    - rewrite Some_included. naive_solver.
    - split; eauto using None_included.
  Qed.

  Lemma option_lra_mixin : LRAMixin (option A).
  Proof.
    constructor.
    - intros [][][]; rewrite /op /option_op_instance ?lra_assoc; eauto.
    - intros [][]; rewrite /op /option_op_instance; try rewrite lra_comm; eauto.
    - intros [][]; rewrite option_pcore; simpl; intros [=]; simpl; eauto.
      rewrite -Some_op; f_equiv. by apply lra_pcore_l.
    - intros [][]; rewrite option_pcore; simpl; intros [=]; simpl; eauto.
      rewrite option_pcore; simpl; f_equiv. by eapply lra_pcore_idemp.
    - intros ma mb mc. setoid_rewrite option_included.
      intros [->|(a&b&->&->&[<-|?])]; simpl; eauto.
      + rewrite option_pcore. intros [= <-].
        rewrite option_pcore. eexists; split; eauto.
      + destruct (pcore a) as [ca|] eqn:Heq; rewrite option_pcore; intros [= <-].
        all: rewrite Heq; simpl; eauto 10.
      + destruct (pcore a) as [ca|] eqn:Heq; rewrite option_pcore; intros [= <-]; eauto.
        destruct (lra_pcore_mono a b ca) as (?&?&?); eauto 10.
    - intros [][]; rewrite ?Some_valid; simpl; try done; eauto using lra_valid_op_l.
  Qed.
  Canonical Structure optionR : lra := Lra (option A) option_lra_mixin.

  Lemma option_ulra_mixin : ULRAMixin (option A).
  Proof. constructor; done. Qed.
  Canonical Structure optionUR : ulra := Ulra (option A) option_lra_mixin option_ulra_mixin.

  (* Updates *)
  Lemma option_updateP (P : A → Prop) (Q : option A → Prop) x :
    lra_updateP x P → (∀ y, P y → Q (Some y)) → lra_updateP (Some x) Q.
  Proof.
    intros Hx Hy; apply lra_total_updateP; intros [y|] ?.
    { destruct (Hx (Some y)) as (y'&?&?); auto. exists (Some y'); auto. }
    destruct (Hx None) as (y'&?&?); rewrite ?cmra_core_r; auto.
    by exists (Some y'); auto.
  Qed.
  Lemma option_updateP' (P : A → Prop) x :
    lra_updateP x P → lra_updateP (Some x) (from_option P False).
  Proof. eauto using option_updateP. Qed.
  Lemma option_update x y : lra_update x y → lra_update (Some x) (Some y).
  Proof. rewrite !lra_update_updateP; eauto using option_updateP with subst. Qed.
End option.
Global Arguments optionUR : clear implicits.

(** ** Sums *)
Inductive csum (A B : Type) :=
  | Cinl : A → csum A B
  | Cinr : B → csum A B
  | CsumBot : csum A B.
Global Arguments Cinl {_ _} _.
Global Arguments Cinr {_ _} _.
Global Arguments CsumBot {_ _}.
Section sum.
  Context {A B : lra}.
  Implicit Types a : A.
  Implicit Types b : B.

  Global Instance Cinl_inj : Inj (=) (=) (@Cinl A B).
  Proof. by inversion_clear 1. Qed.
  Global Instance Cinr_inj : Inj (=) (=) (@Cinr A B).
  Proof. by inversion_clear 1. Qed.

  Local Instance csum_valid_instance : Valid (csum A B) := λ x,
    match x with
    | Cinl a => ✓ a
    | Cinr b => ✓ b
    | CsumBot => False
    end.
  Local Instance csum_pcore_instance : PCore (csum A B) := λ x,
    match x with
    | Cinl a => Cinl <$> pcore a
    | Cinr b => Cinr <$> pcore b
    | CsumBot => Some CsumBot
    end.
  Local Instance csum_op_instance : Op (csum A B) := λ x y,
    match x, y with
    | Cinl a, Cinl a' => Cinl (a ⋅ a')
    | Cinr b, Cinr b' => Cinr (b ⋅ b')
    | _, _ => CsumBot
    end.

  Lemma csum_op (x y : csum A B) :
    x ⋅ y =
    match x, y with
    | Cinl a, Cinl a' => Cinl (a ⋅ a')
    | Cinr b, Cinr b' => Cinr (b ⋅ b')
    | _, _ => CsumBot
    end.
  Proof. done. Qed.
  Lemma csum_valid (x : csum A B) :
    ✓ x =
    match x with
    | Cinl a => ✓ a
    | Cinr b => ✓ b
    | CsumBot => False
    end.
  Proof. done. Qed.
  Lemma csum_pcore (x : csum A B) :
    pcore x =
    match x with
    | Cinl a => Cinl <$> pcore a
    | Cinr b => Cinr <$> pcore b
    | CsumBot => Some CsumBot
    end.
  Proof. done. Qed.

  Lemma Cinl_op a a' : Cinl (a ⋅ a') = Cinl a ⋅ Cinl a'.
  Proof. done. Qed.
  Lemma Cinr_op b b' : Cinr (b ⋅ b') = Cinr b ⋅ Cinr b'.
  Proof. done. Qed.

  Lemma Cinl_valid a : ✓ (Cinl a) ↔ ✓ a.
  Proof. done. Qed.
  Lemma Cinr_valid b : ✓ (Cinr b) ↔ ✓ b.
  Proof. done. Qed.

  Lemma csum_included x y :
    x ≼ y ↔ y = CsumBot ∨ (∃ a a', x = Cinl a ∧ y = Cinl a' ∧ a ≼ a')
                        ∨ (∃ b b', x = Cinr b ∧ y = Cinr b' ∧ b ≼ b').
  Proof.
    split.
    - unfold lra_included. intros [[a'|b'|] Hy]; destruct x as [a|b|];
        inversion_clear Hy; eauto 10.
    - intros [->|[(a&a'&->&->&c&->)|(b&b'&->&->&c&->)]].
      + destruct x; exists CsumBot; constructor.
      + exists (Cinl c); done.
      + exists (Cinr c). done.
  Qed.
  Lemma Cinl_included a a' : Cinl a ≼ Cinl a' ↔ a ≼ a'.
  Proof. rewrite csum_included. naive_solver. Qed.
  Lemma Cinr_included b b' : Cinr b ≼ Cinr b' ↔ b ≼ b'.
  Proof. rewrite csum_included. naive_solver. Qed.

  Lemma csum_lra_mixin : LRAMixin (csum A B).
  Proof.
    split.
    - intros [a1|b1|] [a2|b2|] [a3|b3|]; rewrite -?Cinl_op -?Cinr_op; by rewrite ?assoc.
    - intros [a1|b1|] [a2|b2|]; rewrite csum_op; try done; by rewrite lra_comm.
    - intros [a|b|] ? [= Ha]; subst; auto; rewrite csum_pcore in Ha.
      + destruct (pcore a) as [ca|] eqn:?; simplify_option_eq; rewrite csum_op.
        f_equiv. eauto using lra_pcore_l.
      + destruct (pcore b) as [cb|] eqn:?; simplify_option_eq; rewrite csum_op.
        f_equiv. eauto using lra_pcore_l.
    - intros [a|b|] ? [= Ha]; subst; auto; rewrite csum_pcore in Ha.
      + destruct (pcore a) as [ca|] eqn:?; simplify_option_eq.
        oinversion (lra_pcore_idemp a ca); auto; rewrite csum_pcore; by simplify_option_eq.
      + destruct (pcore b) as [cb|] eqn:?; simplify_option_eq.
        oinversion (lra_pcore_idemp b cb); auto; rewrite csum_pcore; by simplify_option_eq.
    - intros x y ? [->|[(a&a'&->&->&?)|(b&b'&->&->&?)]]%csum_included [= Ha].
      + exists CsumBot. rewrite csum_included; eauto.
      + destruct (pcore a) as [ca|] eqn:?; rewrite csum_pcore; rewrite csum_pcore in Ha; simplify_option_eq.
        destruct (lra_pcore_mono a a' ca) as (ca'&->&?); auto.
        exists (Cinl ca'). rewrite csum_included; eauto 10.
      + destruct (pcore b) as [cb|] eqn:?; rewrite csum_pcore; rewrite csum_pcore in Ha; simplify_option_eq.
        destruct (lra_pcore_mono b b' cb) as (cb'&->&?); auto.
        exists (Cinr cb'). rewrite csum_included; eauto 10.
    - intros [a1|b1|] [a2|b2|]; simpl; rewrite csum_valid csum_op; simpl; eauto using lra_valid_op_l; done.
  Qed.
  Canonical Structure csumR := Lra (csum A B) csum_lra_mixin.

  (** Interesting updates *)
  Lemma csum_upd_injl a1 a2 :
    lra_update a1 a2 → lra_update (Cinl a1) (Cinl a2).
  Proof.
    intros Hf [[ r| r| ] | ]; simpl; rewrite ?csum_op ?csum_valid; try done.
    - apply (Hf (Some r)).
    - apply (Hf None).
  Qed.
  Lemma csum_upd_injr b1 b2 :
    lra_update b1 b2 → lra_update (Cinr b1) (Cinr b2).
  Proof.
    intros Hf [[ r| r| ] | ]; simpl; rewrite ?csum_op ?csum_valid; try done.
    - apply (Hf (Some r)).
    - apply (Hf None).
  Qed.
  Lemma csum_upd_ltr a1 b2 :
    lra_exclusive a1 → ✓ b2 → lra_update (Cinl a1) (Cinr b2).
  Proof.
    intros Hexcl Hv [[ | | ] | ]; simpl; rewrite ?csum_op ?csum_valid; try done.
    intros []%Hexcl.
  Qed.
  Lemma csum_upd_rtl b1 a2 :
    lra_exclusive b1 → ✓ a2 → lra_update (Cinr b1) (Cinl a2).
  Proof.
    intros Hexcl Hv [[ | | ] | ]; simpl; rewrite ?csum_op ?csum_valid; try done.
    intros []%Hexcl.
  Qed.
End sum.

(** ** Exercise: products *)
Section prod.
  Context {A B : lra}.
  (* TODO: this is an exercise for you *)

  Local Instance prod_op_instance : Op (A * B) := λ x y, x (* TODO *).
  Local Instance prod_pcore_instance : PCore (A * B) := λ x,
    None (* TODO *).
  Local Instance prod_valid_instance : Valid (A * B) := λ x, False (* TODO *).

  Lemma prod_included (x y : A * B) : x ≼ y ↔ False (* TODO *).
  Proof.
    (* TODO: exercise *)
  Admitted.


  (** You may want to state some additional lemmas about the operation of the operations on pairs (a, b) *)

  


  Definition prod_lra_mixin : LRAMixin (A * B).
  Proof.
    (* TODO: exercise *)
  Admitted.

  Canonical Structure prodR := Lra (prod A B) prod_lra_mixin.

  Lemma pair_exclusive a b :
    lra_exclusive a ∨ lra_exclusive b → lra_exclusive (a, b).
  Proof.
    (* TODO: exercise *)
  Admitted.

End prod.

(* TODO: if products have a unit, uncomment the following code and fix it*)
(*
Section prod_unit.
  Context {A B : ulra}.
  Instance prod_unit_instance : Unit (A * B) := (??) (* TODO *).

  Lemma prod_ulra_mixin : ULRAMixin (A * B).
  Proof.
    (* TODO *)
  Admitted.
  Canonical Structure prodUR := Ulra (prod A B) prod_lra_mixin prod_ulra_mixin.
End prod_unit.
 *)


(** ** The Excl(A) RA *)
Inductive excl (A : Type) :=
  | Excl : A → excl A
  | ExclBot : excl A.
Global Arguments Excl {_} _.
Global Arguments ExclBot {_}.
Section excl.
  Context {A : Type}.
  Implicit Types a b : A.
  Implicit Types x y : excl A.

  Global Instance Excl_inj : Inj (=) (=) (@Excl A).
  Proof. by inversion_clear 1. Qed.

  Instance excl_valid_instance : Valid (excl A) := λ x,
    match x with Excl _ => True | ExclBot => False end.
  (* no core *)
  Instance excl_pcore_instance : PCore (excl A) := λ _, None.
  (* no composition *)
  Instance excl_op_instance : Op (excl A) := λ x y, ExclBot.

  Lemma excl_op (a b : excl A) : a ⋅ b = ExclBot.
  Proof. done. Qed.
  Lemma excl_pcore (a : excl A) : pcore a = None.
  Proof. done. Qed.
  Lemma excl_valid_Excl a : ✓ (Excl a).
  Proof. done. Qed.
  Lemma excl_not_valid_ExclBot : ¬ ✓ ExclBot.
  Proof. intros []. Qed.

  Lemma excl_lra_mixin : LRAMixin (excl A).
  Proof.
    split; try discriminate.
    - intros [][][]; reflexivity.
    - intros [][]; reflexivity.
    - intros [] []; done.
  Qed.
  Canonical Structure exclR : lra := Lra (excl A) excl_lra_mixin.

  Lemma excl_lra_exclusive (a : excl A) :
    lra_exclusive a.
  Proof.
    intros [ f | ]; rewrite excl_op; apply excl_not_valid_ExclBot.
  Qed.

  Lemma excl_lra_included (a b : excl A) :
    a ≼ b → b = ExclBot.
  Proof.
    intros [f Hf].
    by rewrite excl_op in Hf.
  Qed.
End excl.
Global Arguments exclR _ : clear implicits.

(** ** Agree RA *)
Record agree (A : Type) `{Countable A} : Type := mk_ag {
  agree_car : gset A;
  agree_not_empty : bool_decide (agree_car = ∅) = false
}.
Global Arguments agree_car {_ _ _} _.
Global Arguments agree_not_empty {_} _.
Global Arguments mk_ag {_ _ _} _ _.
Section agree.
  Context {A : Type} `{Countable A}.
  Local Coercion agree_car : agree >-> gset.

  Lemma elem_of_agree (x : agree A) : ∃ a, a ∈ agree_car x.
  Proof.
    apply (set_choose_L (agree_car x)).
    eapply bool_decide_eq_false. apply agree_not_empty.
  Qed.
  Lemma agree_eq (x y : agree A) : agree_car x = agree_car y → x = y.
  Proof.
    destruct x as [a ?], y as [b ?]; simpl.
    intros ->; f_equal. eapply proof_irrel.
  Qed.


  Program Instance agree_op_instance : Op (agree A) :=
    λ a b, mk_ag (agree_car a ∪ agree_car b) _.
  Next Obligation.
    intros a b. apply bool_decide_eq_false.
    intros [Ha _]%empty_union_L.
    exfalso; eapply bool_decide_eq_false; last apply Ha.
    apply agree_not_empty.
  Qed.
  Lemma agree_op a b :
    agree_car (a ⋅ b) = agree_car a ∪ agree_car b.
  Proof. done. Qed.

  Instance agree_valid_instance : Valid (agree A) :=
    λ a, ∃ x, agree_car a = {[ x ]}.
  Lemma agree_valid a :
    ✓ a ↔ ∃ x, agree_car a = {[ x ]}.
  Proof. done. Qed.
  Lemma agree_valid_all_eq a :
    ✓ a ↔ (∃ y, ∀ x, x ∈ agree_car a → x = y).
  Proof.
    rewrite agree_valid. split.
    - intros (x & ->). exists x. intros y.
      rewrite elem_of_singleton. done.
    - intros (y & Ha). exists y.
      apply leibniz_equiv. apply set_equiv.
      intros x. split.
      + intros ->%Ha. by apply elem_of_singleton.
      + rewrite elem_of_singleton. intros ->.
        destruct (elem_of_agree a) as (z & Hz).
        by rewrite -(Ha _ Hz).
  Qed.

  Instance agree_pcore_instance : PCore (agree A) := Some.
  Lemma agree_pcore (a : agree A) :
    pcore a = Some a.
  Proof. done. Qed.

  Lemma agree_incl (a b : agree A) :
    a ≼ b ↔ agree_car a ⊆ agree_car b.
  Proof.
    split.
    - intros (c & ->). rewrite agree_op. set_solver.
    - intros Hincl. exists b.
      rewrite /op /agree_op_instance.
      apply agree_eq; simpl. set_solver.
  Qed.

  Lemma agree_lra_mixin : LRAMixin (agree A).
  Proof.
    split.
    - intros [][][]; apply agree_eq; rewrite !agree_op; simpl. set_solver.
    - intros [][]; apply agree_eq; rewrite agree_op; simpl. set_solver.
    - intros x cx; rewrite agree_pcore; intros [= <-].
      apply agree_eq; rewrite agree_op. set_solver.
    - intros x cx. rewrite agree_pcore; intros [= <-]. apply agree_pcore.
    - intros x y cx. rewrite agree_incl agree_pcore. intros Hincl [= <-].
      exists y. rewrite agree_pcore agree_incl. done.
    - intros x y. rewrite !agree_valid_all_eq. intros (a & Ha).
      rewrite agree_op in Ha. exists a. intros z Hz. apply Ha. set_solver.
  Qed.
  Canonical Structure agreeR : lra := Lra (agree A) agree_lra_mixin.

  Lemma agree_op_idemp (a : agree A) :
    a ⋅ a = a.
  Proof.
    apply agree_eq. set_solver.
  Qed.
  Lemma agree_valid_eq (a b : agree A) :
    ✓ (a ⋅ b) ↔ a = b ∧ ✓ a.
  Proof.
    split.
    - intros Hv. split; last by eapply lra_valid_op_l.
      specialize (lra_valid_op_l _ _ Hv) as Hv1. setoid_rewrite agree_valid in Hv1.
      specialize (lra_valid_op_r _ _ Hv) as Hv2. setoid_rewrite agree_valid in Hv2.
      apply agree_valid_all_eq in Hv. destruct Hv as (y & Hv). rewrite agree_op in Hv.
      apply agree_eq. move : Hv. destruct Hv1 as (x1 & ->). destruct Hv2 as (x2 & ->).
      intros Hv. rewrite (Hv x1); last set_solver. rewrite (Hv x2); last set_solver. done.
    - intros [-> Hv]. by rewrite agree_op_idemp.
  Qed.

  (** Lemmas on [to_agree] *)
  Program Definition to_agree (a : A) : agree A :=
    {| agree_car := {[ a ]}; agree_not_empty := _ |}.
  Next Obligation.
    intros a. apply bool_decide_eq_false. apply non_empty_singleton_L.
  Qed.

  Global Instance to_agree_inj : Inj (=) (=) (to_agree).
  Proof.
    intros a b. intros Heq.
    enough (agree_car (to_agree a) = agree_car (to_agree b)) as Heq_proj.
    { simpl in Heq_proj. by apply singleton_inj in Heq_proj. }
    by rewrite Heq.
  Qed.
  Lemma to_agree_valid a : ✓ (to_agree a).
  Proof. by exists a. Qed.

  Lemma to_agree_valid_eq (a b : A) :
    ✓ (to_agree a ⋅ to_agree b) ↔ a = b.
  Proof.
    rewrite agree_valid_eq. split.
    - by intros [Ha%to_agree_inj _].
    - intros ->. split; first done. apply to_agree_valid.
  Qed.

  Lemma to_agree_incl (a b : A) :
    to_agree a ≼ to_agree b ↔ a = b.
  Proof.
    rewrite agree_incl. split; set_solver.
  Qed.

  Lemma to_agree_update a b :
    lra_update (to_agree a) (to_agree b) ↔ a = b.
  Proof.
    split.
    - intros Hf.
      specialize (Hf (Some (to_agree a))). move : Hf.
      simpl. rewrite agree_op_idemp to_agree_valid_eq.
      intros Hf. rewrite Hf; eauto using to_agree_valid.
    - intros ->. intros [f | ]; simpl; done.
  Qed.
End agree.
Global Arguments agreeR _ {_ _}.

(** ** The Auth(R) RA *)
Inductive auth (A : Type) := Auth (a : (option (excl A))) (f: A).
Global Arguments Auth {_}.
Section auth.
  Context {A : ulra}.

  Definition auth_auth (a : A) : auth A := Auth (Some (Excl a)) ε.
  Definition auth_frag (a : A) : auth A := Auth None a.

  (*Instance auth_equiv_instance : Equiv auth *)
  Instance auth_op_instance : Op (auth A) :=
    λ '(Auth x a) '(Auth y b), Auth (x ⋅ y) (a ⋅ b).
  Instance auth_valid_instance : Valid (auth A) :=
    λ '(Auth x b),
      match x with
      | None => ✓ b
      | Some (Excl a) => b ≼ a ∧ ✓ a
      | _ => False
      end.
  Instance auth_pcore_instance : PCore (auth A) :=
    λ '(Auth x b), pcore b ≫= (λ bc, Some (Auth None bc)).
  Instance auth_unit_instance : Unit (auth A) := Auth None ε.

  Lemma auth_pcore x b : pcore (Auth x b) = pcore b ≫= (λ bc, Some (Auth None bc)).
  Proof. done. Qed.
  Lemma auth_valid x b : ✓ (Auth x b) ↔
      match x with
      | None => ✓ b
      | Some (Excl a) => b ≼ a ∧ ✓ a
      | _ => False
      end.
  Proof. done. Qed.
  Lemma auth_op x a y b : (Auth x a) ⋅ (Auth y b) = Auth (x ⋅ y) (a ⋅ b).
  Proof. done. Qed.

  Lemma auth_frag_pcore a :
    pcore (auth_frag a) = auth_frag <$> (pcore a).
  Proof.
    rewrite auth_pcore. destruct (pcore a); done.
  Qed.
  Lemma auth_frag_op a b :
    auth_frag (a ⋅ b) = auth_frag a ⋅ auth_frag b.
  Proof. done. Qed.
  Lemma auth_frag_valid a :
    ✓ (auth_frag a) ↔ ✓ a.
  Proof. done. Qed.
  Lemma auth_frag_unit :
    auth_frag ε = ε.
  Proof. done. Qed.

  Lemma auth_frag_incl a b :
    auth_frag a ≼ auth_frag b ↔ a ≼ b.
  Proof.
    split; rewrite /auth_frag.
    - intros [[[ca | ] cf] Hc]; first done.
      rewrite -auth_frag_op in Hc. injection Hc as ->.
      apply lra_included_l.
    - intros [c ->]. exists (auth_frag c). done.
  Qed.

  Lemma auth_auth_valid a :
    ✓ auth_auth a ↔ ✓ a.
  Proof.
    split; rewrite /auth_auth.
    - rewrite /valid /auth_valid_instance. intros [_ Ha]. apply Ha.
    - intros Ha. rewrite auth_valid. split; last done.
      apply ulra_unit_included.
  Qed.

  Lemma auth_auth_excl a b:
    ✓ ((auth_auth a) ⋅ (auth_auth b)) → False.
  Proof. done. Qed.

  Lemma auth_auth_frag_valid a b :
    ✓ (auth_auth a ⋅ auth_frag b) ↔ b ≼ a ∧ ✓ a.
  Proof.
    rewrite auth_valid. simpl. rewrite left_id. done.
  Qed.

  Lemma auth_lra_mixin : LRAMixin (auth A).
  Proof.
    split.
    - intros [] [] []. rewrite !auth_op. f_equiv; by rewrite assoc.
    - intros [] []. rewrite !auth_op. f_equiv; by rewrite lra_comm.
    - intros [xa xf] [cxa cxf]. rewrite auth_pcore auth_op.
      destruct (pcore xf) eqn:Ha; simpl; last done.
      injection 1 as <- <-. rewrite left_id. by rewrite lra_pcore_l.
    - intros [xa xf] [cxa cxf]. rewrite auth_pcore.
      destruct (pcore xf) eqn:Heq; last done.
      simpl. injection 1 as <- <-. rewrite auth_pcore.
      by rewrite (lra_pcore_idemp _ _ Heq).
    - intros [xa xf] [ya yf] [cxa cxf]. rewrite auth_pcore.
      intros [[fa ff] Hf]. rewrite auth_op in Hf. injection Hf as -> ->.
      destruct (pcore xf) eqn:Heq; simpl; last done.
      injection 1 as <- <-. rewrite auth_pcore.
      eapply (lra_pcore_mono _ (xf ⋅ ff)) in Heq; last apply lra_included_l.
      destruct Heq as (cy & Hc & Hincl). rewrite Hc. simpl. eexists _.
      split; first done. by rewrite auth_frag_incl.
    - intros [[[xa|] |] xf] [[[ya |] |] yf]; rewrite auth_op !auth_valid; simpl; try done.
      + intros [H1 H2]; split; last done. etrans; last done. apply lra_included_l.
      + intros [Hincl Hv]. eapply lra_included_valid; last done. etrans; last done. apply lra_included_l.
      + apply lra_valid_op_l.
  Qed.
  Canonical Structure authR : lra := Lra (auth A) auth_lra_mixin.

  Lemma auth_ulra_mixin : ULRAMixin (auth A).
  Proof.
    split.
    - intros [xa xf]; by rewrite auth_op !left_id.
    - rewrite auth_valid. apply ulra_unit_valid.
    - rewrite auth_pcore. rewrite ulra_unit_pcore. done.
  Qed.
  Canonical Structure authUR : ulra := Ulra (auth A) auth_lra_mixin auth_ulra_mixin.

  Lemma auth_update a a' b b' :
    lra_local_update (a, b) (a', b') →
    lra_update (auth_auth a ⋅ auth_frag b) (auth_auth a' ⋅ auth_frag b').
  Proof.
    (* TODO: exercise *)
  Admitted.


  Lemma auth_update_auth_auth_frag a a' b' :
    lra_local_update (a, ε) (a', b') →
    lra_update (auth_auth a) (auth_auth a' ⋅ auth_frag b').
  Proof.
    (* TODO: exercise *)
  Admitted.


  Lemma auth_update_auth_auth a a' b' :
    lra_local_update (a, ε) (a', b') →
    lra_update (auth_auth a) (auth_auth a').
  Proof.
    (* TODO: exercise *)
  Admitted.


  Lemma auth_update_auth_frag_auth a b a' :
    lra_local_update (a, b) (a', ε) →
    lra_update (auth_auth a ⋅ auth_frag b) (auth_auth a').
  Proof.
    (* TODO: exercise *)
  Admitted.

End auth.
Global Arguments authR : clear implicits.

(** ** Some local updates we can prove *)
(** Local update for (nat, +) *)
Lemma local_upd_nat_plus (n n' m m' : nat) :
  n + m' = n' + m →
  lra_local_update (n, m) (n', m').
Proof.
  intros Heq [f | ] [_ Hn]; simpl in *.
  - rewrite nat_op in Hn. subst n.
    split; first done. rewrite nat_op. lia.
  - subst. split; first done. lia.
Qed.

(** Local update for (nat, max) *)
Lemma local_upd_nat_max n m k :
  n ≤ k →
  lra_local_update (MaxNat n, MaxNat m) (MaxNat k, MaxNat k).
Proof.
  intros ? [[f] | ] [_ Hn]; simpl in *.
  - split; first done.
    rewrite max_nat_op in Hn. rewrite max_nat_op.
    f_equiv. injection Hn. lia.
  - done.
Qed.

(** Local update for exclusive RA elements *)
Lemma exclusive_local_update {A : lra} (y x x' : A) :
  lra_exclusive y →
  ✓ x' →
  lra_local_update (x, y) (x', x').
Proof.
  intros Hexcl Hv [f | ]; simpl; last done.
  intros [Hx ->]. apply Hexcl in Hx as [].
Qed.

(** Local updates for unital RAs *)
Lemma local_update_unital {A : ulra} (x y x' y' : A) :
  lra_local_update (x,y) (x',y') ↔ ∀ z, ✓ x → x = y ⋅ z → ✓ x' ∧ x' = y' ⋅ z.
Proof.
  split.
  - intros Hup z. intros; by apply (Hup (Some z)).
  - intros Hup [z|]; simpl; intros []; [by auto|].
    subst. rewrite -(right_id ε op y'). apply Hup; first done.
    rewrite right_id. done.
Qed.

(** Local update for option *)
Lemma local_upd_Some {A : lra} (a b c d : A) :
  lra_local_update (a, b) (c, d) →
  lra_local_update (Some a, Some b) (Some c, Some d).
Proof.
  intros Hupd [[f | ] | ]; simpl.
  - rewrite -!Some_op !Some_valid.
    intros [Hf [= ->]].
    destruct  (Hupd (Some f) (conj Hf eq_refl)) as [Hc Heq].
    naive_solver.
  - rewrite !right_id Some_valid. intros [Ha [= <-]].
    destruct (Hupd None (conj Ha eq_refl)). naive_solver.
  - rewrite Some_valid. intros [Ha [= <-]].
    destruct (Hupd None (conj Ha eq_refl)); naive_solver.
Qed.

(** Local update for excl *)
Lemma local_upd_Excl {A : Type} (a b c : A) :
  lra_local_update (Excl a, Excl b) (Excl c, Excl c).
Proof.
  apply exclusive_local_update; last done.
  apply excl_lra_exclusive.
Qed.

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
     mono_nat_own_auth γ n -∗ mono_nat_own_auth γ n ∗ mono_nat_own_frag γ n.
   Proof.
     (* TODO: exercise *)
   Admitted.

 
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
     (* TODO: exercise *)
   Admitted.

 
   Lemma mono_new n :
     ⊢ |==> ∃ γ, mono_nat_own_auth γ n.
   Proof.
     (* TODO: exercise *)
   Admitted.

 End mono_nat.
