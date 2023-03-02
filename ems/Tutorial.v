Require Import Coqlib.
Require Import ITreelib.
Require Import Any.
Require Import STS.
Require Import Behavior.
Require Import ModSem.
Require Import Skeleton.
Require Import Coq.Relations.Relation_Definitions.
Require Import Relation_Operators.
Require Import RelationPairs.
From Ordinal Require Import Ordinal Arithmetic.
From Ordinal Require Import ClassicalOrdinal.

Require Import SimGlobalIndex SimGlobalEquiv SimGlobalIndexFacts.

Set Implicit Arguments.

(**************************************************************************************************)
(**************************************************************************************************)
(**************************************************************************************************)
(**************************************** SETUP ***************************************************)
(**************************************************************************************************)
(**************************************************************************************************)
(**************************************************************************************************)
Lemma itree_eta : forall {E : Type -> Type} {R : Type} (t : itree E R), t = {| _observe := observe t |}.
Proof. i. f. eapply itree_eta. Qed.

Definition dtree E R := (itree (E +' eventE) R).

Definition simg {E R} := @simg E R R (fun _ _ => eq) 0%ord 0%ord.

Notation "(⪸)" := (simg) (at level 60).
Notation "s ⪸ t" := (simg s t) (at level 60).

Global Program Instance simg_PreOrder {E R}: @PreOrder (dtree E R) ((⪸)).
Next Obligation.
  ii. r. eapply simg_postcond_mono; cycle 1. { eapply simg_refl. } ii; ss. tauto.
Qed.
Next Obligation.
  ii. eapply simg_trans; eauto.
Qed.

Global Program Instance eutt_simg {E R}: Proper ((eutt eq) ==> (@eutt (E +' eventE) R R eq) ==> impl) ((⪸)).
Next Obligation.
  ii. etrans; et. { sym in H. eapply SimGlobalIndexFacts.eutt_simg; et. }
  etrans; et. eapply SimGlobalIndexFacts.eutt_simg. ss.
Qed.

Global Program Instance simg_bind {E T U}: Proper ((⪸) ==> (eq ==> (⪸)) ==> (⪸)) (@ITree.bind (E +' eventE) T U).
Next Obligation.
  ii. ginit. guclo bindC_spec. econs; eauto.
  { gfinal. eauto. }
  ii. ss. subst.
  guclo flagC_spec. econs; eauto.
  3: { gfinal. right. specialize (H0 vret_tgt _ eq_refl). eauto. }
  { eapply Ord.O_is_O. }
  { eapply Ord.O_is_O. }
Qed.

Global Program Instance simg_iter {E R I}: Proper ((eq ==> (⪸)) ==> eq ==> (⪸)) (@ITree.iter (E +' eventE) R I).
Next Obligation.
  ii. eapply simg_iter; eauto.
Qed.

Lemma simg_dem_src E R X k_src (i_tgt: dtree E R): (exists x, k_src x ⪸ i_tgt) -> trigger (Choose X) >>= k_src ⪸ i_tgt.
Proof.
  i. ginit. guclo simg_indC_spec. econs; eauto. des. esplits; eauto with paco.
Qed.
Lemma simg_dem_tgt E R X k_tgt (i_src: dtree E R): (forall x, i_src ⪸ k_tgt x) -> i_src ⪸ trigger (Choose X) >>= k_tgt.
Proof.
  i. ginit. guclo simg_indC_spec. econs; eauto. des. i. spc H. esplits; eauto with paco.
Qed.
Lemma simg_ang_src E R X k_src (i_tgt: dtree E R): (forall x, k_src x ⪸ i_tgt) -> trigger (Take X) >>= k_src ⪸ i_tgt.
Proof.
  i. ginit. guclo simg_indC_spec. econs; eauto. des. i. spc H. esplits; eauto with paco.
Qed.
Lemma simg_ang_tgt E R X k_tgt (i_src: dtree E R): (exists x, i_src ⪸ k_tgt x) -> i_src ⪸ trigger (Take X) >>= k_tgt.
Proof.
  i. ginit. guclo simg_indC_spec. econs; eauto. des. esplits; eauto with paco.
Qed.

Global Program Instance simg_dualize {E R}: Proper ((⪸) ==> (flip simg)) (@dualize E R).
Next Obligation.
  ii. eapply simg_dualize; ss. eapply simg_postcond_mono; et. ss.
Qed.

Global Program Instance dualize_simg {E R}: Proper ((fun x y => dualize y ⪸ dualize x) ==> simg) (@id (dtree E R)).
Next Obligation.
  ii. unfold id. eapply dualize_simg. eapply simg_postcond_mono; et. ss.
Qed.

Lemma dualize_ang E X: dualize (trigger (Take X): itree (E +' eventE) X) ≈ (trigger (Choose X)).
Proof.
  unfold dualize. rewrite interp_trigger. cbn. rewrite ! bind_trigger. f_equiv. ii. rewrite tau_eutt; refl.
Qed.

Lemma dualize_dem E X: dualize (trigger (Choose X): itree (E +' eventE) X) ≈ (trigger (Take X)).
Proof.
  unfold dualize. rewrite interp_trigger. cbn. rewrite ! bind_trigger. f_equiv. ii. rewrite tau_eutt; refl.
Qed.



(***********************************************************************************************************************)
(***********************************************************************************************************************)
(***********************************************************************************************************************)
(* Copy-paste (and very little adjustment) of "InteractionTrees/examples/IntroductionSolutions.v" in ITrees repository *)
(***********************************************************************************************************************)
(***********************************************************************************************************************)
(***********************************************************************************************************************)

Ltac force_left :=
  match goal with
  | |- _ ?x _ => rewrite (itree_eta x); cbn
  end.
Ltac force_right :=
  match goal with
  | |- _ _ ?x => rewrite (itree_eta x); cbn
  end.
(* Ltac tau_steps_left := repeat (force_left; rewrite tau_eutt); force_left *)
Ltac tau_steps_left := repeat (force_left; rewrite tau_eutt); force_left.
Ltac tau_steps_right := repeat (force_right; rewrite tau_eutt); force_right.
Ltac tau_steps := tau_steps_left; tau_steps_right.

Section INTRODUCTION.
Variable F: Type -> Type.
Let E := F +' eventE.

Fixpoint factorial_spec (n : nat) : nat :=
  match n with
  | 0 => 1
  | S m => n * factorial_spec m
  end.

(** The generic [rec] interface of the library's [Interp] module can
    be used to define a single recursive function.  The more general
    [mrec] (from which [rec] is defined) allows multiple, mutually
    recursive definitions.

    The argument of [rec] is an interaction tree with an event type
    [callE A B] to represent "recursive calls", with input [A]
    and output [B]. The function [call : A -> itree _ B] can be used
    to make such calls.

    In this case, since [factorial : nat -> nat], we use
    [callE nat nat].
 *)
Definition fact_body (x : nat) : itree (Recursion.callE nat nat +' E) nat :=
  match x with
  | 0 => Ret 1
  | S m =>
    y <- call m ;;  (* Recursively compute [y := m!] *)
    Ret (x * y)
  end.

(** The factorial function itself is defined as an ITree by "tying
    the knot" using [rec].
 *)
Definition factorial (n : nat) : itree E nat :=
  rec fact_body n.

Lemma unfold_factorial : forall x,
    (factorial x) ⪸ (match x with
                  | 0 => Ret 1
                  | S m =>
                    y <- factorial m ;;
                    Ret (x * y)
                  end).
Proof.
  intros x.
  unfold factorial.
  (* ADMITTED *)
  rewrite rec_as_interp; unfold fact_body at 2.
  destruct x.
  - rewrite interp_ret.
    reflexivity.
  - rewrite interp_bind.
    rewrite interp_recursive_call.
    setoid_rewrite InterpFacts.interp_ret.
    reflexivity.
Qed.

(** We can prove that the ITrees version [factorial] is "equivalent"
    to the [factorial_spec] version.  The proof goes by induction on
    [n] and uses only rewriting -- no coinduction necessary.

    Here, we detail each step of rewriting to illustrate the use of
    the equational theory, which is mostly applications of the monad
    laws and the properties of [rec].

    In this proof, we do all of the rewriting steps explicitly.
 *)
Lemma factorial_correct : forall n,
    (factorial n) ⪸ (Ret (factorial_spec n)).
Proof.
  intros n.
  induction n as [ | n' IH ].
  - (* n = 0 *)
    rewrite unfold_factorial.
    reflexivity.
  - (* n = S n' *)
    rewrite unfold_factorial.
    rewrite IH. (* Induction hypothesis *)
    irw.
    reflexivity.
Qed.





Fixpoint fib_spec (n : nat) : nat :=
  match n with
  | 0 => 0
  | S n' =>
    match n' with
    | 0 => 1
    | S n'' => fib_spec n'' + fib_spec n'
    end
  end.

Definition fib_body : nat -> itree (Recursion.callE nat nat +' E) nat
  (* ADMITDEF *)
  := fun n =>
    match n with
    | 0 => Ret 0
    | S n' =>
      match n' with
      | 0 => Ret 1
      | S n'' =>
        y1 <- call n'' ;;
        y2 <- call n' ;;
        Ret (y1 + y2)
      end
    end.
  (* /ADMITDEF *)

Definition fib n : itree E nat :=
  rec fib_body n.

From ExtLib Require Import
     Monad
     Traversable
     Data.List.

Example fib_3_6 : mapT fib [4;5;6] ⪸ Ret [3; 5; 8].
Proof.
  (* Use [tau_steps] to compute. *)
  (* ADMITTED *)
  tau_steps. reflexivity.
Qed. (* /ADMITTED *)

(** Since fib uses two recursive calls, we need to strengthen the
    induction hypothesis.  One way to do that is to prove the
    property for all [m <= n].

    You may find the following two lemmas useful at the start
    of each case.
[[
Nat.le_0_r : forall n : nat, n <= 0 <-> n = 0
Nat.le_succ_r : forall n m : nat, n <= S m <-> n <= m \/ n = S m
]]
 *)

Lemma fib_correct_aux : forall n m, m <= n ->
    fib m ⪸ Ret (fib_spec m).
Proof.
  intros n.
  unfold fib.
  induction n as [ | n' IH ]; intros.
  - (* n = 0 *)
    apply Nat.le_0_r in H. subst m.
    (* ADMIT *)
    rewrite rec_as_interp. simpl.
    rewrite interp_ret.
    (* alternatively, [tau_steps], or [autorewrite with itree] *)
    reflexivity.
    (* /ADMIT *)
  - (* n = S n' *)
    apply Nat.le_succ_r in H.
    (* ADMIT *)
    destruct H.
    + apply IH. auto.
    + rewrite rec_as_interp.
      subst m. simpl.
      destruct n' as [ | n'' ].
      * rewrite interp_ret. reflexivity.
      * rewrite interp_bind. rewrite interp_recursive_call.
        rewrite IH. 2: lia.
        rewrite bind_ret_l. rewrite interp_bind. rewrite interp_recursive_call.
        rewrite IH. 2: lia.
        rewrite bind_ret_l. rewrite interp_ret.
        reflexivity.
    (* /ADMIT *)
(* ADMITTED *) Qed. (* /ADMITTED. *)

(** The final correctness result follows. *)
Lemma fib_correct : forall n,
    fib n ⪸ Ret (fib_spec n).
Proof. (* ADMITTED *)
  intros n.
  eapply fib_correct_aux.
  reflexivity.
Qed. (* /ADMITTED *)

(** ** Logarithm *)

(** An example of a function which is not structurally recursive.
    [log_ b n]: logarithm of [n] in base [b].

    Specification:
      [log_ b (b ^ y) ≈ Ret y] when [1 < b].

    (Note that this only constrains a very small subset of inputs,
    and in fact our solution diverges for some of them.)
 *)
Definition log (b : nat) : nat -> itree E nat
  (* ADMITDEF *)
  := rec-fix log_b n :=
       if (n <=? 1)%nat then
         Ret O
       else
         y <- log_b (n / b) ;; Ret (S y).
  (* /ADMITDEF *)

Example log_2_64 : log 2 (2 ^ 6) ≈ Ret 6.
Proof.
  (* ADMITTED *)
  tau_steps. reflexivity.
Qed. (* /ADMITTED *)

(** These lemmas take care of the boring arithmetic. *)
Lemma log_correct_helper :
  forall b y, 1 < b ->
              (b * b ^ y <=? 1)%nat = false.
Proof.
  intros.
  apply Nat.leb_gt.
  apply Nat.lt_1_mul_pos; auto.
  apply Nat.neq_0_lt_0. intro.
  apply (Nat.pow_nonzero b y); lia.
Qed.

Lemma log_correct_helper2 :
  forall b y, 1 < b ->
              (b * b ^ y / b) = (b ^ y).
Proof.
  intros; rewrite Nat.mul_comm, Nat.div_mul; lia.
Qed.

Lemma log_correct : forall b y, 1 < b -> log b (b ^ y) ⪸ Ret y.
Proof.
  intros b y H.
  (* ADMITTED *)
  unfold log, rec_fix.
  induction y.
  - rewrite rec_as_interp; cbn.
    rewrite interp_ret.
    reflexivity.
  - rewrite rec_as_interp; cbn.
    (* (b * b ^ y <=? 1) = false *)
    rewrite log_correct_helper by auto.
    rewrite interp_bind.
    (* (b * b ^ y / b) = (b ^ y)*)
    rewrite log_correct_helper2 by auto.
    rewrite interp_recursive_call.
    rewrite IHy.
    rewrite bind_ret_l. rewrite interp_ret.
    reflexivity.
Qed. (* /ADMITTED *)
End INTRODUCTION.



Section MORE.
Variable E: Type -> Type.

Example demonic_spin: dtree E unit := ITree.iter (fun _ => trigger (Choose unit);;; Ret (inl tt)) tt.
Example angelic_spin: dtree E unit := ITree.iter (fun _ => trigger (Take unit);;; Ret (inl tt)) tt.
Example tau_spin: dtree E unit := ITree.iter (fun _ => tau;; Ret (inl tt)) tt.

Theorem tau_spin_angelic_spin: tau_spin ⪸ angelic_spin.
Proof.
  unfold tau_spin, angelic_spin.
  eapply simg_iter; ss. ii. subst.
  irw. rewrite ! tau_eutt. rewrite <- ! bind_trigger.
  rewrite <- simg_ang_tgt; try refl. esplits; ss. refl.
Qed.

Theorem tau_spin_angelic_spin_rev: angelic_spin ⪸ tau_spin.
Proof.
  unfold tau_spin, angelic_spin.
  eapply simg_iter; ss. ii. subst.
  irw. rewrite tau_eutt. rewrite <- ! bind_trigger.
  rewrite simg_ang_src; try refl.
Qed.

Lemma tau_spin_dual: dualize tau_spin ≈ tau_spin.
Proof.
  unfold tau_spin. rewrite dualize_iter. eapply eutt_iter; ss. ii.
  unfold dualize. rewrite interp_tau. rewrite ! tau_eutt. rewrite interp_ret. refl.
Qed.

Lemma demonic_angelic_dual: dualize angelic_spin ≈ demonic_spin.
Proof.
  unfold angelic_spin, dualize. erewrite interp_iter'; ss.
  unfold demonic_spin. eapply eutt_iter. ii. rewrite interp_bind. rewrite interp_trigger. grind.
  f_equiv; try refl. ii. grind. rewrite tau_eutt. refl.
Qed.

(*** proof by duality ***)
Corollary tau_spin_demonic_spin: tau_spin ⪸ demonic_spin.
Proof.
  rewrite <- dualize_involution with (d:=tau_spin).
  rewrite <- demonic_angelic_dual.
  eapply simg_dualize.
  rewrite tau_spin_dual.
  eapply tau_spin_angelic_spin_rev.
Qed.

Corollary tau_spin_demonic_spin_rev: demonic_spin ⪸ tau_spin.
Proof.
  rewrite <- dualize_involution with (d:=tau_spin).
  rewrite <- demonic_angelic_dual.
  eapply simg_dualize.
  rewrite tau_spin_dual.
  eapply tau_spin_angelic_spin.
Qed.

(*** examples from CTrees ***)
Remark demonic_comm X Y R (k: X -> Y -> dtree E R):
  (x <- trigger (Choose X);; y <- trigger (Choose Y);; k x y) ⪸ (y <- trigger (Choose Y);; x <- trigger (Choose X);; k x y).
Proof.
  eapply simg_dem_tgt. i.
  eapply simg_dem_tgt. i.
  eapply simg_dem_src. eexists.
  eapply simg_dem_src. eexists.
  refl.
Qed.

Remark demonic_merge X Y R (k: X -> Y -> dtree E R):
  ('(x, y) <- trigger (Choose (X * Y));; k x y) ⪸ (x <- trigger (Choose X);; y <- trigger (Choose Y);; k x y).
Proof.
  eapply simg_dem_tgt. i.
  eapply simg_dem_tgt. i.
  eapply simg_dem_src. eexists (_, _).
  refl.
Qed.

Remark demonic_merge_rev X Y R (k: X -> Y -> dtree E R):
  (x <- trigger (Choose X);; y <- trigger (Choose Y);; k x y) ⪸ ('(x, y) <- trigger (Choose (X * Y));; k x y).
Proof.
  eapply simg_dem_tgt. i. destruct x.
  eapply simg_dem_src. eexists.
  eapply simg_dem_src. eexists.
  refl.
Qed.

(*** proof by duality ***)
Opaque ITree.bind.
Corollary angelic_comm X Y R (k: X -> Y -> dtree E R):
  (x <- trigger (Take X);; y <- trigger (Take Y);; k x y) ⪸ (y <- trigger (Take Y);; x <- trigger (Take X);; k x y).
Proof.
  eapply dualize_simg. rewrite ! dualize_bind. rewrite ! dualize_ang. setoid_rewrite dualize_bind. setoid_rewrite dualize_ang.
  eapply demonic_comm.
Qed.

Corollary angelic_merge X Y R (k: X -> Y -> dtree E R):
  (x <- trigger (Take X);; y <- trigger (Take Y);; k x y) ⪸ ('(x, y) <- trigger (Take (X * Y));; k x y).
Proof.
  eapply dualize_simg. rewrite ! dualize_bind. rewrite ! dualize_ang. setoid_rewrite dualize_bind. setoid_rewrite dualize_ang.
  rewrite <- demonic_merge. f_equiv. ii. subst. destruct y. refl.
Qed.

Corollary angelic_merge_rev X Y R (k: X -> Y -> dtree E R):
  ('(x, y) <- trigger (Take (X * Y));; k x y) ⪸ (x <- trigger (Take X);; y <- trigger (Take Y);; k x y).
Proof.
  eapply dualize_simg. rewrite ! dualize_bind. rewrite ! dualize_ang. setoid_rewrite dualize_bind. setoid_rewrite dualize_ang.
  rewrite demonic_merge_rev. f_equiv. ii. subst. destruct y. refl.
Qed.

End MORE.
