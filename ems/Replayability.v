Require Import Coqlib.
Require Import STS.
Require Import Behavior.
From Ordinal Require Import Ordinal Arithmetic.
Require Import SimSTSIndex.

Set Implicit Arguments.



Module REPLAY.
Section SIM.

  Variable L0 L1: semantics.

  Variant _sim (sim: Ord.t -> Ord.t -> L0.(state) -> L1.(state) -> Prop)
                 (sim_: Ord.t -> Ord.t -> L0.(state) -> L1.(state) -> Prop)
            (i_src0: Ord.t) (i_tgt0: Ord.t) (st_src0: L0.(state)) (st_tgt0: L1.(state)): Prop :=
  | sim_fin
      retv
      (SRT: _.(state_sort) st_src0 = final retv)
      (SRT: _.(state_sort) st_tgt0 = final retv)
    :
      _sim sim sim_ i_src0 i_tgt0 st_src0 st_tgt0

  | sim_vis
      (SRT: _.(state_sort) st_src0 = vis)
      (SRT: _.(state_sort) st_tgt0 = vis)
      (SIM: forall ev st_tgt1
          (STEP: _.(step) st_tgt0 (Some ev) st_tgt1)
        ,
          exists st_src1 i_src1 i_tgt1 (STEP: _.(step) st_src0 (Some ev) st_src1),
            <<SIM: sim i_src1 i_tgt1 st_src1 st_tgt1>>)
    :
      _sim sim sim_ i_src0 i_tgt0 st_src0 st_tgt0

  | sim_vis_stuck_tgt
      (SRT: _.(state_sort) st_tgt0 = vis)
      (STUCK: forall ev st_tgt1, not (_.(step) st_tgt0 (Some ev) st_tgt1))
    :
      _sim sim sim_ i_src0 i_tgt0 st_src0 st_tgt0

  | sim_demonic_src
      (SRT: _.(state_sort) st_src0 = demonic)
      (SIM: exists st_src1 i_src1
                   (STEP: _.(step) st_src0 None st_src1)
        ,
          <<SIM: sim_ i_src1 i_tgt0 st_src1 st_tgt0>>)
    :
      _sim sim sim_ i_src0 i_tgt0 st_src0 st_tgt0
  | sim_demonic_tgt
      (SRT: _.(state_sort) st_tgt0 = demonic)
      (SIM: forall st_tgt1
                   (STEP: _.(step) st_tgt0 None st_tgt1),
          exists i_tgt1,
          <<SIM: sim_ i_src0 i_tgt1 st_src0 st_tgt1>>)
    :
      _sim sim sim_ i_src0 i_tgt0 st_src0 st_tgt0

  | sim_progress
      i_src1 i_tgt1
      (SIM: sim i_src1 i_tgt1 st_src0 st_tgt0)
      (SRC: Ord.lt i_src1 i_src0)
      (TGT: Ord.lt i_tgt1 i_tgt0)
    :
      _sim sim sim_ i_src0 i_tgt0 st_src0 st_tgt0
  .

  Variant _simE (simE: Ord.t -> L0.(state) -> L1.(state) -> Prop)
                  (simE_: Ord.t -> L0.(state) -> L1.(state) -> Prop)
            (i0: Ord.t) (st_src0: L0.(state)) (st_tgt0: L1.(state)): Prop :=
  | simE_fin
      retv
      (SRT: _.(state_sort) st_src0 = final retv)
      (SRT: _.(state_sort) st_tgt0 = final retv)
    :
      _simE simE simE_ i0 st_src0 st_tgt0

  | simE_vis
      (SRT: _.(state_sort) st_src0 = vis)
      (SRT: _.(state_sort) st_tgt0 = vis)
      (SIM: forall ev st_tgt1
          (STEP: _.(step) st_tgt0 (Some ev) st_tgt1)
        ,
          exists st_src1 i1 (STEP: _.(step) st_src0 (Some ev) st_src1),
            <<SIM: simE i1 st_src1 st_tgt1>>)
    :
      _simE simE simE_ i0 st_src0 st_tgt0

  | simE_vis_stuck_tgt
      (SRT: _.(state_sort) st_tgt0 = vis)
      (STUCK: forall ev st_tgt1, not (_.(step) st_tgt0 (Some ev) st_tgt1))
    :
      _simE simE simE_ i0 st_src0 st_tgt0

  | simE_demonic_src
      (SRT: _.(state_sort) st_src0 = demonic)
      (SIM: exists st_src1 i1
                   (LT: Ord.lt i1 i0)
                   (STEP: _.(step) st_src0 None st_src1)
        ,
          <<SIM: simE i1 st_src1 st_tgt0>>)
    :
      _simE simE simE_ i0 st_src0 st_tgt0
  | simE_demonic_tgt
      (SRT: _.(state_sort) st_tgt0 = demonic)
      (SIM: forall st_tgt1
                   (STEP: _.(step) st_tgt0 None st_tgt1),
          exists i1 (LT: Ord.lt i1 i0),
          <<SIM: simE i1 st_src0 st_tgt1>>)
    :
      _simE simE simE_ i0 st_src0 st_tgt0

  | simE_both
      (SRT: _.(state_sort) st_src0 = demonic)
      (SRT: _.(state_sort) st_tgt0 = demonic)
      (SIM: forall st_tgt1
                   (STEP: _.(step) st_tgt0 None st_tgt1),
          exists i1 st_src1 (STEP: _.(step) st_src0 None st_src1),
          <<SIM: simE i1 st_src1 st_tgt1>>)
  .

  Definition _fromE: (Ord.t * state L0 * state L1) -> (Ord.t * Ord.t * state L0 * state L1) :=
    fun '(o, s0, s1) => (o, o, s0, s1).

  Definition fromE: (Ord.t -> state L0 -> state L1 -> Prop) -> (Ord.t -> Ord.t -> state L0 -> state L1 -> Prop) :=
    fun Y o0 o1 s0 s1 => exists yo ys0 ys1 (IN: Y yo ys0 ys1), (_fromE (yo, ys0, ys1)) = (o0, o1, s0, s1).

  Definition fromE_aux: (Ord.t -> state L0 -> state L1 -> Prop) -> (Ord.t -> Ord.t -> state L0 -> state L1 -> Prop) :=
    fun Y o0 o1 s0 s1 => o0 = o1 /\ Y o0 s0 s1.

  Lemma fromE_lemma: fromE_aux = fromE.
  Proof.
    extensionalities Y o0 o1 s0 s1. eapply prop_ext. split; i.
    - rr in H. des; subst. r. eauto.
    - rr in H. des; subst. ss. clarify.
  Qed.

  Fixpoint repeat X (n: nat) (f: X -> X): X -> X :=
    match n with
    | 0 => id
    | S n => f ∘ (repeat n f)
    end
  .

  Goal forall X0 X1 i0 i1 s0 s1, fromE (_simE X0 X1) i0 i1 s0 s1 -> exists n, ((repeat n (_sim (fromE X0))) (fromE X1)) i0 i1 s0 s1.
  Proof.
    i. rewrite <- fromE_lemma in *. red in H. des; subst. inv H0.
    - exists 1. econs 1; eauto.
    - exists 1. econs 2; eauto.
      i. exploit SIM; eauto. i; des. esplits; eauto. r. esplits; eauto.
    - exists 1. econs 3; eauto.
    - exists 2. des. econs 4; eauto. esplits; eauto.
      econsr; eauto. r. eauto.
    - exists 2. des. econs 5; eauto. i. exploit SIM; eauto. i; des. esplits; eauto.
      econsr; eauto. r. eauto.
    - exists 3. des. econs 5; eauto. i.
      exploit SIM; eauto. i; des.
      esplits; eauto. econs 4; eauto. esplits; eauto.
      econsr; eauto.
      { r. esplits; eauto. }
      { instantiate (1:=Ord.S i0). eapply Ord.S_is_S. }
      { instantiate (1:=Ord.S i0). eapply Ord.S_is_S. }
  Qed.

  Variant _simI (simI: L0.(state) -> L1.(state) -> Prop)
                (simI_: L0.(state) -> L1.(state) -> Prop)
                (st_src0: L0.(state)) (st_tgt0: L1.(state)): Prop :=
  | simI_fin
      retv
      (SRT: _.(state_sort) st_src0 = final retv)
      (SRT: _.(state_sort) st_tgt0 = final retv)
    :
      _simI simI simI_ st_src0 st_tgt0

  | simI_vis
      (SRT: _.(state_sort) st_src0 = vis)
      (SRT: _.(state_sort) st_tgt0 = vis)
      (SIM: forall ev st_tgt1
          (STEP: _.(step) st_tgt0 (Some ev) st_tgt1)
        ,
          exists st_src1 (STEP: _.(step) st_src0 (Some ev) st_src1),
            <<SIM: simI st_src1 st_tgt1>>)
    :
      _simI simI simI_ st_src0 st_tgt0

  | simI_vis_stuck_tgt
      (SRT: _.(state_sort) st_tgt0 = vis)
      (STUCK: forall ev st_tgt1, not (_.(step) st_tgt0 (Some ev) st_tgt1))
    :
      _simI simI simI_ st_src0 st_tgt0

  | simI_demonic_src
      (SRT: _.(state_sort) st_src0 = demonic)
      (SIM: exists st_src1
                   (STEP: _.(step) st_src0 None st_src1)
        ,
          <<SIM: simI_ st_src1 st_tgt0>>)
    :
      _simI simI simI_ st_src0 st_tgt0
  | simI_demonic_tgt
      (SRT: _.(state_sort) st_tgt0 = demonic)
      (SIM: forall st_tgt1
                   (STEP: _.(step) st_tgt0 None st_tgt1),
          <<SIM: simI_ st_src0 st_tgt1>>)
    :
      _simI simI simI_ st_src0 st_tgt0

  | simI_both
      (SRT: _.(state_sort) st_src0 = demonic)
      (SRT: _.(state_sort) st_tgt0 = demonic)
      (SIM: forall st_tgt1
                   (STEP: _.(step) st_tgt0 None st_tgt1),
          exists st_src1 (STEP: _.(step) st_src0 None st_src1),
          <<SIM: simI st_src1 st_tgt1>>)
  .

  Definition _fromI: (state L0 * state L1) -> (Ord.t * Ord.t * state L0 * state L1) :=
    fun '(s0, s1) => (Ord.O, Ord.O, s0, s1).

  Definition fromI: (state L0 -> state L1 -> Prop) -> (Ord.t -> Ord.t -> state L0 -> state L1 -> Prop) :=
    fun Y o0 o1 s0 s1 => exists ys0 ys1 (IN: Y ys0 ys1), (_fromI (ys0, ys1)) = (o0, o1, s0, s1).

  Definition fromI_aux: (state L0 -> state L1 -> Prop) -> (Ord.t -> Ord.t -> state L0 -> state L1 -> Prop) :=
    fun Y o0 o1 s0 s1 => o0 = 0 /\ o1 = 0 /\ Y s0 s1.

  Lemma fromI_lemma: fromI_aux = fromI.
  Proof.
    extensionalities Y o0 o1 s0 s1. eapply prop_ext. split; i.
    - rr in H. des; subst. r. eauto.
    - rr in H. des; subst. ss. clarify.
  Qed.

  Goal forall X0 X1 i0 i1 s0 s1, fromI (_simI X0 X1) i0 i1 s0 s1 -> exists n, ((repeat n (_sim (fromI X0))) (fromI X1)) i0 i1 s0 s1.
  Proof.
    i. rewrite <- fromI_lemma in *. red in H. des; subst. inv H1.
    - exists 1. econs 1; eauto.
    - exists 1. econs 2; eauto.
      i. exploit SIM; eauto. i; des. esplits; eauto. r. esplits; eauto.
    - exists 1. econs 3; eauto.
    - exists 1. des. econs 4; eauto. esplits; eauto. rr. eauto.
    - exists 1. des. econs 5; eauto. i. exploit SIM; eauto. i; des. esplits; eauto. rr. eauto.
    - exists 3. des. econs 5; eauto. i.
      exploit SIM; eauto. i; des.
      esplits; eauto. econs 4; eauto. esplits; eauto.
      econsr; eauto.
      { r. esplits; eauto. }
      { instantiate (1:=1). eapply OrdArith.lt_from_nat. lia. }
      { instantiate (1:=1). eapply OrdArith.lt_from_nat. lia. }
  Qed.

End SIM.
End REPLAY.

Reset REPLAY.

Module REPLAY.
Section SIM.

  Variable L0 L1: semantics.

  Inductive _sim (sim: Ord.t -> Ord.t -> L0.(state) -> L1.(state) -> Prop)
    (i_src0: Ord.t) (i_tgt0: Ord.t) (st_src0: L0.(state)) (st_tgt0: L1.(state)): Prop :=
  | sim_fin
      retv
      (SRT: _.(state_sort) st_src0 = final retv)
      (SRT: _.(state_sort) st_tgt0 = final retv)
    :
      _sim sim i_src0 i_tgt0 st_src0 st_tgt0

  | sim_vis
      (SRT: _.(state_sort) st_src0 = vis)
      (SRT: _.(state_sort) st_tgt0 = vis)
      (SIM: forall ev st_tgt1
          (STEP: _.(step) st_tgt0 (Some ev) st_tgt1)
        ,
          exists st_src1 i_src1 i_tgt1 (STEP: _.(step) st_src0 (Some ev) st_src1),
            <<SIM: sim i_src1 i_tgt1 st_src1 st_tgt1>>)
    :
      _sim sim i_src0 i_tgt0 st_src0 st_tgt0

  | sim_vis_stuck_tgt
      (SRT: _.(state_sort) st_tgt0 = vis)
      (STUCK: forall ev st_tgt1, not (_.(step) st_tgt0 (Some ev) st_tgt1))
    :
      _sim sim i_src0 i_tgt0 st_src0 st_tgt0

  | sim_demonic_src
      (SRT: _.(state_sort) st_src0 = demonic)
      (SIM: exists st_src1 i_src1
                   (STEP: _.(step) st_src0 None st_src1)
        ,
          <<SIM: _sim sim i_src1 i_tgt0 st_src1 st_tgt0>>)
    :
      _sim sim i_src0 i_tgt0 st_src0 st_tgt0
  | sim_demonic_tgt
      (SRT: _.(state_sort) st_tgt0 = demonic)
      (SIM: forall st_tgt1
                   (STEP: _.(step) st_tgt0 None st_tgt1),
          exists i_tgt1,
          <<SIM: _sim sim i_src0 i_tgt1 st_src0 st_tgt1>>)
    :
      _sim sim i_src0 i_tgt0 st_src0 st_tgt0

  | sim_progress
      i_src1 i_tgt1
      (SIM: sim i_src1 i_tgt1 st_src0 st_tgt0)
      (SRC: Ord.lt i_src1 i_src0)
      (TGT: Ord.lt i_tgt1 i_tgt0)
    :
      _sim sim i_src0 i_tgt0 st_src0 st_tgt0
  .

  Variant _simE (simE: Ord.t -> L0.(state) -> L1.(state) -> Prop)
    (i0: Ord.t) (st_src0: L0.(state)) (st_tgt0: L1.(state)): Prop :=
  | simE_fin
      retv
      (SRT: _.(state_sort) st_src0 = final retv)
      (SRT: _.(state_sort) st_tgt0 = final retv)
    :
      _simE simE i0 st_src0 st_tgt0

  | simE_vis
      (SRT: _.(state_sort) st_src0 = vis)
      (SRT: _.(state_sort) st_tgt0 = vis)
      (SIM: forall ev st_tgt1
          (STEP: _.(step) st_tgt0 (Some ev) st_tgt1)
        ,
          exists st_src1 i1 (STEP: _.(step) st_src0 (Some ev) st_src1),
            <<SIM: simE i1 st_src1 st_tgt1>>)
    :
      _simE simE i0 st_src0 st_tgt0

  | simE_vis_stuck_tgt
      (SRT: _.(state_sort) st_tgt0 = vis)
      (STUCK: forall ev st_tgt1, not (_.(step) st_tgt0 (Some ev) st_tgt1))
    :
      _simE simE i0 st_src0 st_tgt0

  | simE_demonic_src
      (SRT: _.(state_sort) st_src0 = demonic)
      (SIM: exists st_src1 i1
                   (LT: Ord.lt i1 i0)
                   (STEP: _.(step) st_src0 None st_src1)
        ,
          <<SIM: simE i1 st_src1 st_tgt0>>)
    :
      _simE simE i0 st_src0 st_tgt0
  | simE_demonic_tgt
      (SRT: _.(state_sort) st_tgt0 = demonic)
      (SIM: forall st_tgt1
                   (STEP: _.(step) st_tgt0 None st_tgt1),
          exists i1 (LT: Ord.lt i1 i0),
          <<SIM: simE i1 st_src0 st_tgt1>>)
    :
      _simE simE i0 st_src0 st_tgt0

  | simE_both
      (SRT: _.(state_sort) st_src0 = demonic)
      (SRT: _.(state_sort) st_tgt0 = demonic)
      (SIM: forall st_tgt1
                   (STEP: _.(step) st_tgt0 None st_tgt1),
          exists i1 st_src1 (STEP: _.(step) st_src0 None st_src1),
          <<SIM: simE i1 st_src1 st_tgt1>>)
  .

  Definition _fromE: (Ord.t * state L0 * state L1) -> (Ord.t * Ord.t * state L0 * state L1) :=
    fun '(o, s0, s1) => (o, o, s0, s1).

  Definition fromE: (Ord.t -> state L0 -> state L1 -> Prop) -> (Ord.t -> Ord.t -> state L0 -> state L1 -> Prop) :=
    fun Y o0 o1 s0 s1 => exists yo ys0 ys1 (IN: Y yo ys0 ys1), (_fromE (yo, ys0, ys1)) = (o0, o1, s0, s1).

  Definition fromE_aux: (Ord.t -> state L0 -> state L1 -> Prop) -> (Ord.t -> Ord.t -> state L0 -> state L1 -> Prop) :=
    fun Y o0 o1 s0 s1 => o0 = o1 /\ Y o0 s0 s1.

  Lemma fromE_lemma: fromE_aux = fromE.
  Proof.
    extensionalities Y o0 o1 s0 s1. eapply prop_ext. split; i.
    - rr in H. des; subst. r. eauto.
    - rr in H. des; subst. ss. clarify.
  Qed.

  Goal forall X0 i0 i1 s0 s1,
      fromE (_simE X0) i0 i1 s0 s1 -> (_sim (fromE X0)) i0 i1 s0 s1.
  Proof.
    i. rewrite <- fromE_lemma in *. red in H. des; subst. inv H0.
    - econs 1; eauto.
    - econs 2; eauto.
      i. exploit SIM; eauto. i; des. esplits; eauto. r. esplits; eauto.
    - econs 3; eauto.
    - des. econs 4; eauto. esplits; eauto.
      econsr; eauto. r. eauto.
    - des. econs 5; eauto. i. exploit SIM; eauto. i; des. esplits; eauto.
      econsr; eauto. r. eauto.
    - des. econs 5; eauto. i.
      exploit SIM; eauto. i; des.
      esplits; eauto. econs 4; eauto. esplits; eauto.
      econsr; eauto.
      { r. esplits; eauto. }
      { instantiate (1:=Ord.S i0). eapply Ord.S_is_S. }
      { instantiate (1:=Ord.S i0). eapply Ord.S_is_S. }
  Qed.

  Inductive _simI (simI: L0.(state) -> L1.(state) -> Prop)
    (st_src0: L0.(state)) (st_tgt0: L1.(state)): Prop :=
  | simI_fin
      retv
      (SRT: _.(state_sort) st_src0 = final retv)
      (SRT: _.(state_sort) st_tgt0 = final retv)
    :
      _simI simI st_src0 st_tgt0

  | simI_vis
      (SRT: _.(state_sort) st_src0 = vis)
      (SRT: _.(state_sort) st_tgt0 = vis)
      (SIM: forall ev st_tgt1
          (STEP: _.(step) st_tgt0 (Some ev) st_tgt1)
        ,
          exists st_src1 (STEP: _.(step) st_src0 (Some ev) st_src1),
            <<SIM: simI st_src1 st_tgt1>>)
    :
      _simI simI st_src0 st_tgt0

  | simI_vis_stuck_tgt
      (SRT: _.(state_sort) st_tgt0 = vis)
      (STUCK: forall ev st_tgt1, not (_.(step) st_tgt0 (Some ev) st_tgt1))
    :
      _simI simI st_src0 st_tgt0

  | simI_demonic_src
      (SRT: _.(state_sort) st_src0 = demonic)
      (SIM: exists st_src1
                   (STEP: _.(step) st_src0 None st_src1)
        ,
          <<SIM: _simI simI st_src1 st_tgt0>>)
    :
      _simI simI st_src0 st_tgt0
  | simI_demonic_tgt
      (SRT: _.(state_sort) st_tgt0 = demonic)
      (SIM: forall st_tgt1
                   (STEP: _.(step) st_tgt0 None st_tgt1),
          <<SIM: _simI simI st_src0 st_tgt1>>)
    :
      _simI simI st_src0 st_tgt0

  | simI_both
      (SRT: _.(state_sort) st_src0 = demonic)
      (SRT: _.(state_sort) st_tgt0 = demonic)
      (SIM: forall st_tgt1
                   (STEP: _.(step) st_tgt0 None st_tgt1),
          exists st_src1 (STEP: _.(step) st_src0 None st_src1),
          <<SIM: simI st_src1 st_tgt1>>)
  .

  Lemma _simI_ind2 simI (P: L0.(state) -> L1.(state) -> Prop)
        (FIN: forall
            st_src0 st_tgt0
            retv
            (SRT: _.(state_sort) st_src0 = final retv)
            (SRT: _.(state_sort) st_tgt0 = final retv),
            P st_src0 st_tgt0)
        (VIS: forall
            st_src0 st_tgt0
            (SRT: _.(state_sort) st_src0 = vis)
            (SRT: _.(state_sort) st_tgt0 = vis)
            (SIM: forall ev st_tgt1
                         (STEP: _.(step) st_tgt0 (Some ev) st_tgt1)
              ,
                exists st_src1 (STEP: _.(step) st_src0 (Some ev) st_src1),
                  <<SIM: simI st_src1 st_tgt1>>),
            P st_src0 st_tgt0)
        (VISSTUCK: forall
            st_src0 st_tgt0
            (SRT: _.(state_sort) st_tgt0 = vis)
            (STUCK: forall ev st_tgt1, not (_.(step) st_tgt0 (Some ev) st_tgt1)),
            P st_src0 st_tgt0)
        (DMSRC: forall
            st_src0 st_tgt0
            (SRT: _.(state_sort) st_src0 = demonic)
            (SIM: exists st_src1
                         (STEP: _.(step) st_src0 None st_src1)
              ,
                <<SIM: _simI simI st_src1 st_tgt0>> /\ <<IH: P st_src1 st_tgt0>>),
            P st_src0 st_tgt0)
        (DMTGT: forall
            st_src0 st_tgt0
            (SRT: _.(state_sort) st_tgt0 = demonic)
            (SIM: forall st_tgt1
                         (STEP: _.(step) st_tgt0 None st_tgt1)
              ,
                <<SIM: _simI simI st_src0 st_tgt1>> /\ <<IH: P st_src0 st_tgt1>>),
            P st_src0 st_tgt0)
        (BOTH: forall
            st_src0 st_tgt0
            (SRT: _.(state_sort) st_src0 = demonic)
            (SRT: _.(state_sort) st_tgt0 = demonic)
            (SIM: forall st_tgt1
                         (STEP: _.(step) st_tgt0 None st_tgt1),
              exists st_src1
                         (STEP: _.(step) st_src0 None st_src1),
                <<SIM: simI st_src1 st_tgt1>>),
            P st_src0 st_tgt0)
    :
      forall st_src0 st_tgt0 (SIM: _simI simI st_src0 st_tgt0),
        P st_src0 st_tgt0.
  Proof.
    fix IH 3. i. inv SIM.
    { eapply FIN; eauto. }
    { eapply VIS; eauto. }
    { eapply VISSTUCK; eauto. }
    { eapply DMSRC; eauto.
      des. esplits; eauto. }
    { eapply DMTGT; eauto. i.
      hexploit SIM0; eauto. }
    { eapply BOTH; eauto. }
  Qed.
  

  Definition _fromI: (state L0 * state L1) -> (Ord.t * Ord.t * state L0 * state L1) :=
    fun '(s0, s1) => (Ord.O, Ord.O, s0, s1).

  Definition fromI: (state L0 -> state L1 -> Prop) -> (Ord.t -> Ord.t -> state L0 -> state L1 -> Prop) :=
    fun Y o0 o1 s0 s1 => exists ys0 ys1 (IN: Y ys0 ys1), (_fromI (ys0, ys1)) = (o0, o1, s0, s1).

  Definition fromI_aux: (state L0 -> state L1 -> Prop) -> (Ord.t -> Ord.t -> state L0 -> state L1 -> Prop) :=
    fun Y o0 o1 s0 s1 => o0 = 0 /\ o1 = 0 /\ Y s0 s1.

  Lemma fromI_lemma: fromI_aux = fromI.
  Proof.
    extensionalities Y o0 o1 s0 s1. eapply prop_ext. split; i.
    - rr in H. des; subst. r. eauto.
    - rr in H. des; subst. ss. clarify.
  Qed.

  Goal forall X0 i0 i1 s0 s1,
      fromI (_simI X0) i0 i1 s0 s1 -> (_sim (fromI X0)) i0 i1 s0 s1.
  Proof.
    i. rewrite <- fromI_lemma in *. red in H. des; subst.
    induction H1 using _simI_ind2.
    - econs 1; eauto.
    - econs 2; eauto.
      i. exploit SIM; eauto. i; des. esplits; eauto. r. esplits; eauto.
    - econs 3; eauto.
    - des. econs 4; eauto.
    - des. econs 5; eauto. i. exploit SIM; eauto. i; des. esplits; eauto.
    - econs 5; eauto. i.
      exploit SIM; eauto. i; des. esplits; eauto.
      econs 4; eauto. esplits; eauto.
      econsr; eauto.
      { r. esplits; eauto. }
      { instantiate (1:=1). eapply OrdArith.lt_from_nat. lia. }
      { instantiate (1:=1). eapply OrdArith.lt_from_nat. lia. }
  Qed.

End SIM.
End REPLAY.
