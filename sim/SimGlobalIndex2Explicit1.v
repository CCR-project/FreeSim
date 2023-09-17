Require Import Coqlib.
Require Import ITreelib.
Require Import Any.
Require Import STS.
Require Import Behavior.
Require Import ModSemE.
Require Import Skeleton.
Require Import Coq.Relations.Relation_Definitions.
Require Import Relation_Operators.
Require Import RelationPairs.
From Ordinal Require Import Ordinal Arithmetic.
From Ordinal Require Import ClassicalOrdinal.

Require Import WFLib.
Require Import SimGlobalIndex.

Set Implicit Arguments.

Section SIM.

  Variable E: Type -> Type.

  Inductive _simg_aux
            (simg_aux: forall R0 R1 (RR: Ord.t -> Ord.t -> R0 -> R1 -> Prop), Ord.t -> Ord.t -> (itree (E +' eventE) R0) -> (itree (E +' eventE) R1) -> Prop)
            {R0 R1} (RR: Ord.t -> Ord.t -> R0 -> R1 -> Prop) (f_src f_tgt: Ord.t): (itree (E +' eventE) R0) -> (itree (E +' eventE) R1) -> Prop :=
  | simg_aux_ret
      f_src' f_tgt'
      (LE: (f_src' <= f_src)%ord)
      (LE: (f_tgt' <= f_tgt)%ord)
      r_src r_tgt
      (SIM: RR f_src' f_tgt' r_src r_tgt)
    :
    _simg_aux simg_aux RR f_src f_tgt (Ret r_src) (Ret r_tgt)
  | simg_aux_syscall
      ktr_src0 ktr_tgt0 fn varg rvs
      f_src0 f_tgt0
      (SIM: forall x_src x_tgt (EQ: x_src = x_tgt), @_simg_aux simg_aux _ _ RR f_src0 f_tgt0 (ktr_src0 x_src) (ktr_tgt0 x_tgt))
    :
    _simg_aux simg_aux RR f_src f_tgt (trigger (SyscallOut fn varg rvs) >>= ktr_src0) (trigger (SyscallOut fn varg rvs) >>= ktr_tgt0)

  | simg_aux_syscall_in
      ktr_src0 ktr_tgt0 rv
      f_src0 f_tgt0
      (SIM: @_simg_aux simg_aux _ _ RR f_src0 f_tgt0 (ktr_src0 tt) (ktr_tgt0 tt))
    :
    _simg_aux simg_aux RR f_src f_tgt (trigger (SyscallIn rv) >>= ktr_src0) (trigger (SyscallIn rv) >>= ktr_tgt0)

  | simg_aux_tauL
      itr_src0 itr_tgt0
      f_src0
      (SIM: @_simg_aux simg_aux _ _ RR f_src0 f_tgt itr_src0 itr_tgt0)
    :
    _simg_aux simg_aux RR f_src f_tgt (tau;; itr_src0) (itr_tgt0)
  | simg_aux_tauR
      itr_src0 itr_tgt0
      f_tgt0
      (SIM: @_simg_aux simg_aux _ _ RR f_src f_tgt0 itr_src0 itr_tgt0)
    :
    _simg_aux simg_aux RR f_src f_tgt (itr_src0) (tau;; itr_tgt0)

  | simg_aux_chooseL
      X ktr_src0 itr_tgt0
      f_src0
      (SIM: exists x, _simg_aux simg_aux RR f_src0 f_tgt (ktr_src0 x) itr_tgt0)
    :
    _simg_aux simg_aux RR f_src f_tgt (trigger (Choose X) >>= ktr_src0) (itr_tgt0)
  | simg_aux_chooseR
      X itr_src0 ktr_tgt0
      f_tgt0
      (SIM: forall x, _simg_aux simg_aux RR f_src f_tgt0 itr_src0 (ktr_tgt0 x))
    :
    _simg_aux simg_aux RR f_src f_tgt (itr_src0) (trigger (Choose X) >>= ktr_tgt0)

  | simg_aux_takeL
      X ktr_src0 itr_tgt0
      f_src0
      (SIM: forall x, _simg_aux simg_aux RR f_src0 f_tgt (ktr_src0 x) itr_tgt0)
    :
    _simg_aux simg_aux RR f_src f_tgt (trigger (Take X) >>= ktr_src0) (itr_tgt0)
  | simg_aux_takeR
      X itr_src0 ktr_tgt0
      f_tgt0
      (SIM: exists x, _simg_aux simg_aux RR f_src f_tgt0 itr_src0 (ktr_tgt0 x))
    :
    _simg_aux simg_aux RR f_src f_tgt (itr_src0) (trigger (Take X) >>= ktr_tgt0)

  | simg_aux_progress
      itr_src itr_tgt
      f_src0 f_tgt0
      (SIM: simg_aux _ _ RR f_src0 f_tgt0 itr_src itr_tgt)
      (SRC: (f_src0 < f_src)%ord)
      (TGT: (f_tgt0 < f_tgt)%ord)
    :
    _simg_aux simg_aux RR f_src f_tgt itr_src itr_tgt

  | simg_aux_event
      X (e: E X) ktr_src0 ktr_tgt0
      f_src0 f_tgt0
      (SIM: forall x_src x_tgt (EQ: x_src = x_tgt), @_simg_aux simg_aux _ _ RR f_src0 f_tgt0 (ktr_src0 x_src) (ktr_tgt0 x_tgt))
    :
    _simg_aux simg_aux RR f_src f_tgt (trigger e >>= ktr_src0) (trigger e >>= ktr_tgt0)
  .

  Lemma _simg_aux_ind2 (r: forall R0 R1 (RR: Ord.t -> Ord.t -> R0 -> R1 -> Prop), Ord.t -> Ord.t -> (itree (E +' eventE) R0) -> (itree (E +' eventE) R1) -> Prop)
        R0 R1 (RR: Ord.t -> Ord.t -> R0 -> R1 -> Prop)
        (P: Ord.t -> Ord.t -> (itree (E +' eventE) R0) -> (itree (E +' eventE) R1) -> Prop)
        (RET: forall
            f_src f_tgt
            f_src' f_tgt'
            (LE: (f_src' <= f_src)%ord)
            (LE: (f_tgt' <= f_tgt)%ord)
            r_src r_tgt
            (SIM: RR f_src' f_tgt' r_src r_tgt),
            P f_src f_tgt (Ret r_src) (Ret r_tgt))
        (SYSCALL: forall
            f_src f_tgt
            f_src0 f_tgt0
            ktr_src0 ktr_tgt0 fn varg rvs
            (SIM: forall x_src x_tgt (EQ: x_src = x_tgt), (<<SIM: _simg_aux r RR f_src0 f_tgt0 (ktr_src0 x_src) (ktr_tgt0 x_tgt)>>) /\ (<<IH: P f_src0 f_tgt0 (ktr_src0 x_src) (ktr_tgt0 x_tgt)>>)),
            P f_src f_tgt (trigger (SyscallOut fn varg rvs) >>= ktr_src0) (trigger (SyscallOut fn varg rvs) >>= ktr_tgt0))
        (SYSCALLIN: forall
            f_src f_tgt
            f_src0 f_tgt0
            ktr_src0 ktr_tgt0 rv
            (SIM: (<<SIM: _simg_aux r RR f_src0 f_tgt0 (ktr_src0 tt) (ktr_tgt0 tt)>>) /\ (<<IH: P f_src0 f_tgt0 (ktr_src0 tt) (ktr_tgt0 tt)>>)),
            P f_src f_tgt (trigger (SyscallIn rv) >>= ktr_src0) (trigger (SyscallIn rv) >>= ktr_tgt0))
        (TAUL: forall
            f_src0
            f_src f_tgt
            itr_src0 itr_tgt0
            (TAUL: True)
            (SIM: _simg_aux r RR f_src0 f_tgt itr_src0 itr_tgt0)
            (IH: P f_src0 f_tgt itr_src0 itr_tgt0),
            P f_src f_tgt (tau;; itr_src0) (itr_tgt0))
        (TAUR: forall
            f_tgt0
            f_src f_tgt
            itr_src0 itr_tgt0
            (TAUR: True)
            (SIM: _simg_aux r RR f_src f_tgt0 itr_src0 itr_tgt0)
            (IH: P f_src f_tgt0 itr_src0 itr_tgt0),
            P f_src f_tgt (itr_src0) (tau;;itr_tgt0))
        (CHOOSEL: forall
            f_src0
            f_src f_tgt
            X ktr_src0 itr_tgt0
            (CHOOSEL: True)
            (SIM: exists x, <<SIM: _simg_aux r RR f_src0 f_tgt (ktr_src0 x) itr_tgt0>> /\ <<IH: P f_src0 f_tgt (ktr_src0 x) itr_tgt0>>),
            P f_src f_tgt (trigger (Choose X) >>= ktr_src0) (itr_tgt0))
        (CHOOSER: forall
            f_tgt0
            f_src f_tgt
            X itr_src0 ktr_tgt0
            (CHOOSER: True)
            (SIM: forall x, <<SIM: _simg_aux r RR f_src f_tgt0 itr_src0 (ktr_tgt0 x)>> /\ <<IH: P f_src f_tgt0 itr_src0 (ktr_tgt0 x)>>),
            P f_src f_tgt (itr_src0) (trigger (Choose X) >>= ktr_tgt0))
        (TAKEL: forall
            f_src0
            f_src f_tgt
            X ktr_src0 itr_tgt0
            (TAKEL: True)
            (SIM: forall x, <<SIM: _simg_aux r RR f_src0 f_tgt (ktr_src0 x) itr_tgt0>> /\ <<IH: P f_src0 f_tgt (ktr_src0 x) itr_tgt0>>),
            P f_src f_tgt (trigger (Take X) >>= ktr_src0) (itr_tgt0))
        (TAKER: forall
            f_tgt0
            f_src f_tgt
            X itr_src0 ktr_tgt0
            (TAKER: True)
            (SIM: exists x, <<SIM: _simg_aux r RR f_src f_tgt0 itr_src0 (ktr_tgt0 x)>> /\ <<IH: P f_src f_tgt0 itr_src0 (ktr_tgt0 x)>>),
            P f_src f_tgt (itr_src0) (trigger (Take X) >>= ktr_tgt0))
        (PROGRESS: forall
            f_src0 f_tgt0
            f_src f_tgt
            itr_src itr_tgt
            (SIM: r _ _ RR f_src0 f_tgt0 itr_src itr_tgt)
            (SRC: (f_src0 < f_src)%ord)
            (TGT: (f_tgt0 < f_tgt)%ord),
            P f_src f_tgt itr_src itr_tgt)
        (EVENT: forall
            f_src f_tgt
            f_src0 f_tgt0
            X (e: E X) ktr_src0 ktr_tgt0
            (SIM: forall x_src x_tgt (EQ: x_src = x_tgt), (<<SIM: _simg_aux r RR f_src0 f_tgt0 (ktr_src0 x_src) (ktr_tgt0 x_tgt)>>) /\ (<<IH: P f_src0 f_tgt0 (ktr_src0 x_src) (ktr_tgt0 x_tgt)>>)),
            P f_src f_tgt (trigger e >>= ktr_src0) (trigger e >>= ktr_tgt0))
    :
    forall f_src f_tgt itr_src itr_tgt
      (SIM: _simg_aux r RR f_src f_tgt itr_src itr_tgt),
      P f_src f_tgt itr_src itr_tgt.
  Proof.
    fix IH 5. i. inv SIM.
    { eapply RET; eauto. }
    { eapply SYSCALL; eauto. i. split; eauto. }
    { eapply SYSCALLIN; eauto. }
    { eapply TAUL; eauto. }
    { eapply TAUR; eauto. }
    { eapply CHOOSEL; eauto. des. esplits; eauto. }
    { eapply CHOOSER; eauto. }
    { eapply TAKEL; eauto. }
    { eapply TAKER; eauto. des. esplits; eauto. }
    { eapply PROGRESS; eauto. }
    { eapply EVENT; eauto. i. split; eauto. }
  Qed.

  Definition simg_aux: forall R0 R1 (RR: Ord.t -> Ord.t -> R0 -> R1 -> Prop), Ord.t -> Ord.t -> (itree (E +' eventE) R0) -> (itree (E +' eventE) R1) -> Prop := paco7 _simg_aux bot7.

  Lemma simg_aux_mon: monotone7 _simg_aux.
  Proof.
    ii. induction IN using _simg_aux_ind2.
    { econs 1; eauto. }
    { econs 2; eauto. i. specialize (SIM x_src x_tgt EQ). des; eauto. }
    { econs 3; eauto. eapply SIM; et. }
    { econs 4; eauto. }
    { econs 5; eauto. }
    { econs 6; eauto. des. esplits; eauto. }
    { econs 7; eauto. i. spc SIM. des; et. }
    { econs 8; eauto. i. spc SIM. des; et. }
    { econs 9; eauto. des. esplits; eauto. }
    { econs 10; eauto. }
    { econs 11; eauto. i. specialize (SIM x_src x_tgt EQ). des; eauto. }
  Qed.
  Hint Resolve simg_aux_mon: paco.
  Hint Resolve cpn7_wcompat: paco.


  Variant simg_aux_indC
          (simg_aux: forall R0 R1 (RR: Ord.t -> Ord.t -> R0 -> R1 -> Prop), Ord.t -> Ord.t -> (itree (E +' eventE) R0) -> (itree (E +' eventE) R1) -> Prop)
          {R0 R1} (RR: Ord.t -> Ord.t -> R0 -> R1 -> Prop) (f_src f_tgt: Ord.t): (itree (E +' eventE) R0) -> (itree (E +' eventE) R1) -> Prop :=
    | simg_aux_indC_ret
        f_src' f_tgt'
        (LE: (f_src' <= f_src)%ord)
        (LE: (f_tgt' <= f_tgt)%ord)
        r_src r_tgt
        (SIM: RR f_src' f_tgt' r_src r_tgt)
      :
      simg_aux_indC simg_aux RR f_src f_tgt (Ret r_src) (Ret r_tgt)
    | simg_aux_indC_syscall
        f_src0 f_tgt0
        ktr_src0 ktr_tgt0 fn varg rvs
        (SIM: forall x_src x_tgt (EQ: x_src = x_tgt), simg_aux _ _ RR f_src0 f_tgt0 (ktr_src0 x_src) (ktr_tgt0 x_tgt))
      :
      simg_aux_indC simg_aux RR f_src f_tgt (trigger (SyscallOut fn varg rvs) >>= ktr_src0) (trigger (SyscallOut fn varg rvs) >>= ktr_tgt0)
    | simg_aux_indC_syscall_in
        f_src0 f_tgt0
        ktr_src0 ktr_tgt0 rv
        (SIM: simg_aux _ _ RR f_src0 f_tgt0 (ktr_src0 tt) (ktr_tgt0 tt))
      :
      simg_aux_indC simg_aux RR f_src f_tgt (trigger (SyscallIn rv) >>= ktr_src0) (trigger (SyscallIn rv) >>= ktr_tgt0)

    | simg_aux_indC_tauL
        f_src0
        itr_src0 itr_tgt0
        (SIM: simg_aux _ _ RR f_src0 f_tgt itr_src0 itr_tgt0)
      :
      simg_aux_indC simg_aux RR f_src f_tgt (tau;; itr_src0) (itr_tgt0)
    | simg_aux_indC_tauR
        f_tgt0
        itr_src0 itr_tgt0
        (SIM: simg_aux _ _ RR f_src f_tgt0 itr_src0 itr_tgt0)
      :
      simg_aux_indC simg_aux RR f_src f_tgt (itr_src0) (tau;; itr_tgt0)

    | simg_aux_indC_chooseL
        f_src0
        X ktr_src0 itr_tgt0
        (SIM: exists x, simg_aux _ _ RR f_src0 f_tgt (ktr_src0 x) itr_tgt0)
      :
      simg_aux_indC simg_aux RR f_src f_tgt (trigger (Choose X) >>= ktr_src0) (itr_tgt0)
    | simg_aux_indC_chooseR
        f_tgt0
        X itr_src0 ktr_tgt0
        (SIM: forall x, simg_aux _ _ RR f_src f_tgt0 itr_src0 (ktr_tgt0 x))
      :
      simg_aux_indC simg_aux RR f_src f_tgt (itr_src0) (trigger (Choose X) >>= ktr_tgt0)

    | simg_aux_indC_takeL
        f_src0
        X ktr_src0 itr_tgt0
        (SIM: forall x, simg_aux _ _ RR f_src0 f_tgt (ktr_src0 x) itr_tgt0)
      :
      simg_aux_indC simg_aux RR f_src f_tgt (trigger (Take X) >>= ktr_src0) (itr_tgt0)
    | simg_aux_indC_takeR
        f_tgt0
        X itr_src0 ktr_tgt0
        (SIM: exists x, simg_aux _ _ RR f_src f_tgt0 itr_src0 (ktr_tgt0 x))
      :
      simg_aux_indC simg_aux RR f_src f_tgt (itr_src0) (trigger (Take X) >>= ktr_tgt0)

    | simg_aux_indC_event
        f_src0 f_tgt0
        X (e: E X) ktr_src0 ktr_tgt0
        (SIM: forall x_src x_tgt (EQ: x_src = x_tgt), simg_aux _ _ RR f_src0 f_tgt0 (ktr_src0 x_src) (ktr_tgt0 x_tgt))
      :
      simg_aux_indC simg_aux RR f_src f_tgt (trigger e >>= ktr_src0) (trigger e >>= ktr_tgt0)
  .

  Lemma simg_aux_indC_mon: monotone7 simg_aux_indC.
  Proof.
    ii. inv IN.
    { econs 1; eauto. }
    { econs 2; eauto. }
    { econs 3; eauto. }
    { econs 4; eauto. }
    { econs 5; eauto. }
    { econs 6; eauto. des. esplits; eauto. }
    { econs 7; eauto. }
    { econs 8; eauto. }
    { econs 9; eauto. des. esplits; eauto. }
    { econs 10; eauto. }
  Qed.
  Hint Resolve simg_aux_indC_mon: paco.

  Lemma simg_aux_indC_spec:
    simg_aux_indC <8= gupaco7 _simg_aux (cpn7 _simg_aux).
  Proof.
    eapply wrespect7_uclo; eauto with paco.
    econs; eauto with paco. i. inv PR.
    { econs 1; eauto. }
    { econs 2; eauto. i. specialize (SIM x_src x_tgt EQ). eapply simg_aux_mon. eauto.
      i. eapply rclo7_base. auto. }
    { econs 3; eauto. eapply simg_aux_mon; eauto. i. eapply rclo7_base. auto. }
    { econs 4; eauto. eapply simg_aux_mon; eauto. i. eapply rclo7_base. auto. }
    { econs 5; eauto. eapply simg_aux_mon; eauto. i. eapply rclo7_base. auto. }
    { des. econs 6; eauto. esplits. eapply simg_aux_mon; eauto. i. eapply rclo7_base; eauto. }
    { econs 7; eauto. i. eapply simg_aux_mon; eauto. i. eapply rclo7_base; eauto. }
    { econs 8; eauto. i. eapply simg_aux_mon; eauto. i. eapply rclo7_base; eauto. }
    { des. econs 9; eauto. esplits. eapply simg_aux_mon; eauto. i. eapply rclo7_base; eauto. }
    { econs 11; eauto. i. specialize (SIM x_src x_tgt EQ). eapply simg_aux_mon. eauto.
      i. eapply rclo7_base. auto. }
  Qed.

  Lemma simg_aux_ind R0 R1 (RR: Ord.t -> Ord.t -> R0 -> R1 -> Prop)
        (P: Ord.t -> Ord.t -> (itree (E +' eventE) R0) -> (itree (E +' eventE) R1) -> Prop)
        (RET: forall
            f_src f_tgt
            f_src' f_tgt'
            (LE: (f_src' <= f_src)%ord)
            (LE: (f_tgt' <= f_tgt)%ord)
            r_src r_tgt
            (SIM: RR f_src' f_tgt' r_src r_tgt),
            P f_src f_tgt (Ret r_src) (Ret r_tgt))
        (SYSCALL: forall
            f_src0 f_tgt0
            f_src f_tgt
            ktr_src0 ktr_tgt0 fn varg rvs
            (SIM: forall x_src x_tgt (EQ: x_src = x_tgt), (<<SIMG: simg_aux RR f_src0 f_tgt0 (ktr_src0 x_src) (ktr_tgt0 x_tgt)>>) /\ (<<IH: P f_src0 f_tgt0 (ktr_src0 x_src) (ktr_tgt0 x_tgt)>>)),
            P f_src f_tgt (trigger (SyscallOut fn varg rvs) >>= ktr_src0) (trigger (SyscallOut fn varg rvs) >>= ktr_tgt0))
        (SYSCALLIN: forall
            f_src0 f_tgt0
            f_src f_tgt
            ktr_src0 ktr_tgt0 rv
            (SIM: (<<SIMG: simg_aux RR f_src0 f_tgt0 (ktr_src0 tt) (ktr_tgt0 tt)>>) /\ (<<IH: P f_src0 f_tgt0 (ktr_src0 tt) (ktr_tgt0 tt)>>)),
            P f_src f_tgt (trigger (SyscallIn rv) >>= ktr_src0) (trigger (SyscallIn rv) >>= ktr_tgt0))
        (TAUL: forall
            f_src0
            f_src f_tgt
            itr_src0 itr_tgt0
            (SIM: simg_aux RR f_src0 f_tgt itr_src0 itr_tgt0)
            (IH: P f_src0 f_tgt itr_src0 itr_tgt0),
            P f_src f_tgt (tau;; itr_src0) (itr_tgt0))
        (TAUR: forall
            f_tgt0
            f_src f_tgt
            itr_src0 itr_tgt0
            (SIM: simg_aux RR f_src f_tgt0 itr_src0 itr_tgt0)
            (IH: P f_src f_tgt0 itr_src0 itr_tgt0),
            P f_src f_tgt (itr_src0) (tau;;itr_tgt0))
        (CHOOSEL: forall
            f_src0
            f_src f_tgt
            X ktr_src0 itr_tgt0
            (SIM: exists x, <<SIM: simg_aux RR f_src0 f_tgt (ktr_src0 x) itr_tgt0>> /\ <<IH: P f_src0 f_tgt (ktr_src0 x) itr_tgt0>>),
            P f_src f_tgt (trigger (Choose X) >>= ktr_src0) (itr_tgt0))
        (CHOOSER: forall
            f_tgt0
            f_src f_tgt
            X itr_src0 ktr_tgt0
            (SIM: forall x, <<SIM: simg_aux RR f_src f_tgt0 itr_src0 (ktr_tgt0 x)>> /\ <<IH: P f_src f_tgt0 itr_src0 (ktr_tgt0 x)>>),
            P f_src f_tgt (itr_src0) (trigger (Choose X) >>= ktr_tgt0))
        (TAKEL: forall
            f_src0
            f_src f_tgt
            X ktr_src0 itr_tgt0
            (SIM: forall x, <<SIM: simg_aux RR f_src0 f_tgt (ktr_src0 x) itr_tgt0>> /\ <<IH: P f_src0 f_tgt (ktr_src0 x) itr_tgt0>>),
            P f_src f_tgt (trigger (Take X) >>= ktr_src0) (itr_tgt0))
        (TAKER: forall
            f_tgt0
            f_src f_tgt
            X itr_src0 ktr_tgt0
            (SIM: exists x, <<SIM: simg_aux RR f_src f_tgt0 itr_src0 (ktr_tgt0 x)>> /\ <<IH: P f_src f_tgt0 itr_src0 (ktr_tgt0 x)>>),
            P f_src f_tgt (itr_src0) (trigger (Take X) >>= ktr_tgt0))
        (PROGRESS: forall
            f_src0 f_tgt0
            f_src f_tgt
            itr_src itr_tgt
            (SIM: simg_aux RR f_src0 f_tgt0 itr_src itr_tgt)
            (SRC: (f_src0 < f_src)%ord)
            (TGT: (f_tgt0 < f_tgt)%ord),
            P f_src f_tgt itr_src itr_tgt)
        (EVENT: forall
            f_src0 f_tgt0
            f_src f_tgt
            X (e: E X) ktr_src0 ktr_tgt0
            (SIM: forall x_src x_tgt (EQ: x_src = x_tgt), (<<SIMG: simg_aux RR f_src0 f_tgt0 (ktr_src0 x_src) (ktr_tgt0 x_tgt)>>) /\ (<<IH: P f_src0 f_tgt0 (ktr_src0 x_src) (ktr_tgt0 x_tgt)>>)),
            P f_src f_tgt (trigger e >>= ktr_src0) (trigger e >>= ktr_tgt0))
    :
    forall f_src f_tgt itr_src itr_tgt
      (SIM: simg_aux RR f_src f_tgt itr_src itr_tgt),
      P f_src f_tgt itr_src itr_tgt.
  Proof.
    i. punfold SIM. induction SIM using _simg_aux_ind2; i; clarify.
    { eapply RET; eauto. }
    { eapply SYSCALL; eauto. i. hexploit SIM; eauto. i. des. split; eauto. pfold. auto. }
    { eapply SYSCALLIN; eauto. destruct SIM. split; eauto. pfold. auto. }
    { eapply TAUL; eauto. pfold. auto. }
    { eapply TAUR; eauto. pfold. auto. }
    { eapply CHOOSEL; eauto. des. esplits; eauto. pfold. auto. }
    { eapply CHOOSER; eauto. i. hexploit SIM; eauto. i. des. esplits; eauto. pfold. et. }
    { eapply TAKEL; eauto. i. hexploit SIM; eauto. i. des. esplits; eauto. pfold. auto. }
    { eapply TAKER; eauto. des. esplits; eauto. pfold. auto. }
    { eapply PROGRESS; eauto. pclearbot. auto. }
    { eapply EVENT; eauto. i. hexploit SIM; eauto. i. des. split; eauto. pfold. auto. }
  Qed.

  Hint Constructors _simg_aux: core.
  Hint Unfold simg_aux: core.
  Hint Resolve simg_aux_mon: paco.
  Hint Resolve cpn7_wcompat: paco.

End SIM.

#[export] Hint Constructors _simg_aux: core.
#[export] Hint Unfold simg_aux: core.
#[export] Hint Resolve simg_aux_mon: paco.
#[export] Hint Constructors simg_aux_indC: core.
#[export] Hint Resolve simg_aux_indC_mon: paco.
#[export] Hint Resolve cpn7_wcompat: paco.

Section PROOF.

  Variable E: Type -> Type.

  Lemma simg_implies_simg_aux
        R0 R1 (RR: Ord.t -> Ord.t -> R0 -> R1 -> Prop)
        (itr_src: itree (E +' eventE) R0)
        (itr_tgt: itree (E +' eventE) R1)
        (f_src f_tgt: Ord.t)
        (SIM: simg RR f_src f_tgt (itr_src) (itr_tgt))
    :
    simg_aux RR f_src f_tgt itr_src itr_tgt.
  Proof.
    ginit. revert_until RR. gcofix CIH. i.
    induction SIM using simg_ind.
    { guclo simg_aux_indC_spec. }
    { gstep. econs 2. i. specialize (SIM _ _ EQ).
      instantiate (2:= Ord.S f_src0). instantiate (1:= Ord.S f_tgt0).
      econs 10. gfinal. left. eauto. 1,2: apply Ord.S_lt.
    }
    { gstep. econs 3. econs 10. gfinal. left. eauto. 1,2: apply Ord.S_lt. }
    { guclo simg_aux_indC_spec. }
    { guclo simg_aux_indC_spec. }
    { des. guclo simg_aux_indC_spec. }
    { guclo simg_aux_indC_spec. econs 7. i. specialize (SIM x). des. eauto. }
    { guclo simg_aux_indC_spec. econs 8. i. specialize (SIM x). des. eauto. }
    { des. guclo simg_aux_indC_spec. }
    { gstep. econs 10; eauto. gfinal. left; eauto. }
    { gstep. econs 11. i. specialize (SIM _ _ EQ).
      instantiate (2:= Ord.S f_src0). instantiate (1:= Ord.S f_tgt0).
      econs 10. gfinal. left. eauto. 1,2: apply Ord.S_lt.
    }
  Qed.

End PROOF.



Section GEN.

  Variable E: Type -> Type.
  Variable wf: WF.

  Inductive gen_exp
            {R0 R1} (RR: Ord.t -> Ord.t -> R0 -> R1 -> Prop) (f_src f_tgt: Ord.t): (wf.(T)) -> (itree (E +' eventE) R0) -> (wf.(T)) -> (itree (E +' eventE) R1) -> Prop :=
  | gen_exp_ret
      r_src r_tgt
      f_src' f_tgt'
      (LE: (f_src' <= f_src)%ord)
      (LE: (f_tgt' <= f_tgt)%ord)
      g_src g_tgt
      (GEN: RR f_src' f_tgt' r_src r_tgt)
    :
    gen_exp RR f_src f_tgt (g_src) (Ret r_src) (g_tgt) (Ret r_tgt)
  | gen_exp_syscall
      ktr_src0 ktr_tgt0 fn varg rvs
      f_src0 f_tgt0
      g_src g_tgt g_src0 g_tgt0
      (LTS: wf.(lt) g_src0 g_src)
      (LTT: wf.(lt) g_tgt0 g_tgt)
      (GEN: forall x_src x_tgt (EQ: x_src = x_tgt),
          gen_exp RR f_src0 f_tgt0 (g_src0) (ktr_src0 x_src) (g_tgt0) (ktr_tgt0 x_tgt))
    :
    gen_exp RR f_src f_tgt (g_src) (trigger (SyscallOut fn varg rvs) >>= ktr_src0) (g_tgt) (trigger (SyscallOut fn varg rvs) >>= ktr_tgt0)
  | gen_exp_syscall_in
      ktr_src0 ktr_tgt0 rv
      f_src0 f_tgt0
      g_src g_tgt g_src0 g_tgt0
      (LTS: wf.(lt) g_src0 g_src)
      (LTT: wf.(lt) g_tgt0 g_tgt)
      (GEN: gen_exp RR f_src0 f_tgt0 (g_src0) (ktr_src0 tt) (g_tgt0) (ktr_tgt0 tt))
    :
    gen_exp RR f_src f_tgt (g_src) (trigger (SyscallIn rv) >>= ktr_src0) (g_tgt) (trigger (SyscallIn rv) >>= ktr_tgt0)

  | gen_exp_tauL
      itr_src0 itr_tgt0
      f_src0
      g_src g_tgt g_src0
      (LTS: wf.(lt) g_src0 g_src)
      (SIM: gen_exp RR f_src0 f_tgt (g_src0) (itr_src0) (g_tgt) (itr_tgt0))
    :
    gen_exp RR f_src f_tgt (g_src) (tau;; itr_src0) (g_tgt) (itr_tgt0)
  | gen_exp_tauR
      itr_src0 itr_tgt0
      f_tgt0
      g_src g_tgt g_tgt0
      (LTT: wf.(lt) g_tgt0 g_tgt)
      (SIM: gen_exp RR f_src f_tgt0 (g_src) (itr_src0) (g_tgt0) (itr_tgt0))
    :
    gen_exp RR f_src f_tgt (g_src) (itr_src0) (g_tgt) (tau;; itr_tgt0)

  | gen_exp_chooseL
      X ktr_src0 itr_tgt0
      f_src0
      g_src g_tgt g_src0
      (LTS: wf.(lt) g_src0 g_src)
      x
      (SIM: gen_exp RR f_src0 f_tgt (g_src0) (ktr_src0 x) (g_tgt) (itr_tgt0))
    :
    gen_exp RR f_src f_tgt (g_src) (trigger (Choose X) >>= ktr_src0) (g_tgt) (itr_tgt0)
  | gen_exp_chooseR
      X itr_src0 ktr_tgt0
      f_tgt0
      g_src g_tgt g_tgt0
      (LTT: wf.(lt) g_tgt0 g_tgt)
      (SIM: forall x, gen_exp RR f_src f_tgt0 (g_src) (itr_src0) (g_tgt0) (ktr_tgt0 x))
    :
    gen_exp RR f_src f_tgt (g_src) (itr_src0) (g_tgt) (trigger (Choose X) >>= ktr_tgt0)

  | gen_exp_takeL
      X ktr_src0 itr_tgt0
      f_src0
      g_src g_tgt g_src0
      (LTS: wf.(lt) g_src0 g_src)
      (SIM: forall x, gen_exp RR f_src0 f_tgt (g_src0) (ktr_src0 x) (g_tgt) (itr_tgt0))
    :
    gen_exp RR f_src f_tgt (g_src) (trigger (Take X) >>= ktr_src0) (g_tgt) (itr_tgt0)
  | gen_exp_takeR
      X itr_src0 ktr_tgt0
      f_tgt0
      g_src g_tgt g_tgt0
      (LTT: wf.(lt) g_tgt0 g_tgt)
      x
      (SIM: gen_exp RR f_src f_tgt0 (g_src) (itr_src0) (g_tgt0) (ktr_tgt0 x))
    :
    gen_exp RR f_src f_tgt (g_src) (itr_src0) (g_tgt) (trigger (Take X) >>= ktr_tgt0)

  | gen_exp_progress
      itr_src itr_tgt
      f_src0 f_tgt0
      g_src g_tgt
      (SIM: simg_aux RR f_src0 f_tgt0 itr_src itr_tgt)
      (SRC: (f_src0 < f_src)%ord)
      (TGT: (f_tgt0 < f_tgt)%ord)
    :
    gen_exp RR f_src f_tgt (g_src) (itr_src) (g_tgt) (itr_tgt)

  | gen_exp_event
      X (e: E X) ktr_src0 ktr_tgt0
      f_src0 f_tgt0
      g_src g_tgt g_src0 g_tgt0
      (LTS: wf.(lt) g_src0 g_src)
      (LTT: wf.(lt) g_tgt0 g_tgt)
      (GEN: forall x_src x_tgt (EQ: x_src = x_tgt),
          gen_exp RR f_src0 f_tgt0 (g_src0) (ktr_src0 x_src) (g_tgt0) (ktr_tgt0 x_tgt))
    :
    gen_exp RR f_src f_tgt (g_src) (trigger e >>= ktr_src0) (g_tgt) (trigger e >>= ktr_tgt0)
  .

  Lemma gen_exp_leL
        R0 R1 (RR: Ord.t -> Ord.t -> R0 -> R1 -> Prop)
        (itr_src: itree (E +' eventE) R0)
        (itr_tgt: itree (E +' eventE) R1)
        (f_src f_tgt: Ord.t)
        gs0 gs1 gt
        (LE: wf.(le) gs0 gs1)
        (GEN: gen_exp RR f_src f_tgt gs0 (itr_src) gt (itr_tgt))
    :
    gen_exp RR f_src f_tgt gs1 itr_src gt itr_tgt.
  Proof.
    destruct LE.
    { clarify. }
    rename H into LT. generalize dependent gs1. induction GEN; i.
    { econs 1; eauto. }
    { econs 2.
      3:{ i. specialize (H _ _ EQ _ LTS). eauto. }
      all: auto.
    }
    { econs 3; try eassumption. eauto.
    }
    { econs 4.
      2:{ specialize (IHGEN _ LTS). eauto. }
      auto.
    }
    { econs 5. 2: eauto. auto. }
    { econs 6.
      2:{ specialize (IHGEN _ LTS). eauto. }
      auto.
    }
    { econs 7. 2: eauto. auto. }
    { econs 8.
      2:{ i. specialize (H x _ LTS). eauto. }
      auto.
    }
    { econs 9. 2: eauto. auto. }
    { econs 10. eauto. all: auto. }
    { econs 11.
      3:{ i. specialize (H _ _ EQ _ LTS). eauto. }
      all: auto.
    }
  Qed.

  Lemma gen_exp_leR
        R0 R1 (RR: Ord.t -> Ord.t -> R0 -> R1 -> Prop)
        (itr_src: itree (E +' eventE) R0)
        (itr_tgt: itree (E +' eventE) R1)
        (f_src f_tgt: Ord.t)
        gs gt0 gt1
        (LE: wf.(le) gt0 gt1)
        (GEN: gen_exp RR f_src f_tgt gs (itr_src) gt0 (itr_tgt))
    :
    gen_exp RR f_src f_tgt gs itr_src gt1 itr_tgt.
  Proof.
    destruct LE.
    { clarify. }
    rename H into LT. generalize dependent gt1. induction GEN; i.
    { econs 1; eauto. }
    { econs 2.
      3:{ i. specialize (H _ _ EQ _ LTT). eauto. }
      all: auto.
    }
    { econs 3; try eassumption. eauto.
    }
    { econs 4. 2: eauto. auto. }
    { econs 5.
      2:{ specialize (IHGEN _ LTT). eauto. }
      auto.
    }
    { econs 6. 2: eauto. auto. }
    { econs 7.
      2:{ i. specialize (H x _ LTT). eauto. }
      auto.
    }
    { econs 8. 2: eauto. auto. }
    { econs 9.
      2:{ specialize (IHGEN _ LTT). eauto. }
      auto.
    }
    { econs 10. eauto. all: auto. }
    { econs 11.
      3:{ i. specialize (H _ _ EQ _ LTT). eauto. }
      all: auto.
    }
  Qed.

End GEN.

Global Hint Constructors gen_exp: core.

Section PROOF.

  Variable E: Type -> Type.

  Lemma simg_aux_gen_exp
        R0 R1 (RR: Ord.t -> Ord.t -> R0 -> R1 -> Prop)
        (itr_src: itree (E +' eventE) R0)
        (itr_tgt: itree (E +' eventE) R1)
        (f_src f_tgt: Ord.t)
        (SIM: simg_aux RR f_src f_tgt (itr_src) (itr_tgt))
    :
    exists gs gt, gen_exp (@ord_tree_WF ((itree (E +' eventE) R0) * (itree (E +' eventE) R1)))
                     RR f_src f_tgt gs itr_src gt itr_tgt.
  Proof.
    set (A:= ((itree (E +' eventE) R0) * (itree (E +' eventE) R1))%type). move A before RR.
    set (def:= (@ITree.spin (E +' eventE) R0, @ITree.spin (E +' eventE) R1)). move def before A.
    induction SIM using simg_aux_ind.
    { exists (ord_tree_base A), (ord_tree_base A). econs 1; eauto. }
    { hexploit ord_tree_join.
      { instantiate (2:= A).
        instantiate (2:= (fun '(i_s, i_t) =>
                            exists gs gt, gen_exp (@ord_tree_WF A) RR f_src0 f_tgt0 gs i_s gt i_t)).
        instantiate (1:= fun '(i_s, i_t) o =>
                           exists gt, gen_exp (@ord_tree_WF A) RR f_src0 f_tgt0 o i_s gt i_t).
        i. ss. des_ifs.
      }
      intros JOIN1. des. rename o1 into gsT.
      set (Succ1 := (fun _: A => gsT)). exists (ord_tree_cons Succ1).
      hexploit ord_tree_join.
      { instantiate (2:= A).
        instantiate (2:= (fun '(i_s, i_t) =>
                            exists gt, gen_exp (@ord_tree_WF A) RR f_src0 f_tgt0 gsT i_s gt i_t)).
        instantiate (1:= fun '(i_s, i_t) o =>
                           gen_exp (@ord_tree_WF A) RR f_src0 f_tgt0 gsT i_s o i_t).
        i. ss. des_ifs.
      }
      intros JOIN2. des. rename o1 into gtT.
      set (Succ2 := (fun _: A => gtT)). exists (ord_tree_cons Succ2).
      eapply gen_exp_syscall.
      { instantiate (1:= (Succ1 def)). ss. }
      { instantiate (1:= (Succ2 def)). ss. }
      instantiate (1:=f_tgt0). instantiate (1:=f_src0). i. subst Succ1 Succ2. ss.
      set (itrp := (ktr_src0 x_src, ktr_tgt0 x_tgt)).
      specialize (JOIN2 itrp). specialize (JOIN1 itrp).
      subst itrp. ss. specialize (SIM _ _ EQ). des.
      hexploit JOIN1; clear JOIN1. eauto. i. des.
      hexploit JOIN2; clear JOIN2.
      { exists gt0. eapply gen_exp_leL. 2: eauto. right. auto. }
      i. des. eapply gen_exp_leR. 2: eauto. right. auto.
    }
    { hexploit ord_tree_join.
      { instantiate (2:= A).
        instantiate (2:= (fun '(i_s, i_t) =>
                            exists gs gt, gen_exp (@ord_tree_WF A) RR f_src0 f_tgt0 gs i_s gt i_t)).
        instantiate (1:= fun '(i_s, i_t) o =>
                           exists gt, gen_exp (@ord_tree_WF A) RR f_src0 f_tgt0 o i_s gt i_t).
        i. ss. des_ifs.
      }
      intros JOIN1. des. rename o1 into gsT.
      set (Succ1 := (fun _: A => gsT)). exists (ord_tree_cons Succ1).
      hexploit ord_tree_join.
      { instantiate (2:= A).
        instantiate (2:= (fun '(i_s, i_t) =>
                            exists gt, gen_exp (@ord_tree_WF A) RR f_src0 f_tgt0 gsT i_s gt i_t)).
        instantiate (1:= fun '(i_s, i_t) o =>
                           gen_exp (@ord_tree_WF A) RR f_src0 f_tgt0 gsT i_s o i_t).
        i. ss. des_ifs.
      }
      intros JOIN2. des. rename o1 into gtT.
      set (Succ2 := (fun _: A => gtT)). exists (ord_tree_cons Succ2).
      eapply gen_exp_syscall_in.
      { instantiate (1:= (Succ1 def)). ss. }
      { instantiate (1:= (Succ2 def)). ss. }
      instantiate (1:=f_tgt0). instantiate (1:=f_src0). i. subst Succ1 Succ2. ss.
      set (itrp := (ktr_src0 tt, ktr_tgt0 tt)).
      specialize (JOIN2 itrp). specialize (JOIN1 itrp).
      subst itrp. ss.
      hexploit JOIN1; clear JOIN1. eauto. i. des.
      hexploit JOIN2; clear JOIN2.
      { exists gt0. eapply gen_exp_leL. 2: eauto. right. auto. }
      i. des. eapply gen_exp_leR. 2: eauto. right. auto.
    }
    { des. set (Succ := (fun _: A => gs)). exists (ord_tree_cons Succ), gt.
      econs 4. 2: eauto. replace gs with (Succ def); ss.
    }
    { des. set (Succ := (fun _: A => gt)). exists gs, (ord_tree_cons Succ).
      econs 5. 2: eauto. replace gt with (Succ def); ss.
    }
    { des. set (Succ := (fun _: A => gs)). exists (ord_tree_cons Succ), gt.
      econs 6. 2: eauto. replace gs with (Succ def); ss.
    }
    { hexploit ord_tree_join.
      { instantiate (2:= A).
        instantiate (2:= (fun '(i_s, i_t) =>
                            exists gs gt, gen_exp (@ord_tree_WF A) RR f_src f_tgt0 gs i_s gt i_t)).
        instantiate (1:= fun '(i_s, i_t) o =>
                           exists gt, gen_exp (@ord_tree_WF A) RR f_src f_tgt0 o i_s gt i_t).
        i. ss. des_ifs.
      }
      intros JOIN1. des. rename o1 into gsT. exists gsT.
      hexploit ord_tree_join.
      { instantiate (2:= A).
        instantiate (2:= (fun '(i_s, i_t) =>
                            exists gt, gen_exp (@ord_tree_WF A) RR f_src f_tgt0 gsT i_s gt i_t)).
        instantiate (1:= fun '(i_s, i_t) o =>
                           gen_exp (@ord_tree_WF A) RR f_src f_tgt0 gsT i_s o i_t).
        i. ss. des_ifs.
      }
      intros JOIN2. des. rename o1 into gtT.
      set (Succ := (fun _: A => gtT)). exists (ord_tree_cons Succ).
      eapply gen_exp_chooseR.
      { instantiate (1:= (Succ def)). ss. }
      instantiate (1:=f_tgt0). i. subst Succ. ss.
      set (itrp := (itr_src0, ktr_tgt0 x)). specialize (JOIN2 itrp). specialize (JOIN1 itrp).
      subst itrp. ss. specialize (SIM x). des.
      hexploit JOIN1; clear JOIN1. eauto. i. des.
      hexploit JOIN2; clear JOIN2.
      { exists gt0. eapply gen_exp_leL. 2: eauto. right. auto. }
      i. des. eapply gen_exp_leR. 2: eauto. right. auto.
    }
    { hexploit ord_tree_join.
      { instantiate (2:= A).
        instantiate (2:= (fun '(i_s, i_t) =>
                            exists gs gt, gen_exp (@ord_tree_WF A) RR f_src0 f_tgt gs i_s gt i_t)).
        instantiate (1:= fun '(i_s, i_t) o =>
                           exists gt, gen_exp (@ord_tree_WF A) RR f_src0 f_tgt o i_s gt i_t).
        i. ss. des_ifs.
      }
      intros JOIN1. des. rename o1 into gsT.
      set (Succ := (fun _: A => gsT)). exists (ord_tree_cons Succ).
      hexploit ord_tree_join.
      { instantiate (2:= A).
        instantiate (2:= (fun '(i_s, i_t) =>
                            exists gt, gen_exp (@ord_tree_WF A) RR f_src0 f_tgt gsT i_s gt i_t)).
        instantiate (1:= fun '(i_s, i_t) o =>
                           gen_exp (@ord_tree_WF A) RR f_src0 f_tgt gsT i_s o i_t).
        i. ss. des_ifs.
      }
      intros JOIN2. des. rename o1 into gtT. exists gtT.
      eapply gen_exp_takeL.
      { instantiate (1:= (Succ def)). ss. }
      instantiate (1:=f_src0). i. subst Succ. ss.
      set (itrp := (ktr_src0 x, itr_tgt0)). specialize (JOIN2 itrp). specialize (JOIN1 itrp).
      subst itrp. ss. specialize (SIM x). des.
      hexploit JOIN1; clear JOIN1. eauto. i. des.
      hexploit JOIN2; clear JOIN2.
      { exists gt0. eapply gen_exp_leL. 2: eauto. right. auto. }
      i. des. eapply gen_exp_leR. 2: eauto. right. auto.
    }
    { des. set (Succ := (fun _: A => gt)). exists gs, (ord_tree_cons Succ).
      econs 9. 2: eauto. replace gt with (Succ def); ss.
    }
    { exists (ord_tree_base A), (ord_tree_base A). econs 10; eauto. }
    { hexploit ord_tree_join.
      { instantiate (2:= A).
        instantiate (2:= (fun '(i_s, i_t) =>
                            exists gs gt, gen_exp (@ord_tree_WF A) RR f_src0 f_tgt0 gs i_s gt i_t)).
        instantiate (1:= fun '(i_s, i_t) o =>
                           exists gt, gen_exp (@ord_tree_WF A) RR f_src0 f_tgt0 o i_s gt i_t).
        i. ss. des_ifs.
      }
      intros JOIN1. des. rename o1 into gsT.
      set (Succ1 := (fun _: A => gsT)). exists (ord_tree_cons Succ1).
      hexploit ord_tree_join.
      { instantiate (2:= A).
        instantiate (2:= (fun '(i_s, i_t) =>
                            exists gt, gen_exp (@ord_tree_WF A) RR f_src0 f_tgt0 gsT i_s gt i_t)).
        instantiate (1:= fun '(i_s, i_t) o =>
                           gen_exp (@ord_tree_WF A) RR f_src0 f_tgt0 gsT i_s o i_t).
        i. ss. des_ifs.
      }
      intros JOIN2. des. rename o1 into gtT.
      set (Succ2 := (fun _: A => gtT)). exists (ord_tree_cons Succ2).
      eapply gen_exp_event.
      { instantiate (1:= (Succ1 def)). ss. }
      { instantiate (1:= (Succ2 def)). ss. }
      instantiate (1:=f_tgt0). instantiate (1:=f_src0). i. subst Succ1 Succ2. ss.
      set (itrp := (ktr_src0 x_src, ktr_tgt0 x_tgt)).
      specialize (JOIN2 itrp). specialize (JOIN1 itrp).
      subst itrp. ss. specialize (SIM _ _ EQ). des.
      hexploit JOIN1; clear JOIN1. eauto. i. des.
      hexploit JOIN2; clear JOIN2.
      { exists gt0. eapply gen_exp_leL. 2: eauto. right. auto. }
      i. des. eapply gen_exp_leR. 2: eauto. right. auto.
    }
  Qed.

End PROOF.
