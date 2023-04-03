Require Import Coqlib.
Require Import ITreelib.
Require Import Any.
Require Import STS.
Require Import Behavior ModSemE.
Require Import Skeleton.
Require Import Coq.Relations.Relation_Definitions.
Require Import Relation_Operators.
Require Import RelationPairs.
From Ordinal Require Import Ordinal Arithmetic.
From Ordinal Require Import ClassicalOrdinal.

Set Implicit Arguments.







Section SIM.

Section TY.
(* Context `{R: Type}. *)
Variable E: Type -> Type.

Inductive _simg
          (simg: forall R0 R1 (RR: Ord.t -> Ord.t -> R0 -> R1 -> Prop), Ord.t -> Ord.t -> (itree (E +' eventE) R0) -> (itree (E +' eventE) R1) -> Prop)
          {R0 R1} (RR: Ord.t -> Ord.t -> R0 -> R1 -> Prop) (f_src f_tgt: Ord.t): (itree (E +' eventE) R0) -> (itree (E +' eventE) R1) -> Prop :=
| simg_ret
    r_src r_tgt
    f_src' f_tgt'
    (LE: (f_src' <= f_src)%ord)
    (LE: (f_tgt' <= f_tgt)%ord)
    (SIM: RR f_src' f_tgt' r_src r_tgt)
  :
    _simg simg RR f_src f_tgt (Ret r_src) (Ret r_tgt)
| simg_syscall
    ktr_src0 ktr_tgt0 fn varg rvs
    f_src0 f_tgt0
    (SIM: forall x_src x_tgt (EQ: x_src = x_tgt), simg _ _ RR f_src0 f_tgt0 (ktr_src0 x_src) (ktr_tgt0 x_tgt))
  :
    _simg simg RR f_src f_tgt (trigger (SyscallOut fn varg rvs) >>= ktr_src0) (trigger (SyscallOut fn varg rvs) >>= ktr_tgt0)

| simg_tauL
    itr_src0 itr_tgt0
    (TAUL: True)
    f_src0
    (SIM: @_simg simg _ _ RR f_src0 f_tgt itr_src0 itr_tgt0)
  :
    _simg simg RR f_src f_tgt (tau;; itr_src0) (itr_tgt0)
| simg_tauR
    itr_src0 itr_tgt0
    (TAUR: True)
    f_tgt0
    (SIM: @_simg simg _ _ RR f_src f_tgt0 itr_src0 itr_tgt0)
  :
    _simg simg RR f_src f_tgt (itr_src0) (tau;; itr_tgt0)

| simg_chooseL
    X ktr_src0 itr_tgt0
    (CHOOSEL: True)
    f_src0
    (SIM: exists x, _simg simg RR f_src0 f_tgt (ktr_src0 x) itr_tgt0)
  :
    _simg simg RR f_src f_tgt (trigger (Choose X) >>= ktr_src0) (itr_tgt0)
| simg_chooseR
    X itr_src0 ktr_tgt0
    (CHOOSER: True)
    f_tgt0
    (SIM: forall x, _simg simg RR f_src f_tgt0 itr_src0 (ktr_tgt0 x))
  :
    _simg simg RR f_src f_tgt (itr_src0) (trigger (Choose X) >>= ktr_tgt0)

| simg_takeL
    X ktr_src0 itr_tgt0
    (TAKEL: True)
    f_src0
    (SIM: forall x, _simg simg RR f_src0 f_tgt (ktr_src0 x) itr_tgt0)
  :
    _simg simg RR f_src f_tgt (trigger (Take X) >>= ktr_src0) (itr_tgt0)
| simg_takeR
    X itr_src0 ktr_tgt0
    (TAKER: True)
    f_tgt0
    (SIM: exists x, _simg simg RR f_src f_tgt0 itr_src0 (ktr_tgt0 x))
  :
    _simg simg RR f_src f_tgt (itr_src0) (trigger (Take X) >>= ktr_tgt0)

| simg_progress
    itr_src itr_tgt
    f_src0 f_tgt0
    (SIM: simg _ _ RR f_src0 f_tgt0 itr_src itr_tgt)
    (SRC: (f_src0 < f_src)%ord)
    (TGT: (f_tgt0 < f_tgt)%ord)
  :
    _simg simg RR f_src f_tgt itr_src itr_tgt

| simg_event
    X (e: E X)
    ktr_src0 ktr_tgt0
    f_src0 f_tgt0
    (SIM: forall x_src x_tgt (EQ: x_src = x_tgt), simg _ _ RR f_src0 f_tgt0 (ktr_src0 x_src) (ktr_tgt0 x_tgt))
  :
    _simg simg RR f_src f_tgt (trigger e >>= ktr_src0) (trigger e >>= ktr_tgt0)
.

Lemma _simg_ind2 (r: forall R0 R1 (RR: Ord.t -> Ord.t -> R0 -> R1 -> Prop), Ord.t -> Ord.t -> (itree (E +' eventE) R0) -> (itree (E +' eventE) R1) -> Prop)
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
          (SIM: forall x_src x_tgt (EQ: x_src = x_tgt), r _ _ RR f_src0 f_tgt0 (ktr_src0 x_src) (ktr_tgt0 x_tgt)),
          P f_src f_tgt (trigger (SyscallOut fn varg rvs) >>= ktr_src0) (trigger (SyscallOut fn varg rvs) >>= ktr_tgt0))
      (TAUL: forall
          f_src0
          f_src f_tgt
          itr_src0 itr_tgt0
          (TAUL: True)
          (SIM: _simg r RR f_src0 f_tgt itr_src0 itr_tgt0)
          (IH: P f_src0 f_tgt itr_src0 itr_tgt0),
          P f_src f_tgt (tau;; itr_src0) (itr_tgt0))
      (TAUR: forall
          f_tgt0
          f_src f_tgt
          itr_src0 itr_tgt0
          (TAUR: True)
          (SIM: _simg r RR f_src f_tgt0 itr_src0 itr_tgt0)
          (IH: P f_src f_tgt0 itr_src0 itr_tgt0),
          P f_src f_tgt (itr_src0) (tau;;itr_tgt0))
      (CHOOSEL: forall
          f_src0
          f_src f_tgt
          X ktr_src0 itr_tgt0
          (CHOOSEL: True)
          (SIM: exists x, <<SIM: _simg r RR f_src0 f_tgt (ktr_src0 x) itr_tgt0>> /\ <<IH: P f_src0 f_tgt (ktr_src0 x) itr_tgt0>>),
          P f_src f_tgt (trigger (Choose X) >>= ktr_src0) (itr_tgt0))
      (CHOOSER: forall
          f_tgt0
          f_src f_tgt
          X itr_src0 ktr_tgt0
          (CHOOSER: True)
          (SIM: forall x, <<SIM: _simg r RR f_src f_tgt0 itr_src0 (ktr_tgt0 x)>> /\ <<IH: P f_src f_tgt0 itr_src0 (ktr_tgt0 x)>>),
          P f_src f_tgt (itr_src0) (trigger (Choose X) >>= ktr_tgt0))
      (TAKEL: forall
          f_src0
          f_src f_tgt
          X ktr_src0 itr_tgt0
          (TAKEL: True)
          (SIM: forall x, <<SIM: _simg r RR f_src0 f_tgt (ktr_src0 x) itr_tgt0>> /\ <<IH: P f_src0 f_tgt (ktr_src0 x) itr_tgt0>>),
          P f_src f_tgt (trigger (Take X) >>= ktr_src0) (itr_tgt0))
      (TAKER: forall
          f_tgt0
          f_src f_tgt
          X itr_src0 ktr_tgt0
          (TAKER: True)
          (SIM: exists x, <<SIM: _simg r RR f_src f_tgt0 itr_src0 (ktr_tgt0 x)>> /\ <<IH: P f_src f_tgt0 itr_src0 (ktr_tgt0 x)>>),
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
          (SIM: forall x_src x_tgt (EQ: x_src = x_tgt), r _ _ RR f_src0 f_tgt0 (ktr_src0 x_src) (ktr_tgt0 x_tgt)),
          P f_src f_tgt (trigger e >>= ktr_src0) (trigger e >>= ktr_tgt0))
  :
    forall f_src f_tgt itr_src itr_tgt
           (SIM: _simg r RR f_src f_tgt itr_src itr_tgt),
      P f_src f_tgt itr_src itr_tgt.
Proof.
  fix IH 5. i. inv SIM.
  { eapply RET; eauto. }
  { eapply SYSCALL; eauto. }
  { eapply TAUL; eauto. }
  { eapply TAUR; eauto. }
  { eapply CHOOSEL; eauto. des. esplits; eauto. }
  { eapply CHOOSER; eauto. }
  { eapply TAKEL; eauto. }
  { eapply TAKER; eauto. des. esplits; eauto. }
  { eapply PROGRESS; eauto. }
  { eapply EVENT; eauto. }
Qed.

Definition simg: forall R0 R1 (RR: Ord.t -> Ord.t -> R0 -> R1 -> Prop), Ord.t -> Ord.t -> (itree (E +' eventE) R0) -> (itree (E +' eventE) R1) -> Prop := paco7 _simg bot7.

Lemma simg_mon: monotone7 _simg.
Proof.
  ii. induction IN using _simg_ind2.
  { econs 1; eauto. }
  { econs 2; eauto. }
  { econs 3; eauto. }
  { econs 4; eauto. }
  { econs 5; eauto. des. esplits; eauto. }
  { econs 6; eauto. i. spc SIM. des; et. }
  { econs 7; eauto. i. spc SIM. des; et. }
  { econs 8; eauto. des. esplits; eauto. }
  { econs 9; eauto. }
  { econs 10; eauto. }
Qed.
Hint Resolve simg_mon: paco.
Hint Resolve cpn7_wcompat: paco.


Variant simg_indC
          (simg: forall R0 R1 (RR: Ord.t -> Ord.t -> R0 -> R1 -> Prop), Ord.t -> Ord.t -> (itree (E +' eventE) R0) -> (itree (E +' eventE) R1) -> Prop)
          {R0 R1} (RR: Ord.t -> Ord.t -> R0 -> R1 -> Prop) (f_src f_tgt: Ord.t): (itree (E +' eventE) R0) -> (itree (E +' eventE) R1) -> Prop :=
| simg_indC_ret
    r_src r_tgt
    f_src' f_tgt'
    (LE: (f_src' <= f_src)%ord)
    (LE: (f_tgt' <= f_tgt)%ord)
    (SIM: RR f_src' f_tgt' r_src r_tgt)
  :
    simg_indC simg RR f_src f_tgt (Ret r_src) (Ret r_tgt)
| simg_indC_syscall
    f_src0 f_tgt0
    ktr_src0 ktr_tgt0 fn varg rvs
    (SIM: forall x_src x_tgt (EQ: x_src = x_tgt), simg _ _ RR f_src0 f_tgt0 (ktr_src0 x_src) (ktr_tgt0 x_tgt))
  :
    simg_indC simg RR f_src f_tgt (trigger (SyscallOut fn varg rvs) >>= ktr_src0) (trigger (SyscallOut fn varg rvs) >>= ktr_tgt0)

| simg_indC_tauL
    f_src0
    itr_src0 itr_tgt0
    (TAUL: True)
    (SIM: simg _ _ RR f_src0 f_tgt itr_src0 itr_tgt0)
  :
    simg_indC simg RR f_src f_tgt (tau;; itr_src0) (itr_tgt0)
| simg_indC_tauR
    f_tgt0
    itr_src0 itr_tgt0
    (TAUR: True)
    (SIM: simg _ _ RR f_src f_tgt0 itr_src0 itr_tgt0)
  :
    simg_indC simg RR f_src f_tgt (itr_src0) (tau;; itr_tgt0)

| simg_indC_chooseL
    f_src0
    X ktr_src0 itr_tgt0
    (CHOOSEL: True)
    (SIM: exists x, simg _ _ RR f_src0 f_tgt (ktr_src0 x) itr_tgt0)
  :
    simg_indC simg RR f_src f_tgt (trigger (Choose X) >>= ktr_src0) (itr_tgt0)
| simg_indC_chooseR
    f_tgt0
    X itr_src0 ktr_tgt0
    (CHOOSER: True)
    (SIM: forall x, simg _ _ RR f_src f_tgt0 itr_src0 (ktr_tgt0 x))
  :
    simg_indC simg RR f_src f_tgt (itr_src0) (trigger (Choose X) >>= ktr_tgt0)

| simg_indC_takeL
    f_src0
    X ktr_src0 itr_tgt0
    (TAKEL: True)
    (SIM: forall x, simg _ _ RR f_src0 f_tgt (ktr_src0 x) itr_tgt0)
  :
    simg_indC simg RR f_src f_tgt (trigger (Take X) >>= ktr_src0) (itr_tgt0)
| simg_indC_takeR
    f_tgt0
    X itr_src0 ktr_tgt0
    (TAKER: True)
    (SIM: exists x, simg _ _ RR f_src f_tgt0 itr_src0 (ktr_tgt0 x))
  :
    simg_indC simg RR f_src f_tgt (itr_src0) (trigger (Take X) >>= ktr_tgt0)

| simg_indC_event
    f_src0 f_tgt0
    X (e: E X) ktr_src0 ktr_tgt0
    (SIM: forall x_src x_tgt (EQ: x_src = x_tgt), simg _ _ RR f_src0 f_tgt0 (ktr_src0 x_src) (ktr_tgt0 x_tgt))
  :
    simg_indC simg RR f_src f_tgt (trigger e >>= ktr_src0) (trigger e >>= ktr_tgt0)
.

Lemma simg_indC_mon: monotone7 simg_indC.
Proof.
  ii. inv IN.
  { econs 1; eauto. }
  { econs 2; eauto. }
  { econs 3; eauto. }
  { econs 4; eauto. }
  { econs 5; eauto. des. esplits; eauto. }
  { econs 6; eauto. }
  { econs 7; eauto. }
  { econs 8; eauto. des. esplits; eauto. }
  { econs 9; eauto. }
Qed.
Hint Resolve simg_indC_mon: paco.

Lemma simg_indC_spec:
  simg_indC <8= gupaco7 _simg (cpn7 _simg).
Proof.
  eapply wrespect7_uclo; eauto with paco.
  econs; eauto with paco. i. inv PR.
  { econs 1; eauto. }
  { econs 2; eauto. i. eapply rclo7_base. auto. }
  { econs 3; eauto. eapply simg_mon; eauto. i. eapply rclo7_base. auto. }
  { econs 4; eauto. eapply simg_mon; eauto. i. eapply rclo7_base. auto. }
  { des. econs 5; eauto. esplits. eapply simg_mon; eauto. i. eapply rclo7_base; eauto. }
  { econs 6; eauto. i. eapply simg_mon; eauto. i. eapply rclo7_base; eauto. }
  { econs 7; eauto. i. eapply simg_mon; eauto. i. eapply rclo7_base; eauto. }
  { des. econs 8; eauto. esplits. eapply simg_mon; eauto. i. eapply rclo7_base; eauto. }
  { econs 10; eauto. i. eapply rclo7_base. auto. }
Qed.

Lemma simg_ind R0 R1 (RR: Ord.t -> Ord.t -> R0 -> R1 -> Prop)
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
          (SIM: forall x_src x_tgt (EQ: x_src = x_tgt), simg RR f_src0 f_tgt0 (ktr_src0 x_src) (ktr_tgt0 x_tgt)),
          P f_src f_tgt (trigger (SyscallOut fn varg rvs) >>= ktr_src0) (trigger (SyscallOut fn varg rvs) >>= ktr_tgt0))
      (TAUL: forall
          f_src0
          f_src f_tgt
          itr_src0 itr_tgt0
          (TAUL: True)
          (SIM: simg RR f_src0 f_tgt itr_src0 itr_tgt0)
          (IH: P f_src0 f_tgt itr_src0 itr_tgt0),
          P f_src f_tgt (tau;; itr_src0) (itr_tgt0))
      (TAUR: forall
          f_tgt0
          f_src f_tgt
          itr_src0 itr_tgt0
          (TAUR: True)
          (SIM: simg RR f_src f_tgt0 itr_src0 itr_tgt0)
          (IH: P f_src f_tgt0 itr_src0 itr_tgt0),
          P f_src f_tgt (itr_src0) (tau;;itr_tgt0))
      (CHOOSEL: forall
          f_src0
          f_src f_tgt
          X ktr_src0 itr_tgt0
          (CHOOSEL: True)
          (SIM: exists x, <<SIM: simg RR f_src0 f_tgt (ktr_src0 x) itr_tgt0>> /\ <<IH: P f_src0 f_tgt (ktr_src0 x) itr_tgt0>>),
          P f_src f_tgt (trigger (Choose X) >>= ktr_src0) (itr_tgt0))
      (CHOOSER: forall
          f_tgt0
          f_src f_tgt
          X itr_src0 ktr_tgt0
          (CHOOSER: True)
          (SIM: forall x, <<SIM: simg RR f_src f_tgt0 itr_src0 (ktr_tgt0 x)>> /\ <<IH: P f_src f_tgt0 itr_src0 (ktr_tgt0 x)>>),
          P f_src f_tgt (itr_src0) (trigger (Choose X) >>= ktr_tgt0))
      (TAKEL: forall
          f_src0
          f_src f_tgt
          X ktr_src0 itr_tgt0
          (TAKEL: True)
          (SIM: forall x, <<SIM: simg RR f_src0 f_tgt (ktr_src0 x) itr_tgt0>> /\ <<IH: P f_src0 f_tgt (ktr_src0 x) itr_tgt0>>),
          P f_src f_tgt (trigger (Take X) >>= ktr_src0) (itr_tgt0))
      (TAKER: forall
          f_tgt0
          f_src f_tgt
          X itr_src0 ktr_tgt0
          (TAKER: True)
          (SIM: exists x, <<SIM: simg RR f_src f_tgt0 itr_src0 (ktr_tgt0 x)>> /\ <<IH: P f_src f_tgt0 itr_src0 (ktr_tgt0 x)>>),
          P f_src f_tgt (itr_src0) (trigger (Take X) >>= ktr_tgt0))
      (PROGRESS: forall
          f_src0 f_tgt0
          f_src f_tgt
          itr_src itr_tgt
          (SIM: simg RR f_src0 f_tgt0 itr_src itr_tgt)
          (SRC: (f_src0 < f_src)%ord)
          (TGT: (f_tgt0 < f_tgt)%ord),
          P f_src f_tgt itr_src itr_tgt)
      (EVENT: forall
          f_src0 f_tgt0
          f_src f_tgt
          X (e: E X) ktr_src0 ktr_tgt0
          (SIM: forall x_src x_tgt (EQ: x_src = x_tgt), simg RR f_src0 f_tgt0 (ktr_src0 x_src) (ktr_tgt0 x_tgt)),
          P f_src f_tgt (trigger e >>= ktr_src0) (trigger e >>= ktr_tgt0))
  :
    forall f_src f_tgt itr_src itr_tgt
           (SIM: simg RR f_src f_tgt itr_src itr_tgt),
      P f_src f_tgt itr_src itr_tgt.
Proof.
  i. punfold SIM. induction SIM using _simg_ind2; i; clarify.
  { eapply RET; eauto. }
  { eapply SYSCALL; eauto. i. hexploit SIM; eauto. i. des. pclearbot. eauto. }
  { eapply TAUL; eauto. pfold. auto. }
  { eapply TAUR; eauto. pfold. auto. }
  { eapply CHOOSEL; eauto. des. esplits; eauto. pfold. auto. }
  { eapply CHOOSER; eauto. i. hexploit SIM; eauto. i. des. esplits; eauto. pfold. et. }
  { eapply TAKEL; eauto. i. hexploit SIM; eauto. i. des. esplits; eauto. pfold. auto. }
  { eapply TAKER; eauto. des. esplits; eauto. pfold. auto. }
  { eapply PROGRESS; eauto. pclearbot. auto. }
  { eapply EVENT; eauto. i. hexploit SIM; eauto. i. des. pclearbot. eauto. }
Qed.

End TY.
End SIM.
Hint Constructors _simg.
Hint Unfold simg.
Hint Resolve simg_mon: paco.
Hint Constructors simg_indC: core.
Hint Resolve simg_indC_mon: paco.
Hint Resolve cpn7_wcompat: paco.
