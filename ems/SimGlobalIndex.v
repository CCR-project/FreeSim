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
Require Import SimSTS.

Set Implicit Arguments.







Section SIM.

Section TY.
(* Context `{R: Type}. *)
Inductive _simg
          (simg: forall R0 R1 (RR: Ord.t -> Ord.t -> R0 -> R1 -> Prop), Ord.t -> Ord.t -> (itree eventE R0) -> (itree eventE R1) -> Prop)
          {R0 R1} (RR: Ord.t -> Ord.t -> R0 -> R1 -> Prop) (f_src f_tgt: Ord.t): (itree eventE R0) -> (itree eventE R1) -> Prop :=
| simg_ret
    r_src r_tgt
    (SIM: RR f_src f_tgt r_src r_tgt)
  :
    _simg simg RR f_src f_tgt (Ret r_src) (Ret r_tgt)
| simg_syscall
    ktr_src0 ktr_tgt0 fn varg rvs
    f_src0 f_tgt0
    (SIM: forall x_src x_tgt (EQ: x_src = x_tgt), simg _ _ RR f_src0 f_tgt0 (ktr_src0 x_src) (ktr_tgt0 x_tgt))
  :
    _simg simg RR f_src f_tgt (trigger (Syscall fn varg rvs) >>= ktr_src0) (trigger (Syscall fn varg rvs) >>= ktr_tgt0)

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
.

Lemma _simg_ind2 (r: forall R0 R1 (RR: Ord.t -> Ord.t -> R0 -> R1 -> Prop), Ord.t -> Ord.t -> (itree eventE R0) -> (itree eventE R1) -> Prop)
      R0 R1 (RR: Ord.t -> Ord.t -> R0 -> R1 -> Prop)
      (P: Ord.t -> Ord.t -> (itree eventE R0) -> (itree eventE R1) -> Prop)
      (RET: forall
          f_src f_tgt
          r_src r_tgt
          (SIM: RR f_src f_tgt r_src r_tgt),
          P f_src f_tgt (Ret r_src) (Ret r_tgt))
      (SYSCALL: forall
          f_src f_tgt
          f_src0 f_tgt0
          ktr_src0 ktr_tgt0 fn varg rvs
          (SIM: forall x_src x_tgt (EQ: x_src = x_tgt), r _ _ RR f_src0 f_tgt0 (ktr_src0 x_src) (ktr_tgt0 x_tgt)),
          P f_src f_tgt (trigger (Syscall fn varg rvs) >>= ktr_src0) (trigger (Syscall fn varg rvs) >>= ktr_tgt0))
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
Qed.

Definition simg: forall R0 R1 (RR: Ord.t -> Ord.t -> R0 -> R1 -> Prop), Ord.t -> Ord.t -> (itree eventE R0) -> (itree eventE R1) -> Prop := paco7 _simg bot7.

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
Qed.
Hint Resolve simg_mon: paco.
Hint Resolve cpn7_wcompat: paco.


Variant simg_indC
          (simg: forall R0 R1 (RR: Ord.t -> Ord.t -> R0 -> R1 -> Prop), Ord.t -> Ord.t -> (itree eventE R0) -> (itree eventE R1) -> Prop)
          {R0 R1} (RR: Ord.t -> Ord.t -> R0 -> R1 -> Prop) (f_src f_tgt: Ord.t): (itree eventE R0) -> (itree eventE R1) -> Prop :=
| simg_indC_ret
    r_src r_tgt
    (SIM: RR f_src f_tgt r_src r_tgt)
  :
    simg_indC simg RR f_src f_tgt (Ret r_src) (Ret r_tgt)
| simg_indC_syscall
    f_src0 f_tgt0
    ktr_src0 ktr_tgt0 fn varg rvs
    (SIM: forall x_src x_tgt (EQ: x_src = x_tgt), simg _ _ RR f_src0 f_tgt0 (ktr_src0 x_src) (ktr_tgt0 x_tgt))
  :
    simg_indC simg RR f_src f_tgt (trigger (Syscall fn varg rvs) >>= ktr_src0) (trigger (Syscall fn varg rvs) >>= ktr_tgt0)

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
Qed.

Lemma simg_ind R0 R1 (RR: Ord.t -> Ord.t -> R0 -> R1 -> Prop)
      (P: Ord.t -> Ord.t -> (itree eventE R0) -> (itree eventE R1) -> Prop)
      (RET: forall
          f_src f_tgt
          r_src r_tgt
          (SIM: RR f_src f_tgt r_src r_tgt),
          P f_src f_tgt (Ret r_src) (Ret r_tgt))
      (SYSCALL: forall
          f_src0 f_tgt0
          f_src f_tgt
          ktr_src0 ktr_tgt0 fn varg rvs
          (SIM: forall x_src x_tgt (EQ: x_src = x_tgt), simg RR f_src0 f_tgt0 (ktr_src0 x_src) (ktr_tgt0 x_tgt)),
          P f_src f_tgt (trigger (Syscall fn varg rvs) >>= ktr_src0) (trigger (Syscall fn varg rvs) >>= ktr_tgt0))
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
Qed.

End TY.

Hint Constructors _simg.
Hint Unfold simg.
Hint Resolve simg_mon: paco.
Hint Resolve cpn7_wcompat: paco.

Definition postcond_mon {R0 R1: Type} (RR: Ord.t -> Ord.t -> R0 -> R1 -> Prop): Prop :=
  forall f_src0 f_src1 f_tgt0 f_tgt1 r_src r_tgt
         (LE: (f_src0 <= f_src1)%ord) (LE: (f_tgt0 <= f_tgt1)%ord),
    RR f_src0 f_tgt0 r_src r_tgt -> RR f_src1 f_tgt1 r_src r_tgt.

Variant flagC (r: forall S0 S1 (SS: Ord.t -> Ord.t -> S0 -> S1 -> Prop), Ord.t -> Ord.t -> (itree eventE S0) -> (itree eventE S1) -> Prop):
  forall S0 S1 (SS: Ord.t -> Ord.t -> S0 -> S1 -> Prop), Ord.t -> Ord.t -> (itree eventE S0) -> (itree eventE S1) -> Prop :=
| flagC_intro
    f_src0 f_src1 f_tgt0 f_tgt1 R0 R1 (RR: Ord.t -> Ord.t -> R0 -> R1 -> Prop) itr_src itr_tgt
    (MON: postcond_mon RR)
    (SRC: (f_src0 <= f_src1)%ord)
    (TGT: (f_tgt0 <= f_tgt1)%ord)
    (SIM: r _ _ RR f_src0 f_tgt0 itr_src itr_tgt)
  :
    flagC r RR f_src1 f_tgt1 itr_src itr_tgt
.
Hint Constructors flagC: core.

Lemma flagC_mon
      r1 r2
      (LE: r1 <7= r2)
  :
    flagC r1 <7= flagC r2
.
Proof. ii. destruct PR; econs; et. Qed.
Hint Resolve flagC_mon: paco.

Lemma flagC_wrespectful: wrespectful7 (_simg) flagC.
Proof.
  econs; eauto with paco.
  ii. inv PR. csc.
  eapply GF in SIM.
  revert x3 x4 SRC TGT. induction SIM using _simg_ind2; i; clarify.
  { econs 1; eauto. }
  { econs 2; eauto. i. eapply rclo7_base; eauto. }
  { econs 3; eauto. eapply IHSIM; et. refl. }
  { econs 4; eauto. eapply IHSIM; et. refl. }
  { econs 5; eauto. des. esplits; eauto. eapply IH; et. refl. }
  { econs 6; eauto. i. hexploit SIM; eauto. i. des. eapply IH; et. refl. }
  { econs 7; eauto. i. hexploit SIM; eauto. i. des. eapply IH; et. refl. }
  { econs 8; eauto. des. esplits; eauto. eapply IH; et. refl. }
  { econs 9; eauto.
    - eapply rclo7_clo_base. econs; try apply SIM; et; try refl.
    - eapply Ord.lt_le_lt; et.
    - eapply Ord.lt_le_lt; et. }
Qed.

Lemma flagC_spec: flagC <8= gupaco7 (_simg) (cpn7 (_simg)).
Proof.
  intros. eapply wrespect7_uclo; eauto with paco. eapply flagC_wrespectful.
Qed.

Lemma simg_flag
      r R0 R1 RR itr_src itr_tgt f_src0 f_tgt0 f_src1 f_tgt1
      (MON: postcond_mon RR)
      (SIM: @_simg r R0 R1 RR f_src0 f_tgt0 itr_src itr_tgt)
      (SRC: (f_src0 <= f_src1)%ord)
      (TGT: (f_tgt0 <= f_tgt1)%ord)
  :
    @_simg r R0 R1 RR f_src1 f_tgt1 itr_src itr_tgt.
Proof.
  revert f_src1 f_tgt1 SRC TGT. induction SIM using _simg_ind2; i.
  { econs 1; eauto. }
  { econs 2; eauto. }
  { econs 3; eauto. eapply IHSIM; et. refl. }
  { econs 4; eauto. eapply IHSIM; et. refl. }
  { econs 5; eauto. des. esplits; eauto. eapply IH; et. refl. }
  { econs 6; eauto. i. hexploit SIM; eauto. i. des. eauto. eapply IH; et. refl. }
  { econs 7; eauto. i. hexploit SIM; eauto. i. des. eauto. eapply IH; et. refl. }
  { econs 8; eauto. des. esplits; eauto. eapply IH; et. refl. }
  { econs 9; eauto.
    - eapply Ord.lt_le_lt; et.
    - eapply Ord.lt_le_lt; et. }
Qed.

(* Lemma simg_progress_flag R0 R1 RR r g itr_src itr_tgt *)
(*       (SIM: gpaco7 _simg (cpn7 _simg) g g R0 R1 RR false false itr_src itr_tgt) *)
(*   : *)
(*     gpaco7 _simg (cpn7 _simg) r g R0 R1 RR true true itr_src itr_tgt. *)
(* Proof. *)
(*   gstep. econs; eauto. *)
(* Qed. *)

Lemma simg_flag_down' R0 R1 RR itr_src itr_tgt f_src0 f_tgt0 f_src f_tgt
      (MON: postcond_mon RR)
      (SIM: @simg R0 R1 RR f_src0 f_tgt0 itr_src itr_tgt)
      (SRC: (f_src0 <= f_src)%ord)
      (TGT: (f_tgt0 <= f_tgt)%ord)
  :
    @simg R0 R1 RR f_src f_tgt itr_src itr_tgt.
Proof.
  ginit. guclo flagC_spec.
Qed.

Lemma simg_flag_down R0 R1 RR r g itr_src itr_tgt f_src0 f_tgt0 f_src f_tgt
      (MON: postcond_mon RR)
      (SIM: gpaco7 _simg (cpn7 _simg) r g R0 R1 RR f_src0 f_tgt0 itr_src itr_tgt)
      (SRC: (f_src0 <= f_src)%ord)
      (TGT: (f_tgt0 <= f_tgt)%ord)
  :
    gpaco7 _simg (cpn7 _simg) r g R0 R1 RR f_src f_tgt itr_src itr_tgt.
Proof.
  guclo flagC_spec.
Qed.

Lemma simg_bot_flag_up R0 R1 RR st_src st_tgt f_src0 f_tgt0 f_src f_tgt
      (SIM: @simg R0 R1 (fun _ _ => RR) f_src0 f_tgt0 st_src st_tgt)
  :
    simg (fun _ _ => RR) f_src f_tgt st_src st_tgt.
Proof.
  ginit.
  revert st_src st_tgt f_src f_tgt f_src0 f_tgt0 SIM.
  gcofix CIH. i. revert f_src f_tgt.
  induction SIM using simg_ind.
  { guclo simg_indC_spec. econs 1; eauto. }
  { gstep. econs 2; eauto. i. gbase. eapply CIH; eauto. }
  { guclo simg_indC_spec. econs 3; eauto. }
  { guclo simg_indC_spec. econs 4; eauto. }
  { guclo simg_indC_spec. econs 5; eauto. des. esplits; eauto. }
  { guclo simg_indC_spec. econs 6; eauto. i. hexploit SIM; eauto. i. des. esplits; eauto. }
  { guclo simg_indC_spec. econs 7; eauto. i. hexploit SIM; eauto. i. des. esplits; eauto. }
  { guclo simg_indC_spec. econs 8; eauto. des. esplits; eauto. }
  { i. eapply simg_flag_down; ss.
    - gfinal. right. eapply paco7_mon; eauto. ss.
    -
Admitted.

Variant bindR (r s: forall S0 S1 (SS: Ord.t -> Ord.t -> S0 -> S1 -> Prop), Ord.t -> Ord.t -> (itree eventE S0) -> (itree eventE S1) -> Prop):
  forall S0 S1 (SS: Ord.t -> Ord.t -> S0 -> S1 -> Prop), Ord.t -> Ord.t -> (itree eventE S0) -> (itree eventE S1) -> Prop :=
| bindR_intro
    f_src f_tgt

    R0 R1 RR
    (i_src: itree eventE R0) (i_tgt: itree eventE R1)
    (SIM: r _ _ RR f_src f_tgt i_src i_tgt)

    S0 S1 SS
    (k_src: ktree eventE R0 S0) (k_tgt: ktree eventE R1 S1)
    (SIMK: forall vret_src vret_tgt f_src f_tgt (SIM: RR f_src f_tgt vret_src vret_tgt),
        s _ _ SS f_src f_tgt (k_src vret_src) (k_tgt vret_tgt))
  :
    bindR r s SS f_src f_tgt (ITree.bind i_src k_src) (ITree.bind i_tgt k_tgt)
.

Hint Constructors bindR: core.

Lemma bindR_mon
      r1 r2 s1 s2
      (LEr: r1 <7= r2) (LEs: s1 <7= s2)
  :
    bindR r1 s1 <7= bindR r2 s2
.
Proof. ii. destruct PR; econs; et. Qed.

Definition bindC r := bindR r r.
Hint Unfold bindC: core.



Lemma bindC_wrespectful: wrespectful7 (_simg) bindC.
Proof.
  econs.
  { ii. eapply bindR_mon; eauto. }
  i. inv PR. csc. eapply GF in SIM.
  revert k_src k_tgt SIMK. induction SIM using _simg_ind2; i.
  { irw. hexploit SIMK; eauto. i. eapply GF in H.
    eapply simg_mon; eauto. i. econs; eauto.
  }
  { rewrite ! bind_bind. econs; eauto. ii.
    { econs 2; eauto with paco. econs; eauto with paco. }
  }
  { rewrite ! bind_tau. econs; eauto. }
  { rewrite ! bind_tau. econs; eauto. }
  { rewrite ! bind_bind. econs; eauto. des. esplits; et. }
  { rewrite ! bind_bind. econs; eauto. i. hexploit SIM; eauto. i. des. eauto. }
  { rewrite ! bind_bind. econs; eauto. i. hexploit SIM; eauto. i. des. eauto. }
  { rewrite ! bind_bind. econs; eauto. des. esplits; et. }
  { clarify. econs; eauto. eapply rclo7_clo_base. econs; eauto. }
Qed.

Lemma bindC_spec: bindC <8= gupaco7 (_simg) (cpn7 (_simg)).
Proof.
  intros. eapply wrespect7_uclo; eauto with paco. eapply bindC_wrespectful.
Qed.



Lemma step_trigger_choose_iff X k itr e
      (STEP: ModSemL.step (trigger (Choose X) >>= k) e itr)
  :
    exists x,
      e = None /\ itr = k x.
Proof.
  inv STEP.
  { eapply f_equal with (f:=observe) in H0. ss. }
  { eapply f_equal with (f:=observe) in H0. ss.
    unfold trigger in H0. ss. cbn in H0.
    dependent destruction H0. ired. et.  }
  { eapply f_equal with (f:=observe) in H0. ss. }
  { eapply f_equal with (f:=observe) in H0. ss. }
Qed.

Lemma step_trigger_take_iff X k itr e
      (STEP: ModSemL.step (trigger (Take X) >>= k) e itr)
  :
    exists x,
      e = None /\ itr = k x.
Proof.
  inv STEP.
  { eapply f_equal with (f:=observe) in H0. ss. }
  { eapply f_equal with (f:=observe) in H0. ss. }
  { eapply f_equal with (f:=observe) in H0. ss.
    unfold trigger in H0. ss. cbn in H0.
    dependent destruction H0. ired. et.  }
  { eapply f_equal with (f:=observe) in H0. ss. }
Qed.

Lemma step_tau_iff itr0 itr1 e
      (STEP: ModSemL.step (Tau itr0) e itr1)
  :
    e = None /\ itr0 = itr1.
Proof.
  inv STEP. et.
Qed.

Lemma step_ret_iff rv itr e
      (STEP: ModSemL.step (Ret rv) e itr)
  :
    False.
Proof.
  inv STEP.
Qed.

Lemma step_trigger_syscall_iff fn args rvs k e itr
      (STEP: ModSemL.step (trigger (Syscall fn args rvs) >>= k) e itr)
  :
    exists rv, itr = k rv /\ e = Some (event_sys fn args rv)
               /\ <<RV: rvs rv>> /\ <<SYS: syscall_sem (event_sys fn args rv)>>.
Proof.
  inv STEP.
  { eapply f_equal with (f:=observe) in H0. ss. }
  { eapply f_equal with (f:=observe) in H0. ss. }
  { eapply f_equal with (f:=observe) in H0. ss. }
  { eapply f_equal with (f:=observe) in H0. ss.
    unfold trigger in H0. ss. cbn in H0.
    dependent destruction H0. ired. et. }
Qed.


Lemma itree_eta_eq E R (itr0 itr1: itree E R)
    (OBSERVE: observe itr0 = observe itr1)
  :
    itr0 = itr1.
Proof.
  rewrite (itree_eta_ itr0).
  rewrite (itree_eta_ itr1).
  rewrite OBSERVE. auto.
Qed.

Lemma step_trigger_choose X k x
  :
    ModSemL.step (trigger (Choose X) >>= k) None (k x).
Proof.
  unfold trigger. ss.
  match goal with
  | [ |- ModSemL.step ?itr _ _] =>
    replace itr with (Subevent.vis (Choose X) k)
  end; ss.
  { econs. }
  { eapply itree_eta_eq. ss. cbv. f_equal.
    extensionality x0. eapply itree_eta_eq. ss. }
Qed.

Lemma step_trigger_take X k x
  :
    ModSemL.step (trigger (Take X) >>= k) None (k x).
Proof.
  unfold trigger. ss.
  match goal with
  | [ |- ModSemL.step ?itr _ _] =>
    replace itr with (Subevent.vis (Take X) k)
  end; ss.
  { econs. }
  { eapply itree_eta_eq. ss. cbv. f_equal.
    extensionality x0. eapply itree_eta_eq. ss. }
Qed.

Lemma step_trigger_syscall fn args (rvs: Any.t -> Prop) k rv
      (RV: rvs rv) (SYS: syscall_sem (event_sys fn args rv))
  :
    ModSemL.step (trigger (Syscall fn args rvs) >>= k) (Some (event_sys fn args rv)) (k rv).
Proof.
  unfold trigger. ss.
  match goal with
  | [ |- ModSemL.step ?itr _ _] =>
    replace itr with (Subevent.vis (Syscall fn args rvs) k)
  end; ss.
  { econs; et. }
  { eapply itree_eta_eq. ss. cbv. f_equal.
    extensionality x0. eapply itree_eta_eq. ss. }
Qed.

Lemma step_tau itr
  :
    ModSemL.step (Tau itr) None itr.
Proof.
  econs.
Qed.

Section EUTT.

Theorem eutt_simg: forall R RR (u t: itree eventE R) (EUTT: eqit RR true true u t), simg (fun _ _ => RR) 0%ord 0%ord u t.
Proof.
  i. ginit. revert_until R. gcofix CIH. i.
  punfold EUTT. red in EUTT.
  dependent induction EUTT; try apply simpobs in x; try apply simpobs in x0; try f in x; try f in x0; subst.
  - gstep; econs; eauto.
  - guclo simg_indC_spec. econs; eauto.
    guclo simg_indC_spec. econs; eauto.
    instantiate (1:=1). instantiate (1:=1).
    gstep. econs; eauto; try (instantiate (1:=0); eapply OrdArith.lt_from_nat; lia).
    gbase. eapply CIH. pclearbot. eauto.
  - rewrite <- ! bind_trigger.
    destruct e.
    + guclo simg_indC_spec. econsr; eauto. i.
      guclo simg_indC_spec. econs; eauto.
      instantiate (1:=1). instantiate (1:=1).
      esplits. gstep. econs; eauto; try (instantiate (1:=0); eapply OrdArith.lt_from_nat; lia).
      gbase. eapply CIH. pclearbot. eauto.
    + guclo simg_indC_spec. econs; eauto. i.
      guclo simg_indC_spec. econsr; eauto.
      instantiate (1:=1). instantiate (1:=1).
      esplits. gstep. econs; eauto; try (instantiate (1:=0); eapply OrdArith.lt_from_nat; lia).
      gbase. eapply CIH. pclearbot. eauto.
    + guclo simg_indC_spec. econs; eauto. i. subst.
      instantiate (1:=1). instantiate (1:=1).
      gstep. econs; eauto; try (instantiate (1:=0); eapply OrdArith.lt_from_nat; lia).
      gbase. eapply CIH. pclearbot. eauto.
  - guclo simg_indC_spec. econs; eauto.
  - guclo simg_indC_spec. econs; eauto.
Qed.

Ltac simpobs_all :=
  repeat match goal with
         | [H: VisF _ _ = _ |- _ ] => apply simpobs in H; f in H
         | [H: RetF _ = _ |- _ ] => apply simpobs in H; f in H
         | [H: TauF _ = _ |- _ ] => apply simpobs in H; f in H
         | [H: _ = VisF _ _ |- _ ] => sym in H; apply simpobs in H; f in H
         | [H: _ = RetF _ |- _ ] => sym in H; apply simpobs in H; f in H
         | [H: _ = TauF _ |- _ ] => sym in H; apply simpobs in H; f in H
         end;
  subst.

Lemma euttge_inv
      E R (itr0 itr1: itree E R)
      (TAU: (tau;; itr0) ≳ (tau;; itr1))
  :
  <<TAU: itr0 ≳ itr1>>.
Proof.
  eapply eqit_Tau. eauto.
Qed.

Lemma euttge_tau_inv
      E R (itr0 itr1: itree E R)
      (TAU: itr0 ≳ (tau;; itr1))
  :
  exists itr0', <<EQ: itr0 = tau;; itr0'>> /\ <<TAU: itr0' ≳ itr1>>.
Proof.
  punfold TAU. r in TAU. dup TAU. dependent induction TAU; simpobs_all.
  - pclearbot. esplits; eauto.
  - esplits; eauto. eapply euttge_inv; eauto.
  - rr in CHECK. ss.
Qed.



Variant _eutt0C (r: forall S0 S1 (SS: Ord.t -> Ord.t -> S0 -> S1 -> Prop), Ord.t -> Ord.t -> (itree eventE S0) -> (itree eventE S1) -> Prop):
  forall S0 S1 (SS: Ord.t -> Ord.t -> S0 -> S1 -> Prop), Ord.t -> Ord.t -> (itree eventE S0) -> (itree eventE S1) -> Prop :=
| _eutt0C_intro
    f_src0 f_tgt0 R0 R1 (RR: Ord.t -> Ord.t -> R0 -> R1 -> Prop) itr_src1 itr_src0 itr_tgt0 (* itr_tgt1 *)
    (MON: postcond_mon RR)
    (SIM: r _ _ RR f_src0 f_tgt0 itr_src1 itr_tgt0)
    (LEFT: itr_src0 ≳ itr_src1)
  :
    _eutt0C r RR f_src0 f_tgt0 itr_src0 itr_tgt0
.
Hint Constructors _eutt0C: core.

Lemma _eutt0C_mon
      r1 r2
      (LE: r1 <7= r2)
  :
    _eutt0C r1 <7= _eutt0C r2
.
Proof. ii. destruct PR; econs; et. Qed.
Hint Resolve _eutt0C_mon: paco.

Structure grespectful clo : Prop :=
  grespect_intro {
      grespect_mon: monotone7 clo;
      grespect_respect :
      forall l r
             (LE: l <7= r)
             (GF: l <7= @_simg r),
        clo l <7= gpaco7 _simg (cpn7 _simg) bot7 (rclo7 (clo \8/ gupaco7 _simg (cpn7 _simg)) r);
    }.

Lemma grespect_uclo clo
      (RESPECT: grespectful clo)
  :
  clo <8= gupaco7 (_simg) (cpn7 _simg).
Proof.
  eapply grespect7_uclo; eauto with paco.
  econs.
  { eapply RESPECT. }
  i. hexploit grespect_respect.
  { eauto. }
  { eapply LE. }
  { eapply GF. }
  { eauto. }
  i. inv H. eapply rclo7_mon.
  { eauto. }
  i. ss. des; ss. eapply _paco7_unfold in PR0.
  2:{ ii. eapply simg_mon; [eapply PR1|]. i. eapply rclo7_mon; eauto. }
  ss. eapply simg_mon.
  { eapply PR0; eauto. }
  i. eapply rclo7_clo. right. econs.
  eapply rclo7_mon; eauto. i. inv PR2.
  { left. eapply paco7_mon; eauto. i. ss. des; ss.
    left. auto. }
  { des; ss. right. auto. }
Qed.

Lemma _eutt0C_grespectful: grespectful _eutt0C.
Proof.
  econs; eauto with paco.
  ii. inv PR. csc.
  eapply GF in SIM.
  rename x2 into RR. rename x5 into itr_src0. rename x6 into itr_tgt0.
  (* revert_until RR. gcofix CIH. i. *)
  revert_until SIM. revert itr_src0. induction SIM using _simg_ind2; i; clarify.
  { punfold LEFT. red in LEFT.
    revert SIM. dependent induction LEFT; i; simpobs_all; clarify.
    - gstep. econs; eauto.
    - guclo simg_indC_spec. econs; eauto.
  }
  { punfold LEFT. red in LEFT.
    revert SIM. dependent induction LEFT; i; des_ifs; simpl_existTs; subst; simpobs_all.
    - rewrite bind_trigger in Heq. clarify. simpl_existTs. subst. rewrite <- bind_trigger.
      gstep. econs; eauto. i. subst. gbase. (* eapply CIH0. *) eapply rclo7_clo. left. econs; ss; cycle 1.
      { instantiate (1:=ktr_src0 x_tgt). rr in REL. pclearbot. eauto. }
      eapply rclo7_base. eauto.
    - guclo simg_indC_spec. econs; eauto.
  }
  { eapply euttge_tau_inv in LEFT. des. subst.
    guclo simg_indC_spec. econs; eauto.
  }
  { guclo simg_indC_spec. econs; eauto. }
  { des.
    punfold LEFT. red in LEFT.
    dependent induction LEFT; i; des_ifs; simpl_existTs; subst; simpobs_all.
    - rewrite bind_trigger in Heq. clarify. simpl_existTs. subst. rewrite <- bind_trigger.
      guclo simg_indC_spec. econs; eauto. esplits; eauto.
      eapply IH; ss. rr in REL. pclearbot. eauto.
    - guclo simg_indC_spec. econs; eauto.
  }
  { guclo simg_indC_spec. econs; eauto. i. eapply SIM; ss. }
  { punfold LEFT. red in LEFT.
    dependent induction LEFT; i; des_ifs; simpl_existTs; subst; simpobs_all.
    - rewrite bind_trigger in Heq. clarify. simpl_existTs. subst. rewrite <- bind_trigger.
      guclo simg_indC_spec. econs; eauto. i.
      eapply SIM; ss. rr in REL. pclearbot. eauto.
    - guclo simg_indC_spec. econs; eauto.
  }
  { des. guclo simg_indC_spec. econs; eauto. }
  { gstep. econs; eauto. gbase. eapply rclo7_clo. eauto with paco. }
Qed.

Lemma _eutt0C_spec: _eutt0C <8= gupaco7 (_simg) (cpn7 (_simg)).
Proof.
  intros. eapply grespect_uclo; eauto with paco. eapply _eutt0C_grespectful.
Qed.

Variant _eutt1C (r: forall S0 S1 (SS: Ord.t -> Ord.t -> S0 -> S1 -> Prop), Ord.t -> Ord.t -> (itree eventE S0) -> (itree eventE S1) -> Prop):
  forall S0 S1 (SS: Ord.t -> Ord.t -> S0 -> S1 -> Prop), Ord.t -> Ord.t -> (itree eventE S0) -> (itree eventE S1) -> Prop :=
| _eutt1C_intro
    f_src0 f_tgt0 R0 R1 (RR: Ord.t -> Ord.t -> R0 -> R1 -> Prop) itr_tgt1 itr_src0 itr_tgt0
    (MON: postcond_mon RR)
    (SIM: r _ _ RR f_src0 f_tgt0 itr_src0 itr_tgt1)
    (RIGHT: itr_tgt0 ≳ itr_tgt1)
  :
    _eutt1C r RR f_src0 f_tgt0 itr_src0 itr_tgt0
.
Hint Constructors _eutt1C: core.

Lemma _eutt1C_mon
      r1 r2
      (LE: r1 <7= r2)
  :
    _eutt1C r1 <7= _eutt1C r2
.
Proof. ii. destruct PR; econs; et. Qed.
Hint Resolve _eutt1C_mon: paco.

Lemma _eutt1C_grespectful: grespectful _eutt1C.
Proof.
  econs; eauto with paco.
  ii. inv PR. csc.
  eapply GF in SIM.
  rename x2 into RR. rename x5 into itr_src0. rename x6 into itr_tgt0.
  (* revert_until RR. gcofix CIH. i. *)
  revert_until SIM. revert itr_tgt0. induction SIM using _simg_ind2; i; clarify.
  { punfold RIGHT. red in RIGHT.
    revert SIM. dependent induction RIGHT; i; simpobs_all; clarify.
    - gstep. econs; eauto.
    - guclo simg_indC_spec. econs; eauto.
  }
  { punfold RIGHT. red in RIGHT.
    revert SIM. dependent induction RIGHT; i; des_ifs; simpl_existTs; subst; simpobs_all.
    - rewrite bind_trigger in Heq. clarify. simpl_existTs. subst. rewrite <- bind_trigger.
      gstep. econs; eauto. i. subst. gbase. (* eapply CIH0. *) eapply rclo7_clo. left. econs; ss; cycle 1.
      { instantiate (1:=ktr_tgt0 x_tgt). rr in REL. pclearbot. eauto. }
      eapply rclo7_base. eauto.
    - guclo simg_indC_spec. econs; eauto.
  }
  { guclo simg_indC_spec. econs; eauto. }
  { eapply euttge_tau_inv in RIGHT. des. subst.
    guclo simg_indC_spec. econs; eauto.
  }
  { des. guclo simg_indC_spec. econs; eauto. }
  { punfold RIGHT. red in RIGHT.
    dependent induction RIGHT; i; des_ifs; simpl_existTs; subst; simpobs_all.
    - rewrite bind_trigger in Heq. clarify. simpl_existTs. subst. rewrite <- bind_trigger.
      guclo simg_indC_spec. econs; eauto. esplits; eauto.
      eapply SIM; ss. rr in REL. pclearbot. eauto.
    - guclo simg_indC_spec. econs; eauto.
  }
  { guclo simg_indC_spec. econs; eauto. i. eapply SIM; ss. }
  { des.
    punfold RIGHT. red in RIGHT.
    dependent induction RIGHT; i; des_ifs; simpl_existTs; subst; simpobs_all.
    - rewrite bind_trigger in Heq. clarify. simpl_existTs. subst. rewrite <- bind_trigger.
      guclo simg_indC_spec. econs; eauto. esplits; eauto.
      eapply IH; ss. rr in REL. pclearbot. eauto.
    - guclo simg_indC_spec. econs; eauto.
  }
  { gstep. econs; eauto. gbase. eapply rclo7_clo. eauto with paco. }
Qed.

Lemma _eutt1C_spec: _eutt1C <8= gupaco7 (_simg) (cpn7 (_simg)).
Proof.
  intros. eapply grespect_uclo; eauto with paco. eapply _eutt1C_grespectful.
Qed.

Variant euttC (r: forall S0 S1 (SS: Ord.t -> Ord.t -> S0 -> S1 -> Prop), Ord.t -> Ord.t -> (itree eventE S0) -> (itree eventE S1) -> Prop):
  forall S0 S1 (SS: Ord.t -> Ord.t -> S0 -> S1 -> Prop), Ord.t -> Ord.t -> (itree eventE S0) -> (itree eventE S1) -> Prop :=
| euttC_intro
    f_src0 f_tgt0 R0 R1 (RR: Ord.t -> Ord.t -> R0 -> R1 -> Prop) itr_src1 itr_tgt1 itr_src0 itr_tgt0
    (SIM: r _ _ RR f_src0 f_tgt0 itr_src1 itr_tgt1)
    (LEFT: itr_src0 ≳ itr_src1)
    (RIGHT: itr_tgt0 ≳ itr_tgt1)
    (MON: postcond_mon RR)
  :
    euttC r RR f_src0 f_tgt0 itr_src0 itr_tgt0
.
Hint Constructors euttC: core.

Lemma euttC_mon
      r1 r2
      (LE: r1 <7= r2)
  :
    euttC r1 <7= euttC r2
.
Proof. ii. destruct PR; econs; et. Qed.
Hint Resolve euttC_mon: paco.

Lemma euttC_grespectful: grespectful euttC.
Proof.
  econs; eauto with paco.
  ii. inv PR. csc.
  eapply GF in SIM.
  rename x2 into RR. rename x5 into itr_src0. rename x6 into itr_tgt0.

  guclo _eutt0C_spec. econs; eauto.
  guclo _eutt1C_spec. econs; eauto.
  gfinal. right. pfold. eapply simg_mon; eauto. ii. right. eapply rclo7_base. eauto.
Qed.

Lemma euttC_spec: euttC <8= gupaco7 (_simg) (cpn7 (_simg)).
Proof.
  intros. eapply grespect_uclo; eauto with paco. eapply euttC_grespectful.
Qed.

End EUTT.

Section TRANS.

Lemma simg_tau_inv_l
        R0 R1 (RR: R0 -> R1 -> Prop)
        f0 f1 i0 i1
        (SIM: simg (fun _ _ => RR) f0 f1 (tau;; i0) i1)
  :
  simg (fun _ _ => RR) f0 f1 i0 i1
.
Proof.
  ginit. revert_until RR. gcofix CIH. i.
  remember (tau;; i0) as tmp. revert i0 Heqtmp.
  induction SIM using simg_ind; intros ? EQ; irw in EQ; csc.
  - gfinal. right.
    eapply simg_bot_flag_up in SIM.
    eapply paco7_mon; et. i; ss.
  - guclo simg_indC_spec. econs; eauto.
  - guclo simg_indC_spec. econs; eauto. i. specialize (SIM x). des. eapply IH; ss.
  - guclo simg_indC_spec. econs; eauto. des. esplits; eauto.
  - gstep. econs; eauto. gbase. eapply CIH; ss.
Qed.

Lemma simg_take_inv_l
        R0 R1 (RR: R0 -> R1 -> Prop)
        X
        f0 f1 k0 i1
        (SIM: simg (fun _ _ => RR) f0 f1 (trigger (Take X) >>= k0) i1)
  :
  forall x, simg (fun _ _ => RR) f0 f1 (k0 x) i1
.
Proof.
  i. ginit. revert_until RR. gcofix CIH. i.
  remember (` x : _ <- trigger (Take X);; k0 x) as tmp. revert k0 Heqtmp.
  induction SIM using simg_ind; intros ? EQ; irw in EQ; csc.
  - exploit IHSIM; et. { irw; ss. } i; des.
    guclo simg_indC_spec. econs; et.
  - guclo simg_indC_spec. econs; et. i. eapply SIM. irw; ss.
  - assert(ktr_src0 = k0) by eauto. subst. clear_tac.
    spc SIM. des.
    eapply simg_bot_flag_up in SIM0; et.
    gfinal. right. eapply paco7_mon; et. i; ss.
  - des.
    guclo simg_indC_spec. econs; et. esplits; et. eapply IH. irw; ss.
  - gstep. econs; et. gbase. eapply CIH; et. rewrite <- bind_trigger in *. ss.
Qed.

Lemma simg_tau_inv_r
        R0 R1 (RR: R0 -> R1 -> Prop)
        f0 f1 i0 i1
        (SIM: simg (fun _ _ => RR) f0 f1 (i0) (tau;; i1))
  :
  simg (fun _ _ => RR) f0 f1 i0 i1
.
Proof.
  ginit. revert_until RR. gcofix CIH. i.
  remember (tau;; i1) as tmp. revert i1 Heqtmp.
  induction SIM using simg_ind; intros ? EQ; irw in EQ; csc.
  - guclo simg_indC_spec. econs; eauto.
  - gfinal. right.
    eapply simg_bot_flag_up in SIM.
    eapply paco7_mon; et. i; ss.
  - guclo simg_indC_spec. econs; eauto. des. esplits; eauto.
  - guclo simg_indC_spec. econs; eauto. i. specialize (SIM x). des. eapply IH; ss.
  - gstep. econs; eauto. gbase. eapply CIH; ss.
Qed.

Lemma simg_choose_inv_r
        R0 R1 (RR: R0 -> R1 -> Prop)
        X
        f0 f1 k1 i0
        (SIM: simg (fun _ _ => RR) f0 f1 i0 (trigger (Choose X) >>= k1))
  :
  forall x, simg (fun _ _ => RR) f0 f1 i0 (k1 x)
.
Proof.
  i. ginit. revert_until RR. gcofix CIH. i.
  remember (` x : _ <- trigger (Choose X);; k1 x) as tmp. revert k1 Heqtmp.
  induction SIM using simg_ind; intros ? EQ; irw in EQ; csc.
  - exploit IHSIM; et. { irw; ss. } i; des.
    guclo simg_indC_spec. econs; et.
  - rename X0 into Y. des. rename x0 into y. guclo simg_indC_spec. econs; et. esplits; et. eapply IH. irw; ss.
  - assert(ktr_tgt0 = k1) by eauto. subst. clear_tac.
    spc SIM. des.
    eapply simg_bot_flag_up in SIM0; et.
    gfinal. right. eapply paco7_mon; et. i; ss.
  - guclo simg_indC_spec. econs; et. i. eapply SIM. irw; ss.
  - gstep. econs; et. gbase. eapply CIH; et. rewrite <- bind_trigger in *. ss.
Qed.

Variant mapC (r: forall S0 S1 (SS: Ord.t -> Ord.t -> S0 -> S1 -> Prop), Ord.t -> Ord.t -> (itree eventE S0) -> (itree eventE S1) -> Prop):
  forall S0 S1 (SS: Ord.t -> Ord.t -> S0 -> S1 -> Prop), Ord.t -> Ord.t -> (itree eventE S0) -> (itree eventE S1) -> Prop :=
| mapC_intro
    f_src f_tgt R0 R1 (RR: Ord.t -> Ord.t -> R0 -> R1 -> Prop) itr_src itr_tgt
    T0 T1
    (f0: R0 -> T0)
    (f1: R1 -> T1)
    (SIM: r _ _ (fun f_src f_tgt t0 t1 => forall r0 r1, f0 r0 = t0 -> f1 r1 = t1 -> RR f_src f_tgt r0 r1)
            (* f_src f_tgt (f0 <$> itr_src) (f1 <$> itr_tgt)) *)
            f_src f_tgt (r0 <- itr_src;; Ret (f0 r0)) (r1 <- itr_tgt;; Ret (f1 r1)))
  :
    mapC r RR f_src f_tgt itr_src itr_tgt
.
Hint Constructors mapC: core.

Lemma mapC_mon
      r1 r2
      (LE: r1 <7= r2)
  :
    mapC r1 <7= mapC r2
.
Proof. ii. destruct PR; econs; et. Qed.
Hint Resolve mapC_mon: paco.

Lemma eqitree_inv_bind_ret:
  forall {E : Type -> Type} {A B : Type} (ma : itree E A) (kb : A -> itree E B) (b : B),
  ` x : _ <- ma;; kb x = Ret b -> exists a : A, ma = Ret a /\ kb a = Ret b.
Proof.
  i. f in H. eapply eqitree_inv_bind_ret in H. des. esplits; eauto.
  { f. eauto. }
  { f. eauto. }
Qed.

Lemma eqitree_inv_bind_tau:
  forall {E : Type -> Type} {A B : Type} (ma : itree E A) (kab : A -> itree E B)
    (t : itree E B),
  ` x : _ <- ma;; kab x = (tau;; t) ->
  (exists ma' : itree E A, ma = (tau;; ma') /\ ` x : _ <- ma';; kab x = t) \/
  (exists a : A, ma = Ret a /\ kab a = (tau;; t)).
Proof.
  i. f in H. eapply eqitree_inv_bind_tau in H. des.
  - left. esplits; eauto.
    { f. eauto. }
    { f. eauto. }
  - right. esplits; eauto.
    { f. eauto. }
    { f. eauto. }
Qed.

Lemma eqitree_inv_bind_vis:
  forall {A B : Type} {E : Type -> Type} {X : Type} (ma : itree E A)
    (kab : A -> itree E B) (e : E X) (kxb : X -> itree E B),
  ` x : _ <- ma;; kab x = Vis e kxb ->
  (exists kca : X -> itree E A,
     ma = Vis e kca /\ (forall x : X, ` x : _ <- kca x;; kab x = kxb x)) \/
  (exists a : A, ma = Ret a /\ kab a = Vis e kxb).
Proof.
  i. f in H. eapply eqitree_inv_bind_vis in H. des.
  - left. esplits; eauto. { f. eauto. } i. f. eauto.
  - right. esplits; eauto. { f. eauto. } f. eauto.
Qed.

(* Lemma eqitree_inv_bind: *)
(*   forall {A B : Type} {E : Type -> Type} {X : Type} (ma : itree E A) *)
(*     (kab : A -> itree E B) (e : E X) (kxb : X -> itree E B), *)
(*   ` x : _ <- ma;; kab x = trigger e >>= kxb -> *)
(*   (exists kca : X -> itree E A, *)
(*      ma = e kca /\ (forall x : X, ` x : _ <- kca x;; kab x = kxb x)) \/ *)
(*   (exists a : A, ma = Ret a /\ kab a = Vis e kxb). *)
(* Proof. *)
(*   i. f in H. eapply eqitree_inv_bind_vis in H. des. *)
(*   - left. esplits; eauto. { f. eauto. } i. f. eauto. *)
(*   - right. esplits; eauto. { f. eauto. } f. eauto. *)
(* Qed. *)

Lemma mapC_grespectful: grespectful mapC.
Proof.
  econs; eauto with paco.
  ii. inv PR. csc.
  (* revert_until GF. gcofix CIH. i. *)
  eapply GF in SIM.
  remember (` r0 : x0 <- x5;; Ret (f0 r0)) as tmp0.
  remember (` r1 : x1 <- x6;; Ret (f1 r1)) as tmp1.
  (* remember (` r0 : x7 <- x12;; Ret (f0 r0)) as tmp0. *)
  (* remember (` r1 : x8 <- x13;; Ret (f1 r1)) as tmp1. *)
  revert Heqtmp0 Heqtmp1.
  rename r into rrr.
  induction SIM using _simg_ind2; intros EQ0 EQ1; irw in EQ0; irw in EQ1; csc.
  { sym in EQ0. eapply eqitree_inv_bind_ret in EQ0.
    sym in EQ1. eapply eqitree_inv_bind_ret in EQ1.
    des. clarify. gstep. econs 1; eauto. }
  { sym in EQ0. eapply eqitree_inv_bind_vis in EQ0.
    sym in EQ1. eapply eqitree_inv_bind_vis in EQ1.
    des; rewrite <- bind_trigger in *; clarify.
    - gstep. econs 2; eauto. i. subst. gbase.
Abort.

Theorem simg_map
        R0 R1 (RR: Ord.t -> Ord.t -> R0 -> R1 -> Prop)
        S0 S1 g0 g1
        f0 f1 i0 i1
        (SIM: simg (fun f_src f_tgt (s0: S0) (s1: S1) => forall r0 r1,
                        s0 = g0 r0 -> s1 = g1 r1 -> RR f_src f_tgt r0 r1) f0 f1
                (g0 <$> i0) (g1 <$> i1))
  :
  simg RR f0 f1 i0 i1
.
Proof.
  i. ginit. revert_until g1. gcofix CIH. i.
  unfold fmap in *. ss. unfold ITree.map in *.
  remember (` x : R0 <- i0;; Ret (g0 x)) as tmp0.
  remember (` x : R1 <- i1;; Ret (g1 x)) as tmp1.
  revert Heqtmp0 Heqtmp1.
  (* remember (fun (s0 : S0) (s1 : S1) => *)
  (*          forall (r0 : R0) (r1 : R1), s0 = g0 r0 -> s1 = g1 r1 -> RR r0 r1) as tmp2. *)
  (* revert Heqtmp2. *)
  induction SIM using simg_ind; intros EQ0 EQ1; irw in EQ0; irw in EQ1; csc.
  - sym in EQ0. apply eqitree_inv_bind_ret in EQ0.
    sym in EQ1. apply eqitree_inv_bind_ret in EQ1.
    des. subst. clarify. gstep. econs; eauto.
  - sym in EQ0. eapply eqitree_inv_bind_vis in EQ0.
    sym in EQ1. eapply eqitree_inv_bind_vis in EQ1. des; clarify.
    rewrite <- ! bind_trigger. gstep. econs; eauto.
    i. subst. gbase. eapply CIH. rewrite EQ3. rewrite EQ2. eauto.
  - sym in EQ0. eapply eqitree_inv_bind_tau in EQ0. des; clarify.
    guclo simg_indC_spec. econs; eauto.
Abort.

(** YJ: I think we need an induction principle without the tail. @minki ? **)

Lemma simg_ret_inv_l
        R0 R1 R2 (eq0: R0 -> R2 -> Prop) (eq1: R1 -> R2 -> Prop)
        f0 f1 r0 r1 i1
        (IMPL: forall r2, eq0 r0 r2 -> eq1 r1 r2)
        (SIM: simg (fun _ _ => eq0) f0 f1 (Ret r0) i1)
  :
  simg (fun _ _ => eq1) f0 f1 (Ret r1) i1
.
Proof.
  i. ginit. revert_until eq1. gcofix CIH. i.
  remember (Ret r0) as tmp. revert Heqtmp.
  induction SIM using simg_ind; intros EQ; irw in EQ; csc.
  - gstep. econs; eauto.
  - guclo simg_indC_spec. econs; et.
  - guclo simg_indC_spec. econs; et.
    i. spc SIM. des. eapply IH. ss.
  - des. guclo simg_indC_spec. econs; et.
  - gstep. econs; et. gbase. eapply CIH; et.
Qed.

Lemma simg_ret_inv_r
        R0 R1 R2 (eq0: R0 -> R1 -> Prop)
        (eq1: R0 -> R2 -> Prop)
        f0 f1 i0 r1 r2
        (IMPL: forall r0, eq0 r0 r1 -> eq1 r0 r2)
        (SIM: simg (fun _ _ => eq0) f0 f1 i0 (Ret r1))
  :
  simg (fun _ _ => eq1) f0 f1 i0 (Ret r2)
.
Proof.
  i. ginit. revert_until eq1. gcofix CIH. i.
  remember (Ret r1) as tmp. revert Heqtmp.
  induction SIM using simg_ind; intros EQ; irw in EQ; csc.
  - gstep. econs; eauto.
  - guclo simg_indC_spec. econs; et.
  - des. guclo simg_indC_spec. econs; et.
  - guclo simg_indC_spec. econs; et.
    i. spc SIM. des. eapply IH. ss.
  - gstep. econs; et. gbase. eapply CIH; et.
Qed.




Lemma simg_trans_aux
  R0 R1 R2
  (eq0: R0 -> R1 -> Prop)
  (eq1: R1 -> R2 -> Prop)
  itr0 itr1 itr2
  f0 f1 f2 f3
  (SIM0: simg (fun _ _ => eq0) f0 f1 itr0 itr1)
  (SIM1: simg (fun _ _ => eq1) f2 f3 itr1 itr2)
  :
  <<SIM: simg (fun _ _ r0 r2 => exists r1, eq0 r0 r1 /\ eq1 r1 r2)
           (f0) (f3) itr0 itr2>>
.
Proof.
  assert(MON: postcond_mon
                (fun _ _ r0 r2 => exists r1 : R1, eq0 r0 r1 /\ eq1 r1 r2)).
  { r. ii. des. esplits; eauto. }
  ginit.
  revert_until eq1.
  gcofix CIH.
  i.
  revert SIM1. revert itr2. revert f2 f3.
  induction SIM0 using simg_ind; i; clarify.
  - gfinal. right. eapply paco7_mon.
    { eapply simg_bot_flag_up; et. eapply simg_ret_inv_l in SIM1.
      { ginit. guclo flagC_spec. econs; eauto with paco; try refl. }
      ii. ss. esplits; et. }
    i; ss.
  - remember (` x : _ <- trigger (Syscall fn varg rvs);; ktr_tgt0 x) as tmp. revert Heqtmp.
    eapply simg_bot_flag_up in SIM1.
    instantiate (1:=f3) in SIM1. instantiate (1:=f_src) in SIM1.
    induction SIM1 using simg_ind; intros ?EQ; irw in EQ; csc.
    + change (fun x : Any.t => ktr_src1 x) with ktr_src1 in *.
      change (fun x : Any.t => ktr_tgt0 x) with ktr_tgt0 in *. subst.
      gstep. econs; eauto. i. subst. gbase. eapply CIH; et.
    + guclo simg_indC_spec. econs; eauto. eapply IHSIM1. irw; ss.
    + guclo simg_indC_spec. econs; eauto. i. spc SIM0. des. eapply IH. irw; ss.
    + guclo simg_indC_spec. econs; eauto. des. esplits; et. eapply IH. irw; ss.
    + gstep. econs; eauto. gbase. eapply CIH; et.
      rewrite <- bind_trigger. ginit. gstep. econs; eauto. i. subst. gfinal. right. eapply paco7_mon; try eapply SIM; ss.
  - guclo simg_indC_spec. econs; eauto.
  - eapply IHSIM0. eapply simg_tau_inv_l; et.
  - des. guclo simg_indC_spec. econs; eauto.
  - remember (` x : _ <- trigger (Choose X);; ktr_tgt0 x) as tmp. revert Heqtmp.
    eapply simg_bot_flag_up in SIM1.
    instantiate (1:=f3) in SIM1. instantiate (1:=f_src) in SIM1.
    induction SIM1 using simg_ind; intros ?EQ; irw in EQ; csc.
    + guclo simg_indC_spec. econs; et. eapply IHSIM1; et. irw; ss.
    + assert(ktr_src0 = ktr_tgt0) by eauto. subst. clear_tac.
      des. eapply SIM; et.
    + guclo simg_indC_spec. econs; et. i. eapply SIM0; et. irw; ss.
    + des. guclo simg_indC_spec. econs; et. esplits; et. eapply IH; et. irw; ss.
    + gstep. econs; eauto. gbase. eapply CIH; et.
      ginit. guclo simg_indC_spec. rewrite <- bind_trigger. econs; et. i.
      spc SIM. des.
      eapply simg_bot_flag_up in SIM0. gfinal. right. eapply paco7_mon; eauto.
  - guclo simg_indC_spec. econs; eauto.
    i. spc SIM. des. eapply IH; et.
  - des. eapply IH; et. instantiate (1:=f2). clear IH. clear_tac. clear SIM0.
    eapply simg_take_inv_l; et.
  - revert SIM0. revert itr_src. induction SIM1 using simg_ind; i; clarify.
    + eapply simg_bot_flag_up in SIM0.
      eapply simg_ret_inv_r in SIM0.
      { gfinal. right. eapply paco7_mon; et. i; ss. }
      ss. esplits; et.
    + remember (` x : _ <- trigger (Syscall fn varg rvs);; ktr_src0 x) as tmp. revert Heqtmp.
      rename SIM0 into T.
      eapply simg_bot_flag_up in T.
      instantiate (1:=0%ord) in T. instantiate (1:=0%ord) in T.
      remember (Ord.from_nat 0) as tmp1 in T. revert Heqtmp1.
      induction T using simg_ind; intros ??EQ; irw in EQ; csc.
      * assert(ktr_tgt1 = ktr_src0) by eauto; subst.
        gstep. econs; eauto. i. subst. gbase. eapply CIH; et.
      * guclo simg_indC_spec. econs; eauto. eapply IHT; ss. irw; ss.
      * guclo simg_indC_spec. des. econs; eauto. esplits; et. eapply IH; ss. irw; ss.
      * guclo simg_indC_spec. econs; eauto. i. eapply SIM0; ss. irw; ss.
      * contradict TGT0.
        admit "ez".
    + eapply IHSIM1. eapply simg_tau_inv_r; et.
    + guclo simg_indC_spec. econs; eauto.
    + des. eapply IH; et. eapply simg_choose_inv_r; et.
    + guclo simg_indC_spec. econs; eauto.
      i. spc SIM. des. eapply IH; et.
    + remember (` x : _ <- trigger (Take X);; ktr_src0 x) as tmp. revert Heqtmp.
      rename SIM0 into T.
      eapply simg_bot_flag_up in T.
      instantiate (1:=0%ord) in T. instantiate (1:=0%ord) in T.
      remember (Ord.from_nat 0) as tmp1 in T. revert Heqtmp1.
      induction T using simg_ind; intros ??EQ; irw in EQ; csc.
      * guclo simg_indC_spec. econs; et. eapply IHT; et. irw; ss.
      * guclo simg_indC_spec. econs; et. des. esplits; et. eapply IH; et. irw; ss.
      * guclo simg_indC_spec. econs; et. i. eapply SIM0; et. irw; ss.
      * assert(ktr_src0 = ktr_tgt0) by eauto. subst. clear_tac.
        des. spc SIM. des. eapply IH0; et.
        eapply simg_bot_flag_up; eauto.
      * contradict TGT0.
        admit "ez".
    + des. guclo simg_indC_spec. econs; et.
    + gstep. econs; eauto. gbase. eapply CIH; et.
Unshelve.
  all: ss.
Qed.

Theorem simg_trans
  R
  (itr0 itr1 itr2: itree _ R)
  f0 f1 f2 f3
  (SIM0: simg (fun _ _ => eq) f0 f1 itr0 itr1)
  (SIM1: simg (fun _ _ => eq) f2 f3 itr1 itr2)
  :
  <<SIM: simg (fun _ _ => eq) (f0) (f3) itr0 itr2>>
.
Proof.
  exploit simg_trans_aux.
  { eapply SIM0. }
  { eapply SIM1. }
  intro T; des.
  replace (fun r0 r2 : R => exists r1 : R, r0 = r1 /\ r1 = r2) with (@eq R) in T; ss.
  extensionality r0. extensionality r1.
  eapply prop_ext. split; i; des; clarify; et.
Qed.

End TRANS.

Context {CONFS CONFT: EMSConfig}.
Hypothesis (FINSAME: (@finalize CONFS) = (@finalize CONFT)).

Theorem adequacy_global_itree itr_src itr_tgt
        (SIM: simg (fun _ _ => eq) 0 0 itr_src itr_tgt)
  :
    Beh.of_program (@ModSemL.compile_itree CONFT itr_tgt)
    <1=
    Beh.of_program (@ModSemL.compile_itree CONFS itr_src).
Proof.
  unfold Beh.of_program. ss.
  remember false as o_src0 in SIM at 1.
  remember false as o_tgt0 in SIM at 1. clear Heqo_src0 Heqo_tgt0.
  i. eapply adequacy_aux; et.
  instantiate (1:=o_tgt0). instantiate (1:=o_src0). clear x0 PR.
  generalize itr_tgt at 1 as md_tgt.
  generalize itr_src at 1 as md_src. i. ginit.
  revert o_src0 o_tgt0 itr_src itr_tgt SIM. gcofix CIH.
  i. induction SIM using simg_ind; i; clarify.
  { gstep. destruct (finalize r_tgt) eqn:T.
    { eapply sim_fin; ss; cbn; des_ifs; rewrite FINSAME in *; clarify. }
    { eapply sim_angelic_src.
      { cbn. des_ifs; rewrite FINSAME in *; clarify. }
      i. exfalso. inv STEP.
    }
  }
  { gstep. eapply sim_vis; ss. i.
    eapply step_trigger_syscall_iff in STEP. des. clarify.
    esplits.
    { eapply step_trigger_syscall; et. }
    { gbase. eapply CIH. hexploit SIM; et. }
  }
  { guclo sim_indC_spec. eapply sim_indC_demonic_src; ss.
    esplits; eauto. eapply step_tau; et.
  }
  { guclo sim_indC_spec. eapply sim_indC_demonic_tgt; ss. i.
    eapply step_tau_iff in STEP. des. clarify.
  }
  { des. guclo sim_indC_spec. eapply sim_indC_demonic_src; ss.
    esplits; eauto. eapply step_trigger_choose; et.
  }
  { guclo sim_indC_spec. eapply sim_indC_demonic_tgt; ss.
    i.  eapply step_trigger_choose_iff in STEP. des. clarify.
    hexploit (SIM x); et. i. des. esplits; eauto.
  }
  { guclo sim_indC_spec. eapply sim_indC_angelic_src; ss. i.
    eapply step_trigger_take_iff in STEP. des. clarify.
    hexploit (SIM x); et. i. des. esplits; et.
  }
  { des. guclo sim_indC_spec. eapply sim_indC_angelic_tgt; ss.
    esplits; eauto. eapply step_trigger_take; et.
  }
  { gstep. eapply sim_progress; eauto. gbase. auto. }
Qed.


Variable md_src md_tgt: ModL.t.
Let ms_src: ModSemL.t := md_src.(ModL.enclose).
Let ms_tgt: ModSemL.t := md_tgt.(ModL.enclose).

Section ADEQUACY.
Hypothesis (SIM: simg eq false false (@ModSemL.initial_itr ms_src CONFS (Some (ModL.wf md_src))) (@ModSemL.initial_itr ms_tgt CONFT (Some (ModL.wf md_tgt)))).


Theorem adequacy_global: Beh.of_program (@ModL.compile _ CONFT md_tgt) <1= Beh.of_program (@ModL.compile _ CONFS md_src).
Proof.
  eapply adequacy_global_itree. eapply SIM.
Qed.
End ADEQUACY.
End SIM.

Hint Constructors _simg.
Hint Unfold simg.
Hint Resolve simg_mon: paco.
Hint Constructors flagC: core.
Hint Resolve flagC_mon: paco.
Hint Constructors bindR: core.
Hint Unfold bindC: core.
Hint Constructors simg_indC: core.
Hint Resolve sim_indC_mon: paco.


Variant _simg_safe
          (simg: forall R0 R1 (RR: R0 -> R1 -> Prop), Ord.t -> Ord.t -> (itree eventE R0) -> (itree eventE R1) -> Prop)
          {R0 R1} (RR: R0 -> R1 -> Prop) (f_src f_tgt: Ord.t): (itree eventE R0) -> (itree eventE R1) -> Prop :=
| simg_safe_ret
    r_src r_tgt
    (SIM: RR r_src r_tgt)
  :
    _simg_safe simg RR f_src f_tgt (Ret r_src) (Ret r_tgt)
| simg_safe_syscall
    ktr_src0 ktr_tgt0 fn varg rvs
    (SIM: forall x_src x_tgt (EQ: x_src = x_tgt), simg _ _ RR true true (ktr_src0 x_src) (ktr_tgt0 x_tgt))
  :
    _simg_safe simg RR f_src f_tgt (trigger (Syscall fn varg rvs) >>= ktr_src0) (trigger (Syscall fn varg rvs) >>= ktr_tgt0)

| simg_safe_tauL
    itr_src0 itr_tgt0
    (TAUL: True)
    (SIM: simg _ _ RR true f_tgt itr_src0 itr_tgt0)
  :
    _simg_safe simg RR f_src f_tgt (tau;; itr_src0) (itr_tgt0)
| simg_safe_tauR
    itr_src0 itr_tgt0
    (TAUR: True)
    (SIM: simg _ _ RR f_src true itr_src0 itr_tgt0)
  :
    _simg_safe simg RR f_src f_tgt (itr_src0) (tau;; itr_tgt0)

| simg_safe_chooseR
    X itr_src0 ktr_tgt0
    (CHOOSER: True)
    (SIM: forall x, simg _ _ RR f_src true itr_src0 (ktr_tgt0 x))
  :
    _simg_safe simg RR f_src f_tgt (itr_src0) (trigger (Choose X) >>= ktr_tgt0)

| simg_safe_takeL
    X ktr_src0 itr_tgt0
    (TAKEL: True)
    (SIM: forall x, simg _ _ RR true f_tgt (ktr_src0 x) itr_tgt0)
  :
    _simg_safe simg RR f_src f_tgt (trigger (Take X) >>= ktr_src0) (itr_tgt0)
.

Lemma simg_safe_spec:
  _simg_safe <8= gupaco7 _simg (cpn7 _simg).
Proof.
  i. eapply simg_indC_spec. inv PR.
  { econs; eauto. }
  { econs; eauto. }
  { econs; eauto. }
  { econs; eauto. }
  { econs; eauto. }
  { econs; eauto. }
Qed.
