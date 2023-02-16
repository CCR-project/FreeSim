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

Set Implicit Arguments.

Section SIM.

  Variant _simg_exp
          (simg_exp: forall R0 R1 (RR: Ord.t -> Ord.t -> R0 -> R1 -> Prop), Ord.t -> Ord.t -> (itree eventE R0) -> (itree eventE R1) -> Prop)
          {R0 R1} (RR: Ord.t -> Ord.t -> R0 -> R1 -> Prop) (f_src f_tgt: Ord.t): (itree eventE R0) -> (itree eventE R1) -> Prop :=
    | simg_exp_ret
        r_src r_tgt
        (SIM: RR f_src f_tgt r_src r_tgt)
      :
      _simg_exp simg_exp RR f_src f_tgt (Ret r_src) (Ret r_tgt)
    | simg_exp_syscall
        ktr_src0 ktr_tgt0 fn varg rvs
        f_src0 f_tgt0
        (SIM: forall x_src x_tgt (EQ: x_src = x_tgt), simg_exp _ _ RR f_src0 f_tgt0 (ktr_src0 x_src) (ktr_tgt0 x_tgt))
      :
      _simg_exp simg_exp RR f_src f_tgt (trigger (Syscall fn varg rvs) >>= ktr_src0) (trigger (Syscall fn varg rvs) >>= ktr_tgt0)

    | simg_exp_tauL
        itr_src0 itr_tgt0
        f_src0 f_tgt0
        (LT: Ord.lt f_src0 f_src)
        (SIM: @simg_exp _ _ RR f_src0 f_tgt0 itr_src0 itr_tgt0)
      :
      _simg_exp simg_exp RR f_src f_tgt (tau;; itr_src0) (itr_tgt0)
    | simg_exp_tauR
        itr_src0 itr_tgt0
        f_src0 f_tgt0
        (LT: Ord.lt f_tgt0 f_tgt)
        (SIM: @simg_exp _ _ RR f_src0 f_tgt0 itr_src0 itr_tgt0)
      :
      _simg_exp simg_exp RR f_src f_tgt (itr_src0) (tau;; itr_tgt0)

    | simg_exp_chooseL
        X ktr_src0 itr_tgt0
        f_src0 f_tgt0
        (LT: Ord.lt f_src0 f_src)
        (SIM: exists x, @simg_exp _ _ RR f_src0 f_tgt0 (ktr_src0 x) itr_tgt0)
      :
      _simg_exp simg_exp RR f_src f_tgt (trigger (Choose X) >>= ktr_src0) (itr_tgt0)
    | simg_exp_chooseR
        X itr_src0 ktr_tgt0
        f_src0 f_tgt0
        (LT: Ord.lt f_tgt0 f_tgt)
        (SIM: forall x, @simg_exp _ _ RR f_src0 f_tgt0 itr_src0 (ktr_tgt0 x))
      :
      _simg_exp simg_exp RR f_src f_tgt (itr_src0) (trigger (Choose X) >>= ktr_tgt0)

    | simg_exp_takeL
        X ktr_src0 itr_tgt0
        f_src0 f_tgt0
        (LT: Ord.lt f_src0 f_src)
        (SIM: forall x, @simg_exp _ _ RR f_src0 f_tgt0 (ktr_src0 x) itr_tgt0)
      :
      _simg_exp simg_exp RR f_src f_tgt (trigger (Take X) >>= ktr_src0) (itr_tgt0)
    | simg_exp_takeR
        X itr_src0 ktr_tgt0
        f_src0 f_tgt0
        (LT: Ord.lt f_tgt0 f_tgt)
        (SIM: exists x, @simg_exp _ _ RR f_src0 f_tgt0 itr_src0 (ktr_tgt0 x))
      :
      _simg_exp simg_exp RR f_src f_tgt (itr_src0) (trigger (Take X) >>= ktr_tgt0)
  .

  Definition simg_exp: forall R0 R1 (RR: Ord.t -> Ord.t -> R0 -> R1 -> Prop), Ord.t -> Ord.t -> (itree eventE R0) -> (itree eventE R1) -> Prop := paco7 _simg_exp bot7.

  Lemma simg_exp_mon: monotone7 _simg_exp.
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
  Hint Resolve simg_exp_mon: paco.
  Hint Resolve cpn7_wcompat: paco.

  Definition postcond_mon_exp {R0 R1: Type} (RR: Ord.t -> Ord.t -> R0 -> R1 -> Prop): Prop :=
    forall f_src0 f_src1 f_tgt0 f_tgt1 r_src r_tgt
      (LE: (f_src0 <= f_src1)%ord) (LE: (f_tgt0 <= f_tgt1)%ord),
      RR f_src0 f_tgt0 r_src r_tgt -> RR f_src1 f_tgt1 r_src r_tgt.

  Variant simg_exp_leC
          (simg_exp: forall R0 R1 (RR: Ord.t -> Ord.t -> R0 -> R1 -> Prop), Ord.t -> Ord.t -> (itree eventE R0) -> (itree eventE R1) -> Prop)
          {R0 R1} (RR: Ord.t -> Ord.t -> R0 -> R1 -> Prop) (f_src f_tgt: Ord.t): (itree eventE R0) -> (itree eventE R1) -> Prop :=
    | simg_exp_ltC_intro
        itr_src itr_tgt
        f_src0 f_tgt0
        (MON: postcond_mon_exp RR)
        (LES: Ord.le f_src0 f_src)
        (LET: Ord.le f_tgt0 f_tgt)
        (SIM: simg_exp _ _ RR f_src0 f_tgt0 (itr_src) (itr_tgt))
      :
      simg_exp_leC simg_exp RR f_src f_tgt (itr_src) (itr_tgt)
  .

  Lemma simg_exp_leC_mon: monotone7 simg_exp_leC.
  Proof.
    ii. inv IN. econs; eauto.
  Qed.
  Hint Resolve simg_exp_leC_mon: paco.

  Lemma simg_exp_leC_spec:
    simg_exp_leC <8= gupaco7 _simg_exp (cpn7 _simg_exp).
  Proof.
    eapply wrespect7_uclo; eauto with paco.
    econs; eauto with paco. i. inv PR. eapply GF in SIM. inv SIM.
    { econs 1. eapply MON. 3: eauto. all: auto. }
    { econs 2. i. clarify. eapply rclo7_base. eauto. }
    { econs 3. eapply Ord.lt_le_lt. 2: eauto. eauto. eapply rclo7_base. eauto. }
    { econs 4. eapply Ord.lt_le_lt. 2: eauto. eauto. eapply rclo7_base. eauto. }
    { econs 5. eapply Ord.lt_le_lt. 2: eauto. eauto. des. exists x. eapply rclo7_base. eauto. }
    { econs 6. eapply Ord.lt_le_lt. 2: eauto. eauto. i. eapply rclo7_base. eauto. }
    { econs 7. eapply Ord.lt_le_lt. 2: eauto. eauto. i. eapply rclo7_base. eauto. }
    { econs 8. eapply Ord.lt_le_lt. 2: eauto. eauto. des. exists x. eapply rclo7_base. eauto. }
  Qed.

End SIM.

Hint Constructors _simg_exp.
Hint Unfold simg_exp.
Hint Resolve simg_exp_mon: paco.
Hint Resolve cpn7_wcompat: paco.
