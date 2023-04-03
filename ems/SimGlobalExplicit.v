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

Set Implicit Arguments.

Section SIM.

  Variable E: Type -> Type.
  Variable wfo: WF.

  Variant _simg_exp
          (simg_exp: forall R0 R1 (RR: R0 -> R1 -> Prop), wfo.(T) -> wfo.(T) -> (itree (E +' eventE) R0) -> (itree (E +' eventE) R1) -> Prop)
          {R0 R1} (RR: R0 -> R1 -> Prop) (f_src f_tgt: wfo.(T)): (itree (E +' eventE) R0) -> (itree (E +' eventE) R1) -> Prop :=
    | simg_exp_ret
        r_src r_tgt
        (SIM: RR r_src r_tgt)
      :
      _simg_exp simg_exp RR f_src f_tgt (Ret r_src) (Ret r_tgt)
    | simg_exp_syscall
        ktr_src0 ktr_tgt0 fn varg rvs
        f_src0 f_tgt0
        (SIM: forall x_src x_tgt (EQ: x_src = x_tgt), simg_exp _ _ RR f_src0 f_tgt0 (ktr_src0 x_src) (ktr_tgt0 x_tgt))
      :
      _simg_exp simg_exp RR f_src f_tgt (trigger (SyscallOut fn varg rvs) >>= ktr_src0) (trigger (SyscallOut fn varg rvs) >>= ktr_tgt0)

    | simg_exp_tauL
        itr_src0 itr_tgt0
        f_src0 f_tgt0
        (LT: wfo.(lt) f_src0 f_src)
        (SIM: @simg_exp _ _ RR f_src0 f_tgt0 itr_src0 itr_tgt0)
      :
      _simg_exp simg_exp RR f_src f_tgt (tau;; itr_src0) (itr_tgt0)
    | simg_exp_tauR
        itr_src0 itr_tgt0
        f_src0 f_tgt0
        (LT: wfo.(lt) f_tgt0 f_tgt)
        (SIM: @simg_exp _ _ RR f_src0 f_tgt0 itr_src0 itr_tgt0)
      :
      _simg_exp simg_exp RR f_src f_tgt (itr_src0) (tau;; itr_tgt0)

    | simg_exp_chooseL
        X ktr_src0 itr_tgt0
        f_src0 f_tgt0
        (LT: wfo.(lt) f_src0 f_src)
        (SIM: exists x, @simg_exp _ _ RR f_src0 f_tgt0 (ktr_src0 x) itr_tgt0)
      :
      _simg_exp simg_exp RR f_src f_tgt (trigger (Choose X) >>= ktr_src0) (itr_tgt0)
    | simg_exp_chooseR
        X itr_src0 ktr_tgt0
        f_src0 f_tgt0
        (LT: wfo.(lt) f_tgt0 f_tgt)
        (SIM: forall x, @simg_exp _ _ RR f_src0 f_tgt0 itr_src0 (ktr_tgt0 x))
      :
      _simg_exp simg_exp RR f_src f_tgt (itr_src0) (trigger (Choose X) >>= ktr_tgt0)

    | simg_exp_takeL
        X ktr_src0 itr_tgt0
        f_src0 f_tgt0
        (LT: wfo.(lt) f_src0 f_src)
        (SIM: forall x, @simg_exp _ _ RR f_src0 f_tgt0 (ktr_src0 x) itr_tgt0)
      :
      _simg_exp simg_exp RR f_src f_tgt (trigger (Take X) >>= ktr_src0) (itr_tgt0)
    | simg_exp_takeR
        X itr_src0 ktr_tgt0
        f_src0 f_tgt0
        (LT: wfo.(lt) f_tgt0 f_tgt)
        (SIM: exists x, @simg_exp _ _ RR f_src0 f_tgt0 itr_src0 (ktr_tgt0 x))
      :
      _simg_exp simg_exp RR f_src f_tgt (itr_src0) (trigger (Take X) >>= ktr_tgt0)

    | simg_exp_eventE
        X (e: E X) ktr_src0 ktr_tgt0
        f_src0 f_tgt0
        (SIM: forall x_src x_tgt (EQ: x_src = x_tgt), simg_exp _ _ RR f_src0 f_tgt0 (ktr_src0 x_src) (ktr_tgt0 x_tgt))
      :
      _simg_exp simg_exp RR f_src f_tgt (trigger e >>= ktr_src0) (trigger e >>= ktr_tgt0)
  .

  Definition simg_exp: forall R0 R1 (RR: R0 -> R1 -> Prop), wfo.(T) -> wfo.(T) -> (itree (E +' eventE) R0) -> (itree (E +' eventE) R1) -> Prop := paco7 _simg_exp bot7.

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
    { econs 9; eauto. }
  Qed.
  Hint Resolve simg_exp_mon: paco.
  Hint Resolve cpn7_wcompat: paco.


  Variant simg_exp_leC
          (simg_exp: forall R0 R1 (RR: R0 -> R1 -> Prop), wfo.(T) -> wfo.(T) -> (itree (E +' eventE) R0) -> (itree (E +' eventE) R1) -> Prop)
          {R0 R1} (RR: R0 -> R1 -> Prop) (f_src f_tgt: wfo.(T)): (itree (E +' eventE) R0) -> (itree (E +' eventE) R1) -> Prop :=
    | simg_exp_leC_intro
        itr_src itr_tgt
        f_src0 f_tgt0
        (LES: wfo.(le) f_src0 f_src)
        (LET: wfo.(le) f_tgt0 f_tgt)
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
    econs; eauto with paco. i. inv PR.
    eapply GF in SIM. inv SIM.
    { econs 1. auto. }
    { econs 2. i. clarify. eapply rclo7_base. eauto. }
    { destruct LES; clarify.
      - econs 3; eauto. eapply rclo7_base. eauto.
      - econs 3. eauto. eapply rclo7_clo. econs. right; eauto. left; eauto.
        eapply rclo7_base; eauto.
    }
    { destruct LET; clarify.
      - econs 4; eauto. eapply rclo7_base. eauto.
      - econs 4. eauto. eapply rclo7_clo. econs. left; eauto. right; eauto.
        eapply rclo7_base; eauto.
    }
    { des. destruct LES; clarify.
      - econs 5; eauto. eexists. eapply rclo7_base. eauto.
      - econs 5. eauto. eexists. eapply rclo7_clo. econs. right; eauto. left; eauto.
        eapply rclo7_base; eauto.
    }
    { destruct LET; clarify.
      - econs 6; eauto. i. eapply rclo7_base. eauto.
      - econs 6. eauto. i. eapply rclo7_clo. econs. left; eauto. right; eauto.
        eapply rclo7_base; eauto.
    }
    { destruct LES; clarify.
      - econs 7; eauto. i. eapply rclo7_base. eauto.
      - econs 7. eauto. i. eapply rclo7_clo. econs. right; eauto. left; eauto.
        eapply rclo7_base; eauto.
    }
    { des. destruct LET; clarify.
      - econs 8; eauto. eexists. eapply rclo7_base. eauto.
      - econs 8. eauto. eexists. eapply rclo7_clo. econs. left; eauto. right; eauto.
        eapply rclo7_base; eauto.
    }
    { econs 9. i. clarify. eapply rclo7_base. eauto. }
  Qed.

End SIM.

Hint Constructors _simg_exp.
Hint Unfold simg_exp.
Hint Resolve simg_exp_mon: paco.
Hint Resolve cpn7_wcompat: paco.
