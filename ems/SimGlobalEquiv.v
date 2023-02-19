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

Require Import WFLib.
Require Import SimGlobalIndexTemp
        SimGlobalAlts
        SimGlobalIndex2Explicit2
        SimGlobalExplicit2Alts
        SimGlobalAlts2Index.

Set Implicit Arguments.

Section EQUIV.

  Theorem eq1_simg_implies_simg_alt_exp
          R0 R1 (RR: R0 -> R1 -> Prop)
          (itr_src: itree eventE R0)
          (itr_tgt: itree eventE R1)
          (f_src f_tgt: Ord.t)
          (SIM: simg (fun _ _ => RR) f_src f_tgt (itr_src) (itr_tgt))
    :
    exists wfo exp,
      simg_alt_exp wfo RR exp itr_src itr_tgt.
  Proof.
    eapply simg_implies_simg_exp in SIM.
    { des. eapply simg_exp_implies_simg_alt_exp in SIM. eauto. }
    ss.
  Qed.

  Theorem eq2_simg_alt_exp_implies_simg_alt_imp
          R0 R1 (RR: R0 -> R1 -> Prop)
          (itr_src: itree eventE R0)
          (itr_tgt: itree eventE R1)
          wfo (exp: wfo.(T))
          (SIM: simg_alt_exp wfo RR exp (itr_src) (itr_tgt))
    :
    simg_alt_imp RR itr_src itr_tgt.
  Proof.
    eapply simg_alt_exp_implies_simg_alt_imp in SIM. auto.
  Qed.

  Theorem eq3_simg_alt_imp_implies_simg
          R0 R1 (RR: R0 -> R1 -> Prop)
          (itr_src: itree eventE R0)
          (itr_tgt: itree eventE R1)
          (SIM: simg_alt_imp RR (itr_src) (itr_tgt))
    :
    forall f_src f_tgt, simg (fun _ _ => RR) f_src f_tgt itr_src itr_tgt.
  Proof.
    i. eapply simg_alt_imp_implies_simg in SIM; eauto. ss.
  Qed.

  Corollary simg_bot_flag_up
            R0 R1 RR st_src st_tgt f_src0 f_tgt0 f_src f_tgt
            (SIM: @simg R0 R1 (fun _ _ => RR) f_src0 f_tgt0 st_src st_tgt)
    :
    simg (fun _ _ => RR) f_src f_tgt st_src st_tgt.
  Proof.
    eapply eq1_simg_implies_simg_alt_exp in SIM. des.
    eapply eq2_simg_alt_exp_implies_simg_alt_imp in SIM.
    eapply eq3_simg_alt_imp_implies_simg in SIM.
    eauto.
  Qed.

End EQUIV.
