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
Require Import SimGlobalExplicit SimGlobalAlts.

Set Implicit Arguments.

Section PROOF.

  Theorem simg_exp_implies_simg_alt_exp
          R0 R1 (RR: R0 -> R1 -> Prop)
          (itr_src: itree eventE R0)
          (itr_tgt: itree eventE R1)
          (wf_exp: WF)
          (e_src e_tgt: wf_exp.(T))
          (SIM: simg_exp wf_exp RR e_src e_tgt (itr_src) (itr_tgt))
    :
    exists wfo exp,
      simg_alt_exp wfo RR exp itr_src itr_tgt.
  Proof.
    set (wfo := prod_WF wf_exp wf_exp). Local Opaque prod_WF.
    move wfo before RR. exists wfo. exists (e_tgt, e_src).
    ginit. revert_until wfo. gcofix CIH. i.
    move e_tgt before CIH. revert_until e_tgt. pattern e_tgt. revert e_tgt.
    apply (well_founded_induction wf_exp.(wf)). intros e_tgt IHt. i.
    punfold SIM. inv SIM.
    { gstep. left. esplits; eauto. all: econs; eauto. }
    { gstep. right. do 3 right. econs 1. right. exists (fn, varg, rvs). i. econs; eauto.
      econs 1. right. exists (fn, varg, rvs). i. econs; eauto.
      i. inversion H. specialize (SIM0 v v0 H1). destruct SIM0; clarify.
      exists (f_tgt0, f_src0). gfinal. left. eapply CIH; eauto.
    }
    { destruct SIM0 as [SIM | SIM]; clarify. 

    


End PROOF.
