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
    exists wfo f_tgt,
      simg_alt_exp wfo RR f_tgt itr_src itr_tgt.
  Proof.


End PROOF.
