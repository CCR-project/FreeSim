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

Require Import SimGlobalExplicit SimGlobalIndex2Explicit.

Set Implicit Arguments.

Section PROOF.

  Lemma gen_exp_implies_simg_exp
        R0 R1 (RR: Ord.t -> Ord.t -> R0 -> R1 -> Prop)
        (itr_src: itree eventE R0)
        (itr_tgt: itree eventE R1)
        (f_src f_tgt: Ord.t)
        (g_src g_tgt: Ord.t)
        (GEN: gen_exp RR f_src f_tgt (g_src) (itr_src) (g_tgt) (itr_tgt))
    :
    simg_exp RR (f_tgt + g_src)%ord (f_src + g_tgt)%ord itr_src itr_tgt.
  Proof.
    ginit.
    revert_until RR.
    gcofix CIH. i. move f_src before CIH. revert_until f_src.
    pattern f_src. revert f_src. eapply (well_founded_induction Ord.lt_well_founded).
    intros f_src IHo. i. induction GEN.
    { gstep. econs 1. admit "RR". }
    { gstep. econs 2. i. specialize (GEN x_src x_tgt EQ). gfinal. left. eauto. }
    { gstep. econs 3. instantiate (1:= (f_tgt + g_src0)%ord). apply OrdArith.lt_add_r. auto.
      gfinal. left. eauto. }
    { gstep. econs 4. instantiate (1:= (f_src + g_tgt0)%ord). apply OrdArith.lt_add_r. auto.
      gfinal. left. eauto. }
    { gstep. econs 5. instantiate (1:= (f_tgt + g_src0)%ord). apply OrdArith.lt_add_r. auto.
      des. exists x. gfinal. left. eauto. }
    { gstep. econs 6. instantiate (1:= (f_src + g_tgt0)%ord). apply OrdArith.lt_add_r. auto.
      i. gfinal. left. eauto. }
    { gstep. econs 7. instantiate (1:= (f_tgt + g_src0)%ord). apply OrdArith.lt_add_r. auto.
      i. gfinal. left. eauto. }
    { gstep. econs 8. instantiate (1:= (f_src + g_tgt0)%ord). apply OrdArith.lt_add_r. auto.
      des. exists x. gfinal. left. eauto. }
    { assert (TODO: simg_aux RR f_src0 f_tgt0 itr_src itr_tgt ->
                    exists gs gt, gen_exp RR f_src0 f_tgt0 gs itr_src gt itr_tgt).
      { admit "TODO". }
      apply TODO in SIM. des. guclo simg_exp_leC_spec. econs.
      { admit "RR?". }
      3:{ eapply IHo. 2: eauto. auto. }
      { admit "needs lex-order". }
      { admit "needs lex-order". }

  Abort.


End PROOF.
