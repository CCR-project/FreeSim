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
Require Import SimGlobalIndexTemp.
Require Import SimGlobalExplicit SimGlobalIndex2Explicit1.

Set Implicit Arguments.

Section PROOF.

  Definition RR_top {R0 R1} (RRp: Ord.t -> Ord.t -> R0 -> R1 -> Prop) (RR: R0 -> R1 -> Prop) :=
    forall o0 o1 r0 r1, (RRp o0 o1 r0 r1) -> (RR r0 r1).

  Let Ord_WF := mk_wf (Ord.lt_well_founded).

  Lemma gen_exp_implies_simg_exp
        R0 R1
        (RRp: Ord.t -> Ord.t -> R0 -> R1 -> Prop)
        (RR: R0 -> R1 -> Prop)
        (TOP: RR_top RRp RR)
        (itr_src: itree eventE R0)
        (itr_tgt: itree eventE R1)
        (f_src f_tgt: Ord.t)
        (g_src g_tgt: (@ord_tree_WF ((itree eventE R0) * (itree eventE R1))).(T))
        (GEN: gen_exp (@ord_tree_WF ((itree eventE R0) * (itree eventE R1)))
                      RRp f_src f_tgt (g_src) (itr_src) (g_tgt) (itr_tgt))
    :
    exists wf_exp e_src e_tgt,
      simg_exp wf_exp RR e_src e_tgt itr_src itr_tgt.
  Proof.
    set (wf_gen:= (@ord_tree_WF ((itree eventE R0) * (itree eventE R1)))).
    exists (prod_WF Ord_WF wf_gen). exists (f_tgt, g_src), (f_src, g_tgt).
    ginit. revert_until TOP.
    gcofix CIH. i. move f_src before CIH. revert_until f_src.
    pattern f_src. revert f_src. eapply (well_founded_induction Ord.lt_well_founded).
    intros f_src IHo. i. induction GEN.
    { gstep. econs 1. eapply TOP. eauto. }
    { gstep. econs 2. i. specialize (GEN x_src x_tgt EQ).
      gfinal. left. eapply CIH. eapply GEN. }
    { gstep. econs 3. instantiate (1:= (f_tgt, g_src0)). econs 2; auto.
      gfinal. left. eapply CIH. eauto. }
    { gstep. econs 4. instantiate (1:= (f_src, g_tgt0)). econs 2; auto.
      gfinal. left. eapply CIH. eauto. }
    { gstep. econs 5. instantiate (1:= (f_tgt, g_src0)). econs 2; auto.
      des. exists x. gfinal. left. eapply CIH. eauto. }
    { gstep. econs 6. instantiate (1:= (f_src, g_tgt0)). econs 2; auto.
      i. gfinal. left. eapply CIH. eauto. }
    { gstep. econs 7. instantiate (1:= (f_tgt, g_src0)). econs 2; auto.
      i. gfinal. left. eapply CIH. eauto. }
    { gstep. econs 8. instantiate (1:= (f_src, g_tgt0)). econs 2; auto.
      des. exists x. gfinal. left. eapply CIH. eauto. }
    { eapply simg_aux_gen_exp in SIM. des.
      guclo simg_exp_leC_spec. econs.
      3:{ eapply IHo. 2: eauto. auto. }
      { right. econs 1. auto. }
      { right. econs 1. auto. }
    }
  Qed.



  Theorem simg_implies_simg_exp
          R0 R1
          (RRp: Ord.t -> Ord.t -> R0 -> R1 -> Prop)
          (RR: R0 -> R1 -> Prop)
          (TOP: RR_top RRp RR)
          (itr_src: itree eventE R0)
          (itr_tgt: itree eventE R1)
          (f_src f_tgt: Ord.t)
          (SIM: simg RRp f_src f_tgt (itr_src) (itr_tgt))
    :
    exists wf_exp e_src e_tgt,
      simg_exp wf_exp RR e_src e_tgt itr_src itr_tgt.
  Proof.
    apply simg_implies_simg_aux in SIM.
    apply simg_aux_gen_exp in SIM.
    des. eapply gen_exp_implies_simg_exp in SIM; eauto.
  Qed.

End PROOF.
