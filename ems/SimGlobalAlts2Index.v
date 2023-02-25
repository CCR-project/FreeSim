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

Require Import SimGlobalAlts SimGlobalIndex.

Set Implicit Arguments.

Section PROOF.

  Variable E: Type -> Type.

  Definition RR_bot {R0 R1} (RRp: Ord.t -> Ord.t -> R0 -> R1 -> Prop) (RR: R0 -> R1 -> Prop) :=
    forall r0 r1, (RR r0 r1) -> (forall o0 o1, RRp o0 o1 r0 r1).

  Theorem simg_alt_imp_implies_simg
          R0 R1
          (RR: R0 -> R1 -> Prop)
          (RRp: Ord.t -> Ord.t -> R0 -> R1 -> Prop)
          (TOP: RR_bot RRp RR)
          (itr_src: itree (E +' eventE) R0)
          (itr_tgt: itree (E +' eventE) R1)
          (SIM: simg_alt_imp RR itr_src itr_tgt)
    :
    forall (f_src f_tgt: Ord.t), simg RRp f_src f_tgt (itr_src) (itr_tgt).
  Proof.
    ginit. revert_until TOP. gcofix CIH. i.
    revert_until SIM. induction SIM using simg_alt_imp_ind; i.
    { inv TGT. inv SRC. guclo simg_indC_spec. econs 1; eauto. all: refl. }
    { inv TGT. inv SRC. inv ARG. gstep. econs 2. i. specialize (SIM _ _ EQ).
      inv SIM. inv REL. clarify. rewrite ! bind_trigger in *.
      inv H0. apply inj_pair2 in H2. eapply equal_f in H2.
      inv H1. apply inj_pair2 in H0. eapply equal_f in H0.
      rewrite H0, H2 in REL0. gfinal. left. eapply CIH. auto.
    }
    { inv TGT. inv SRC. gstep. econs 10. i. specialize (SIM _ _ EQ).
      inv SIM. inv REL. clarify. rewrite ! bind_trigger in *.
      inv H0. apply inj_pair2 in H3. eapply equal_f in H3.
      inv H1. apply inj_pair2 in H4. eapply equal_f in H4.
      rewrite H3, H4 in REL0. gfinal. left. eapply CIH. auto.
    }
    { guclo simg_indC_spec. inv SIM.
      - econs; auto. des; eauto.
        guclo simg_indC_spec. inv REL; eauto.
        + econs; auto. gstep. econs 9. gfinal; left. eauto. all: eapply Ord.S_lt.
        + des. econs; auto. eexists. gstep. econs 9. gfinal; left. eauto. all: eapply Ord.S_lt.
        + econs; auto. i. gstep. econs 9. gfinal; left. eauto. all: eapply Ord.S_lt.
      - econs; auto. i. specialize (REL x). des; eauto. guclo simg_indC_spec. inv REL; eauto.
        + econs; auto. gstep. econs 9. gfinal; left. eauto. all: eapply Ord.S_lt.
        + des. econs; auto. eexists. gstep. econs 9. gfinal; left. eauto. all: eapply Ord.S_lt.
        + econs; auto. i. gstep. econs 9. gfinal; left. eauto. all: eapply Ord.S_lt.
      - destruct REL as [x REL]. econs; auto. exists x. des; eauto.
        guclo simg_indC_spec. inv REL; eauto.
        + econs; auto. gstep. econs 9. gfinal; left. eauto. all: eapply Ord.S_lt.
        + des. econs; auto. eexists. gstep. econs 9. gfinal; left. eauto. all: eapply Ord.S_lt.
        + econs; auto. i. gstep. econs 9. gfinal; left. eauto. all: eapply Ord.S_lt.
    }
    { guclo simg_indC_spec. inv SIM.
      - econs; auto. des; eauto. guclo simg_indC_spec. inv REL; eauto.
        + econs; auto. gstep. econs 9. gfinal; left. eauto. all: eapply Ord.S_lt.
        + econs; auto. i. gstep. econs 9. gfinal; left. eauto. all: eapply Ord.S_lt.
        + des. econs; auto. eexists. gstep. econs 9. gfinal; left. eauto. all: eapply Ord.S_lt.
      - destruct REL as [x REL]. econs; auto. exists x. des; eauto.
        guclo simg_indC_spec. inv REL; eauto.
        + econs; auto. gstep. econs 9. gfinal; left. eauto. all: eapply Ord.S_lt.
        + econs; auto. i. gstep. econs 9. gfinal; left. eauto. all: eapply Ord.S_lt.
        + des. econs; auto. eexists. gstep. econs 9. gfinal; left. eauto. all: eapply Ord.S_lt.
      - econs; auto. i. specialize (REL x). des; eauto. guclo simg_indC_spec. inv REL; eauto.
        + econs; auto. gstep. econs 9. gfinal; left. eauto. all: eapply Ord.S_lt.
        + econs; auto. i. gstep. econs 9. gfinal; left. eauto. all: eapply Ord.S_lt.
        + des. econs; auto. eexists. gstep. econs 9. gfinal; left. eauto. all: eapply Ord.S_lt.
    }
    Unshelve. all: exact f_src.
  Qed.

End PROOF.
