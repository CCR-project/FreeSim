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

  Lemma src_aux
        R0 R1 (RR: R0 -> R1 -> Prop)
        (wf_exp : WF)
        (wfo := option_bot_WF (prod_WF wf_exp wf_exp) : WF)
        (r : forall x x0 : Type, (x -> x0 -> Prop) -> T wfo -> itree eventE x -> itree eventE x0 -> Prop)
        (CIH : forall (itr_src : itree eventE R0) (itr_tgt : itree eventE R1) (f_src f_tgt : T wf_exp),
            simg_exp wf_exp RR f_src f_tgt itr_src itr_tgt ->
            r R0 R1 RR (Some (f_tgt, f_src)) itr_src itr_tgt)
        (f_src0 : T wf_exp)
        (f_tgt : T wf_exp)
        (itr_tgt : itree eventE R1)
        (f_src : T wf_exp)
        (itr_src0 : itree eventE R0)
        (f_tgt0 : T wf_exp)
        (LT : lt wf_exp f_src0 f_src)
        (SIM : paco7 (_simg_exp wf_exp) bot7 R0 R1 RR f_src0 f_tgt0 itr_src0 itr_tgt)
    :
    (tt_step
       (fun (ktr_tgt : itree eventE R1) =>
          exists exp0 : T wfo,
            gpaco6 (_simg_alt_exp wfo) (cpn6 (_simg_alt_exp wfo)) r r R0 R1 RR exp0 itr_src0 ktr_tgt)
       itr_tgt) \/
      (exists exp0 : T wfo,
          gpaco6 (_simg_alt_exp wfo) (cpn6 (_simg_alt_exp wfo)) r r R0 R1 RR exp0 itr_src0 itr_tgt /\
            lt wfo exp0 (Some (f_tgt, f_src))).
  Proof.
    move f_src0 before CIH. revert_until f_src0. pattern f_src0. revert f_src0.
    apply (well_founded_induction wf_exp.(wf)). intros f_src0 IHs. i.
    punfold SIM. inv SIM.
    { right. exists None. split. gstep. left. esplits; eauto. all: econs; eauto. }
    { right. exists (Some (f_tgt, f_src0)). split.
      2:{ econs. econs 2; eauto. }
      gstep. right. left. exists (fn, varg, rvs). splits; [econs; eauto| econs; eauto |].
      i. specialize (SIM0 _ _ EQ). pclearbot; clarify.
      econs; eauto. econs; eauto.
      exists (Some (f_tgt1, f_src1)). gfinal. left. eapply CIH; eauto.
    }
    { pclearbot. right. exists (Some (f_tgt, f_src0)). split.
      2:{ econs. econs 2; eauto. }
      gstep. do 2 right. right. econs 1. eapply IHs; eauto.
    }
    { pclearbot. left. econs 1. exists (Some (f_tgt1, f_src1)). gfinal. left. auto. }
    { des. pclearbot. right. exists (Some (f_tgt, f_src0)). split.
      2:{ econs. econs 2; eauto. }
      gstep. do 2 right. right. econs 2. exists x. eapply IHs; eauto.
    }
    { pclearbot. left. econs 2. i. specialize (SIM0 x).
      exists (Some (f_tgt1, f_src1)). gfinal. left. auto.
    }
    { pclearbot. right. exists (Some (f_tgt, f_src0)). split.
      2:{ econs. econs 2; eauto. }
      gstep. do 2 right. right. econs 3. i. specialize (SIM0 x). eapply IHs; eauto.
    }
    { des. pclearbot. left. econs 3. exists x. i. exists (Some (f_tgt1, f_src1)). gfinal. left. auto. }
  Qed.

  Theorem simg_exp_implies_simg_alt_exp
          R0 R1 (RR: R0 -> R1 -> Prop)
          (itr_src: itree eventE R0)
          (itr_tgt: itree eventE R1)
          (wf_exp: WF)
          (f_src f_tgt: wf_exp.(T))
          (SIM: simg_exp wf_exp RR f_src f_tgt (itr_src) (itr_tgt))
    :
    exists wfo exp,
      simg_alt_exp wfo RR exp itr_src itr_tgt.
  Proof.
    set (wfo := option_bot_WF (prod_WF wf_exp wf_exp)).
    Local Opaque option_bot_WF prod_WF. move wfo before RR.
    exists wfo. exists (Some (f_tgt, f_src)).
    ginit. revert_until wfo. gcofix CIH. i.
    punfold SIM. inv SIM.
    { gstep. left. esplits; eauto. all: econs; eauto. }
    { gstep. right. left. exists (fn, varg, rvs). splits; [econs; eauto | econs; eauto |].
      i. specialize (SIM0 _ _ EQ). pclearbot; clarify.
      econs; eauto. econs; eauto.
      exists (Some (f_tgt0, f_src0)). gfinal. left. eapply CIH; eauto.
    }
    { destruct SIM0 as [SIM | SIM]; clarify.
      gstep. do 2 right. right. econs 1.
      eapply src_aux; eauto.
    }
    { destruct SIM0 as [SIM | SIM]; clarify.
      gstep. do 2 right. left. econs 1.
      right. exists (Some (f_tgt0, f_src0)). split.
      2:{ econs. econs 1; auto. }
      gfinal. left; eauto.
    }
    { des. destruct SIM0 as [SIM | SIM]; clarify.
      gstep. do 2 right. right. econs 2. exists x.
      eapply src_aux; eauto.
    }
    { gstep. do 2 right. left. econs 2. i.
      right. exists (Some (f_tgt0, f_src0)). split.
      2:{ econs. econs 1; auto. }
      destruct (SIM0 x) as [SIM | SIM]; clarify.
      gfinal. left; eauto.
    }
    { gstep. do 2 right. right. econs 3. i.
      destruct (SIM0 x) as [SIM | SIM]; clarify.
      eapply src_aux; eauto.
    }
    { des. destruct SIM0 as [SIM | SIM]; clarify.
      gstep. do 2 right. left. econs 3. exists x.
      right. exists (Some (f_tgt0, f_src0)). split.
      2:{ econs. econs 1; auto. }
      gfinal. left; eauto.
    }
  Qed.

End PROOF.
