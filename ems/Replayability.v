Require Import Coqlib.
Set Implicit Arguments.


Module Galois.
  Record t A B: Type :=
    mk {
        alpha: (A -> Prop) -> (B -> Prop);
        gamma: (B -> Prop) -> (A -> Prop);
        alpha_mon: forall a0 a1 (LE: a0 <1= a1), alpha a0 <1= alpha a1;
        gamma_mon: forall b0 b1 (LE: b0 <1= b1), gamma b0 <1= gamma b1;
        adjunct_iso0: forall a b, (alpha a <1= b) -> (a <1= gamma b);
        adjunct_iso1: forall a b, (a <1= gamma b) -> (alpha a <1= b);
      }.

  Lemma counit A B (c: t A B)
    :
    forall b, c.(alpha) (c.(gamma) b) <1= b.
  Proof.
    i. eapply c.(adjunct_iso1) in PR; eauto.
  Qed.

  Lemma unit A B (c: t A B)
    :
    forall a, a <1= c.(gamma) (c.(alpha) a).
  Proof.
    i. eapply c.(adjunct_iso0) in PR; eauto.
  Qed.

  Program Definition refl A: t A A := mk id id _ _ _ _.
  Next Obligation.
    eapply H; eauto.
  Qed.

  Program Definition trans A B C (f: t A B) (g: t B C): t A C :=
    mk (compose g.(alpha) f.(alpha)) (compose f.(gamma) g.(gamma)) _ _ _ _.
  Next Obligation.
    unfold compose in *. eapply g.(alpha_mon); [|eapply PR].
    eapply f.(alpha_mon); eauto.
  Qed.
  Next Obligation.
    unfold compose in *. eapply f.(gamma_mon); [|eapply PR].
    eapply g.(gamma_mon); eauto.
  Qed.
  Next Obligation.
    eapply f.(adjunct_iso0); [|eapply PR].
    eapply g.(adjunct_iso0). eauto.
  Qed.
  Next Obligation.
    eapply g.(adjunct_iso1); [|eapply PR].
    eapply f.(adjunct_iso1). eauto.
  Qed.
End Galois.


Section REPLAY.
  Hint Resolve cpn1_wcompat: paco.

  Variable A: Type.
  Variable B: Type.
  Variable F: (A -> Prop) -> (A -> Prop).
  Variable G: (B -> Prop) -> (B -> Prop).
  Variable c: Galois.t A B.

  Definition replay := forall a, c.(Galois.alpha) (F a) <1= G (c.(Galois.alpha) a).

  Hypothesis F_mon: monotone1 F. Hint Resolve F_mon: paco.
  Hypothesis G_mon: monotone1 G. Hint Resolve G_mon: paco.
  Hypothesis REPLAY: replay.

  Lemma replay_coind_step r g a
        (STEP: a <1= F (c.(Galois.gamma) (gpaco1 G (cpn1 G) g g)))
    :
    a <1= c.(Galois.gamma) (gpaco1 G (cpn1 G) r g).
  Proof.
    eapply c.(Galois.adjunct_iso0). i. gstep. eapply G_mon.
    { eapply REPLAY. eapply c.(Galois.alpha_mon); [|eapply PR]. eapply STEP. }
    eapply (Galois.counit c).
  Qed.

  Lemma replay_implication
    :
    c.(Galois.alpha) (paco1 F bot1) <1= paco1 G bot1.
  Proof.
    ginit. gcofix CIH. eapply c.(Galois.adjunct_iso1).
    i. punfold PR. eapply replay_coind_step; [|eapply PR].
    i. eapply F_mon; eauto. eapply c.(Galois.adjunct_iso0).
    i. gbase. eapply CIH. eapply c.(Galois.alpha_mon); [|eapply PR1].
    i. pclearbot. auto.
  Qed.
End REPLAY.

Lemma replay_refl A (F: (A -> Prop) -> (A -> Prop))
  :
  replay F F (Galois.refl A).
Proof.
  rr. i. ss.
Qed.

Lemma replay_trans A B C
      (F: (A -> Prop) -> (A -> Prop))
      (G: (B -> Prop) -> (B -> Prop))
      (H: (C -> Prop) -> (C -> Prop))
      c0 c1
      (REPLAY0: replay F G c0)
      (REPLAY1: replay G H c1)
  :
  replay F H (Galois.trans c0 c1).
Proof.
  rr. i. ss. eapply REPLAY1. eapply c1.(Galois.alpha_mon); [|eapply PR].
  eapply REPLAY0.
Qed.


Require Import ITreelib.
From Ordinal Require Import Ordinal Arithmetic.
Require Import SimGlobalIndex.
Require Import SimGlobalAlts.

Lemma trigger_inj2 E X R (e0 e1: E X) (k0 k1: X -> itree E R)
      (EQ: trigger e0 >>= k0 = trigger e1 >>= k1)
  :
  e0 = e1 /\ k0 = k1.
Proof.
  eapply f_equal with (f:=_observe) in EQ. compute in EQ.
  dependent destruction EQ.
  split; auto. extensionality x0.
  eapply equal_f in x. instantiate (1:=x0) in x.
  eapply f_equal with (f:=_observe) in x. compute in x.
  eapply observe_eta. auto.
Qed.

Require Import WFLib.

Section SIM.
  Variable E: Type -> Type.

  Section IMPLICIT.
    Variable f_src f_tgt: Ord.t.

    Definition isim_galois_alpha
               R0 R1
               (r: forall (itr_src: itree (E +' ModSemE.eventE) R0)
                          (itr_tgt: itree (E +' ModSemE.eventE) R1), Prop)
               (f_src' f_tgt': Ord.t)
               (itr_src: itree (E +' ModSemE.eventE) R0)
               (itr_tgt: itree (E +' ModSemE.eventE) R1): Prop :=
      (<<SIM: r itr_src itr_tgt>>) /\
        (<<SRC: Ord.le f_src f_src'>>) /\ (<<TGT: Ord.le f_tgt f_tgt'>>).

    Definition isim_galois_gamma
               R0 R1
               (r: forall (f_src f_tgt: Ord.t)
                          (itr_src: itree (E +' ModSemE.eventE) R0)
                          (itr_tgt: itree (E +' ModSemE.eventE) R1), Prop)
               (itr_src: itree (E +' ModSemE.eventE) R0)
               (itr_tgt: itree (E +' ModSemE.eventE) R1): Prop :=
      forall f_src' f_tgt' (SRC: Ord.le f_src f_src') (TGT: Ord.le f_tgt f_tgt'),
        r f_src' f_tgt' itr_src itr_tgt.

    Lemma isim_galois_adjunct_iso0
          R0 R1
      :
      forall a b, @isim_galois_alpha R0 R1 a <4= b -> a <2= @isim_galois_gamma R0 R1 b.
    Proof.
      i. rr. i. eapply H; eauto. rr. esplits; eauto.
    Qed.

    Lemma isim_galois_adjunct_iso1
          R0 R1
      :
      forall a b, a <2= @isim_galois_gamma R0 R1 b -> @isim_galois_alpha R0 R1 a <4= b.
    Proof.
      i. rr in PR. des; subst. eapply H in SIM. rr in SIM. eapply SIM; eauto.
    Qed.

    Lemma psim_replay_isim
          r
          R0 R1 (RR: R0 -> R1 -> Prop)
      :
      @isim_galois_alpha R0 R1 (@_simg_alt_imp E r _ _ RR)
      <4=
        (@_simg E (fun R0 R1 RR => @isim_galois_alpha R0 R1 (r R0 R1 (fun r0 r1 => exists i0 i1, RR i0 i1 r0 r1))) _ _ (fun _ _ => RR)).
    Proof.
      assert (REQ: forall R0 R1 (RR: R0 -> R1 -> Prop), (fun (r0 : R0) (r1 : R1) => exists _ _ : Ord.t, RR r0 r1) = RR).
      { i. extensionality r0. extensionality r1. eapply prop_ext. split; i; des; eauto. }
      i. rr in PR. des; subst.
      revert x0 x1 SRC TGT.
      induction SIM using _simg_alt_imp_ind2; i.
      { inv SRC. inv TGT. eapply simg_ret; eauto; try refl. }
      { inv SIM. inv TGT. inv SRC. inv REL. clarify.
        econs 2. i. subst. r. esplits; eauto. destruct x_tgt.
        eapply trigger_inj2 in H0. eapply trigger_inj2 in H1. des; subst.
        rewrite REQ; auto.
      }
      { inv SIM. inv TGT. inv SRC. inv REL.
        eapply trigger_inj2 in H0. eapply trigger_inj2 in H1. des; subst.
        econs 3. r. esplits; eauto.
        rewrite REQ; auto.
      }
      { inv TGT. inv SRC. eapply simg_event. i. subst.
        specialize (SIM x_tgt _ eq_refl). inv SIM. inv REL.
        eapply trigger_inj2 in H0. eapply trigger_inj2 in H1. des; subst.
        rr. esplits; eauto.
        rewrite REQ; auto.
      }
      { inv SIM; des.
        { eapply simg_tauR; auto. inv REL.
          { eapply simg_tauL; auto. eapply simg_progress.
            { rr. esplits; eauto. rewrite REQ; eauto. }
            { eapply Ord.S_lt. }
            { eapply Ord.S_lt. }
          }
          { des. eapply simg_chooseL; auto. eexists. eapply simg_progress.
            { rr. esplits; eauto. rewrite REQ; eauto. }
            { eapply Ord.S_lt. }
            { eapply Ord.S_lt. }
          }
          { eapply simg_takeL; auto. i. eapply simg_progress.
            { rr. esplits; eauto. rewrite REQ; eauto. }
            { eapply Ord.S_lt. }
            { eapply Ord.S_lt. }
          }
        }
        { eapply simg_tauR; auto. inv SIM. des; eauto. }
        { eapply simg_chooseR; auto. i. specialize (REL x). inv REL.
          { inv H.
            { eapply simg_tauL; auto. eapply simg_progress.
              { rr. esplits; eauto. rewrite REQ; eauto. }
              { eapply Ord.S_lt. }
              { eapply Ord.S_lt. }
            }
            { des. eapply simg_chooseL; auto. eexists. eapply simg_progress.
              { rr. esplits; eauto. rewrite REQ; eauto. }
              { eapply Ord.S_lt. }
              { eapply Ord.S_lt. }
            }
            { eapply simg_takeL; auto. i. eapply simg_progress.
              { rr. esplits; eauto. rewrite REQ; eauto. }
              { eapply Ord.S_lt. }
              { eapply Ord.S_lt. }
            }
          }
          { des. eapply IH; eauto. etrans; eauto. eapply Ord.S_le. }
        }
        { eapply simg_takeR; auto. eexists. inv REL.
          { eapply simg_tauL; auto. eapply simg_progress.
            { rr. esplits; eauto. rewrite REQ; eauto. }
            { eapply Ord.S_lt. }
            { eapply Ord.S_lt. }
          }
          { des. eapply simg_chooseL; auto. eexists. eapply simg_progress.
            { rr. esplits; eauto. rewrite REQ; eauto. }
            { eapply Ord.S_lt. }
            { eapply Ord.S_lt. }
          }
          { eapply simg_takeL; auto. i. eapply simg_progress.
            { rr. esplits; eauto. rewrite REQ; eauto. }
            { eapply Ord.S_lt. }
            { eapply Ord.S_lt. }
          }
        }
        { eapply simg_takeR; auto. inv SIM. des; eauto. }
      }
      { inv SIM; des.
        { eapply simg_tauL; auto. inv REL.
          { eapply simg_tauR; auto. eapply simg_progress.
            { rr. esplits; eauto. rewrite REQ; eauto. }
            { eapply Ord.S_lt. }
            { eapply Ord.S_lt. }
          }
          { des. eapply simg_chooseR; auto. i. eapply simg_progress.
            { rr. esplits; eauto. rewrite REQ; eauto. }
            { eapply Ord.S_lt. }
            { eapply Ord.S_lt. }
          }
          { des. eapply simg_takeR; auto. eexists. eapply simg_progress.
            { rr. esplits; eauto. rewrite REQ; eauto. }
            { eapply Ord.S_lt. }
            { eapply Ord.S_lt. }
          }
        }
        { eapply simg_tauL; auto. inv SIM. des; eauto. }
        { eapply simg_chooseL; auto. eexists. inv REL.
          { eapply simg_tauR; auto. eapply simg_progress.
            { rr. esplits; eauto. rewrite REQ; eauto. }
            { eapply Ord.S_lt. }
            { eapply Ord.S_lt. }
          }
          { eapply simg_chooseR; auto. i. eapply simg_progress.
            { rr. esplits; eauto. rewrite REQ; eauto. }
            { eapply Ord.S_lt. }
            { eapply Ord.S_lt. }
          }
          { des. eapply simg_takeR; auto. eexists. eapply simg_progress.
            { rr. esplits; eauto. rewrite REQ; eauto. }
            { eapply Ord.S_lt. }
            { eapply Ord.S_lt. }
          }
        }
        { eapply simg_chooseL; auto. eexists. eapply IH; eauto. }
        { eapply simg_takeL; eauto. i. specialize (REL x). inv REL.
          { inv H.
            { eapply simg_tauR; auto. eapply simg_progress.
              { rr. esplits; eauto. rewrite REQ; eauto. }
              { eapply Ord.S_lt. }
              { eapply Ord.S_lt. }
            }
            { eapply simg_chooseR; auto. i. eapply simg_progress.
              { rr. esplits; eauto. rewrite REQ; eauto. }
              { eapply Ord.S_lt. }
              { eapply Ord.S_lt. }
            }
            { des. eapply simg_takeR; auto. eexists. eapply simg_progress.
              { rr. esplits; eauto. rewrite REQ; eauto. }
              { eapply Ord.S_lt. }
              { eapply Ord.S_lt. }
            }
          }
          { des. eapply IH; eauto. etrans; eauto. eapply Ord.S_le. }
        }
      }
    Qed.
  End IMPLICIT.


  Section EXPLICIT.
    Variable wfo: WF.

    Definition esim_galois_alpha
               R0 R1
               (r: forall (o: wfo.(T))
                          (itr_src: itree (E +' ModSemE.eventE) R0)
                          (itr_tgt: itree (E +' ModSemE.eventE) R1), Prop)
               (f_src f_tgt: Ord.t)
               (itr_src: itree (E +' ModSemE.eventE) R0)
               (itr_tgt: itree (E +' ModSemE.eventE) R1): Prop :=
      exists o,
        (<<SIM: r o itr_src itr_tgt>>) /\
          (<<SRC: f_src = Ord.from_wf wfo.(wf) o>>) /\ (<<TGT: f_tgt = Ord.from_wf wfo.(wf) o>>).

    Definition esim_galois_gamma
               R0 R1
               (r: forall (f_src f_tgt: Ord.t)
                          (itr_src: itree (E +' ModSemE.eventE) R0)
                          (itr_tgt: itree (E +' ModSemE.eventE) R1), Prop)
               (o: wfo.(T))
               (itr_src: itree (E +' ModSemE.eventE) R0)
               (itr_tgt: itree (E +' ModSemE.eventE) R1): Prop :=
      r (Ord.from_wf wfo.(wf) o) (Ord.from_wf wfo.(wf) o) itr_src itr_tgt.

    Lemma esim_galois_adjunct_iso0
          R0 R1
      :
      forall a b, @esim_galois_alpha R0 R1 a <4= b -> a <3= @esim_galois_gamma R0 R1 b.
    Proof.
      i. rr. i. eapply H; eauto. rr. esplits; eauto.
    Qed.

    Lemma esim_galois_adjunct_iso1
          R0 R1
      :
      forall a b, a <3= @esim_galois_gamma R0 R1 b -> @esim_galois_alpha R0 R1 a <4= b.
    Proof.
      i. rr in PR. des; subst. eapply H in SIM. rr in SIM. eapply SIM; eauto.
    Qed.

    Lemma psim_replay_esim
          r
          R0 R1 (RR: R0 -> R1 -> Prop)
      :
      @esim_galois_alpha R0 R1 (@_simg_alt_exp E wfo r _ _ RR)
      <4=
        (@_simg E (fun R0 R1 RR => @esim_galois_alpha R0 R1 (r R0 R1 (fun r0 r1 => exists i0 i1, RR i0 i1 r0 r1))) _ _ (fun _ _ => RR)).
    Proof.
      assert (REQ: forall R0 R1 (RR: R0 -> R1 -> Prop), (fun (r0 : R0) (r1 : R1) => exists _ _ : Ord.t, RR r0 r1) = RR).
      { i. extensionality r0. extensionality r1. eapply prop_ext. split; i; des; eauto. exists Ord.O, Ord.O. auto. }
      i. rr in PR. des; subst. inv SIM; des.
      { inv SRC. inv TGT. eapply simg_ret; eauto; try refl. }
      { inv OBS. inv REL. inv H. inv H0. des. clarify.
        eapply trigger_inj2 in H1. eapply trigger_inj2 in H2. des; subst.
        econs 2. r. esplits; eauto. destruct x_src, x_tgt.
        rewrite REQ; eauto.
      }
      { inv OBS. inv REL. inv H. inv H0. des. clarify.
        eapply trigger_inj2 in H1. eapply trigger_inj2 in H2. des; subst.
        econs 3. r. esplits; eauto. rewrite REQ; eauto.
      }
      { inv H. inv H1. eapply simg_event. i. subst.
        specialize (H0 x_tgt _ eq_refl). des. inv H0. inv REL.
        eapply trigger_inj2 in H0. eapply trigger_inj2 in H1. des; subst.
        rr. rewrite REQ. esplits; eauto.
        rewrite REQ; eauto. eapply REL0.
      }
      { inv SIM; des.
        { eapply simg_tauR; auto. inv REL.
          { eapply simg_tauL; auto. eapply simg_progress.
            { rr. esplits; eauto. rewrite REQ; eauto. }
            { eapply Ord.S_lt. }
            { eapply Ord.S_lt. }
          }
          { des. eapply simg_chooseL; auto. eexists. eapply simg_progress.
            { rr. esplits; eauto. rewrite REQ; eauto. }
            { eapply Ord.S_lt. }
            { eapply Ord.S_lt. }
          }
          { eapply simg_takeL; auto. i. eapply simg_progress.
            { rr. esplits; eauto. rewrite REQ; eauto. }
            { eapply Ord.S_lt. }
            { eapply Ord.S_lt. }
          }
        }
        { eapply simg_tauR; auto. inv SIM. des; eauto. }
        { eapply simg_chooseR; auto. i. specialize (REL x). inv REL.
          { inv H.
            { eapply simg_tauL; auto. eapply simg_progress.
              { rr. esplits; eauto. rewrite REQ; eauto. }
              { eapply Ord.S_lt. }
              { eapply Ord.S_lt. }
            }
            { des. eapply simg_chooseL; auto. eexists. eapply simg_progress.
              { rr. esplits; eauto. rewrite REQ; eauto. }
              { eapply Ord.S_lt. }
              { eapply Ord.S_lt. }
            }
            { eapply simg_takeL; auto. i. eapply simg_progress.
              { rr. esplits; eauto. rewrite REQ; eauto. }
              { eapply Ord.S_lt. }
              { eapply Ord.S_lt. }
            }
          }
          { des. eapply IH; eauto. etrans; eauto. eapply Ord.S_le. }
        }
        { eapply simg_takeR; auto. eexists. inv REL.
          { eapply simg_tauL; auto. eapply simg_progress.
            { rr. esplits; eauto. rewrite REQ; eauto. }
            { eapply Ord.S_lt. }
            { eapply Ord.S_lt. }
          }
          { des. eapply simg_chooseL; auto. eexists. eapply simg_progress.
            { rr. esplits; eauto. rewrite REQ; eauto. }
            { eapply Ord.S_lt. }
            { eapply Ord.S_lt. }
          }
          { eapply simg_takeL; auto. i. eapply simg_progress.
            { rr. esplits; eauto. rewrite REQ; eauto. }
            { eapply Ord.S_lt. }
            { eapply Ord.S_lt. }
          }
        }
        { eapply simg_takeR; auto. inv SIM. des; eauto. }
      }
      { inv SIM; des.
        { eapply simg_tauL; auto. inv REL.
          { eapply simg_tauR; auto. eapply simg_progress.
            { rr. esplits; eauto. rewrite REQ; eauto. }
            { eapply Ord.S_lt. }
            { eapply Ord.S_lt. }
          }
          { des. eapply simg_chooseR; auto. i. eapply simg_progress.
            { rr. esplits; eauto. rewrite REQ; eauto. }
            { eapply Ord.S_lt. }
            { eapply Ord.S_lt. }
          }
          { des. eapply simg_takeR; auto. eexists. eapply simg_progress.
            { rr. esplits; eauto. rewrite REQ; eauto. }
            { eapply Ord.S_lt. }
            { eapply Ord.S_lt. }
          }
        }
        { eapply simg_tauL; auto. inv SIM. des; eauto. }
        { eapply simg_chooseL; auto. eexists. inv REL.
          { eapply simg_tauR; auto. eapply simg_progress.
            { rr. esplits; eauto. rewrite REQ; eauto. }
            { eapply Ord.S_lt. }
            { eapply Ord.S_lt. }
          }
          { eapply simg_chooseR; auto. i. eapply simg_progress.
            { rr. esplits; eauto. rewrite REQ; eauto. }
            { eapply Ord.S_lt. }
            { eapply Ord.S_lt. }
          }
          { des. eapply simg_takeR; auto. eexists. eapply simg_progress.
            { rr. esplits; eauto. rewrite REQ; eauto. }
            { eapply Ord.S_lt. }
            { eapply Ord.S_lt. }
          }
        }
        { eapply simg_chooseL; auto. eexists. eapply IH; eauto. }
        { eapply simg_takeL; eauto. i. specialize (REL x). inv REL.
          { inv H.
            { eapply simg_tauR; auto. eapply simg_progress.
              { rr. esplits; eauto. rewrite REQ; eauto. }
              { eapply Ord.S_lt. }
              { eapply Ord.S_lt. }
            }
            { eapply simg_chooseR; auto. i. eapply simg_progress.
              { rr. esplits; eauto. rewrite REQ; eauto. }
              { eapply Ord.S_lt. }
              { eapply Ord.S_lt. }
            }
            { des. eapply simg_takeR; auto. eexists. eapply simg_progress.
              { rr. esplits; eauto. rewrite REQ; eauto. }
              { eapply Ord.S_lt. }
              { eapply Ord.S_lt. }
            }
          }
          { des. eapply IH; eauto. etrans; eauto. eapply Ord.S_le. }
        }
      }
    Qed.
  End IMPLICIT.


      eapply simg_takeL; auto. i. eapply IH; eauto. }

      }
      }
      { eapply simg_takeR; auto. eexists. inv REL.
        { eapply simg_tauL; auto. eapply simg_progress.
          { rr. esplits; eauto. rewrite REQ; eauto. }
          { eapply Ord.S_lt. }
          { eapply Ord.S_lt. }
        }
        { des. eapply simg_chooseL; auto. eexists. eapply simg_progress.
          { rr. esplits; eauto. rewrite REQ; eauto. }
          { eapply Ord.S_lt. }
          { eapply Ord.S_lt. }
        }
        { eapply simg_takeL; auto. i. eapply simg_progress.
          { rr. esplits; eauto. rewrite REQ; eauto. }
          { eapply Ord.S_lt. }
          { eapply Ord.S_lt. }
        }
      }
      { eapply simg_takeR; auto. inv SIM. des; eauto. }
      }
      { in

        { des. eapply IH; eauto. etrans; eauto. eapply Ord.S_le. }
      }

          admit ".


            eapply IH. }

          simg_tauL; auto. eapply simg_progress.
            { rr. esplits; eauto. rewrite REQ; eauto. }
            { eapply Ord.S_lt. }
            { eapply Ord.S_lt. }
          }
          { des. eapply simg_chooseL; auto. eexists. eapply simg_progress.
            { rr. esplits; eauto. rewrite REQ; eauto. }
            { eapply Ord.S_lt. }
            { eapply Ord.S_lt. }
          }
          { eapply simg_takeL; auto. i. eapply simg_progress.
            { rr. esplits; eauto. rewrite REQ; eauto. }
            { eapply Ord.S_lt. }
            { eapply Ord.S_lt. }
          }
        }

                rr. esplits; eauto. rewrite REQ; auto. }



        unfold subevent, resum, ReSum_inl, resum, ReSum_id, id_, Id_IFun in H0. ss.

        inv H0. inv H1.


        inv REL.
        eapply trigger_inj in H0. eapply trigger_inj in H1. subst.
        econs 3. r. esplits; eauto.
        replace (fun (r0 : R0) (r1 : R1) => exists _ _ : Ord.t, RR r0 r1) with RR; auto.
        extensionality r0. extensionality r1. eapply prop_ext. split; i; des; eauto.
      }


extensionality r0.


        auto.

        eapply f_equal with (f:=_observe) in H1. inv H1. des_ifs. ss.


ITree.trigger
        Set Printing All.



      revert x2 x3.

      inv SIM.



    Definition isim_galois_alpha
               R0 R1 (RR: R0 -> R1 -> Prop)
               (r: forall (itr_src: itree (E +' ModSemE.eventE) R0)
                          (itr_tgt: itree (E +' ModSemE.eventE) R1), Prop)
               (f_src' f_tgt': Ord.t)
               (itr_src: itree (E +' ModSemE.eventE) R0)
               (itr_tgt: itree (E +' ModSemE.eventE) R1): Prop :=
      (<<SIM: r itr_src itr_tgt>>) /\
        (<<SRC: f_src' = f_src>>) /\ (<<TGT: f_tgt' = f_tgt>>).

    Definition isim_galois_gamma
               R0 R1 (RR: R0 -> R1 -> Prop)
               (r: forall (f_src f_tgt: Ord.t)
                          (itr_src: itree (E +' ModSemE.eventE) R0)
                          (itr_tgt: itree (E +' ModSemE.eventE) R1), Prop)
               (itr_src: itree (E +' ModSemE.eventE) R0)
               (itr_tgt: itree (E +' ModSemE.eventE) R1): Prop :=
      r f_src f_tgt itr_src itr_tgt.

    Lemma isim_galois_adjunct_iso0
          R0 R1 (RR: R0 -> R1 -> Prop)
      :
      forall a b, isim_galois_alpha RR a <4= b -> a <2= isim_galois_gamma RR b.
    Proof.
      i. rr. eapply H; eauto. rr. esplits; eauto.
    Qed.

    Lemma isim_galois_adjunct_iso1
          R0 R1 (RR: R0 -> R1 -> Prop)
      :
      forall a b, a <2= isim_galois_gamma RR b -> isim_galois_alpha RR a <4= b.
    Proof.
      i. rr in PR. des; subst. eapply H in SIM. rr in SIM. auto.
    Qed.

    Lemma psim_replay_isim
          R0 R1 (RR: R0 -> R1 -> Prop)
          r
      :
      isim_galois_alpha RR (@_simg_alt_imp E r _ _ RR) <4= (_simg (fun R0 R1 RR => isim_galois_alpha RR (r R0 R1 (fun _ _ => RR)))).



                                                 (fun R0 R1 RR => isim_galois_alpha (y R0 R1 (fun r0 r1 => exists i0 i1, RR i0 i1 r0 r1)))).



          (x R0 R1 (fun _ _ => RR)) <4=
          _simg (fun R0 R1 RR => isim_galois_alpha (x R0 R1 (fun _ _ => RR))) (fun _ _ => RR).

    Lemma psim_replay_isim
      :
      forall x y,
        isim_galois_alpha
          (_simg_alt_imp (fun R0 R1 RR => isim_galois_alpha (y R0 R1 (fun r0 r1 => exists i0 i1, RR i0 i1 r0 r1)))) <4=
          _simg y (fun _ _ => RR).

      (isim_galois_alpha


        (r: forall R0 R1 (RR: R0 -> R1 -> Prop)
                        (itr_src: itree (E +' ModSemE.eventE) R0)
                        (itr_tgt: itree (E +' ModSemE.eventE) R1), Prop),
        isim_galois_alpha (_simg_alt_imp (fun R0 R1 RR itr_src itr_tgt =>



    Definition isim_galois_alpha
               (r: forall (itr_src: itree (E +' ModSemE.eventE) R0)
                          (itr_tgt: itree (E +' ModSemE.eventE) R1), Prop)
               (f_src' f_tgt': Ord.t)
               (itr_src: itree (E +' ModSemE.eventE) R0)
               (itr_tgt: itree (E +' ModSemE.eventE) R1): Prop :=
      (<<SIM: r itr_src itr_tgt>>) /\
        (<<SRC: f_src' = f_src>>) /\ (<<TGT: f_tgt' = f_tgt>>).

    Definition isim_galois_gamma
               (r: forall (f_src f_tgt: Ord.t)
                          (itr_src: itree (E +' ModSemE.eventE) R0)
                          (itr_tgt: itree (E +' ModSemE.eventE) R1), Prop)
               (itr_src: itree (E +' ModSemE.eventE) R0)
               (itr_tgt: itree (E +' ModSemE.eventE) R1): Prop :=
      r f_src f_tgt itr_src itr_tgt.

    Lemma isim_galois_adjunct_iso0
      :
      forall a b, isim_galois_alpha a <4= b -> a <2= isim_galois_gamma b.
    Proof.
      i. rr. eapply H; eauto. rr. esplits; eauto.
    Qed.

    Lemma isim_galois_adjunct_iso1
      :
      forall a b, a <2= isim_galois_gamma b -> isim_galois_alpha a <4= b.
    Proof.
      i. rr in PR. des; subst. eapply H in SIM. rr in SIM. auto.
    Qed.

    Lemma psim_replay_isim
      :
      forall (r: forall R0 R1 (RR: R0 -> R1 -> Prop)
                        (itr_src: itree (E +' ModSemE.eventE) R0)
                        (itr_tgt: itree (E +' ModSemE.eventE) R1), Prop),
        isim_galois_alpha (_simg_alt_imp (fun R0 R1 RR itr_src itr_tgt =>

                                            E R0 R1 RR)
        <2=
          _simg r (fun _ _ => RR) itr_src itr_tgt.

  Definition replay := forall a, c.(Galois.alpha) (F a) <1= G (c.(Galois.alpha) a).


                (isim_galois_alpha a).


    >>)
    .





    Definition isim_galois_alpha
               (r: forall (R0 R1: Type) (RR: R0 -> R1 -> Prop)
                          (itr_src: itree (E +' ModSemE.eventE) R0)
                          (itr_tgt: itree (E +' ModSemE.eventE) R1), Prop)
               (R0 R1: Type) (RR: Ord.t -> Ord.t -> R0 -> R1 -> Prop)
               (f_src' f_tgt': Ord.t)
               (itr_src: itree (E +' ModSemE.eventE) R0)
               (itr_tgt: itree (E +' ModSemE.eventE) R1): Prop :=
      forall RR' (IMPL: forall r0 r1, RR f_src f_tgt r0 r1 -> RR' r0 r1: Prop),
        (<<SIM: r R0 R1 RR' itr_src itr_tgt>>) /\
          (<<SRC: f_src' = f_src>>) /\ (<<TGT: f_tgt' = f_tgt>>).

    Definition isim_galois_gamma
               (r: forall (R0 R1: Type) (RR: Ord.t -> Ord.t -> R0 -> R1 -> Prop)
                          (f_src f_tgt: Ord.t)
                          (itr_src: itree (E +' ModSemE.eventE) R0)
                          (itr_tgt: itree (E +' ModSemE.eventE) R1), Prop)
               (R0 R1: Type) (RR: R0 -> R1 -> Prop)
               (itr_src: itree (E +' ModSemE.eventE) R0)
               (itr_tgt: itree (E +' ModSemE.eventE) R1): Prop :=
      exists RR' (SIM: forall r0 r1, RR r0 r1 -> RR' f_src f_tgt r0 r1: Prop),
        (<<SIM: r R0 R1 RR' f_src f_tgt itr_src itr_tgt>>)
    .

    Lemma isim_galois_adjunct_iso0
      :
      forall a b, isim_galois_alpha a <7= b -> a <5= isim_galois_gamma b.
    Proof.
      i. rr. eexists (fun _ _ => x2). esplits; eauto.
      eapply H. rr. esplits; eauto.
    Qed.

    Lemma isim_galois_adjunct_iso1
      :
      forall a b, a <5= isim_galois_gamma b -> isim_galois_alpha a <7= b.
    Proof.
      i. rr in PR. des; subst. eapply H in SIM. rr in SIM. des.


      replace x2 with (fun (f_src' f_tgt' : Ord.t) (r0 : x0) (r1 : x1) =>
                         f_src' = f_src -> f_tgt' = f_tgt -> x2 f_src f_tgt r0 r1); auto.
      extensionality r0. extensionality r1.
      extensionality i0. extensionality i1.
      eapply prop_ext. split; i; des; subst; eauto. eapply H0; eauto. splits; eauto.

      [eapply H|eauto].
      { rr. esplits; eauto. i.

      { eapply H.

      apply H. rr. esplits; eauto.
      replace (fun (r0 : x0) (r1 : x1) => f_src = f_src -> f_tgt = f_tgt -> x2 r0 r1) with x2; auto.
      extensionality r0. extensionality r1.
      eapply prop_ext. split; i; des; eauto.
    Qed.

    Lemma isim_galois_adjunct_iso1
      :
      forall a b, a <5= isim_galois_gamma b -> isim_galois_alpha a <7= b.
    Proof.
      i. rr in PR. des; subst. eapply H in SIM. rr in SIM.
      replace x2 with (fun (f_src' f_tgt' : Ord.t) (r0 : x0) (r1 : x1) =>
                         f_src' = f_src -> f_tgt' = f_tgt -> x2 f_src f_tgt r0 r1); auto.
      extensionality r0. extensionality r1.
      extensionality i0. extensionality i1.
      eapply prop_ext. split; i; des; subst; eauto. eapply H0; eauto. splits; eauto.

      eapply H; eauto.
    Qed.

    Lemma psim_replay_isim
      :
      forall (a: forall (itr_src: itree (E +' ModSemE.eventE) R0)
                        (itr_tgt: itree (E +' ModSemE.eventE) R1), Prop),
        isim_galois_alpha (_simg_alt_imp E R0 R1 RR) <2= simg (fun _ _ => RR) (isim_galois_alpha a).


  Definition replay := forall a, c.(Galois.alpha) (F a) <1= G (c.(Galois.alpha) a).


      rr. apply H. rr. esplits; eauto.
    Qed.



        adjunct_iso0: forall a b, (alpha a <1= b) -> (a <1= gamma b);
        adjunct_iso1: forall a b, (a <1= gamma b) -> (alpha a <1= b);


               (f_src' f_tgt': Ord.t)
               (itr_src: itree (E +' ModSemE.eventE) R0)
               (itr_tgt: itree (E +' ModSemE.eventE) R1): Prop :=
      (<<SRC: f_src' = f_src>>) /\ (<<TGT: f_tgt' = f_tgt>>) /\ (<<SIM: a itr_src itr_tgt>>).


    Ord.t -> Ord.t ->
    itree (E +' ModSemE.eventE) R0 -> itree (E +' ModSemE.eventE) R1

    Prop


    (

  Variable R0 R1: Type.
  Variable (RR: R0 -> R1 -> Prop).


                                  simg_alt_imp

  Lemma psim_replay_isim f_src f_tgt
    :



  Variable L0 L1: semantics.

  Variant _sim (sim: Ord.t -> Ord.t -> L0.(state) -> L1.(state) -> Prop)
                 (sim_: Ord.t -> Ord.t -> L0.(state) -> L1.(state) -> Prop)
            (i_src0: Ord.t) (i_tgt0: Ord.t) (st_src0: L0.(state)) (st_tgt0: L1.(state)): Prop :=
  | sim_fin
      retv
      (SRT: _.(state_sort) st_src0 = final retv)
      (SRT: _.(state_sort) st_tgt0 = final retv)
    :
      _sim sim sim_ i_src0 i_tgt0 st_src0 st_tgt0

  | sim_vis
      (SRT: _.(state_sort) st_src0 = vis)
      (SRT: _.(state_sort) st_tgt0 = vis)
      (SIM: forall ev st_tgt1
          (STEP: _.(step) st_tgt0 (Some ev) st_tgt1)
        ,
          exists st_src1 i_src1 i_tgt1 (STEP: _.(step) st_src0 (Some ev) st_src1),
            <<SIM: sim i_src1 i_tgt1 st_src1 st_tgt1>>)
    :
      _sim sim sim_ i_src0 i_tgt0 st_src0 st_tgt0

  | sim_vis_stuck_tgt
      (SRT: _.(state_sort) st_tgt0 = vis)
      (STUCK: forall ev st_tgt1, not (_.(step) st_tgt0 (Some ev) st_tgt1))
    :
      _sim sim sim_ i_src0 i_tgt0 st_src0 st_tgt0

  | sim_demonic_src
      (SRT: _.(state_sort) st_src0 = demonic)
      (SIM: exists st_src1 i_src1
                   (STEP: _.(step) st_src0 None st_src1)
        ,
          <<SIM: sim_ i_src1 i_tgt0 st_src1 st_tgt0>>)
    :
      _sim sim sim_ i_src0 i_tgt0 st_src0 st_tgt0
  | sim_demonic_tgt
      (SRT: _.(state_sort) st_tgt0 = demonic)
      (SIM: forall st_tgt1
                   (STEP: _.(step) st_tgt0 None st_tgt1),
          exists i_tgt1,
          <<SIM: sim_ i_src0 i_tgt1 st_src0 st_tgt1>>)
    :
      _sim sim sim_ i_src0 i_tgt0 st_src0 st_tgt0

  | sim_progress
      i_src1 i_tgt1
      (SIM: sim i_src1 i_tgt1 st_src0 st_tgt0)
      (SRC: Ord.lt i_src1 i_src0)
      (TGT: Ord.lt i_tgt1 i_tgt0)
    :
      _sim sim sim_ i_src0 i_tgt0 st_src0 st_tgt0
  .

  Variant _simE (simE: Ord.t -> L0.(state) -> L1.(state) -> Prop)
                  (simE_: Ord.t -> L0.(state) -> L1.(state) -> Prop)
            (i0: Ord.t) (st_src0: L0.(state)) (st_tgt0: L1.(state)): Prop :=
  | simE_fin
      retv
      (SRT: _.(state_sort) st_src0 = final retv)
      (SRT: _.(state_sort) st_tgt0 = final retv)
    :
      _simE simE simE_ i0 st_src0 st_tgt0

  | simE_vis
      (SRT: _.(state_sort) st_src0 = vis)
      (SRT: _.(state_sort) st_tgt0 = vis)
      (SIM: forall ev st_tgt1
          (STEP: _.(step) st_tgt0 (Some ev) st_tgt1)
        ,
          exists st_src1 i1 (STEP: _.(step) st_src0 (Some ev) st_src1),
            <<SIM: simE i1 st_src1 st_tgt1>>)
    :
      _simE simE simE_ i0 st_src0 st_tgt0

  | simE_vis_stuck_tgt
      (SRT: _.(state_sort) st_tgt0 = vis)
      (STUCK: forall ev st_tgt1, not (_.(step) st_tgt0 (Some ev) st_tgt1))
    :
      _simE simE simE_ i0 st_src0 st_tgt0

  | simE_demonic_src
      (SRT: _.(state_sort) st_src0 = demonic)
      (SIM: exists st_src1 i1
                   (LT: Ord.lt i1 i0)
                   (STEP: _.(step) st_src0 None st_src1)
        ,
          <<SIM: simE i1 st_src1 st_tgt0>>)
    :
      _simE simE simE_ i0 st_src0 st_tgt0
  | simE_demonic_tgt
      (SRT: _.(state_sort) st_tgt0 = demonic)
      (SIM: forall st_tgt1
                   (STEP: _.(step) st_tgt0 None st_tgt1),
          exists i1 (LT: Ord.lt i1 i0),
          <<SIM: simE i1 st_src0 st_tgt1>>)
    :
      _simE simE simE_ i0 st_src0 st_tgt0

  | simE_both
      (SRT: _.(state_sort) st_src0 = demonic)
      (SRT: _.(state_sort) st_tgt0 = demonic)
      (SIM: forall st_tgt1
                   (STEP: _.(step) st_tgt0 None st_tgt1),
          exists i1 st_src1 (STEP: _.(step) st_src0 None st_src1),
          <<SIM: simE i1 st_src1 st_tgt1>>)
  .

  Definition _fromE: (Ord.t * state L0 * state L1) -> (Ord.t * Ord.t * state L0 * state L1) :=
    fun '(o, s0, s1) => (o, o, s0, s1).

  Definition fromE: (Ord.t -> state L0 -> state L1 -> Prop) -> (Ord.t -> Ord.t -> state L0 -> state L1 -> Prop) :=
    fun Y o0 o1 s0 s1 => exists yo ys0 ys1 (IN: Y yo ys0 ys1), (_fromE (yo, ys0, ys1)) = (o0, o1, s0, s1).

  Definition fromE_aux: (Ord.t -> state L0 -> state L1 -> Prop) -> (Ord.t -> Ord.t -> state L0 -> state L1 -> Prop) :=
    fun Y o0 o1 s0 s1 => o0 = o1 /\ Y o0 s0 s1.

  Lemma fromE_lemma: fromE_aux = fromE.
  Proof.
    extensionalities Y o0 o1 s0 s1. eapply prop_ext. split; i.
    - rr in H. des; subst. r. eauto.
    - rr in H. des; subst. ss. clarify.
  Qed.

  Fixpoint repeat X (n: nat) (f: X -> X): X -> X :=
    match n with
    | 0 => id
    | S n => f ∘ (repeat n f)
    end
  .

  Goal forall X0 X1 i0 i1 s0 s1, fromE (_simE X0 X1) i0 i1 s0 s1 -> exists n, ((repeat n (_sim (fromE X0))) (fromE X1)) i0 i1 s0 s1.
  Proof.
    i. rewrite <- fromE_lemma in *. red in H. des; subst. inv H0.
    - exists 1. econs 1; eauto.
    - exists 1. econs 2; eauto.
      i. exploit SIM; eauto. i; des. esplits; eauto. r. esplits; eauto.
    - exists 1. econs 3; eauto.
    - exists 2. des. econs 4; eauto. esplits; eauto.
      econsr; eauto. r. eauto.
    - exists 2. des. econs 5; eauto. i. exploit SIM; eauto. i; des. esplits; eauto.
      econsr; eauto. r. eauto.
    - exists 3. des. econs 5; eauto. i.
      exploit SIM; eauto. i; des.
      esplits; eauto. econs 4; eauto. esplits; eauto.
      econsr; eauto.
      { r. esplits; eauto. }
      { instantiate (1:=Ord.S i0). eapply Ord.S_is_S. }
      { instantiate (1:=Ord.S i0). eapply Ord.S_is_S. }
  Qed.

  Variant _simI (simI: L0.(state) -> L1.(state) -> Prop)
                (simI_: L0.(state) -> L1.(state) -> Prop)
                (st_src0: L0.(state)) (st_tgt0: L1.(state)): Prop :=
  | simI_fin
      retv
      (SRT: _.(state_sort) st_src0 = final retv)
      (SRT: _.(state_sort) st_tgt0 = final retv)
    :
      _simI simI simI_ st_src0 st_tgt0

  | simI_vis
      (SRT: _.(state_sort) st_src0 = vis)
      (SRT: _.(state_sort) st_tgt0 = vis)
      (SIM: forall ev st_tgt1
          (STEP: _.(step) st_tgt0 (Some ev) st_tgt1)
        ,
          exists st_src1 (STEP: _.(step) st_src0 (Some ev) st_src1),
            <<SIM: simI st_src1 st_tgt1>>)
    :
      _simI simI simI_ st_src0 st_tgt0

  | simI_vis_stuck_tgt
      (SRT: _.(state_sort) st_tgt0 = vis)
      (STUCK: forall ev st_tgt1, not (_.(step) st_tgt0 (Some ev) st_tgt1))
    :
      _simI simI simI_ st_src0 st_tgt0

  | simI_demonic_src
      (SRT: _.(state_sort) st_src0 = demonic)
      (SIM: exists st_src1
                   (STEP: _.(step) st_src0 None st_src1)
        ,
          <<SIM: simI_ st_src1 st_tgt0>>)
    :
      _simI simI simI_ st_src0 st_tgt0
  | simI_demonic_tgt
      (SRT: _.(state_sort) st_tgt0 = demonic)
      (SIM: forall st_tgt1
                   (STEP: _.(step) st_tgt0 None st_tgt1),
          <<SIM: simI_ st_src0 st_tgt1>>)
    :
      _simI simI simI_ st_src0 st_tgt0

  | simI_both
      (SRT: _.(state_sort) st_src0 = demonic)
      (SRT: _.(state_sort) st_tgt0 = demonic)
      (SIM: forall st_tgt1
                   (STEP: _.(step) st_tgt0 None st_tgt1),
          exists st_src1 (STEP: _.(step) st_src0 None st_src1),
          <<SIM: simI st_src1 st_tgt1>>)
  .

  Definition _fromI: (state L0 * state L1) -> (Ord.t * Ord.t * state L0 * state L1) :=
    fun '(s0, s1) => (Ord.O, Ord.O, s0, s1).

  Definition fromI: (state L0 -> state L1 -> Prop) -> (Ord.t -> Ord.t -> state L0 -> state L1 -> Prop) :=
    fun Y o0 o1 s0 s1 => exists ys0 ys1 (IN: Y ys0 ys1), (_fromI (ys0, ys1)) = (o0, o1, s0, s1).

  Definition fromI_aux: (state L0 -> state L1 -> Prop) -> (Ord.t -> Ord.t -> state L0 -> state L1 -> Prop) :=
    fun Y o0 o1 s0 s1 => o0 = 0 /\ o1 = 0 /\ Y s0 s1.

  Lemma fromI_lemma: fromI_aux = fromI.
  Proof.
    extensionalities Y o0 o1 s0 s1. eapply prop_ext. split; i.
    - rr in H. des; subst. r. eauto.
    - rr in H. des; subst. ss. clarify.
  Qed.

  Goal forall X0 X1 i0 i1 s0 s1, fromI (_simI X0 X1) i0 i1 s0 s1 -> exists n, ((repeat n (_sim (fromI X0))) (fromI X1)) i0 i1 s0 s1.
  Proof.
    i. rewrite <- fromI_lemma in *. red in H. des; subst. inv H1.
    - exists 1. econs 1; eauto.
    - exists 1. econs 2; eauto.
      i. exploit SIM; eauto. i; des. esplits; eauto. r. esplits; eauto.
    - exists 1. econs 3; eauto.
    - exists 1. des. econs 4; eauto. esplits; eauto. rr. eauto.
    - exists 1. des. econs 5; eauto. i. exploit SIM; eauto. i; des. esplits; eauto. rr. eauto.
    - exists 3. des. econs 5; eauto. i.
      exploit SIM; eauto. i; des.
      esplits; eauto. econs 4; eauto. esplits; eauto.
      econsr; eauto.
      { r. esplits; eauto. }
      { instantiate (1:=1). eapply OrdArith.lt_from_nat. lia. }
      { instantiate (1:=1). eapply OrdArith.lt_from_nat. lia. }
  Qed.

End SIM.
End REPLAY.

Reset REPLAY.

Module REPLAY.
Section SIM.

  Variable L0 L1: semantics.

  Inductive _sim (sim: Ord.t -> Ord.t -> L0.(state) -> L1.(state) -> Prop)
    (i_src0: Ord.t) (i_tgt0: Ord.t) (st_src0: L0.(state)) (st_tgt0: L1.(state)): Prop :=
  | sim_fin
      retv
      (SRT: _.(state_sort) st_src0 = final retv)
      (SRT: _.(state_sort) st_tgt0 = final retv)
    :
      _sim sim i_src0 i_tgt0 st_src0 st_tgt0

  | sim_vis
      (SRT: _.(state_sort) st_src0 = vis)
      (SRT: _.(state_sort) st_tgt0 = vis)
      (SIM: forall ev st_tgt1
          (STEP: _.(step) st_tgt0 (Some ev) st_tgt1)
        ,
          exists st_src1 i_src1 i_tgt1 (STEP: _.(step) st_src0 (Some ev) st_src1),
            <<SIM: sim i_src1 i_tgt1 st_src1 st_tgt1>>)
    :
      _sim sim i_src0 i_tgt0 st_src0 st_tgt0

  | sim_vis_stuck_tgt
      (SRT: _.(state_sort) st_tgt0 = vis)
      (STUCK: forall ev st_tgt1, not (_.(step) st_tgt0 (Some ev) st_tgt1))
    :
      _sim sim i_src0 i_tgt0 st_src0 st_tgt0

  | sim_demonic_src
      (SRT: _.(state_sort) st_src0 = demonic)
      (SIM: exists st_src1 i_src1
                   (STEP: _.(step) st_src0 None st_src1)
        ,
          <<SIM: _sim sim i_src1 i_tgt0 st_src1 st_tgt0>>)
    :
      _sim sim i_src0 i_tgt0 st_src0 st_tgt0
  | sim_demonic_tgt
      (SRT: _.(state_sort) st_tgt0 = demonic)
      (SIM: forall st_tgt1
                   (STEP: _.(step) st_tgt0 None st_tgt1),
          exists i_tgt1,
          <<SIM: _sim sim i_src0 i_tgt1 st_src0 st_tgt1>>)
    :
      _sim sim i_src0 i_tgt0 st_src0 st_tgt0

  | sim_progress
      i_src1 i_tgt1
      (SIM: sim i_src1 i_tgt1 st_src0 st_tgt0)
      (SRC: Ord.lt i_src1 i_src0)
      (TGT: Ord.lt i_tgt1 i_tgt0)
    :
      _sim sim i_src0 i_tgt0 st_src0 st_tgt0
  .

  Variant _simE (simE: Ord.t -> L0.(state) -> L1.(state) -> Prop)
    (i0: Ord.t) (st_src0: L0.(state)) (st_tgt0: L1.(state)): Prop :=
  | simE_fin
      retv
      (SRT: _.(state_sort) st_src0 = final retv)
      (SRT: _.(state_sort) st_tgt0 = final retv)
    :
      _simE simE i0 st_src0 st_tgt0

  | simE_vis
      (SRT: _.(state_sort) st_src0 = vis)
      (SRT: _.(state_sort) st_tgt0 = vis)
      (SIM: forall ev st_tgt1
          (STEP: _.(step) st_tgt0 (Some ev) st_tgt1)
        ,
          exists st_src1 i1 (STEP: _.(step) st_src0 (Some ev) st_src1),
            <<SIM: simE i1 st_src1 st_tgt1>>)
    :
      _simE simE i0 st_src0 st_tgt0

  | simE_vis_stuck_tgt
      (SRT: _.(state_sort) st_tgt0 = vis)
      (STUCK: forall ev st_tgt1, not (_.(step) st_tgt0 (Some ev) st_tgt1))
    :
      _simE simE i0 st_src0 st_tgt0

  | simE_demonic_src
      (SRT: _.(state_sort) st_src0 = demonic)
      (SIM: exists st_src1 i1
                   (LT: Ord.lt i1 i0)
                   (STEP: _.(step) st_src0 None st_src1)
        ,
          <<SIM: simE i1 st_src1 st_tgt0>>)
    :
      _simE simE i0 st_src0 st_tgt0
  | simE_demonic_tgt
      (SRT: _.(state_sort) st_tgt0 = demonic)
      (SIM: forall st_tgt1
                   (STEP: _.(step) st_tgt0 None st_tgt1),
          exists i1 (LT: Ord.lt i1 i0),
          <<SIM: simE i1 st_src0 st_tgt1>>)
    :
      _simE simE i0 st_src0 st_tgt0

  | simE_both
      (SRT: _.(state_sort) st_src0 = demonic)
      (SRT: _.(state_sort) st_tgt0 = demonic)
      (SIM: forall st_tgt1
                   (STEP: _.(step) st_tgt0 None st_tgt1),
          exists i1 st_src1 (STEP: _.(step) st_src0 None st_src1),
          <<SIM: simE i1 st_src1 st_tgt1>>)
  .

  Definition _fromE: (Ord.t * state L0 * state L1) -> (Ord.t * Ord.t * state L0 * state L1) :=
    fun '(o, s0, s1) => (o, o, s0, s1).

  Definition fromE: (Ord.t -> state L0 -> state L1 -> Prop) -> (Ord.t -> Ord.t -> state L0 -> state L1 -> Prop) :=
    fun Y o0 o1 s0 s1 => exists yo ys0 ys1 (IN: Y yo ys0 ys1), (_fromE (yo, ys0, ys1)) = (o0, o1, s0, s1).

  Definition fromE_aux: (Ord.t -> state L0 -> state L1 -> Prop) -> (Ord.t -> Ord.t -> state L0 -> state L1 -> Prop) :=
    fun Y o0 o1 s0 s1 => o0 = o1 /\ Y o0 s0 s1.

  Lemma fromE_lemma: fromE_aux = fromE.
  Proof.
    extensionalities Y o0 o1 s0 s1. eapply prop_ext. split; i.
    - rr in H. des; subst. r. eauto.
    - rr in H. des; subst. ss. clarify.
  Qed.

  Goal forall X0 i0 i1 s0 s1,
      fromE (_simE X0) i0 i1 s0 s1 -> (_sim (fromE X0)) i0 i1 s0 s1.
  Proof.
    i. rewrite <- fromE_lemma in *. red in H. des; subst. inv H0.
    - econs 1; eauto.
    - econs 2; eauto.
      i. exploit SIM; eauto. i; des. esplits; eauto. r. esplits; eauto.
    - econs 3; eauto.
    - des. econs 4; eauto. esplits; eauto.
      econsr; eauto. r. eauto.
    - des. econs 5; eauto. i. exploit SIM; eauto. i; des. esplits; eauto.
      econsr; eauto. r. eauto.
    - des. econs 5; eauto. i.
      exploit SIM; eauto. i; des.
      esplits; eauto. econs 4; eauto. esplits; eauto.
      econsr; eauto.
      { r. esplits; eauto. }
      { instantiate (1:=Ord.S i0). eapply Ord.S_is_S. }
      { instantiate (1:=Ord.S i0). eapply Ord.S_is_S. }
  Qed.

  Inductive _simI (simI: L0.(state) -> L1.(state) -> Prop)
    (st_src0: L0.(state)) (st_tgt0: L1.(state)): Prop :=
  | simI_fin
      retv
      (SRT: _.(state_sort) st_src0 = final retv)
      (SRT: _.(state_sort) st_tgt0 = final retv)
    :
      _simI simI st_src0 st_tgt0

  | simI_vis
      (SRT: _.(state_sort) st_src0 = vis)
      (SRT: _.(state_sort) st_tgt0 = vis)
      (SIM: forall ev st_tgt1
          (STEP: _.(step) st_tgt0 (Some ev) st_tgt1)
        ,
          exists st_src1 (STEP: _.(step) st_src0 (Some ev) st_src1),
            <<SIM: simI st_src1 st_tgt1>>)
    :
      _simI simI st_src0 st_tgt0

  | simI_vis_stuck_tgt
      (SRT: _.(state_sort) st_tgt0 = vis)
      (STUCK: forall ev st_tgt1, not (_.(step) st_tgt0 (Some ev) st_tgt1))
    :
      _simI simI st_src0 st_tgt0

  | simI_demonic_src
      (SRT: _.(state_sort) st_src0 = demonic)
      (SIM: exists st_src1
                   (STEP: _.(step) st_src0 None st_src1)
        ,
          <<SIM: _simI simI st_src1 st_tgt0>>)
    :
      _simI simI st_src0 st_tgt0
  | simI_demonic_tgt
      (SRT: _.(state_sort) st_tgt0 = demonic)
      (SIM: forall st_tgt1
                   (STEP: _.(step) st_tgt0 None st_tgt1),
          <<SIM: _simI simI st_src0 st_tgt1>>)
    :
      _simI simI st_src0 st_tgt0

  | simI_both
      (SRT: _.(state_sort) st_src0 = demonic)
      (SRT: _.(state_sort) st_tgt0 = demonic)
      (SIM: forall st_tgt1
                   (STEP: _.(step) st_tgt0 None st_tgt1),
          exists st_src1 (STEP: _.(step) st_src0 None st_src1),
          <<SIM: simI st_src1 st_tgt1>>)
  .

  Lemma _simI_ind2 simI (P: L0.(state) -> L1.(state) -> Prop)
        (FIN: forall
            st_src0 st_tgt0
            retv
            (SRT: _.(state_sort) st_src0 = final retv)
            (SRT: _.(state_sort) st_tgt0 = final retv),
            P st_src0 st_tgt0)
        (VIS: forall
            st_src0 st_tgt0
            (SRT: _.(state_sort) st_src0 = vis)
            (SRT: _.(state_sort) st_tgt0 = vis)
            (SIM: forall ev st_tgt1
                         (STEP: _.(step) st_tgt0 (Some ev) st_tgt1)
              ,
                exists st_src1 (STEP: _.(step) st_src0 (Some ev) st_src1),
                  <<SIM: simI st_src1 st_tgt1>>),
            P st_src0 st_tgt0)
        (VISSTUCK: forall
            st_src0 st_tgt0
            (SRT: _.(state_sort) st_tgt0 = vis)
            (STUCK: forall ev st_tgt1, not (_.(step) st_tgt0 (Some ev) st_tgt1)),
            P st_src0 st_tgt0)
        (DMSRC: forall
            st_src0 st_tgt0
            (SRT: _.(state_sort) st_src0 = demonic)
            (SIM: exists st_src1
                         (STEP: _.(step) st_src0 None st_src1)
              ,
                <<SIM: _simI simI st_src1 st_tgt0>> /\ <<IH: P st_src1 st_tgt0>>),
            P st_src0 st_tgt0)
        (DMTGT: forall
            st_src0 st_tgt0
            (SRT: _.(state_sort) st_tgt0 = demonic)
            (SIM: forall st_tgt1
                         (STEP: _.(step) st_tgt0 None st_tgt1)
              ,
                <<SIM: _simI simI st_src0 st_tgt1>> /\ <<IH: P st_src0 st_tgt1>>),
            P st_src0 st_tgt0)
        (BOTH: forall
            st_src0 st_tgt0
            (SRT: _.(state_sort) st_src0 = demonic)
            (SRT: _.(state_sort) st_tgt0 = demonic)
            (SIM: forall st_tgt1
                         (STEP: _.(step) st_tgt0 None st_tgt1),
              exists st_src1
                         (STEP: _.(step) st_src0 None st_src1),
                <<SIM: simI st_src1 st_tgt1>>),
            P st_src0 st_tgt0)
    :
      forall st_src0 st_tgt0 (SIM: _simI simI st_src0 st_tgt0),
        P st_src0 st_tgt0.
  Proof.
    fix IH 3. i. inv SIM.
    { eapply FIN; eauto. }
    { eapply VIS; eauto. }
    { eapply VISSTUCK; eauto. }
    { eapply DMSRC; eauto.
      des. esplits; eauto. }
    { eapply DMTGT; eauto. i.
      hexploit SIM0; eauto. }
    { eapply BOTH; eauto. }
  Qed.


  Definition _fromI: (state L0 * state L1) -> (Ord.t * Ord.t * state L0 * state L1) :=
    fun '(s0, s1) => (Ord.O, Ord.O, s0, s1).

  Definition fromI: (state L0 -> state L1 -> Prop) -> (Ord.t -> Ord.t -> state L0 -> state L1 -> Prop) :=
    fun Y o0 o1 s0 s1 => exists ys0 ys1 (IN: Y ys0 ys1), (_fromI (ys0, ys1)) = (o0, o1, s0, s1).

  Definition fromI_aux: (state L0 -> state L1 -> Prop) -> (Ord.t -> Ord.t -> state L0 -> state L1 -> Prop) :=
    fun Y o0 o1 s0 s1 => o0 = 0 /\ o1 = 0 /\ Y s0 s1.

  Lemma fromI_lemma: fromI_aux = fromI.
  Proof.
    extensionalities Y o0 o1 s0 s1. eapply prop_ext. split; i.
    - rr in H. des; subst. r. eauto.
    - rr in H. des; subst. ss. clarify.
  Qed.

  Goal forall X0 i0 i1 s0 s1,
      fromI (_simI X0) i0 i1 s0 s1 -> (_sim (fromI X0)) i0 i1 s0 s1.
  Proof.
    i. rewrite <- fromI_lemma in *. red in H. des; subst.
    induction H1 using _simI_ind2.
    - econs 1; eauto.
    - econs 2; eauto.
      i. exploit SIM; eauto. i; des. esplits; eauto. r. esplits; eauto.
    - econs 3; eauto.
    - des. econs 4; eauto.
    - des. econs 5; eauto. i. exploit SIM; eauto. i; des. esplits; eauto.
    - econs 5; eauto. i.
      exploit SIM; eauto. i; des. esplits; eauto.
      econs 4; eauto. esplits; eauto.
      econsr; eauto.
      { r. esplits; eauto. }
      { instantiate (1:=1). eapply OrdArith.lt_from_nat. lia. }
      { instantiate (1:=1). eapply OrdArith.lt_from_nat. lia. }
  Qed.

End SIM.
End REPLAY.
