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

Lemma replay_mon A B
      (F0 F1: (A -> Prop) -> (A -> Prop))
      (G0 G1: (B -> Prop) -> (B -> Prop))
      c
      (REPLAY: replay F1 G0 c)
      (LE0: forall r, F0 r <1= F1 r)
      (LE1: forall r, G0 r <1= G1 r)
  :
  replay F0 G1 c.
Proof.
  rr. i. eapply LE1. eapply REPLAY.
  eapply c.(Galois.alpha_mon); [|eauto]. eauto.
Qed.

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

Lemma replay_join A B I
      (F: I -> (A -> Prop) -> (A -> Prop))
      (G: (B -> Prop) -> (B -> Prop))
      c
      (REPLAY: forall i, replay (F i) G c)
  :
  replay (fun r x => exists i, F i r x) G c.
Proof.
  intros a. eapply c.(Galois.adjunct_iso1). intros. destruct PR.
  eapply c.(Galois.adjunct_iso0); [eapply REPLAY|]. eauto.
Qed.

Lemma replay_union A B
      (F0 F1: (A -> Prop) -> (A -> Prop))
      (G: (B -> Prop) -> (B -> Prop))
      c
      (REPLAY0: replay F0 G c)
      (REPLAY1: replay F1 G c)
  :
  replay (fun r x => F0 r x \/ F1 r x) G c.
Proof.
  intros a. eapply c.(Galois.adjunct_iso1). intros. destruct PR.
  { eapply c.(Galois.adjunct_iso0); [eapply REPLAY0|]. eauto. }
  { eapply c.(Galois.adjunct_iso0); [eapply REPLAY1|]. eauto. }
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
          (<<SRC: Ord.le (Ord.from_wf wfo.(wf) o) f_src>>) /\ (<<TGT: Ord.le (Ord.from_wf wfo.(wf) o) f_tgt>>).

    Definition esim_galois_gamma
               R0 R1
               (r: forall (f_src f_tgt: Ord.t)
                          (itr_src: itree (E +' ModSemE.eventE) R0)
                          (itr_tgt: itree (E +' ModSemE.eventE) R1), Prop)
               (o: wfo.(T))
               (itr_src: itree (E +' ModSemE.eventE) R0)
               (itr_tgt: itree (E +' ModSemE.eventE) R1): Prop :=
      forall f_src f_tgt
             (SRC: Ord.le (Ord.from_wf wfo.(wf) o) f_src)
             (TGT: Ord.le (Ord.from_wf wfo.(wf) o) f_tgt),
        r f_src f_tgt itr_src itr_tgt.

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
      { inv SRC0. inv TGT0. eapply simg_ret; eauto; try refl. }
      { inv OBS. inv REL. inv H. inv H0. des. clarify.
        eapply trigger_inj2 in H1. eapply trigger_inj2 in H2. des; subst.
        econs 2. r. rewrite REQ. destruct x_src, x_tgt. esplits; eauto.
        { refl. }
        { refl. }
      }
      { inv OBS. inv REL. inv H. inv H0. des. clarify.
        eapply trigger_inj2 in H1. eapply trigger_inj2 in H2. des; subst.
        econs 3. r. rewrite REQ. esplits; eauto.
        { refl. }
        { refl. }
      }
      { inv H. inv H1. eapply simg_event. i. subst.
        specialize (H0 x_tgt _ eq_refl). des. inv H0. inv REL.
        eapply trigger_inj2 in H0. eapply trigger_inj2 in H1. des; subst.
        rr. rewrite REQ. esplits; eauto.
        { eapply Ord.lt_le. eapply Ord.from_wf_set_upperbound. }
        { eapply Ord.lt_le. eapply Ord.from_wf_set_upperbound. }
      }
      { inv TGT0; des.
        { eapply simg_tauR; auto. inv REL; des.
          { eapply simg_tauL; auto. eapply simg_progress.
            { rewrite REQ. rr. esplits; eauto.
              { refl. }
              { refl. }
            }
            { eapply Ord.from_wf_set_upperbound. }
            { eapply Ord.from_wf_set_upperbound. }
          }
          { eapply simg_chooseL; auto. eexists. eapply simg_progress.
            { rewrite REQ. rr. esplits; eauto.
              { refl. }
              { refl. }
            }
            { eapply Ord.from_wf_set_upperbound. }
            { eapply Ord.from_wf_set_upperbound. }
          }
          { eapply simg_takeL; auto. i. specialize (REL0 x). des. eapply simg_progress.
            { rewrite REQ. rr. esplits; eauto.
              { refl. }
              { refl. }
            }
            { eapply Ord.from_wf_set_upperbound. }
            { eapply Ord.from_wf_set_upperbound. }
          }
        }
        { eapply simg_tauR; auto. eapply simg_progress.
          { rr. rewrite REQ. esplits; eauto.
            { refl. }
            { refl. }
          }
          { eapply Ord.lt_le_lt; [|eauto]. eapply Ord.lt_from_wf; eauto. }
          { eapply Ord.lt_le_lt; [|eauto]. eapply Ord.lt_from_wf; eauto. }
        }
        { eapply simg_chooseR; auto. i. specialize (REL x). inv REL.
          { inv H; des.
            { eapply simg_tauL; auto. eapply simg_progress.
              { rr. rewrite REQ; eauto. esplits; eauto.
                { refl. }
                { refl. }
              }
              { eapply Ord.from_wf_set_upperbound. }
              { eapply Ord.from_wf_set_upperbound. }
            }
            { des. eapply simg_chooseL; auto. eexists. eapply simg_progress.
              { rr. rewrite REQ; eauto. esplits; eauto.
                { refl. }
                { refl. }
              }
              { eapply Ord.from_wf_set_upperbound. }
              { eapply Ord.from_wf_set_upperbound. }
            }
            { eapply simg_takeL; auto. i. specialize (REL x2). des. eapply simg_progress.
              { rr. rewrite REQ. esplits; eauto.
                { refl. }
                { refl. }
              }
              { eapply Ord.from_wf_set_upperbound. }
              { eapply Ord.from_wf_set_upperbound. }
            }
          }
          { des. eapply simg_progress.
            { rr. rewrite REQ. esplits; eauto.
              { refl. }
              { refl. }
            }
            { eapply Ord.lt_le_lt; [|eauto]. eapply Ord.lt_from_wf; eauto. }
            { eapply Ord.from_wf_set_upperbound. }
          }
        }
        { eapply simg_takeR; auto. eexists. inv REL; des.
          { eapply simg_tauL; auto. eapply simg_progress.
            { rr. rewrite REQ. esplits; eauto.
              { refl. }
              { refl. }
            }
            { eapply Ord.from_wf_set_upperbound. }
            { eapply Ord.from_wf_set_upperbound. }
          }
          { des. eapply simg_chooseL; auto. eexists. eapply simg_progress.
            { rr. rewrite REQ. esplits; eauto.
              { refl. }
              { refl. }
            }
            { eapply Ord.from_wf_set_upperbound. }
            { eapply Ord.from_wf_set_upperbound. }
          }
          { eapply simg_takeL; auto. i. specialize (REL0 x2). des. eapply simg_progress.
            { rr. rewrite REQ. esplits; eauto.
              { refl. }
              { refl. }
            }
            { eapply Ord.from_wf_set_upperbound. }
            { eapply Ord.from_wf_set_upperbound. }
          }
        }
        { eapply simg_takeR; auto. eexists. eapply simg_progress.
          { rr. rewrite REQ. esplits; eauto.
            { refl. }
            { refl. }
          }
          { eapply Ord.lt_le_lt; [|eauto]. eapply Ord.lt_from_wf; eauto. }
          { eapply Ord.from_wf_set_upperbound. }
        }
      }
      { inv SRC0; des.
        { eapply simg_tauL; auto. inv REL; des.
          { eapply simg_tauR; auto. eapply simg_progress.
            { rr. rewrite REQ. esplits; eauto.
              { refl. }
              { refl. }
            }
            { eapply Ord.from_wf_set_upperbound. }
            { eapply Ord.from_wf_set_upperbound. }
          }
          { des. eapply simg_chooseR; auto. i. specialize (REL0 x). des. eapply simg_progress.
            { rr. rewrite REQ. esplits; eauto.
              { refl. }
              { refl. }
            }
            { eapply Ord.from_wf_set_upperbound. }
            { eapply Ord.from_wf_set_upperbound. }
          }
          { des. eapply simg_takeR; auto. eexists. eapply simg_progress.
            { rr. rewrite REQ. esplits; eauto.
              { refl. }
              { refl. }
            }
            { eapply Ord.from_wf_set_upperbound. }
            { eapply Ord.from_wf_set_upperbound. }
          }
        }
        { eapply simg_tauL; auto. eapply simg_progress.
          { rr. rewrite REQ. esplits; eauto.
            { refl. }
            { refl. }
          }
          { eapply Ord.from_wf_set_upperbound. }
          { eapply Ord.lt_le_lt; [|eauto]. eapply Ord.lt_from_wf; eauto. }
        }
        { eapply simg_chooseL; auto. eexists. inv REL; des.
          { eapply simg_tauR; auto. eapply simg_progress.
            { rr. rewrite REQ. esplits; eauto.
              { refl. }
              { refl. }
            }
            { eapply Ord.from_wf_set_upperbound. }
            { eapply Ord.from_wf_set_upperbound. }
          }
          { eapply simg_chooseR; auto. i. specialize (REL0 x2). des. eapply simg_progress.
            { rr. rewrite REQ. esplits; eauto.
              { refl. }
              { refl. }
            }
            { eapply Ord.from_wf_set_upperbound. }
            { eapply Ord.from_wf_set_upperbound. }
          }
          { des. eapply simg_takeR; auto. eexists. eapply simg_progress.
            { rr. rewrite REQ. esplits; eauto.
              { refl. }
              { refl. }
            }
            { eapply Ord.from_wf_set_upperbound. }
            { eapply Ord.from_wf_set_upperbound. }
          }
        }
        { eapply simg_chooseL; auto. eexists. eapply simg_progress.
          { rr. rewrite REQ. esplits; eauto.
            { refl. }
            { refl. }
          }
          { eapply Ord.from_wf_set_upperbound. }
          { eapply Ord.lt_le_lt; [|eauto]. eapply Ord.lt_from_wf; eauto. }
        }
        { eapply simg_takeL; eauto. i. specialize (REL x). inv REL; des.
          { inv H; des.
            { eapply simg_tauR; auto. eapply simg_progress.
              { rr. rewrite REQ. esplits; eauto.
                { refl. }
                { refl. }
              }
              { eapply Ord.from_wf_set_upperbound. }
              { eapply Ord.from_wf_set_upperbound. }
            }
            { eapply simg_chooseR; auto. i. specialize (REL x2). des. eapply simg_progress.
              { rr. rewrite REQ. esplits; eauto.
                { refl. }
                { refl. }
              }
              { eapply Ord.from_wf_set_upperbound. }
              { eapply Ord.from_wf_set_upperbound. }
            }
            { des. eapply simg_takeR; auto. eexists. eapply simg_progress.
              { rr. rewrite REQ. esplits; eauto.
                { refl. }
                { refl. }
              }
              { eapply Ord.from_wf_set_upperbound. }
              { eapply Ord.from_wf_set_upperbound. }
            }
          }
          { eapply simg_progress.
            { rr. rewrite REQ. esplits; eauto.
              { refl. }
              { refl. }
            }
            { eapply Ord.from_wf_set_upperbound. }
            { eapply Ord.lt_le_lt; [|eauto]. eapply Ord.lt_from_wf; eauto. }
          }
        }
      }
    Qed.
  End EXPLICIT.

End SIM.
