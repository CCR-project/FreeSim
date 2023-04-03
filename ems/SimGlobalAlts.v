Require Import Coqlib.
Require Import ITreelib.
Require Import Any.
Require Import STS.
Require Import Behavior ModSemE.
Require Import Skeleton.
Require Import Coq.Relations.Relation_Definitions.
Require Import Relation_Operators.
Require Import RelationPairs.
From Ordinal Require Import Ordinal Arithmetic.
From Ordinal Require Import ClassicalOrdinal.

Require Import WFLib.

Set Implicit Arguments.

Section COMMON.

  Variable E: Type -> Type.
  Variable R: Type.
  Let ITR := (itree (E +' eventE) R).

  Variant obs_step (args: string * Any.t * (Any.t -> Prop) * Any.t) (r: ITR -> Prop): ITR -> Prop :=
    | obs_step_syscall
        fn varg rvs ktr v
        (REL: r (ktr v))
        (ARGS: args = (fn, varg, rvs, v))
      :
      obs_step args r (trigger (SyscallOut fn varg rvs) >>= ktr)
  .

  Variant obs_step_in (args: Any.t) (r: ITR -> Prop): ITR -> Prop :=
    | obs_step_syscall_in
        rv ktr
        (REL: r (ktr tt))
        (ARGS: args = rv)
      :
      obs_step_in args r (trigger (SyscallIn rv) >>= ktr)
  .

  Variant is_obs (arg: string * Any.t * (Any.t -> Prop)): ITR -> Prop :=
    | is_obs_intro
        fn varg rvs ktr
        (ARG: arg = (fn, varg, rvs))
      :
      is_obs arg (trigger (SyscallOut fn varg rvs) >>= ktr).

  Variant is_obs_in (arg: Any.t): ITR -> Prop :=
    | is_obs_in_intro
        rv ktr
        (ARG: arg = rv)
      :
      is_obs_in arg (trigger (SyscallIn rv) >>= ktr).

  Variant event_step {X: Type} (x: X) (r: ITR -> Prop): ITR -> Prop :=
    | event_step_intro
        (e: E X) ktr
        (REL: r (ktr x))
      :
      event_step x r (trigger e >>= ktr)
  .

  Variant is_event {X: Type} (e: E X): ITR -> Prop :=
    | is_event_intro
        ktr
      :
      is_event e (trigger e >>= ktr).

  Variant is_ret (rv: R): ITR -> Prop :=
    | is_ret_intro: is_ret rv (Ret rv).


  (* roperties *)
  Lemma obs_step_mon
        args (r0 r1: ITR -> Prop) itr
        (MON: forall itr, (r0 itr) -> (r1 itr))
    :
    (obs_step args r0 itr) -> (obs_step args r1 itr).
  Proof. i. inv H. econs; eauto. Qed.

  Lemma obs_step_in_mon
        args (r0 r1: ITR -> Prop) itr
        (MON: forall itr, (r0 itr) -> (r1 itr))
    :
    (obs_step_in args r0 itr) -> (obs_step_in args r1 itr).
  Proof. i. inv H. econs; eauto. Qed.

  Lemma event_step_mon
        X (x: X) (r0 r1: ITR -> Prop) itr
        (MON: forall itr, (r0 itr) -> (r1 itr))
    :
    (event_step x r0 itr) -> (event_step x r1 itr).
  Proof. i. inv H. econs; eauto. Qed.

End COMMON.

Section SRCSTEPS.

  Variable E: Type -> Type.
  Variable R: Type.
  Let ITR := (itree (E +' eventE) R).
  Let ARGS := (option (string * Any.t * (Any.t -> Prop) * Any.t)).

  (* src tau step *)
  Variant st_step (r: ITR -> Prop): ITR -> Prop :=
    | st_step_tau
        ktr
        (REL: r ktr)
      :
      st_step r (tau;; ktr)
    | st_step_choose
        X ktr
        (REL: exists x, r (ktr x))
      :
      st_step r (trigger (Choose X) >>= ktr)
    | st_step_take
        X ktr
        (REL: forall x, r (ktr x))
      :
      st_step r (trigger (Take X) >>= ktr)
  .

  (* properties *)
  Lemma st_step_mon
        (r0 r1: ITR -> Prop) itr
        (MON: forall itr, (r0 itr) -> (r1 itr))
    :
    (st_step r0 itr) -> (st_step r1 itr).
  Proof.
    i. inv H; econs; eauto. des. eauto.
  Qed.

End SRCSTEPS.

Section TGTSTEPS.

  Variable E: Type -> Type.
  Variable R: Type.
  Let ITR := (itree (E +' eventE) R).
  Let ARGS := (option (string * Any.t * (Any.t -> Prop) * Any.t)).

  (* tgt tau step *)
  Variant tt_step (r: ITR -> Prop): ITR -> Prop :=
    | tt_step_tau
        ktr
        (REL: r ktr)
      :
      tt_step r (tau;; ktr)
    | tt_step_choose
        X ktr
        (REL: forall x, r (ktr x))
      :
      tt_step r (trigger (Choose X) >>= ktr)
    | tt_step_take
        X ktr
        (REL: exists x, r (ktr x))
      :
      tt_step r (trigger (Take X) >>= ktr)
  .

  (* properties *)
  Lemma tt_step_mon
        (r0 r1: ITR -> Prop) itr
        (MON: forall itr, (r0 itr) -> (r1 itr))
    :
    (tt_step r0 itr) -> (tt_step r1 itr).
  Proof.
    i. inv H; econs; eauto. des. eauto.
  Qed.

End TGTSTEPS.

Section EXP_SIM.

  Variable E: Type -> Type.
  Variable wfo: WF.

  Definition _simg_alt_exp
             (simg_alt_exp: forall R0 R1 (RR: R0 -> R1 -> Prop), wfo.(T) -> (itree (E +' eventE) R0) -> (itree (E +' eventE) R1) -> Prop)
             {R0 R1} (RR: R0 -> R1 -> Prop) (exp: wfo.(T)): (itree (E +' eventE) R0) -> (itree (E +' eventE) R1) -> Prop :=
    fun itr_src itr_tgt =>
      (exists rs rt, (<<TGT: is_ret rt itr_tgt>>) /\ (<<SRC: is_ret rs itr_src>>) /\ (<<RET: RR rs rt>>))
      \/
        (exists arg,
            ((is_obs arg itr_src) /\ (is_obs arg itr_tgt)) /\
              ((<<OBS: forall rv, obs_step (arg, rv) (fun ktr_tgt => obs_step (arg, rv) (fun ktr_src => exists exp0, (simg_alt_exp _ _ RR exp0 ktr_src ktr_tgt)) itr_src) itr_tgt>>)))
      \/
        (exists arg,
            ((is_obs_in arg itr_src) /\ (is_obs_in arg itr_tgt)) /\
              ((<<OBS: obs_step_in (arg) (fun ktr_tgt => obs_step_in (arg) (fun ktr_src => exists exp0, (simg_alt_exp _ _ RR exp0 ktr_src ktr_tgt)) itr_src) itr_tgt>>)))
      \/
        (exists X (e: E X),
            ((is_event e itr_src) /\ (is_event e itr_tgt)) /\
              (forall (xs xt: X) (EQ: xs = xt), (<<EVE: event_step xt (fun ktr_tgt => event_step xs (fun ktr_src => exists exp0, (simg_alt_exp _ _ RR exp0 ktr_src ktr_tgt)) itr_src) itr_tgt>>)))
      \/
        (
          (<<TGT: (tt_step (fun ktr_tgt =>
                              (st_step (fun ktr_src => exists exp0, (simg_alt_exp _ _ RR exp0 ktr_src ktr_tgt)) itr_src)
                              \/ (exists exp0, (simg_alt_exp _ _ RR exp0 itr_src ktr_tgt) /\ (wfo.(lt) exp0 exp))
                           ) itr_tgt)>>)
          \/
            (<<SRC: (st_step (fun ktr_src =>
                                (tt_step (fun ktr_tgt => exists exp0, (simg_alt_exp _ _ RR exp0 ktr_src ktr_tgt)) itr_tgt)
                                \/ (exists exp0, (simg_alt_exp _ _ RR exp0 ktr_src itr_tgt) /\ (wfo.(lt) exp0 exp))
                             ) itr_src)>>)
        )
  .

  Definition simg_alt_exp: forall R0 R1 (RR: R0 -> R1 -> Prop), wfo.(T) -> (itree (E +' eventE) R0) -> (itree (E +' eventE) R1) -> Prop := paco6 _simg_alt_exp bot6.

  Lemma simg_alt_exp_mon: monotone6 _simg_alt_exp.
  Proof.
    ii. inv IN.
    { left. eauto. }
    right. des; [left | right; left | do 2 right; left | do 3 right; left | repeat right].
    { exists arg. splits; auto. i. eapply obs_step_mon; [|eauto]. i; ss.
      eapply obs_step_mon; [|eauto]. i; ss. des; eauto.
    }
    { exists arg. splits; auto. eapply obs_step_in_mon; [|eauto]. i; ss.
      eapply obs_step_in_mon; [|eauto]. i; ss. des; eauto.
    }
    { exists X, e. splits; auto. i. specialize (H0 _ _ EQ). eapply event_step_mon; [|eauto]. i; ss.
      eapply event_step_mon; [|eauto]. i; ss. des; eauto.
    }    
    { eapply tt_step_mon. 2: eauto. i; ss. des; [left | right].
      - eapply st_step_mon. 2: eauto. i; ss. des; eauto.
      - esplits; eauto.
    }
    { eapply st_step_mon. 2: eauto. i; ss. des; [left | right].
      - eapply tt_step_mon. 2: eauto. i; ss. des; eauto.
      - esplits; eauto.
    }
  Qed.

  Hint Resolve simg_alt_exp_mon: paco.
  Hint Resolve cpn6_wcompat: paco.

End EXP_SIM.
Hint Unfold simg_alt_exp.
Hint Resolve simg_alt_exp_mon: paco.
Hint Resolve cpn6_wcompat: paco.


Section IMP_SIM.

  Variable E: Type -> Type.

  Inductive _simg_alt_imp
            (simg_alt_imp: forall R0 R1 (RR: R0 -> R1 -> Prop), (itree (E +' eventE) R0) -> (itree (E +' eventE) R1) -> Prop)
            {R0 R1} (RR: R0 -> R1 -> Prop)
            (itr_src: itree (E +' eventE) R0) (itr_tgt: itree (E +' eventE) R1): Prop :=
  | simg_alt_imp_intro
      (SIM:
        (exists rs rt, (<<TGT: is_ret rt itr_tgt>>) /\ (<<SRC: is_ret rs itr_src>>) /\ (<<RET: RR rs rt>>))
        \/
          (exists arg,
              ((is_obs arg itr_src) /\ (is_obs arg itr_tgt)) /\
                (<<OBS: forall rv, obs_step (arg, rv) (fun ktr_tgt => obs_step (arg, rv) (fun ktr_src => (simg_alt_imp _ _ RR ktr_src ktr_tgt)) itr_src) itr_tgt>>))
        \/
          (exists arg,
              ((is_obs_in arg itr_src) /\ (is_obs_in arg itr_tgt)) /\
                (<<OBS: obs_step_in (arg) (fun ktr_tgt => obs_step_in (arg) (fun ktr_src => (simg_alt_imp _ _ RR ktr_src ktr_tgt)) itr_src) itr_tgt>>))
        \/
          (exists X (e: E X),
              ((is_event e itr_src) /\ (is_event e itr_tgt)) /\
                (forall (xs xt: X) (EQ: xs = xt), (<<EVE: event_step xt (fun ktr_tgt => event_step xs (fun ktr_src => (simg_alt_imp _ _ RR ktr_src ktr_tgt)) itr_src) itr_tgt>>)))
        \/
          (
            (<<TGT: (tt_step (fun ktr_tgt =>
                                (st_step (fun ktr_src => (simg_alt_imp _ _ RR ktr_src ktr_tgt)) itr_src)
                                \/ (_simg_alt_imp simg_alt_imp RR itr_src ktr_tgt)
                             ) itr_tgt)>>)
            \/
              (<<SRC: (st_step (fun ktr_src =>
                                  (tt_step (fun ktr_tgt => (simg_alt_imp _ _ RR ktr_src ktr_tgt)) itr_tgt)
                                  \/ (_simg_alt_imp simg_alt_imp RR ktr_src itr_tgt)
                               ) itr_src)>>)
      ))
  .

  Lemma _simg_alt_imp_ind2
        (r: forall R0 R1 (RR: R0 -> R1 -> Prop), (itree (E +' eventE) R0) -> (itree (E +' eventE) R1) -> Prop)
        R0 R1 (RR: R0 -> R1 -> Prop)
        (P: (itree (E +' eventE) R0) -> (itree (E +' eventE) R1) -> Prop)
        (RET: forall
            itr_src itr_tgt rs rt
            (TGT: is_ret rt itr_tgt)
            (SRC: is_ret rs itr_src)
            (SIM: RR rs rt),
            P itr_src itr_tgt)
        (OBS: forall
            itr_src itr_tgt arg
            (SRC: is_obs arg itr_src)
            (TGT: is_obs arg itr_tgt)
            (SIM: forall rv,
              obs_step (arg, rv) (fun ktr_tgt => obs_step (arg, rv) (fun ktr_src => (r _ _ RR ktr_src ktr_tgt)) itr_src) itr_tgt),
            P itr_src itr_tgt)
        (OBSIN: forall
            itr_src itr_tgt arg
            (SRC: is_obs_in arg itr_src)
            (TGT: is_obs_in arg itr_tgt)
            (SIM:
              obs_step_in (arg) (fun ktr_tgt => obs_step_in (arg) (fun ktr_src => (r _ _ RR ktr_src ktr_tgt)) itr_src) itr_tgt),
            P itr_src itr_tgt)
        (EVE: forall
            X (e: E X) itr_src itr_tgt
            (SRC: is_event e itr_src)
            (TGT: is_event e itr_tgt)
            (SIM: forall (xs xt: X) (EQ: xs = xt),
                event_step xt (fun ktr_tgt => event_step xs (fun ktr_src => (r _ _ RR ktr_src ktr_tgt)) itr_src) itr_tgt),
            P itr_src itr_tgt)
        (TGT: forall
            itr_src itr_tgt
            (SIM: tt_step (fun ktr_tgt => (st_step (fun ktr_src => (r _ _ RR ktr_src ktr_tgt)) itr_src) \/ ((<<SIM: _simg_alt_imp r RR itr_src ktr_tgt>>) /\ (<<IH: P itr_src ktr_tgt>>))) itr_tgt),
            P itr_src itr_tgt)
        (SRC: forall
            itr_src itr_tgt
            (SIM: st_step (fun ktr_src => (tt_step (fun ktr_tgt => (r _ _ RR ktr_src ktr_tgt)) itr_tgt) \/ ((<<SIM: _simg_alt_imp r RR ktr_src itr_tgt>>) /\ (<<IH: P ktr_src itr_tgt>>))) itr_src),
            P itr_src itr_tgt)
    :
    forall itr_src itr_tgt
      (SIM: _simg_alt_imp r RR itr_src itr_tgt),
      P itr_src itr_tgt.
  Proof.
    fix IH 3. i. inv SIM. des.
    { eapply RET; eauto. }
    { eapply OBS; eauto. }
    { eapply OBSIN; eauto. }
    { eapply EVE; eauto. }
    { eapply TGT; eauto. inv TGT0.
      - econs 1. des; [left|right]; eauto.
      - econs 2. i. specialize (REL x). des; [left|right]; eauto.
      - econs 3. destruct REL as [x REL]. exists x. des; [left|right]; eauto.
    }
    { eapply SRC; eauto. inv SRC0.
      - econs 1. des; [left|right]; eauto.
      - econs 2. destruct REL as [x REL]. exists x. des; [left|right]; eauto.
      - econs 3. i. specialize (REL x). des; [left|right]; eauto.
    }
  Qed.

  Definition simg_alt_imp: forall R0 R1 (RR: R0 -> R1 -> Prop), (itree (E +' eventE) R0) -> (itree (E +' eventE) R1) -> Prop := paco5 _simg_alt_imp bot5.

  Lemma simg_alt_imp_mon: monotone5 _simg_alt_imp.
  Proof.
    ii. induction IN using _simg_alt_imp_ind2.
    { econs. left; eauto. }
    { econs. right; left. esplits; eauto. i.
      eapply obs_step_mon; [|eauto]. i; ss. eapply obs_step_mon; [|eauto]. i; ss. auto.
    }
    { econs. do 2 right; left. esplits; eauto. i.
      eapply obs_step_in_mon; [|eauto]. i; ss. eapply obs_step_in_mon; [|eauto]. i; ss. auto.
    }
    { econs. do 3 right; left. esplits; eauto. i. specialize (SIM _ _ EQ).
      eapply event_step_mon; [|eauto]. i; ss. eapply event_step_mon; [|eauto]. i; ss. auto.
    }
    { econs. do 4 right; left. eapply tt_step_mon; [|eauto]. i; ss. des; [left|right]; auto.
      eapply st_step_mon; [|eauto]. i; ss. auto.
    }
    { econs. do 5 right. eapply st_step_mon; [|eauto]. i; ss. des; [left|right]; auto.
      eapply tt_step_mon; [|eauto]. i; ss. auto.
    }
  Qed.
  Hint Resolve simg_alt_imp_mon: paco.
  Hint Resolve cpn5_wcompat: paco.


  Variant simg_alt_imp_indC
          (simg_alt_imp: forall R0 R1 (RR: R0 -> R1 -> Prop), (itree (E +' eventE) R0) -> (itree (E +' eventE) R1) -> Prop)
          {R0 R1} (RR: R0 -> R1 -> Prop): (itree (E +' eventE) R0) -> (itree (E +' eventE) R1) -> Prop :=
    | simg_alt_imp_indC_ret
        itr_src itr_tgt rs rt
        (TGT: is_ret rt itr_tgt)
        (SRC: is_ret rs itr_src)
        (SIM: RR rs rt)
      :
      simg_alt_imp_indC simg_alt_imp RR itr_src itr_tgt
    | simg_alt_imp_indC_obs
        itr_src itr_tgt arg
        (SRC: is_obs arg itr_src)
        (TGT: is_obs arg itr_tgt)
        (SIM: forall rv,
            obs_step (arg, rv) (fun ktr_tgt => obs_step (arg, rv) (fun ktr_src => (simg_alt_imp _ _ RR ktr_src ktr_tgt)) itr_src) itr_tgt)
      :
      simg_alt_imp_indC simg_alt_imp RR itr_src itr_tgt
    | simg_alt_imp_indC_obs_in
        itr_src itr_tgt arg
        (SRC: is_obs_in arg itr_src)
        (TGT: is_obs_in arg itr_tgt)
        (SIM:
            obs_step_in (arg) (fun ktr_tgt => obs_step_in (arg) (fun ktr_src => (simg_alt_imp _ _ RR ktr_src ktr_tgt)) itr_src) itr_tgt)
      :
      simg_alt_imp_indC simg_alt_imp RR itr_src itr_tgt
    | simg_alt_imp_indC_event
        X (e: E X) itr_src itr_tgt
        (SRC: is_event e itr_src)
        (TGT: is_event e itr_tgt)
        (SIM: forall (xs xt: X) (EQ: xs = xt),
            event_step xt (fun ktr_tgt => event_step xs (fun ktr_src => (simg_alt_imp _ _ RR ktr_src ktr_tgt)) itr_src) itr_tgt)
      :
      simg_alt_imp_indC simg_alt_imp RR itr_src itr_tgt
    | simg_alt_imp_indC_tgt
        itr_src itr_tgt
        (SIM: tt_step (fun ktr_tgt => (st_step (fun ktr_src => (simg_alt_imp _ _ RR ktr_src ktr_tgt)) itr_src) \/ (<<SIM: simg_alt_imp _ _ RR itr_src ktr_tgt>>)) itr_tgt)
      :
      simg_alt_imp_indC simg_alt_imp RR itr_src itr_tgt
    | simg_alt_imp_indC_src
        itr_src itr_tgt
        (SIM: st_step (fun ktr_src => (tt_step (fun ktr_tgt => (simg_alt_imp _ _ RR ktr_src ktr_tgt)) itr_tgt) \/ (<<SIM: simg_alt_imp _ _ RR ktr_src itr_tgt>>)) itr_src)
      :
      simg_alt_imp_indC simg_alt_imp RR itr_src itr_tgt
  .

  Lemma simg_alt_imp_indC_mon: monotone5 simg_alt_imp_indC.
  Proof.
    ii. inv IN.
    { econs 1; eauto. }
    { econs 2; eauto. i.
      eapply obs_step_mon; [|eauto]. i; ss. eapply obs_step_mon; [|eauto]. i; ss. auto.
    }
    { econs 3; eauto. i.
      eapply obs_step_in_mon; [|eauto]. i; ss. eapply obs_step_in_mon; [|eauto]. i; ss. auto.
    }
    { econs 4; eauto. i. specialize (SIM _ _ EQ).
      eapply event_step_mon; [|eauto]. i; ss. eapply event_step_mon; [|eauto]. i; ss. auto.
    }
    { econs 5; eauto. eapply tt_step_mon; [|eauto]. i; ss. des; eauto. left.
      eapply st_step_mon; [|eauto]. i; ss. auto.
    }
    { econs 6; eauto. eapply st_step_mon; [|eauto]. i; ss. des; eauto. left.
      eapply tt_step_mon; [|eauto]. i; ss. auto.
    }
  Qed.
  Hint Resolve simg_alt_imp_indC_mon: paco.

  Lemma simg_alt_imp_indC_spec:
    simg_alt_imp_indC <6= gupaco5 _simg_alt_imp (cpn5 _simg_alt_imp).
  Proof.
    eapply wrespect5_uclo; eauto with paco.
    econs; eauto with paco. i. inv PR.
    { econs. left; eauto. }
    { econs. right; left. esplits; eauto. i.
      eapply obs_step_mon; [|eauto]. i; ss. eapply obs_step_mon; [|eauto]. i; ss.
      apply rclo5_base. auto.
    }
    { econs. do 2 right; left. esplits; eauto. i.
      eapply obs_step_in_mon; [|eauto]. i; ss. eapply obs_step_in_mon; [|eauto]. i; ss.
      apply rclo5_base. auto.
    }
    { econs. do 3 right; left. esplits; eauto. i. specialize (SIM _ _ EQ).
      eapply event_step_mon; [|eauto]. i; ss. eapply event_step_mon; [|eauto]. i; ss.
      apply rclo5_base. auto.
    }
    { econs. do 4 right; left. eapply tt_step_mon; [|eauto]. i; ss. des; [left|right].
      - eapply st_step_mon; [|eauto]. i; ss. apply rclo5_base. auto.
      - eapply simg_alt_imp_mon; eauto. i. apply rclo5_base; auto.
    }
    { econs. do 5 right. eapply st_step_mon; [|eauto]. i; ss. des; [left|right].
      - eapply tt_step_mon; [|eauto]. i; ss. apply rclo5_base. auto.
      - eapply simg_alt_imp_mon; eauto. i. apply rclo5_base; auto.
    }
  Qed.

  Lemma simg_alt_imp_ind R0 R1 (RR: R0 -> R1 -> Prop)
        (P: (itree (E +' eventE) R0) -> (itree (E +' eventE) R1) -> Prop)
        (RET: forall
            itr_src itr_tgt rs rt
            (TGT: is_ret rt itr_tgt)
            (SRC: is_ret rs itr_src)
            (SIM: RR rs rt),
            P itr_src itr_tgt)
        (OBS: forall
            itr_src itr_tgt arg
            (SRC: is_obs arg itr_src)
            (TGT: is_obs arg itr_tgt)
            (SIM: forall rv,
                obs_step (arg, rv) (fun ktr_tgt => obs_step (arg, rv) (fun ktr_src => (simg_alt_imp RR ktr_src ktr_tgt)) itr_src) itr_tgt),
            P itr_src itr_tgt)
        (OBSIN: forall
            itr_src itr_tgt arg
            (SRC: is_obs_in arg itr_src)
            (TGT: is_obs_in arg itr_tgt)
            (SIM:
                obs_step_in (arg) (fun ktr_tgt => obs_step_in (arg) (fun ktr_src => (simg_alt_imp RR ktr_src ktr_tgt)) itr_src) itr_tgt),
            P itr_src itr_tgt)
        (EVE: forall
            X (e: E X) itr_src itr_tgt
            (SRC: is_event e itr_src)
            (TGT: is_event e itr_tgt)
            (SIM: forall (xs xt: X) (EQ: xs = xt),
                event_step xt (fun ktr_tgt => event_step xs (fun ktr_src => (simg_alt_imp RR ktr_src ktr_tgt)) itr_src) itr_tgt),
            P itr_src itr_tgt)
        (TGT: forall
            itr_src itr_tgt
            (SIM: tt_step (fun ktr_tgt => (st_step (fun ktr_src => (simg_alt_imp RR ktr_src ktr_tgt)) itr_src) \/ ((<<SIM: simg_alt_imp RR itr_src ktr_tgt>>) /\ (<<IH: P itr_src ktr_tgt>>))) itr_tgt),
            P itr_src itr_tgt)
        (SRC: forall
            itr_src itr_tgt
            (SIM: st_step (fun ktr_src => (tt_step (fun ktr_tgt => (simg_alt_imp RR ktr_src ktr_tgt)) itr_tgt) \/ ((<<SIM: simg_alt_imp RR ktr_src itr_tgt>>) /\ (<<IH: P ktr_src itr_tgt>>))) itr_src),
            P itr_src itr_tgt)
    :
    forall itr_src itr_tgt
      (SIM: simg_alt_imp RR itr_src itr_tgt),
      P itr_src itr_tgt.
  Proof.
    i. punfold SIM. induction SIM using _simg_alt_imp_ind2; i; clarify.
    { eapply RET; eauto. }
    { eapply OBS; eauto. i.
      eapply obs_step_mon; [|eauto]. i; ss. eapply obs_step_mon; [|eauto]. i; ss.
      pclearbot. eauto.
    }
    { eapply OBSIN; eauto. i.
      eapply obs_step_in_mon; [|eauto]. i; ss. eapply obs_step_in_mon; [|eauto]. i; ss.
      pclearbot. eauto.
    }
    { eapply EVE; eauto. i. specialize (SIM _ _ EQ).
      eapply event_step_mon; [|eauto]. i; ss. eapply event_step_mon; [|eauto]. i; ss.
      pclearbot. eauto.
    }
    { eapply TGT; eauto.
      eapply tt_step_mon; [|eauto]. i; ss. des; [left|des; right; split]; eauto.
      - eapply st_step_mon; [|eauto]. i; ss. pclearbot. auto.
      - pfold. auto.
    }
    { eapply SRC; eauto.
      eapply st_step_mon; [|eauto]. i; ss. des; [left|des; right; split]; eauto.
      - eapply tt_step_mon; [|eauto]. i; ss. pclearbot. auto.
      - pfold. auto.
    }
  Qed.

End IMP_SIM.
Hint Constructors _simg_alt_imp.
Hint Unfold simg_alt_imp.
Hint Resolve simg_alt_imp_mon: paco.
Hint Resolve cpn5_wcompat: paco.


(** obs steps asynchronous **)
(* Section EXP_SIM. *)

(*   Variable wfo: WF. *)

(*   Definition _simg_alt_exp *)
(*              (simg_alt_exp: forall R0 R1 (RR: R0 -> R1 -> Prop), wfo.(T) -> (itree (E +' eventE) R0) -> (itree (E +' eventE) R1) -> Prop) *)
(*              {R0 R1} (RR: R0 -> R1 -> Prop) (exp: wfo.(T)): (itree (E +' eventE) R0) -> (itree (E +' eventE) R1) -> Prop := *)
(*     fun itr_src itr_tgt => *)
(*       (exists rt rs, (<<TGT: is_ret rt itr_tgt>>) /\ (<<SRC: is_ret rs itr_src>>) /\ (<<RET: RR rs rt>>)) *)
(*       \/ *)
(*         ( *)
(*           (<<TGT: (tgt_step (fun targ ktr_tgt => *)
(*                                (src_step (fun sarg ktr_src => (<<EQ: targ = sarg>>) -> exists exp0, (simg_alt_exp _ _ RR exp0 ktr_src ktr_tgt)) itr_src) *)
(*                                \/ ((targ = None) /\ exists exp0, (simg_alt_exp _ _ RR exp0 itr_src ktr_tgt) /\ (wfo.(lt) exp0 exp)) *)
(*                             ) itr_tgt)>>) *)
(*           \/ *)
(*             (<<SRC: (src_step (fun sarg ktr_src => *)
(*                                  (tgt_step (fun targ ktr_tgt => (<<EQ: sarg = targ>>) -> exists exp0, (simg_alt_exp _ _ RR exp0 ktr_src ktr_tgt)) itr_tgt) *)
(*                                  \/ ((sarg = None) /\ exists exp0, (simg_alt_exp _ _ RR exp0 ktr_src itr_tgt) /\ (wfo.(lt) exp0 exp)) *)
(*                               ) itr_src)>>) *)
(*         ) *)
(*   . *)

(*   Definition simg_alt_exp: forall R0 R1 (RR: R0 -> R1 -> Prop), wfo.(T) -> (itree (E +' eventE) R0) -> (itree (E +' eventE) R1) -> Prop := paco6 _simg_alt_exp bot6. *)

(*   Lemma simg_alt_exp_mon: monotone6 _simg_alt_exp. *)
(*   Proof. *)
(*     ii. inv IN. *)
(*     { left. eauto. } *)
(*     right. des; [left | right]. *)
(*     { eapply tgt_step_mon. 2: eauto. i; ss. des; [left | right]. *)
(*       - eapply src_step_mon. 2: eauto. i; ss. specialize (H0 H1). des; eauto. *)
(*       - split; eauto. *)
(*     } *)
(*     { eapply src_step_mon. 2: eauto. i; ss. des; [left | right]. *)
(*       - eapply tgt_step_mon. 2: eauto. i; ss. specialize (H0 H1). des; eauto. *)
(*       - split; eauto. *)
(*     } *)
(*   Qed. *)

(*   Hint Resolve simg_alt_exp_mon: paco. *)
(*   Hint Resolve cpn6_wcompat: paco. *)

(* End EXP_SIM. *)
(* Hint Unfold simg_alt_exp. *)
(* Hint Resolve simg_alt_exp_mon: paco. *)
(* Hint Resolve cpn6_wcompat: paco. *)


(** star and plus steps **)
(* Section EXP_SIM. *)

(*   Variable wfo: WF. *)

(*   Definition _simg_alt_exp *)
(*              (simg_alt_exp: forall R0 R1 (RR: R0 -> R1 -> Prop), wfo.(T) -> (itree (E +' eventE) R0) -> (itree (E +' eventE) R1) -> Prop) *)
(*              {R0 R1} (RR: R0 -> R1 -> Prop) (exp: wfo.(T)): (itree (E +' eventE) R0) -> (itree (E +' eventE) R1) -> Prop := *)
(*     fun itr_src itr_tgt => *)
(*       (exists rt rs, (<<TGT: is_ret rt itr_tgt>>) /\ (<<SRC: is_ret rs itr_src>>) /\ (<<RET: RR rs rt>>)) *)
(*       \/ *)
(*         ((<<TGT: (tt_step (fun ktr_tgt => (st_star (fun ktr_src => exists exp0, (simg_alt_exp _ _ RR exp0 ktr_src ktr_tgt) /\ (wfo.(lt) exp0 exp)) itr_src)) itr_tgt)>>) *)
(*          \/ *)
(*            (<<SRC: (st_step (fun ktr_src => (tt_star (fun ktr_tgt => exists exp0, (simg_alt_exp _ _ RR exp0 ktr_src ktr_tgt) /\ (wfo.(lt) exp0 exp)) itr_tgt)) itr_src)>>) *)
(*          \/ *)
(*            (<<TPLUS: (tgt_plus (fun targ ktr_tgt => (src_plus (fun sarg ktr_src => (<<EQ: targ = sarg>>) -> exists exp0, (simg_alt_exp _ _ RR exp0 ktr_src ktr_tgt)) itr_src)) itr_tgt)>>) *)
(*          \/ *)
(*            (<<SPLUS: (src_plus (fun sarg ktr_src => (tgt_plus (fun targ ktr_tgt => (<<EQ: sarg = targ>>) -> exists exp0, (simg_alt_exp _ _ RR exp0 ktr_src ktr_tgt)) itr_tgt)) itr_src)>>) *)
(*         ) *)
(*   . *)

(*   Definition simg_alt_exp: forall R0 R1 (RR: R0 -> R1 -> Prop), wfo.(T) -> (itree (E +' eventE) R0) -> (itree (E +' eventE) R1) -> Prop := paco6 _simg_alt_exp bot6. *)

(*   Lemma simg_alt_exp_mon: monotone6 _simg_alt_exp. *)
(*   Proof. *)
(*     ii. inv IN. *)
(*     { left. eauto. } *)
(*     right. des; [left | right; left | do 2 right; left | do 3 right]. *)
(*     { eapply tt_step_mon. 2: eauto. i; ss. eapply st_star_mon. 2: eauto. i; ss. des; eauto. } *)
(*     { eapply st_step_mon. 2: eauto. i; ss. eapply tt_star_mon. 2: eauto. i; ss. des; eauto. } *)
(*     { eapply tgt_plus_mon. 2: eauto. i; ss. eapply src_plus_mon. 2: eauto. i; ss. *)
(*       specialize (H0 H1). des; eauto. } *)
(*     { eapply src_plus_mon. 2: eauto. i; ss. eapply tgt_plus_mon. 2: eauto. i; ss. *)
(*       specialize (H0 H1). des; eauto. } *)
(*   Qed. *)

(*   Hint Resolve simg_alt_exp_mon: paco. *)
(*   Hint Resolve cpn6_wcompat: paco. *)

(* End EXP_SIM. *)
(* Hint Unfold simg_alt_exp. *)
(* Hint Resolve simg_alt_exp_mon: paco. *)
(* Hint Resolve cpn6_wcompat: paco. *)
