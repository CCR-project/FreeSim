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

Set Implicit Arguments.

Section COMMON.

  Variable R: Type.
  Let ITR := (itree eventE R).

  Variant obs_step (args: string * Any.t * (Any.t -> Prop) * Any.t) (r: ITR -> Prop): ITR -> Prop :=
    | obs_step_syscall
        fn varg rvs ktr v
        (REL: r (ktr v))
        (ARGS: args = (fn, varg, rvs, v))
      :
      obs_step args r (trigger (Syscall fn varg rvs) >>= ktr)
  .

  Variant is_ret (rv: R): ITR -> Prop :=
    | is_ret_intro: is_ret rv (Ret rv).

  Lemma obs_step_mon
        args (r0 r1: ITR -> Prop) itr
        (MON: forall itr, (r0 itr) -> (r1 itr))
    :
    (obs_step args r0 itr) -> (obs_step args r1 itr).
  Proof.
    i. inv H. econs; eauto.
  Qed.

End COMMON.

Section SRCSTEPS.

  Variable R: Type.
  Let ITR := (itree eventE R).

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

  Inductive st_star (r: ITR -> Prop): ITR -> Prop :=
  | st_star_base itr (REL: r itr): st_star r itr
  | st_star_step itr (REL: st_step (fun ktr => st_star r ktr) itr): st_star r itr
  .

  Definition src_step (r: (option (string * Any.t * (Any.t -> Prop) * Any.t)) -> ITR -> Prop):
    ITR -> Prop :=
    fun itr =>
      (<<TAU: st_step (r None) itr>>) \/ (<<OBS: exists args, obs_step args (r (Some args)) itr>>)
  .

  Definition src_plus (r: (option (string * Any.t * (Any.t -> Prop) * Any.t)) -> ITR -> Prop):
    ITR -> Prop := (st_star (fun ktr => src_step r ktr))
  .

  Definition st_plus (r: ITR -> Prop): ITR -> Prop := src_plus (fun args ktr => (args = None) /\ (r ktr)).

  (* properties *)
  Lemma st_step_mon
        (r0 r1: ITR -> Prop) itr
        (MON: forall itr, (r0 itr) -> (r1 itr))
    :
    (st_step r0 itr) -> (st_step r1 itr).
  Proof.
    i. inv H; econs; eauto. des. eauto.
  Qed.

  Lemma st_star_ind2 (r: ITR -> Prop) (P: ITR -> Prop)
        (BASE: forall itr (REL: r itr), P itr)
        (STEP: forall itr (REL: st_step (fun ktr => (<<STAR: st_star r ktr>>) /\ (<<IH: P ktr>>)) itr),
            P itr)
    :
    forall itr (STAR: st_star r itr), P itr.
  Proof.
    fix IH 2. i. inv STAR. eauto.
    eapply STEP. inv REL.
    { econs 1. split; auto. }
    { econs 2. des. exists x. split; auto. }
    { econs 3. i. split; auto. }
  Qed.

  Lemma st_star_mon
        (r0 r1: ITR -> Prop) itr
        (MON: forall itr, (r0 itr) -> (r1 itr))
    :
    (st_star r0 itr) -> (st_star r1 itr).
  Proof.
    i. induction H using st_star_ind2. econs 1; eauto.
    econs 2. eapply st_step_mon. 2: eauto. i; ss. des. auto.
  Qed.

  Lemma src_step_mon
        (r0 r1: (option (string * Any.t * (Any.t -> Prop) * Any.t)) -> ITR -> Prop) itr
        (MON: forall args itr, (r0 args itr) -> (r1 args itr))
    :
    (src_step r0 itr) -> (src_step r1 itr).
  Proof.
    i. inv H.
    - econs 1. eapply st_step_mon. 2: eauto. eauto.
    - des. econs 2. exists args. eapply obs_step_mon. 2: eauto. eauto.
  Qed.

  Lemma src_plus_mon
        (r0 r1: (option (string * Any.t * (Any.t -> Prop) * Any.t)) -> ITR -> Prop) itr
        (MON: forall args itr, (r0 args itr) -> (r1 args itr))
    :
    (src_plus r0 itr) -> (src_plus r1 itr).
  Proof.
    i. eapply st_star_mon. 2: eauto. i; ss. eapply src_step_mon. 2: eauto. eauto.
  Qed.


  (* Lemma st_step_comp *)
  (*       (r0: ITR -> Prop) itr *)
  (*       (STEP0: st_step r0 itr) *)
  (*       ktr (CONT0: r0 ktr) *)
  (*       (r1: ITR -> Prop) *)
  (*       (STEP1: st_step r1 ktr) *)
  (*       ctr (CONT1: r1 ctr) *)
  (*   : *)
  (*   exists r2, (st_step r2 itr) /\ (r2 ctr). *)
  (* Proof. *)
  (*   inv STEP0. *)
  (*   - inv STEP1. *)
  (*     + exists  econs 1. *)

  Lemma st_star_st_step_comp
        (r0: ITR -> Prop) itr
        (STAR: st_star r0 itr)
        ktr (CONT0: r0 ktr)
        (r1: ITR -> Prop)
        (STEP: st_step r1 ktr)
        ctr (CONT1: r1 ctr)
    :
    exists r2, (st_star r2 itr) /\ (r2 ctr).
  Proof.
    revert_until STAR. induction STAR using st_star_ind2. i.
    { 
    inv STEP0.
    - inv STEP1.
      + exists  econs 1.


  Lemma st_star_st_step_comp
        (r0: ITR -> Prop) itr
        (STEP0: st_star r0 itr)
        (r1: ITR -> Prop) ktr
        (CONT: r0 ktr)
        (STEP1: st_step r1 ktr)
    :
    st_star (fun ktr => (st_step r1 ktr)) itr.
  Proof.
    inv STEP0.
    - inv STEP1.
      + econs 1.

    econs 1.
    unfold st_plus, src_plus in *. 

  Lemma st_plus_trans
        (r0 r1: ITR -> Prop) itr
        (PLUS: st_plus r0 itr)
        ktr
        (CONT: r0 ktr)
        (STEP: st_plus r1 ktr)
    :
    st_plus r1 itr.
  Proof.
    unfold st_plus, src_plus in *. 



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

  Inductive st_star (r: ITR -> Prop): ITR -> Prop :=
  | st_star_base itr (REL: r itr): st_star r itr
  | st_star_step itr (REL: st_step (fun ktr => st_star r ktr) itr): st_star r itr
  .

  Definition src_step (r: (option (string * Any.t * (Any.t -> Prop) * Any.t)) -> ITR -> Prop):
    ITR -> Prop :=
    fun itr =>
      (<<TAU: st_step (r None) itr>>) \/ (<<OBS: exists args, obs_step args (r (Some args)) itr>>)
  .

  Definition src_plus (r: (option (string * Any.t * (Any.t -> Prop) * Any.t)) -> ITR -> Prop):
    ITR -> Prop := (st_star (fun ktr => src_step r ktr))
  .

  Definition st_plus (r: ITR -> Prop): ITR -> Prop := src_plus (fun args ktr => (args = None) /\ (r ktr)).

End SRCSTEPS.

Section TGTSTEPS.

  Variable R: Type.
  Let ITR := (itree eventE R).

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

  Definition tgt_step (r: (option (string * Any.t * (Any.t -> Prop) * Any.t)) -> ITR -> Prop):
    ITR -> Prop :=
    fun itr =>
      (<<TAU: tt_step (r None) itr>>) \/ (<<OBS: exists args, obs_step args (r (Some args)) itr>>)
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

  Lemma tgt_step_mon
        (r0 r1: (option (string * Any.t * (Any.t -> Prop) * Any.t)) -> ITR -> Prop) itr
        (MON: forall args itr, (r0 args itr) -> (r1 args itr))
    :
    (tgt_step r0 itr) -> (tgt_step r1 itr).
  Proof.
    i. inv H.
    - econs 1. eapply tt_step_mon. 2: eauto. eauto.
    - des. econs 2. exists args. eapply obs_step_mon. 2: eauto. eauto.
  Qed.

End TGTSTEPS.



Section EXP_SIM.

  Variable wfo: WF.

  Definition _simg_alt_exp
             (simg_alt_exp: forall R0 R1 (RR: R0 -> R1 -> Prop), wfo.(T) -> (itree eventE R0) -> (itree eventE R1) -> Prop)
             {R0 R1} (RR: R0 -> R1 -> Prop) (f_tgt: wfo.(T)): (itree eventE R0) -> (itree eventE R1) -> Prop :=
    fun itr_src itr_tgt =>
      (<<RET: exists rt, (<<RETTGT: is_ret rt itr_tgt>>) ->
                    (<<RETSRC: st_star (fun ktr => exists rs, (is_ret rs ktr) /\ (RR rs rt)) itr_src>>)>>)
      /\
        (
          (<<STAR: (tt_step (fun ktr_tgt => (st_star (fun ktr_src => exists f_tgt0, (simg_alt_exp _ _ RR f_tgt0 ktr_src ktr_tgt) /\ (wfo.(lt) f_tgt0 f_tgt)) itr_src)) itr_tgt)>>)
          \/
            (<<PLUS: (tgt_step (fun targs ktr_tgt => (src_plus (fun sargs ktr_src => exists f_tgt0, (simg_alt_exp _ _ RR f_tgt0 ktr_src ktr_tgt) /\ (targs = sargs)) itr_src)) itr_tgt)>>)
        )
  .

  Definition simg_alt_exp: forall R0 R1 (RR: R0 -> R1 -> Prop), wfo.(T) -> (itree eventE R0) -> (itree eventE R1) -> Prop := paco6 _simg_alt_exp bot6.

  Lemma simg_alt_exp_mon: monotone6 _simg_alt_exp.
  Proof.
    ii. inv IN. des.
    { unfold _simg_alt_exp. split; eauto.
      left. eapply tt_step_mon. 2: eauto. i; ss. eapply st_star_mon. 2: eauto. i; ss.
      des. eauto.
    }
    { unfold _simg_alt_exp. split; eauto.
      right. eapply tgt_step_mon. 2: eauto. i; ss. eapply src_plus_mon. 2: eauto. i; ss.
      des. eauto.
    }
  Qed.

  Hint Resolve simg_alt_exp_mon: paco.
  Hint Resolve cpn6_wcompat: paco.


End EXP_SIM.
Hint Unfold simg_alt_exp.
Hint Resolve simg_alt_exp_mon: paco.
Hint Resolve cpn6_wcompat: paco.
