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
        fn varg rvs v ktr
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

  Inductive st_star (r: ITR -> Prop): ITR -> Prop :=
  | st_star_base itr (REL: r itr): st_star r itr
  | st_star_step itr (REL: st_step (fun ktr => st_star r ktr) itr): st_star r itr
  .

  Definition src_step (r: ARGS -> ITR -> Prop):
    ITR -> Prop :=
    fun itr =>
      (<<TAU: st_step (r None) itr>>) \/
        (<<OBS: exists arg, forall v, obs_step (arg, v) (r (Some (arg, v))) itr>>)
  .

  Inductive src_star (r: ARGS -> ITR -> Prop): ARGS -> ITR -> Prop :=
  | src_star_base
      args itr
      (REL: r args itr)
    :
    src_star r args itr
  | src_star_step_tau
      itr
      (REL: src_step (fun args1 ktr => src_star r args1 ktr) itr)
    :
    src_star r None itr
  | src_star_step_obs
      args0 itr
      (REL: st_step (fun ktr => src_star r (Some args0) ktr) itr)
    :
    src_star r (Some args0) itr
  .

  Definition src_plus (r: ARGS -> ITR -> Prop): ITR -> Prop :=
    (src_step (fun args ktr => src_star r args ktr))
  .

  (* Definition src_plus (r: (option (string * Any.t * (Any.t -> Prop) * Any.t)) -> ITR -> Prop): *)
  (*   ITR -> Prop := (st_star (fun ktr => src_step r ktr)) *)
  (* . *)

  (* Definition st_plus (r: ITR -> Prop): ITR -> Prop := src_plus (fun args ktr => (args = None) /\ (r ktr)). *)

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
    - des. econs 2. exists arg. i. eapply obs_step_mon. 2: eauto. eauto.
  Qed.

  Lemma src_star_ind2 (r: ARGS -> ITR -> Prop) (P: ARGS -> ITR -> Prop)
        (BASE: forall args itr (REL: r args itr), P args itr)
        (TAU: forall itr
                (REL: src_step (fun args1 ktr => (<<STAR: src_star r args1 ktr>>) /\
                                                (<<IH: P args1 ktr>>)) itr),
            P None itr)
        (OBS: forall args0 itr
                (REL: st_step (fun ktr => (<<STAR: src_star r (Some args0) ktr>>) /\
                                         (<<IH: P (Some args0) ktr>>)) itr),
            P (Some args0) itr)
    :
    forall args itr (STAR: src_star r args itr), P args itr.
  Proof.
    fix IH 3. i. inv STAR. eauto.
    - eapply TAU. inv REL.
      + left. inv H.
        { econs 1. split; auto. }
        { econs 2. des. exists x. split; auto. }
        { econs 3. i. split; auto. }
      + des. right. exists arg. i. specialize (H v). inv H. clarify. econs; eauto.
    - eapply OBS. inv REL.
      { econs 1. split; auto. }
      { econs 2. des. exists x. split; auto. }
      { econs 3. i. split; auto. }
  Qed.

  Lemma src_star_mon
        (r0 r1: (option (string * Any.t * (Any.t -> Prop) * Any.t)) -> ITR -> Prop)
        args itr
        (MON: forall args itr, (r0 args itr) -> (r1 args itr))
    :
    (src_star r0 args itr) -> (src_star r1 args itr).
  Proof.
    i. induction H using src_star_ind2. econs 1; eauto.
    - econs 2. eapply src_step_mon. 2: eauto. i; ss. des. auto.
    - econs 3. eapply st_step_mon. 2: eauto. i; ss. des. auto.
  Qed.

  Lemma src_plus_mon
        (r0 r1: (option (string * Any.t * (Any.t -> Prop) * Any.t)) -> ITR -> Prop) itr
        (MON: forall args itr, (r0 args itr) -> (r1 args itr))
    :
    (src_plus r0 itr) -> (src_plus r1 itr).
  Proof.
    i. inv H.
    - econs 1. eapply st_step_mon. 2: eauto. i; ss.
      eapply src_star_mon. 2: eauto. i; ss. auto.
    - des. econs 2. exists arg. i. eapply obs_step_mon. 2: eauto. i; ss.
      eapply src_star_mon. 2: eauto. i; ss. auto.
  Qed.

End SRCSTEPS.

Section TGTSTEPS.

  Variable R: Type.
  Let ITR := (itree eventE R).
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

  Inductive tt_star (r: ITR -> Prop): ITR -> Prop :=
  | tt_star_base itr (REL: r itr): tt_star r itr
  | tt_star_step itr (REL: tt_step (fun ktr => tt_star r ktr) itr): tt_star r itr
  .

  Definition tgt_step (r: (option (string * Any.t * (Any.t -> Prop) * Any.t)) -> ITR -> Prop):
    ITR -> Prop :=
    fun itr =>
      (<<TAU: tt_step (r None) itr>>) \/
        (<<OBS: exists arg, forall v, obs_step (arg, v) (r (Some (arg, v))) itr>>)
  .

  Inductive tgt_star (r: ARGS -> ITR -> Prop): ARGS -> ITR -> Prop :=
  | tgt_star_base
      args itr
      (REL: r args itr)
    :
    tgt_star r args itr
  | tgt_star_step_tau
      itr
      (REL: tgt_step (fun args1 ktr => tgt_star r args1 ktr) itr)
    :
    tgt_star r None itr
  | tgt_star_step_obs
      args0 itr
      (REL: tt_step (fun ktr => tgt_star r (Some args0) ktr) itr)
    :
    tgt_star r (Some args0) itr
  .

  Definition tgt_plus (r: ARGS -> ITR -> Prop): ITR -> Prop :=
    (tgt_step (fun args ktr => tgt_star r args ktr))
  .

  (* Definition tgt_plus (r: (option (string * Any.t * (Any.t -> Prop) * Any.t)) -> ITR -> Prop): *)
  (*   ITR -> Prop := (tt_star (fun ktr => tgt_step r ktr)) *)
  (* . *)

  (* Definition tt_plus (r: ITR -> Prop): ITR -> Prop := tgt_plus (fun args ktr => (args = None) /\ (r ktr)). *)

  (* properties *)
  Lemma tt_step_mon
        (r0 r1: ITR -> Prop) itr
        (MON: forall itr, (r0 itr) -> (r1 itr))
    :
    (tt_step r0 itr) -> (tt_step r1 itr).
  Proof.
    i. inv H; econs; eauto. des. eauto.
  Qed.

  Lemma tt_star_ind2 (r: ITR -> Prop) (P: ITR -> Prop)
        (BASE: forall itr (REL: r itr), P itr)
        (STEP: forall itr (REL: tt_step (fun ktr => (<<STAR: tt_star r ktr>>) /\ (<<IH: P ktr>>)) itr),
            P itr)
    :
    forall itr (STAR: tt_star r itr), P itr.
  Proof.
    fix IH 2. i. inv STAR. eauto.
    eapply STEP. inv REL.
    { econs 1. split; auto. }
    { econs 2. i. split; auto. }
    { econs 3. des. exists x. split; auto. }
  Qed.

  Lemma tt_star_mon
        (r0 r1: ITR -> Prop) itr
        (MON: forall itr, (r0 itr) -> (r1 itr))
    :
    (tt_star r0 itr) -> (tt_star r1 itr).
  Proof.
    i. induction H using tt_star_ind2. econs 1; eauto.
    econs 2. eapply tt_step_mon. 2: eauto. i; ss. des. auto.
  Qed.

  Lemma tgt_step_mon
        (r0 r1: (option (string * Any.t * (Any.t -> Prop) * Any.t)) -> ITR -> Prop) itr
        (MON: forall args itr, (r0 args itr) -> (r1 args itr))
    :
    (tgt_step r0 itr) -> (tgt_step r1 itr).
  Proof.
    i. inv H.
    - econs 1. eapply tt_step_mon. 2: eauto. eauto.
    - des. econs 2. exists arg. i. eapply obs_step_mon. 2: eauto. eauto.
  Qed.

  Lemma tgt_star_ind2 (r: ARGS -> ITR -> Prop) (P: ARGS -> ITR -> Prop)
        (BASE: forall args itr (REL: r args itr), P args itr)
        (TAU: forall itr
                (REL: tgt_step (fun args1 ktr => (<<STAR: tgt_star r args1 ktr>>) /\
                                                (<<IH: P args1 ktr>>)) itr),
            P None itr)
        (OBS: forall args0 itr
                (REL: tt_step (fun ktr => (<<STAR: tgt_star r (Some args0) ktr>>) /\
                                         (<<IH: P (Some args0) ktr>>)) itr),
            P (Some args0) itr)
    :
    forall args itr (STAR: tgt_star r args itr), P args itr.
  Proof.
    fix IH 3. i. inv STAR. eauto.
    - eapply TAU. inv REL.
      + left. inv H.
        { econs 1. split; auto. }
        { econs 2. i. split; auto. }
        { econs 3. des. exists x. split; auto. }
      + des. right. exists arg. i. specialize (H v). inv H. clarify. econs; eauto.
    - eapply OBS. inv REL.
      { econs 1. split; auto. }
      { econs 2. i. split; auto. }
      { econs 3. des. exists x. split; auto. }
  Qed.

  Lemma tgt_star_mon
        (r0 r1: (option (string * Any.t * (Any.t -> Prop) * Any.t)) -> ITR -> Prop)
        args itr
        (MON: forall args itr, (r0 args itr) -> (r1 args itr))
    :
    (tgt_star r0 args itr) -> (tgt_star r1 args itr).
  Proof.
    i. induction H using tgt_star_ind2. econs 1; eauto.
    - econs 2. eapply tgt_step_mon. 2: eauto. i; ss. des. auto.
    - econs 3. eapply tt_step_mon. 2: eauto. i; ss. des. auto.
  Qed.

  Lemma tgt_plus_mon
        (r0 r1: (option (string * Any.t * (Any.t -> Prop) * Any.t)) -> ITR -> Prop) itr
        (MON: forall args itr, (r0 args itr) -> (r1 args itr))
    :
    (tgt_plus r0 itr) -> (tgt_plus r1 itr).
  Proof.
    i. inv H.
    - econs 1. eapply tt_step_mon. 2: eauto. i; ss.
      eapply tgt_star_mon. 2: eauto. i; ss. auto.
    - des. econs 2. exists arg. i. eapply obs_step_mon. 2: eauto. i; ss.
      eapply tgt_star_mon. 2: eauto. i; ss. auto.
  Qed.

End TGTSTEPS.

Section EXP_SIM.

  Variable wfo: WF.

  Definition _simg_alt_exp
             (simg_alt_exp: forall R0 R1 (RR: R0 -> R1 -> Prop), wfo.(T) -> (itree eventE R0) -> (itree eventE R1) -> Prop)
             {R0 R1} (RR: R0 -> R1 -> Prop) (exp: wfo.(T)): (itree eventE R0) -> (itree eventE R1) -> Prop :=
    fun itr_src itr_tgt =>
      (exists rt rs, (<<TGT: is_ret rt itr_tgt>>) /\ (<<SRC: is_ret rs itr_src>>) /\ (<<RET: RR rs rt>>))
      \/
        (
          (<<TGT: (tgt_step (fun targ ktr_tgt =>
                               (src_step (fun sarg ktr_src => (<<EQ: targ = sarg>>) -> exists exp0, (simg_alt_exp _ _ RR exp0 ktr_src ktr_tgt)) itr_src)
                               \/ ((targ = None) /\ exists exp0, (simg_alt_exp _ _ RR exp0 itr_src ktr_tgt) /\ (wfo.(lt) exp0 exp))
                            ) itr_tgt)>>)
          \/
            (<<SRC: (src_step (fun sarg ktr_src =>
                                 (tgt_step (fun targ ktr_tgt => (<<EQ: sarg = targ>>) -> exists exp0, (simg_alt_exp _ _ RR exp0 ktr_src ktr_tgt)) itr_tgt)
                                 \/ ((sarg = None) /\ exists exp0, (simg_alt_exp _ _ RR exp0 ktr_src itr_tgt) /\ (wfo.(lt) exp0 exp))
                              ) itr_src)>>)
        )
  .

  Definition simg_alt_exp: forall R0 R1 (RR: R0 -> R1 -> Prop), wfo.(T) -> (itree eventE R0) -> (itree eventE R1) -> Prop := paco6 _simg_alt_exp bot6.

  Lemma simg_alt_exp_mon: monotone6 _simg_alt_exp.
  Proof.
    ii. inv IN.
    { left. eauto. }
    right. des; [left | right].
    { eapply tgt_step_mon. 2: eauto. i; ss. des; [left | right].
      - eapply src_step_mon. 2: eauto. i; ss. specialize (H0 H1). des; eauto.
      - split; eauto.
    }
    { eapply src_step_mon. 2: eauto. i; ss. des; [left | right].
      - eapply tgt_step_mon. 2: eauto. i; ss. specialize (H0 H1). des; eauto.
      - split; eauto.
    }
  Qed.

  Hint Resolve simg_alt_exp_mon: paco.
  Hint Resolve cpn6_wcompat: paco.

End EXP_SIM.
Hint Unfold simg_alt_exp.
Hint Resolve simg_alt_exp_mon: paco.
Hint Resolve cpn6_wcompat: paco.


(** star and plus steps **)
(* Section EXP_SIM. *)

(*   Variable wfo: WF. *)

(*   Definition _simg_alt_exp *)
(*              (simg_alt_exp: forall R0 R1 (RR: R0 -> R1 -> Prop), wfo.(T) -> (itree eventE R0) -> (itree eventE R1) -> Prop) *)
(*              {R0 R1} (RR: R0 -> R1 -> Prop) (exp: wfo.(T)): (itree eventE R0) -> (itree eventE R1) -> Prop := *)
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

(*   Definition simg_alt_exp: forall R0 R1 (RR: R0 -> R1 -> Prop), wfo.(T) -> (itree eventE R0) -> (itree eventE R1) -> Prop := paco6 _simg_alt_exp bot6. *)

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


(* Section EXP_SIM_AUX. *)

(*   Variable wfo: WF. *)

(*   Definition _simg_alt_exp_aux *)
(*              (simg_alt_exp_aux: forall R0 R1 (RR: R0 -> R1 -> Prop), wfo.(T) -> (itree eventE R0) -> (itree eventE R1) -> Prop) *)
(*              {R0 R1} (RR: R0 -> R1 -> Prop) (exp: wfo.(T)): (itree eventE R0) -> (itree eventE R1) -> Prop := *)
(*     fun itr_src itr_tgt => *)
(*       (exists rt rs, (<<TGT: is_ret rt itr_tgt>>) /\ (<<SRC: is_ret rs itr_src>>) /\ (<<RET: RR rs rt>>)) *)
(*       \/ *)
(*         ((<<TGT: (tt_step (fun ktr_tgt => (st_star (fun ktr_src => exists exp0, (simg_alt_exp_aux _ _ RR exp0 ktr_src ktr_tgt) /\ (wfo.(lt) exp0 exp)) itr_src)) itr_tgt)>>) *)
(*          \/ *)
(*            (<<SRC: (st_step (fun ktr_src => (tt_star (fun ktr_tgt => exists exp0, (simg_alt_exp_aux _ _ RR exp0 ktr_src ktr_tgt) /\ (wfo.(lt) exp0 exp)) itr_tgt)) itr_src)>>) *)
(*          \/ *)
(*            (<<TPLUS: (tgt_plus (fun targ ktr_tgt => (src_plus (fun sarg ktr_src => (<<EQ: targ = sarg>>) -> exists exp0, (simg_alt_exp_aux _ _ RR exp0 ktr_src ktr_tgt)) itr_src)) itr_tgt)>>) *)
(*          \/ *)
(*            (<<SPLUS: (src_plus (fun sarg ktr_src => *)
(*                                   match sarg with *)
(*                                   | Some _ => (tgt_plus (fun targ ktr_tgt => (<<EQ: sarg = targ>>) -> exists exp0, (simg_alt_exp_aux _ _ RR exp0 ktr_src ktr_tgt)) itr_tgt) *)
(*                                   | None => (src_star (fun sarg0 ktr_src0 => (tgt_plus (fun targ ktr_tgt => (<<EQ: sarg0 = targ>>) -> exists exp0, (simg_alt_exp_aux _ _ RR exp0 ktr_src0 ktr_tgt)) itr_tgt)) ktr_src) *)
(*                                   end *)
(*                                ) itr_src)>>) *)
(*         ) *)
(*   . *)

(*   Definition simg_alt_exp_aux: forall R0 R1 (RR: R0 -> R1 -> Prop), wfo.(T) -> (itree eventE R0) -> (itree eventE R1) -> Prop := paco6 _simg_alt_exp_aux bot6. *)

(*   Lemma simg_alt_exp_aux_mon: monotone6 _simg_alt_exp_aux. *)
(*   Proof. *)
(*     ii. inv IN. *)
(*     { left. eauto. } *)
(*     right. des; [left | right; left | do 2 right; left | do 3 right]. *)
(*     { eapply tt_step_mon. 2: eauto. i; ss. eapply st_star_mon. 2: eauto. i; ss. des; eauto. } *)
(*     { eapply st_step_mon. 2: eauto. i; ss. eapply tt_star_mon. 2: eauto. i; ss. des; eauto. } *)
(*     { eapply tgt_plus_mon. 2: eauto. i; ss. eapply src_plus_mon. 2: eauto. i; ss. *)
(*       specialize (H0 H1). des; eauto. } *)
(*     { eapply src_plus_mon. 2: eauto. i; ss. des_ifs. *)
(*       - eapply tgt_plus_mon. 2: eauto. i; ss. specialize (H0 H1). des; eauto. *)
(*       - eapply src_star_mon. 2: eauto. i; ss. *)
(*         eapply tgt_plus_mon. 2: eauto. i; ss. specialize (H1 H2). des; eauto. *)
(*     } *)
(*   Qed. *)

(*   Hint Resolve simg_alt_exp_aux_mon: paco. *)
(*   Hint Resolve cpn6_wcompat: paco. *)

(* End EXP_SIM_AUX. *)
(* Hint Unfold simg_alt_exp_aux. *)
(* Hint Resolve simg_alt_exp_aux_mon: paco. *)
(* Hint Resolve cpn6_wcompat: paco. *)


(** target step **)
(* Section AUX2EXP. *)

(*   Lemma simg_alt_exp_aux_implies_simg_alt_exp *)
(*         R0 R1 (RR: R0 -> R1 -> Prop) *)
(*         (itr_src: itree eventE R0) *)
(*         (itr_tgt: itree eventE R1) *)
(*         (wfo: WF) *)
(*         exp *)
(*         (SIM: simg_alt_exp_aux wfo RR exp (itr_src) (itr_tgt)) *)
(*     : *)
(*     simg_alt_exp wfo RR exp itr_src itr_tgt. *)
(*   Proof. *)
(*     ginit. revert_until RR. gcofix CIH. i. *)
(*     (* move exp before CIH. revert_until exp. pattern exp. revert exp. *) *)
(*     (* apply (well_founded_induction wfo.(wf)). intros exp IHe. i. *) *)
(*     punfold SIM. inv SIM; des. *)
(*     { gstep. left. esplits; eauto. } *)
(*     { gstep. right; left. eapply tt_step_mon. 2: eauto. i; ss. *)
(*       eapply st_star_mon. 2: eauto. i; ss. des. esplits; eauto. *)
(*       pclearbot. gfinal. left; eauto. *)
(*     } *)
(*     { gstep. do 2 right; left. eapply st_step_mon. 2: eauto. i; ss. *)
(*       eapply tt_star_mon. 2: eauto. i; ss. des. esplits; eauto. *)
(*       pclearbot. gfinal. left; eauto. *)
(*     } *)
(*     { gstep. do 3 right; left. eapply tgt_plus_mon. 2: eauto. i; ss. *)
(*       eapply src_plus_mon. 2: eauto. i; ss. specialize (H0 H1). des. exists exp0. *)
(*       pclearbot. gfinal. left; eauto. *)
(*     } *)
(*     { gstep. do 4 right. unfold src_plus in *. induction SPLUS using st_star_ind2. *)
(*       { unfold src_step in REL. des. *)
(*         { inv TAU. *)
(*           { red. unfold src_star in REL. *)
(*             (* inv REL. *) *)
(*             induction REL using st_star_ind2. *)
(*             { des. *)
(*               - econs 1. left. econs 1. eapply tgt_plus_mon. 2: eauto. i; ss. *)
(*                 specialize (H H0). des. exists exp0. pclearbot. gfinal. left; auto. *)
(*               - econs 2. econs 1. econs 1. right. exists arg. i. specialize (REL v). *)
(*                 eapply obs_step_mon. 2: eauto. i; ss. eapply tgt_plus_mon. 2: eauto. i; ss. *)
(*                 specialize (H0 H1). des. exists exp0. pclearbot. gfinal. left; auto. *)
(*             } *)
(*             { inv REL; des. *)
(*               - econs 2. econs 1. auto. *)
(*               - econs 2. econs 2. auto. *)
(*               -  *)
(* End AUX2EXP. *)


(* Section EXP_SIM. *)

(*   Variable wfo: WF. *)

(*   Definition _simg_alt_exp *)
(*              (simg_alt_exp: forall R0 R1 (RR: R0 -> R1 -> Prop), wfo.(T) -> (itree eventE R0) -> (itree eventE R1) -> Prop) *)
(*              {R0 R1} (RR: R0 -> R1 -> Prop) (f_tgt: wfo.(T)): (itree eventE R0) -> (itree eventE R1) -> Prop := *)
(*     fun itr_src itr_tgt => *)
(*       (<<RET: exists rt, (<<RETTGT: is_ret rt itr_tgt>>) -> *)
(*                     (<<RETSRC: st_star (fun ktr => exists rs, (is_ret rs ktr) /\ (RR rs rt)) itr_src>>)>>) *)
(*       /\ *)
(*         ( *)
(*           (<<STAR: (tt_step (fun ktr_tgt => (st_star (fun ktr_src => exists f_tgt0, (simg_alt_exp _ _ RR f_tgt0 ktr_src ktr_tgt) /\ (wfo.(lt) f_tgt0 f_tgt)) itr_src)) itr_tgt)>>) *)
(*           \/ *)
(*             (<<PLUS: (tgt_step (fun targs ktr_tgt => (src_plus (fun sargs ktr_src => exists f_tgt0, (simg_alt_exp _ _ RR f_tgt0 ktr_src ktr_tgt) /\ (targs = sargs)) itr_src)) itr_tgt)>>) *)
(*         ) *)
(*   . *)

(*   Definition simg_alt_exp: forall R0 R1 (RR: R0 -> R1 -> Prop), wfo.(T) -> (itree eventE R0) -> (itree eventE R1) -> Prop := paco6 _simg_alt_exp bot6. *)

(*   Lemma simg_alt_exp_mon: monotone6 _simg_alt_exp. *)
(*   Proof. *)
(*     ii. inv IN. des. *)
(*     { unfold _simg_alt_exp. split; eauto. *)
(*       left. eapply tt_step_mon. 2: eauto. i; ss. eapply st_star_mon. 2: eauto. i; ss. *)
(*       des. eauto. *)
(*     } *)
(*     { unfold _simg_alt_exp. split; eauto. *)
(*       right. eapply tgt_step_mon. 2: eauto. i; ss. eapply src_plus_mon. 2: eauto. i; ss. *)
(*       des. eauto. *)
(*     } *)
(*   Qed. *)

(*   Hint Resolve simg_alt_exp_mon: paco. *)
(*   Hint Resolve cpn6_wcompat: paco. *)


(* End EXP_SIM. *)
(* Hint Unfold simg_alt_exp. *)
(* Hint Resolve simg_alt_exp_mon: paco. *)
(* Hint Resolve cpn6_wcompat: paco. *)
