Require Import Mem0 Mem1 HoareDef SimModSem.
Require Import Coqlib.
Require Import Universe.
Require Import Skeleton.
Require Import PCM.
Require Import ModSem Behavior.
Require Import Relation_Definitions.

(*** TODO: export these in Coqlib or Universe ***)
Require Import Relation_Operators.
Require Import RelationPairs.
From ITree Require Import
     Events.MapDefault.
From ExtLib Require Import
     Core.RelDec
     Structures.Maps
     Data.Map.FMapAList.
Require Import TODOYJ.
Require Import HTactics.

Generalizable Variables E R A B C X Y.

Set Implicit Arguments.

Local Open Scope nat_scope.



(*** black + delta --> new_black ***)
Definition add_delta_to_black `{M: URA.t} (b: URA.auth_t) (w: URA.auth_t): URA.auth_t :=
  match b, w with
  | URA.excl e _, URA.frag f1 => URA.excl (URA.add e f1) URA.unit
  | _, _ => URA.boom
  end
.


(* Notation "wf n *)
(* '------------------------------------------------------------------' *)
(* src0 tgt0 *)
(* '------------------------------------------------------------------' *)
(* src1 tgt1 *)
(* '------------------------------------------------------------------' *)
(* src2 tgt2" := *)
(*   (sim_itree wf n (([(_, src0)], src1), src2) (([(_, tgt0)], tgt1), tgt2)) *)
(*     (at level 60, *)
(*      format "wf  n '//' *)
(* '------------------------------------------------------------------' '//' *)
(* src0 '//' *)
(* tgt0 '//' *)
(* '------------------------------------------------------------------' '//' *)
(* src1 '//' *)
(* tgt1 '//' *)
(* '------------------------------------------------------------------' '//' *)
(* src2 '//' '//' '//' *)
(* tgt2 '//' *)
(* "). *)
(******** TODO: it works in emacs but fails in coqc -- try coq 8.13 and uncomment it ***********)



Section SIMMODSEM.

  Context `{Σ: GRA.t}.
  Context `{@GRA.inG Mem1.memRA Σ} `{@GRA.inG (RA.excl Mem.t) Σ}.

  Let W: Type := (alist mname (Σ * Any.t)) * (alist mname (Σ * Any.t)).
  (* Eval compute in (@RA.car (RA.excl Mem.t)). *)
  Eval compute in (@URA.car Mem1._memRA).
  Inductive sim_loc: option val -> (option val + unit) -> Prop :=
  | sim_loc_present v: sim_loc (Some v) (inl (Some v))
  | sim_loc_absent: sim_loc None (inr tt)
  .

  Let wf: W -> Prop :=
    fun '(mrps_src0, mrps_tgt0) =>
      exists mem_src (mem_tgt: Mem.t),
        (<<SRC: mrps_src0 = Maps.add "Mem" ((GRA.padding ((URA.black mem_src): URA.car (t:=Mem1.memRA))), tt↑) Maps.empty>>) /\
        (<<TGT: mrps_tgt0 = Maps.add "Mem" (ε, mem_tgt↑) Maps.empty>>) /\
        (<<SIM: forall b ofs, sim_loc ((mem_tgt.(Mem.cnts)) b ofs) (mem_src b ofs)>>)
  .

  Local Opaque points_to.

  Hint Resolve sim_itree_mon: paco.

  Opaque URA.unit.

  Theorem correct: ModSemPair.sim Mem1.MemSem Mem0.MemSem.
  Proof.
   econstructor 1 with (wf:=wf) (le:=top2); et; swap 2 3.
    { typeclasses eauto. }
    { ss. esplits; ss; et. ii.
      destruct (classic (b = 0%nat /\ ofs = 0%Z)).
      - des. subst. ss. unfold update. des_ifs. econs.
      - des_ifs; bsimpl; des; des_sumbool; ss; try rewrite Nat.eqb_neq in *; try rewrite Z.eqb_neq in *;
          apply_all_once Nat.eqb_eq; apply_all_once Z.eqb_eq; subst; try lia.
        + unfold update. des_ifs; econs; et.
        + unfold update. des_ifs; econs; et.
    }

    econs; ss.
    { unfold allocF. init. harg_tac. des; clarify.
      unfold interp_hCallE_tgt, APC. steps. anytac. ss.
      steps. force_l. exists 0. steps. force_l. exists (Vptr (Mem.nb mem_tgt) 0).
      set (blk := (Mem.nb mem_tgt)). rename x into sz.
      assert(WFA: forall ofs, mem_src (Mem.nb mem_tgt) ofs = inr tt).
      { i.
        destruct (mem_src (Mem.nb mem_tgt) ofs) eqn:A; cycle 1.
        { des_u; ss. }
        destruct o.
        - admit "ez - add tgt wf".
        - admit "ez - inl None is boom in RA.excl".
      }
      hret_tac (GRA.padding (add_delta_to_black
                               (URA.black (mem_src: URA.car (t:=Mem1._memRA)))
                               (points_to (blk, 0%Z) (repeat (Vint 0) sz)): URA.car (t:=Mem1.memRA)))
      (GRA.padding ((blk, 0%Z) |-> (List.repeat (Vint 0) sz))).
      { Local Opaque URA.add. etrans.
        { eapply URA.extends_updatable. eexists; et. }
        erewrite GRA.padding_add. eapply GRA.padding_updatable.
        ss. des_ifs. eapply URA.auth_alloc2.
        eapply URA.wf_mon in VALID.
        eapply GRA.padding_wf in VALID. des.
        clear - VALID WFA Heq SIM.
        Local Transparent URA.add points_to.
        ss. des. unfold URA.white in Heq. clarify.
        ii. des_ifs; ss.
        - bsimpl; des; des_sumbool; clarify.
          exploit WFA; et. intro A. rewrite A in *; ss.
        - specialize (VALID0 k k0). bsimpl; des; des_sumbool; clarify; des_ifs.
        - specialize (VALID0 k k0). bsimpl; des; des_sumbool; clarify; des_ifs.
          apply_all_once Z.leb_le. apply_all_once Z.ltb_lt.
          intro A. apply nth_error_None in A. rewrite repeat_length in *.
          apply inj_le in A. rewrite Z2Nat.id in A; cycle 1.
          { lia. }
          lia.
          Local Opaque URA.add points_to.
      }
      { esplits; ss. }
      { Local Opaque URA.wf.
        Local Opaque URA.add points_to.
        Local Transparent points_to.
        ss. esplits; ss. i. ss.
        destruct (dec b blk).
        + subst. unfold blk. unfold update. des_ifs_safe. ss.
          des_ifs.
          * bsimpl; des; try rewrite Z.leb_le in *; try rewrite Z.ltb_lt in *.
            Local Transparent URA.add.
            s.
            Local Opaque URA.add.
            des_ifs; bsimpl; des; des_sumbool; ss; clarify; try rewrite Z.leb_le in *; try rewrite Z.ltb_lt in *;
              try rewrite Z.leb_gt in *; try rewrite Z.ltb_ge in *; try lia; et.
            { exploit WFA; et. intro A. rewrite A in *; ss. }
            { exploit WFA; et. intro A. rewrite A in *; ss. }
            { rewrite Z.sub_0_r.
              destruct (nth_error (repeat (Vint 0) sz) (Z.to_nat ofs)) eqn:U.
              - eapply nth_error_In in U. eapply repeat_spec in U. subst. econs; et.
              - eapply nth_error_None in U. lia.
            }
            { rewrite repeat_length in *. lia. }
          * Local Transparent URA.add.
            s.
            Local Opaque URA.add.
            des_ifs; bsimpl; des; des_sumbool; ss; clarify; try rewrite Z.leb_le in *; try rewrite Z.ltb_lt in *;
              try rewrite Z.leb_gt in *; try rewrite Z.ltb_ge in *; try lia; et;
                try (by exploit WFA; et; intro A; rewrite A in *; ss).
            { rewrite Z.sub_0_r. rewrite repeat_length in *. lia. }
            { econs; eauto. }
            { econs; eauto. }
        + Local Transparent URA.add.
          ss.
          hexploit (SIM b ofs); et. intro A. inv A.
          {
            des_ifs; bsimpl; des; des_sumbool; clarify.
            - unfold update. des_ifs. rewrite <- H1. econs.
            - unfold update. des_ifs. rewrite <- H1. econs.
            - unfold update. des_ifs. rewrite <- H1. econs.
          }
          {
            des_ifs; bsimpl; des; des_sumbool; clarify.
            - unfold update. des_ifs. rewrite <- H1. econs.
            - unfold update. des_ifs. rewrite <- H1. econs.
            - unfold update. des_ifs. rewrite <- H1. econs.
          }
      }
    }
    econs; ss.
    { unfold freeF. init. harg_tac. des; clarify.
      unfold interp_hCallE_tgt, APC. steps. anytac. ss.
      steps. force_l. exists 0. steps. anytac. ss. steps.
      rewrite URA.unit_idl in *. rewrite GRA.padding_add in *. eapply GRA.padding_wf in VALID. des.
      rename n into b. rename z into ofs.
      assert(A: mem_src b ofs = inl (Some v)).
      { Local Transparent URA.wf.
        ss.
        Local Transparent URA.add.
        ss. des_ifs. des. specialize (VALID0 b ofs).
        Local Transparent URA.add.
        clear SIM.
        Local Transparent URA.unit.
        ss. clarify. rr in VALID. des. clarify. ss.
        des_ifs;
          bsimpl; des; des_sumbool; ss;
          repeat des_u;
          clear_tac;
          try rewrite Z.leb_le in *; try rewrite Z.leb_gt in *; try rewrite Z.ltb_lt in *; try rewrite Z.ltb_ge in *;
          try rewrite Z.sub_diag in *;
          try lia; ss.
        Local Opaque URA.wf URA.add URA.unit.
      }

      set (mem_src' := fun _b _ofs => if dec _b b && dec _ofs ofs then inr () else mem_src _b _ofs).
      assert(WF': URA.wf (mem_src': URA.car (t:=Mem1._memRA))).
      { Local Transparent URA.add URA.wf.
        ss. ii. des_ifs.
        ss. clarify.
        subst mem_src'. ss. des_ifs. des. specialize (VALID0 k k0). bsimpl. des; des_sumbool; des_ifs.
        Local Opaque URA.wf URA.add.
      }
      hexploit (SIM b ofs); et. intro B. rewrite A in *. inv B.
      force_r.
      { exfalso. unfold Mem.free in *. des_ifs. }
      rename t into mem_tgt'.
      assert(SIM': forall b ofs, sim_loc (Mem.cnts mem_tgt' b ofs) (mem_src' b ofs)).
      { i.
        unfold Mem.free in _UNWRAPU. des_ifs. ss.
        subst mem_src'. ss.
        destruct (classic (b = b0 /\ ofs = ofs0)); des; clarify.
        - destruct H0; clarify. (**** TODO: FIX ****) unfold update. des_ifs. econs.
        - des_ifs.
          { Psimpl. bsimpl; des; des_sumbool; ss; clarify. destruct H0; ss. destruct H1; ss. (**** TODO: FIX ****)}
          replace (update (Mem.cnts mem_tgt) b (update (Mem.cnts mem_tgt b) ofs None) b0 ofs0) with
              (Mem.cnts mem_tgt b0 ofs0); cycle 1.
          { unfold update. des_ifs. Psimpl. des_ifs; bsimpl; des; des_sumbool; ss; clarify. }
          et.
      }
      force_l. esplits. steps.
      hret_tac (GRA.padding (URA.black (mem_src': URA.car (t:=Mem1._memRA)))) (@URA.unit Σ).
      { rewrite URA.unit_id.
        rewrite ! GRA.padding_add. apply GRA.padding_updatable.
        apply URA.auth_dealloc.
        clear - WF' VALID.
        r. i. rewrite URA.unit_idl.
        ss. destruct H; clear H. (*** coq bug; des infloops ***) des. clarify.
        esplits; et.
        apply func_ext. intro _b. apply func_ext. intro _ofs.
        destruct (classic (b = _b /\ ofs = _ofs)).
        - destruct H; clear H. clarify.
          subst mem_src'. ss. des_ifs; bsimpl; des; des_sumbool; clarify.
          clear - H0.
          Local Transparent URA.wf.
          Local Transparent URA.add.
          specialize (H0 _b _ofs). ss.
          des_ifs; bsimpl; des; des_sumbool;
            try rewrite Z.leb_le in *; try rewrite Z.leb_gt in *; try rewrite Z.ltb_lt in *; try rewrite Z.ltb_ge in *;
              try rewrite Z.sub_diag in *;
              try lia; ss.
          des_u. ss.
        - Psimpl.
          subst mem_src'. s.
          des_ifs; bsimpl; des; des_sumbool;
            try rewrite Z.leb_le in *; try rewrite Z.leb_gt in *; try rewrite Z.ltb_lt in *; try rewrite Z.ltb_ge in *;
              try rewrite Z.sub_diag in *;
              try lia; ss.
          Local Opaque URA.wf.
          Local Opaque URA.add.
      }
      { split; ss. }
      { unfold wf. esplits; eauto. }
    }
    econs; ss.
    { unfold loadF. init. harg_tac. des; clarify.
      unfold interp_hCallE_tgt, APC. steps. anytac. ss.
      steps. force_l. exists 0. steps. anytac. ss. steps.
      rewrite URA.unit_idl in *. rewrite GRA.padding_add in *. apply_all_once GRA.padding_wf. des.
      rename n into b. rename z into ofs.
      assert(T: mem_src b ofs = inl (Some v)).
      { Local Transparent points_to URA.add URA.wf URA.unit.
        clear - VALID.
        ss. des. do 2 spc VALID0. rr in VALID. des. ss.
        des_ifs; bsimpl; des; des_sumbool; ss;
          try rewrite Z.leb_le in *; try rewrite Z.leb_gt in *; try rewrite Z.ltb_lt in *; try rewrite Z.ltb_ge in *;
            try rewrite Z.sub_diag in *; try lia; ss.
        Local Opaque points_to URA.add URA.wf URA.unit.
      }
      exploit SIM; et. intro U. rewrite T in U. inv U; ss. unfold Mem.load.
      force_r; ss. clarify. steps. force_l. esplits.
      hret_tac (GRA.padding (URA.black (mem_src: URA.car (t:=Mem1._memRA)))) (GRA.padding ((b, ofs) |-> [v0])); ss.
      esplits; eauto.
    }
    econs; ss.
    { unfold storeF. init. harg_tac. des; clarify.
      unfold interp_hCallE_tgt, APC. steps. anytac. ss.
      steps. force_l. exists 0. steps. anytac. ss. steps.
      rewrite URA.unit_idl in *. rewrite GRA.padding_add in *. apply_all_once GRA.padding_wf. des.
      rename n into b. rename z into ofs.
      set (mem_src' := fun _b _ofs => if dec _b b && dec _ofs ofs then inl (Some v) else mem_src _b _ofs).
      assert(WF0: URA.wf (mem_src': URA.car (t:=Mem1._memRA))).
      { Local Transparent URA.wf.
        clear - VALID. apply URA.wf_mon in VALID. ss. des.
        ii. specialize (VALID0 k k0). des_ifs_safe. unfold mem_src' in *. des_ifs.
        Local Opaque URA.wf.
      }
      assert(U: mem_src b ofs = inl (Some v_old)).
      { Local Transparent URA.add GRA.to_URA points_to URA.wf URA.unit.
        clear - VALID. ss. des. specialize (VALID0 b ofs). r in VALID. des; clarify. ss.
        des_ifs; bsimpl; des; des_sumbool; ss; subst;
          try rewrite Z.leb_le in *; try rewrite Z.leb_gt in *; try rewrite Z.ltb_lt in *; try rewrite Z.ltb_ge in *;
            try rewrite Z.sub_diag in *; try lia; ss.
        Local Opaque URA.add GRA.to_URA points_to URA.wf URA.unit.
      }
      hexploit SIM; et. intro V. rewrite U in V. inv V; ss. unfold Mem.store. rewrite <- H1. steps.
      force_l. esplit.
      hret_tac (GRA.padding (URA.black (mem_src': URA.car (t:=Mem1._memRA)))) (GRA.padding ((b, ofs) |-> [v])).
      { rewrite ! GRA.padding_add. eapply GRA.padding_updatable.
        clear - VALID WF0. clear VALID.
        Local Transparent URA.add GRA.to_URA points_to URA.wf URA.unit.
        eapply URA.auth_update; et.
        rr. ii. destruct H; clear H. (*** FIXME: des runs infloop ***)
        des. subst. esplits; et.
        subst mem_src'. do 2 (apply func_ext; i). specialize (H0 x x0). specialize (WF0 x x0). ss.
        des_ifs; bsimpl; des; des_sumbool; ss; subst;
          try rewrite Z.leb_le in *; try rewrite Z.leb_gt in *; try rewrite Z.ltb_lt in *; try rewrite Z.ltb_ge in *;
            try rewrite Z.sub_diag in *; try lia; ss.
        Local Opaque URA.add GRA.to_URA points_to URA.wf URA.unit.
      }
      { splits; eauto. }
      { unfold wf. esplits; eauto. esplits; ss; et. des_ifs.
        - bsimpl; des; des_sumbool; ss; subst. unfold mem_src'. des_ifs; bsimpl; des; des_sumbool; ss. econs; et.
        - unfold mem_src'. des_ifs. bsimpl; des; des_sumbool; subst; ss.
      }
    }
    econs; ss.
    { unfold cmpF. init. harg_tac. unfold interp_hCallE_tgt, APC. steps.
      destruct PRE as [[? []] ?]. subst.
      set (resource := c).
      assert (VALIDPTR: forall b ofs v (WF: URA.wf ((URA.black (mem_src: URA.car (t:=Mem1._memRA))) ⋅ ((b, ofs) |-> [v]))),
                 Mem.valid_ptr mem_tgt b ofs = true).
      { clear - SIM. i. cut (mem_src b ofs = inl (Some v)).
        - i. unfold Mem.valid_ptr.
          specialize (SIM b ofs). rewrite H in *. inv SIM. ss.
        - Local Transparent points_to URA.add URA.wf URA.unit.
          ss. des. specialize (WF0 b ofs). r in WF. des; clarify. ss.
          des_ifs; bsimpl; des; des_sumbool; ss; subst;
            try rewrite Z.leb_le in *; try rewrite Z.leb_gt in *; try rewrite Z.ltb_lt in *; try rewrite Z.ltb_ge in *;
              try rewrite Z.sub_diag in *; try lia; ss.
          Local Opaque URA.add GRA.to_URA points_to URA.wf URA.unit.
      }
      force_l. exists 0. steps. force_l. exists (if b then Vint 1 else Vint 0). des; clarify.
      - anytac. ss. steps.
        rewrite URA.unit_idl in *. rewrite GRA.padding_add in *. apply_all_once GRA.padding_wf. des.
        erewrite VALIDPTR; cycle 1.
        { instantiate (1:=v). eapply VALID. }
        steps. hret_tac (GRA.padding (URA.black (mem_src: URA.car (t:=Mem1._memRA)))) resource; ss.
        esplits; eauto.
      - anytac. ss. steps.
        rewrite URA.unit_idl in *. rewrite GRA.padding_add in *. apply_all_once GRA.padding_wf. des.
        erewrite VALIDPTR; cycle 1.
        { instantiate (1:=v). eapply VALID. }
        steps. hret_tac (GRA.padding (URA.black (mem_src: URA.car (t:=Mem1._memRA)))) resource; ss.
        esplits; eauto.
      - anytac. ss. steps.
        rewrite URA.unit_idl in *. repeat rewrite GRA.padding_add in *. apply_all_once GRA.padding_wf. des.
        erewrite VALIDPTR; cycle 1.
        { instantiate (1:=v0). clear - VALID.
          eapply URA.wf_mon. erewrite <- URA.add_assoc. eapply VALID. }
        erewrite VALIDPTR; cycle 1.
        { instantiate (1:=v1). clear - VALID.
          eapply URA.wf_mon. erewrite <- URA.add_assoc.
          erewrite URA.add_comm with (a:=(b1, ofs1) |-> [v1]). eapply VALID. }
        ss. destruct (dec b0 b1); cycle 1.
        { ss. steps. hret_tac (GRA.padding (URA.black (mem_src: URA.car (t:=Mem1._memRA)))) resource; ss.
          esplits; eauto. }
        destruct (dec ofs0 ofs1); cycle 1.
        { ss. steps. hret_tac (GRA.padding (URA.black (mem_src: URA.car (t:=Mem1._memRA)))) resource; ss.
          esplits; eauto. }
        subst. exfalso.
        erewrite URA.add_comm in VALID. eapply URA.wf_mon in VALID.
        Local Transparent points_to URA.add URA.wf URA.unit.
        ss. specialize (VALID b1 ofs1).
        destruct (dec b1 b1); ss. erewrite Z.leb_refl in *. ss.
        replace (ofs1 <? ofs1 + 1)%Z with true in *; ss.
        clear. symmetry. eapply Z.ltb_lt. lia.
        Local Opaque URA.add GRA.to_URA points_to URA.wf URA.unit.
      - anytac. ss. steps.
        rewrite URA.unit_idl in *. rewrite GRA.padding_add in *. apply_all_once GRA.padding_wf. des.
        erewrite VALIDPTR; cycle 1.
        { instantiate (1:=v). eapply VALID. }
        ss. destruct (dec b0 b0); ss. destruct (dec ofs ofs); ss. steps.
        hret_tac (GRA.padding (URA.black (mem_src: URA.car (t:=Mem1._memRA)))) resource; ss.
        esplits; eauto.
      - anytac. ss. steps. rewrite URA.unit_idl in *.
        hret_tac (GRA.padding (URA.black (mem_src: URA.car (t:=Mem1._memRA)))) resource; ss.
        esplits; eauto.
    }
  Qed.

End SIMMODSEM.
