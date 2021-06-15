Require Import Coqlib.
Require Import Universe.
Require Import STS.
Require Import Behavior.
Require Import ModSem.
Require Import Skeleton.
Require Import PCM.
Require Import HoareDef OpenDef.
Require Import Logic.
Require Import Mem1.
Require Import TODOYJ.
Require Import AList.
Require Import NewStackHeader.

Set Implicit Arguments.



Definition _stkRA: URA.t := (mblock ==> (Excl.t (list Z)))%ra.
Instance stkRA: URA.t := Auth.t _stkRA.

Section PROOF.

  Context `{Σ: GRA.t}.
  Context `{@GRA.inG stkRA Σ}.

  Compute (URA.car (t:=_stkRA)).
  Definition _is_stack (h: mblock) (stk: list Z): _stkRA :=
    (fun _h => if (dec _h h) then Some stk else ε)
  .

  Definition is_stack (h: mblock) (stk: list Z): stkRA := Auth.white (_is_stack h stk).

  Definition new_spec: fspec :=
    (* (mk_simple (X:=unit) *)
    (*            (fun _ => ( *)
    (*                 (fun varg o => (⌜varg = ([]: list val)↑ /\ o = ord_pure 0⌝: iProp)%I), *)
    (*                 (fun vret => (∃ h, ⌜vret = (Vptr h 0)↑⌝ ** OwnM (is_stack h []): iProp)%I) *)
    (* ))) *)
    (mk_fspec
       (fun (_: unit) _ varg o => (⌜varg = ([]: list val)↑ ∧ o = ord_pure 0⌝: iProp)%I)
       (fun (_: unit) virtual_ret vret =>
          (∃ h, ⌜virtual_ret = ([]: list val)↑ ∧ vret = (Vptr h 0)↑⌝ ** OwnM(is_stack h []): iProp)%I)
    )
  .

  (*** varg stands for (physical) value arguments... bad naming and will be changed later ***)
  Definition pop_spec: fspec :=
    (* (X:=(mblock * list Z)) (AA:=list Z) (AR:=Z * list Z) *)
    mk (fun '(h, stk0) virtual_arg varg o =>
          (⌜stk0 = virtual_arg /\ varg = ([Vptr h 0%Z]: list val)↑ /\ o = ord_top⌝
            ** OwnM (is_stack h stk0): iProp)%I)
       (fun '(h, stk0) '(x, stk1) vret =>
          (match stk0 with
           | [] => ⌜x = (- 1)%Z /\ (stk1 = [])⌝ ** OwnM (is_stack h stk1)
           | hd :: tl => ⌜x = hd /\ (stk1 = tl)⌝ ** OwnM (is_stack h stk1)
           end: iProp)%I)
  .

  Definition push_spec: fspec :=
    mk (fun '(h, x, stk0) virtual_arg varg o =>
          (⌜(x, stk0) = virtual_arg /\ varg = ([Vptr h 0%Z; Vint x]: list val)↑ /\ o = ord_top⌝
            ** OwnM (is_stack h stk0): iProp)%I)
       (fun '(h, x, stk0) stk1 vret => (⌜stk1 = x :: stk0⌝ ** OwnM (is_stack h stk1): iProp)%I)
  .


  (*** TODO: remove redundancy with NewStack2 ***)
  Notation pget := (p0 <- trigger PGet;; `p0: (gmap mblock (list Z)) <- p0↓ǃ;; Ret p0) (only parsing).
  Notation pput p0 := (trigger (PPut (p0: (gmap mblock (list Z)))↑)) (only parsing).

  Definition new_body: list val -> itree (kCallE +' pE +' eventE) val :=
    fun args =>
      _ <- (pargs [] args)?;;
      handle <- trigger (Choose _);;
      stk_mgr0 <- pget;;
      guarantee(stk_mgr0 !! handle = None);;;
      let stk_mgr1 := <[handle:=[]]> stk_mgr0 in
      pput stk_mgr1;;;
      Ret (Vptr handle 0)
  .

  Definition pop_body: list val -> itree (kCallE +' pE +' eventE) val :=
    fun args =>
      handle <- (pargs [Tblk] args)?;;
      stk_mgr0 <- pget;;
      stk0 <- (stk_mgr0 !! handle)?;;
      match stk0 with
      | x :: stk1 =>
        pput (<[handle:=stk1]> stk_mgr0);;;
        trigger (kCall unknown "debug" ([Vint 0; Vint x])↑);;;
        Ret (Vint x)
      | _ => Ret (Vint (- 1))
      end
  .

  Definition push_body: list val -> itree (kCallE +' pE +' eventE) val :=
    fun args =>
      '(handle, x) <- (pargs [Tblk; Tint] args)?;;
      stk_mgr0 <- pget;;
      stk0 <- (stk_mgr0 !! handle)?;;
      pput (<[handle:=(x :: stk0)]> stk_mgr0);;;
      trigger (kCall unknown "debug" ([Vint 1; Vint x]↑));;;
      Ret Vundef
  .


  Definition StackSbtb: list (gname * kspecbody) :=
    [("new", mk_kspecbody new_spec (cfun new_body) (fun _ => trigger (Choose _)));
    ("pop",  mk_kspecbody pop_spec (cfun pop_body)
                          (cfun (fun (stk0: list Z) =>
                                   match stk0 with
                                   | [] => Ret ((- 1)%Z, [])
                                   | x :: stk1 =>
                                     trigger (kCall unknown "debug" [Vint 0; Vint x]↑);;; Ret (x, stk1)
                                   end)));
    ("push", mk_kspecbody push_spec (cfun push_body)
                          (cfun (fun '(x, stk0) =>
                                   trigger (kCall unknown "debug" [Vint 1; Vint x]↑);;;
                                           Ret (x :: stk0))))
    ]
  .

  Definition StackStb: list (gname * fspec).
    eapply (Seal.sealing "stb").
    let x := constr:(List.map (map_snd (fun ksb => (KModSem.disclose_ksb ksb): fspec)) StackSbtb) in
    let y := eval cbn in x in
    eapply y.
  Defined.

  Definition KStackSem: KModSem.t := {|
    KModSem.fnsems := StackSbtb;
    KModSem.mn := "Stack";
    KModSem.initial_mr := ε;
    KModSem.initial_st := (∅: gmap mblock (list Z))↑;
  |}
  .
  Definition SStackSem: SModSem.t := KStackSem.
  Definition StackSem (stb: list (string * fspec)): ModSem.t :=
    (SModSem.to_tgt stb) SStackSem.



  Definition KStack: KMod.t := {|
    KMod.get_modsem := fun _ => KStackSem;
    KMod.sk := Sk.unit;
  |}
  .
  Definition SStack: SMod.t := KStack.
  Definition Stack (stb: Sk.t -> list (string * fspec)): Mod.t :=
    SMod.to_tgt stb SStack.

End PROOF.
Global Hint Unfold StackStb: stb.
