Require Import Coqlib.
Require Import ITreelib.
Require Import Universe.
Require Import STS.
Require Import Behavior.
Require Import ModSem.
Require Import Skeleton.
Require Import PCM.

Generalizable Variables E R A B C X Y Σ.

Set Implicit Arguments.



(***
r <- Take;;
FAdd(r);; <-------------------------- illegal in some sense
assume((blk |-> R) <= r \/ (blk |-> G) <= r \/ (blk |-> B) <= r);;  (iProp???)
meta-assume(list mname(for modular reasoning), current stackframe);;

r <- Choose;;
FSub(r);; := Get;; Choose;; guarantee;; Set;;
guarantee(blk |-> v <= r);;
(call f);;
r <- Take;;
FAdd(r);; <-------------------------- illegal in some sense
assume(some_other_resource <= r);;
meta-assume(list mname(for modular reasoning), current stackframe);;

r <- Choose;;
FSub(r);;
guarantee(blk |-> v <= r);;
***)

(***
HoareFun := FPush;; [[boilerplate]] real_code [[boilerplate]] FPop;;
real_code := itree, using HoareCall, not benign call
             calling meta-assume is allowed. "list mname" is hard-coded in the module.
HoareCall := [[boilerplate]] call [[boilerplate]]

the illegal update (FAdd(r)) is only allowed in boilerplate code.
FPush/FPop is only allowed in boilerplate code.
***)

(***
FPush
  r <- Take;
  assume(P /\ IP r);
  cur <- FGet; FPut (cur * r);



    r <- Choose;
    guarantee(P /\ IP r);
    cur <- FGet; cur' <- Choose; guarantee(cur' * r = cur); FPut cur';
      call;
    ...
    ...
    ...

  ...
  ...
  ...
FPop

NB: this "discarded" resource is *actually* discarded; the user can't access it in the real_code
***)

(***
Where does the `Function Locality` appear in our scenario?
Use Rely/Guarantee in simulation technique.



FPush
  r <- Take;
  assume(P /\ IP r);
  cur <- FGet; FPut (cur * r);



    r <- Choose;
    guarantee(P /\ IP r);
    cur <- FGet; cur' <- Choose; guarantee(cur' * r = cur); FPut cur';
      call;
    ...
    ...
    ...

  ...
  ...
  ...
FPop

***)
Section PROOF.
  (* Context {myRA} `{@GRA.inG myRA Σ}. *)
  Context {Σ: GRA.t}.
  Let GURA: URA.t := GRA.to_URA Σ.
  Local Existing Instance GURA.
  Variable mn: mname.

  Definition HoareFun
             (I: URA.car -> Prop)
             (P: URA.car -> list val -> Prop)
             (Q: URA.car -> list val -> URA.car -> val -> Prop)
             (f: list val -> itree Es val):
    list val -> itree Es val :=
    fun varg =>
      rarg <- trigger (Take URA.car);; trigger (Forge rarg);; (*** virtual resource passing ***)
      assume(P rarg varg);; (*** precondition ***)
      mopen <- trigger (MGet mn);; assume(I mopen);; (*** opening the invariant ***)

      vret <- f varg;; (*** body ***)

      mclose <- trigger (MGet mn);; guarantee(I mclose);; (*** closing the invariant ***)
      rret <- trigger (Choose URA.car);; guarantee(Q rarg varg rret vret);; (*** postcondition ***)
      trigger (Discard rret);; (*** virtual resource passing ***)

      Ret vret (*** return ***)
  .

  Definition HoareCall
             (I: URA.car -> Prop)
             (P: URA.car -> list val -> Prop)
             (Q: URA.car -> list val -> URA.car -> val -> Prop):
    fname -> list val -> itree Es val :=
    fun fn varg =>
      mclose <- trigger (MGet mn);; guarantee(I mclose);; (*** closing the invariant ***)
      rarg <- trigger (Choose URA.car);; guarantee(P rarg varg);; (*** precondition ***)
      trigger (Discard rarg);; (*** virtual resource passing ***)

      vret <- trigger (Call fn varg);; (*** call ***)

      rret <- trigger (Take URA.car);; trigger (Forge rret);; (*** virtual resource passing ***)
      assume(Q rarg varg rret vret);; (*** postcondition ***)
      mopen <- trigger (MGet mn);; assume(I mopen);; (*** opening the invariant ***)

      Ret vret (*** return to body ***)
  .

  (* Definition HoareFun *)
  (*            (INV: URA.car -> Prop) *)
  (*            (P: URA.car -> list val -> Prop) *)
  (*            (Q: URA.car -> list val -> URA.car -> val -> Prop) *)
  (*            (f: list val -> itree Es val): *)
  (*   list val -> itree Es val := *)
  (*   fun vs0 => *)
  (*     ld0 <- trigger (MGet mn);; *)
  (*     r <- trigger (Take URA.car);; *)
  (*     assume(P ld0 r vs0);; *)
  (*     FAdd r;; *)

  (*     assume(<<WTY: URA.wf (URA.add ld0 r)>>);; *)
  (*     vr <- (f vs0);; *)

  (*     ld1 <- trigger (MGet mn);; *)
  (*     rr <- trigger (Choose URA.car);; *)
  (*     guarantee(Q ld0 r vs0 ld1 rr vr);; *)
  (*     FSub rr;; *)
  (*     Ret vr *)
  (* . *)

  (* Definition HoareCall *)
  (*            (P: URA.car -> URA.car -> list val -> Prop) *)
  (*            (Q: URA.car -> URA.car -> list val -> URA.car -> URA.car -> val -> Prop): *)
  (*   fname -> list val -> itree (callE +' mdE +' fnE +' eventE) val := *)
  (*   fun fn vs0 => *)
  (*     ld0 <- trigger (MGet mn);; *)
  (*     r <- trigger (Choose URA.car);; *)
  (*     FSub r;; *)
  (*     guarantee(P ld0 r vs0);; *)

  (*     vr <- trigger (Call fn vs0);; *)

  (*     Ret vr *)
  (* . *)

End PROOF.

