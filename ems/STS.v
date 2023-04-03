Require Import sflib.
Require Import String.
Require Import Coqlib.
Require Import Any.

Set Implicit Arguments.


Inductive event: Type :=
| event_out
    (fn: string)
    (args: Any.t)
| event_in
    (rv: Any.t)
.
Parameter syscall_sem: string -> Any.t -> Any.t -> Prop.


Inductive sort: Type :=
| angelic
| demonic
| final (retv: Any.t)
| vis (ev: event)
.

Record semantics : Type := Semantics_gen {
  state: Type;
  step : state -> option event -> state -> Prop;
  initial_state: state;
  state_sort: state -> sort;
  (* wf_vis: forall st0 (VIS: state_sort st0 = vis), exists ! ev st1, step st0 (Some ev) st1; *)
  (* wf_vis: forall st0 (VIS: state_sort st0 = vis), exists ev st1, step st0 (Some ev) st1; *)
  (** wf_vis might be completely removed with a new transformation pass *)
  wf_vis: forall
      st0 ev ev0 ev1 st1 st2
      (VIS: state_sort st0 = vis ev)
      (STEP: step st0 ev0 st1)
      (STEP: step st0 ev1 st2)
    ,
      (Some ev = ev0 /\ Some ev = ev1 /\ st1 = st2);
  wf_angelic: forall st0 ev st1 (VIS: state_sort st0 = angelic) (STEP: step st0 ev st1), ev = None;
  wf_demonic: forall st0 ev st1 (VIS: state_sort st0 = demonic) (STEP: step st0 ev st1), ev = None;
  wf_final: forall st0 ev st1 r (FIN: state_sort st0 = final r) (STEP: step st0 ev st1), False;
}.
