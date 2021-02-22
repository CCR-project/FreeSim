Require Import Coqlib.
Require Import ITreelib.
Require Import Universe.
Require Import STS.
Require Import Behavior.
Require Import ModSem.
Require Import Skeleton.
Require Import PCM.
Require Import Hoare.
Require Import MutHeader.

Generalizable Variables E R A B C X Y Σ.

Set Implicit Arguments.



Section PROOF.

  Context `{Σ: GRA.t}.

  Definition Gsbtb: list (string * fspecbody) := [("g", mk_specbody g_spec (fun _ => triggerUB))].

  Definition GSem: ModSem.t := {|
    ModSem.fnsems := List.map (fun '(fn, body) => (fn, fun_to_tgt GlobalStb fn body)) Gsbtb;
    ModSem.initial_mrs := [("G", (ε, unit↑))];
  |}
  .

  Definition G: Mod.t := {|
    Mod.get_modsem := fun _ => GSem;
    Mod.sk := [("g", Sk.Gfun)];
  |}
  .
End PROOF.
