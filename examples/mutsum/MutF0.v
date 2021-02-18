Require Import Coqlib.
Require Import ITreelib.
Require Import Universe.
Require Import STS.
Require Import Behavior.
Require Import ModSem.
Require Import Skeleton.
Require Import PCM.
Require Import Hoare.

Generalizable Variables E R A B C X Y Σ.

Set Implicit Arguments.



Section PROOF.

  Context `{Σ: GRA.t}.
  (* Context `{@GRA.inG memRA Σ}. *)

  (***
    f(n) := if (n == 0) then 0 else (n + g(n-1))
  ***)
  Definition fF: Any.t -> itree Es Any.t :=
    fun varg =>
      varg <- varg↓ǃ;;
      match varg with
      | [Vint n] =>
        if dec n 0%Z
        then Ret (Vint 0)↑
        else m <- trigger (Call "g" [Vint (n - 1)]↑);; m <- m↓ǃ;; r <- (vadd (Vint n) m)?;; Ret r↑
      | _ => triggerUB
      end
  .

  Definition FSem: ModSem.t := {|
    ModSem.fnsems := [("f", fF)];
    ModSem.initial_mrs := [("F", (ε, unit↑))];
  |}
  .

  Definition F: Mod.t := {|
    Mod.get_modsem := fun _ => FSem;
    Mod.sk := [("f", Sk.Gfun)];
  |}
  .
End PROOF.
