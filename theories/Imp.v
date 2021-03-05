(** * The Imp language  *)

(* begin hide *)
From Coq Require Import
     Arith.PeanoNat
     Lists.List
     Strings.String
     Morphisms
     Setoid
     RelationClasses.

From ExtLib Require Import
     Data.String
     Structures.Monad
     Structures.Traversable
     Data.List.

From ITree Require Import
     ITree
     ITreeFacts
     Events.MapDefault
     Events.StateFacts.

Import Monads.
Import MonadNotation.
Local Open Scope monad_scope.
Local Open Scope string_scope.

Require Import Any.
Require Import Coqlib.
Require Import ITreelib.
Require Import Universe.
Require Import Skeleton.
Require Import PCM.
Require Import ModSem.

Set Implicit Arguments.
(* end hide *)

(* ========================================================================== *)
(** ** Syntax *)

(** Imp manipulates a countable set of variables represented as [string]s: *)
Definition var : Set := string.

Inductive fun_type : Type :=
| Fun (_ : gname)
| Sys (_ : gname).

(** Expressions are made of variables, constant literals, and arithmetic operations. *)
Inductive expr : Type :=
| Var (_ : var)
| Lit (_ : val)
| Plus  (_ _ : expr)
| Minus (_ _ : expr)
| Mult  (_ _ : expr).

(** LDJ: function call exists only as a statement *)
Inductive stmt : Type :=
| Assign (x : var) (e : expr)    (* x = e *)
| Seq    (a b : stmt)            (* a ; b *)
| If     (i : expr) (t e : stmt) (* if (i) then { t } else { e } *)
| While  (t : expr) (b : stmt)   (* while (t) { b } *)
| Skip                           (* ; *)
| CallFun (x : var) (f : fun_type) (args : list expr)  (* x = f(args) *)
| Expr (e : expr)    (* evaluates expression, will be returned if the last stmt *)
.

(** LDJ: information of a function, maybe add return type? *)
Record function : Type :=
  mk_function { params : list var ; body : stmt }.

(** LDJ: a program is a list of (function name, body) *)
Definition program : Type := list (gname * function).

(* ========================================================================== *)
(** ** Notations *)

Module ImpNotations.

  (** A few notations for convenience.  *)
  Definition Expr_coerce: expr -> stmt := Expr.
  Definition Var_coerce: string -> expr := Var.
  Definition Lit_coerce: val -> expr := Lit.
  Definition Vint_coerce: Z -> val := Vint.
  Coercion Expr_coerce: expr >-> stmt.
  Coercion Var_coerce: string >-> expr.
  Coercion Lit_coerce: val >-> expr.
  Coercion Vint_coerce: Z >-> val.

  Bind Scope expr_scope with expr.

  Infix "+" := Plus : expr_scope.
  Infix "-" := Minus : expr_scope.
  Infix "*" := Mult : expr_scope.

  Bind Scope stmt_scope with stmt.

  Notation "x '=#' e" :=
    (Assign x e) (at level 60, e at level 50): stmt_scope.

  Notation "a ';;#' b" :=
    (Seq a b)
      (at level 100, right associativity,
       format
         "'[v' a  ';;#' '/' '[' b ']' ']'"
      ): stmt_scope.

  Notation "'if#' i 'then#' t 'else#' e 'fi#'" :=
    (If i t e)
      (at level 100,
       right associativity,
       format
         "'[v ' 'if#'  i '/' '[' 'then#'  t  ']' '/' '[' 'else#'  e ']' 'fi#' ']'").

  Notation "'while#' t 'do#' b 'end#'" :=
    (While t b)
      (at level 100,
       right associativity,
       format
         "'[v  ' 'while#'  t  'do#' '/' '[v' b  ']' ']' 'end#'").

  Notation "x ':=#' '(' f ')' args" :=
    (CallFun x f args) (at level 60): stmt_scope.

End ImpNotations.

Import ImpNotations.

(* ========================================================================== *)
(** ** Semantics *)

(** _Imp_ produces effects by manipulating its variables.  To account for this,
    we define a type of _external interactions_ [ImpState] modeling reads and
    writes to global variables.

    A read, [GetVar], takes a variable as an argument and expects the
    environment to answer with a value, hence defining an event of type
    [ImpState value].

    Similarly, [SetVar] is a write event parameterized by both a variable and a
    value to be written, and defines an event of type [ImpState unit], no
    informative answer being expected from the environment.  *)
Variant ImpState : Type -> Type :=
| GetVar (x : var) : ImpState val
| SetVar (x : var) (v : val) : ImpState unit.

Section Denote.

  (** We now proceed to denote _Imp_ expressions and statements.
      We could simply fix in stone the universe of events to be considered,
      taking as a semantic domain for _Imp_ [itree ImpState X]. That would be
      sufficient to give meaning to _Imp_, but would prohibit us from relating this
      meaning to [itree]s stemmed from other entities. Therefore, we
      parameterize the denotation of _Imp_ by a larger universe of events [eff],
      of which [ImpState] is assumed to be a subevent. *)

  Context `{Σ: GRA.t}.
  Context {eff : Type -> Type}.
  Context {HasImpState : ImpState -< eff}.
  Context {HasCall : callE -< eff}.
  Context {HasEvent : eventE -< eff}.

  (** _Imp_ expressions are denoted as [itree eff value], where the returned
      value in the tree is the value computed by the expression.
      In the [Var] case, the [trigger] operator smoothly lifts a single event to
      an [itree] by performing the corresponding [Vis] event and returning the
      environment's answer immediately.
      A constant (literal) is simply returned.
      Usual monadic notations are used in the other cases: we can [bind]
      recursive computations in the case of operators as one would expect. *)

  Fixpoint denote_expr (e : expr) : itree eff val :=
    match e with
    | Var v     => trigger (GetVar v)
    | Lit n     => ret n
    | Plus a b  => l <- denote_expr a ;; r <- denote_expr b ;; (vadd l r)?
    | Minus a b => l <- denote_expr a ;; r <- denote_expr b ;; (vsub l r)?
    | Mult a b  => l <- denote_expr a ;; r <- denote_expr b ;; (vmul l r)?
    end.

  (** We turn to the denotation of statements. As opposed to expressions,
      statements do not return any value: their semantic domain is therefore
      [itree eff unit]. The most interesting construct is, naturally, [while].

      To define its meaning, we make use of the [iter] combinator provided by
      the [itree] library:

      [iter : (A -> itree E (A + B)) -> A -> itree E B].

      The combinator takes as argument the body of the loop, i.e. a function
      that maps inputs of type [A], the accumulator, to an [itree] computing
      either a new [A] that can be fed back to the loop, or a return value of
      type [B]. The combinator builds the fixpoint of the body, hiding away the
      [A] argument from the return type.

      Compared to the [mrec] and [rec] combinators introduced in
      [Introduction.v], [iter] is more restricted in that it naturally
      represents tail recursive functions.  It, however, enjoys a rich equational
      theory: its addition grants the type of _continuation trees_ (named
      [ktree]s in the library), a structure of _traced monoidal category_.

      We use [loop] to first build a new combinator [while].
      The accumulator degenerates to a single [unit] value indicating
      whether we entered the body of the while loop or not. Since the
      the operation does not return any value, the return type is also
      taken to be [unit].
      That is, the right tag [inr tt] says to exit the loop,
      while the [inl tt] says to continue. *)

  Definition while (step : itree eff (unit + val)) : itree eff val :=
    ITree.iter (fun _ => step) tt.

  (** Casting values into [bool]:  [0] corresponds to [false] and any nonzero
      value corresponds to [true].  *)
  Definition is_true (v : val) : option bool :=
    match v with
    | Vint n => if (n =? 0)%Z then Some false else Some true
    | _ => None
    end.

  (* LDJ: can use vcmp instead if we include Mem.t features *)
  Definition if_itree {B} (c : itree eff bool) (t f : itree eff B) : itree eff B :=
    match c with
    | Ret b => if b then t else f
    | _ => triggerUB
    end.

  (** The meaning of Imp statements is now easy to define. They are all
      straightforward, except for [While], which uses our new [while] combinator
      over the computation that evaluates the conditional, and then the body if
      the former was true.  *)

  (* change to "v <- ccall f eval_args ;;" ? *)
  Fixpoint denote_stmt (s : stmt) : itree eff val :=
    match s with
    | Assign x e =>  v <- denote_expr e ;; trigger (SetVar x v) ;; ret Vundef
    | Seq a b    =>
      denote_stmt a ;; denote_stmt b
    | If i t e   =>
      v <- denote_expr i ;;
      if_itree (is_true v)? (denote_stmt t) (denote_stmt e)

    | While t b =>
      while (v <- denote_expr t ;;
             if_itree (is_true v)? (denote_stmt b ;; ret (inl tt)) (ret (inr Vundef)))

    | Skip => ret Vundef
    | CallFun x ft args =>
      match ft with
      | Fun f =>
        eval_args <- (mapT denote_expr args) ;;
        v <- trigger (Call f (eval_args↑)) ;; v <- unwrapN (v↓);;
        trigger (SetVar x v) ;; ret Vundef
      | Sys f =>
        eval_args <- (mapT denote_expr args) ;;
        v <- trigger (Syscall f eval_args) ;;
        trigger (SetVar x v) ;; ret Vundef
      end

    | Expr e => v <- denote_expr e ;; Ret v
    end.

End Denote.

(* ========================================================================== *)
(** ** Interpretation *)

(* begin hide *)
From ITree Require Import
     Events.MapDefault.

From ExtLib Require Import
     Core.RelDec
     Structures.Maps
     Data.Map.FMapAList.

(** These enable typeclass instances for Maps keyed by strings and values *)
Instance RelDec_string : RelDec (@eq string) :=
  { rel_dec := fun s1 s2 => if string_dec s1 s2 then true else false}.

Instance RelDec_string_Correct: RelDec_Correct RelDec_string.
Proof.
  constructor; intros x y.
  split.
  - unfold rel_dec; simpl.
    destruct (string_dec x y) eqn:EQ; intros; eauto.
    inversion H.
  - unfold rel_dec; simpl.
    destruct (string_dec x y) eqn:EQ; intros; eauto.
Qed.
(* end hide *)

(** We provide an _ITree event handler_ to interpret away [ImpState] events.  We
    use an _environment event_ to do so, modeling the environment as a
    0-initialized map from strings to values.  Recall from [Introduction.v] that
    a _handler_ for the events [ImpState] is a function of type [forall R, ImpState R
    -> M R] for some monad [M].  Here we take for our monad the special case of
    [M = itree E] for some universe of events [E] required to contain the
    environment events [mapE] provided by the library. It comes with an event
    interpreter [interp_map] that yields a computation in the state monad.  *)
Definition handle_ImpState {E: Type -> Type} `{mapE var (Vundef) -< E}: ImpState ~> itree E :=
  fun _ e =>
    match e with
    | GetVar x => lookup_def x
    | SetVar x v => insert x v
    end.

(** We now concretely implement this environment using ExtLib's finite maps. *)
Definition fun_loc_env := alist var val.

(** Finally, we can define an evaluator for our statements.
   To do so, we first denote them, leading to an [itree ImpState unit].
   We then [interp]ret [ImpState] into [mapE] using [handle_ImpState], leading to
   an [itree (mapE var value) unit].
   Finally, [interp_map] interprets the latter [itree] into the state monad,
   resulting in an [itree] free of any event, but returning the final
   _Imp_ env.
 *)
(* SAZ: would rather write something like the following:
 h : E ~> M A
 h' : F[void1] ~> M A
forall eff, {pf:E -< eff == F[E]} (t : itree eff A)
        interp pf h h' t : M A
*)

Definition interp_function `{Σ: GRA.t} {A} (t : itree (ImpState +' Es) A) : stateT fun_loc_env (itree Es) A :=
  let t' := interp (bimap handle_ImpState (id_ Es)) t in
  interp_map t'.

Definition eval_function `{Σ: GRA.t} (f: function) (args: list val) : itree Es val :=
  if (List.length f.(params) =? List.length args)%nat
  then '(_, retv) <- (interp_function (denote_stmt f.(body)) (List.combine f.(params) args));; Ret retv
  else triggerUB.

(* ========================================================================== *)
(**
Section InterpImpProperties.
  (** We can lift the underlying equational theory on [itree]s to include new
      equations for working with [interp_imp].

      In particular, we have:
         - [interp_imp] respects [≈]
         - [interp_imp] commutes with [bind].

      We could justify more equations than just the ones below.  For instance,
      _Imp_ programs also respect a coarser notation of equivalence for the
      [env] state.  We exploit this possibility to implement optimzations
      at the _Asm_ level (see AsmOptimizations.v).
   *)

  Context {E': Type -> Type}.
  Notation E := (ImpState +' E').

  (** This interpreter is compatible with the equivalence-up-to-tau. *)
  Global Instance eutt_interp_imp {R}:
    Proper (@eutt E R R eq ==> eq ==> @eutt E' (prod (env) R) (prod _ R) eq)
           interp_imp.
  Proof.
    repeat intro.
    unfold interp_imp.
    unfold interp_map.
    rewrite H0. eapply eutt_interp_state_eq; auto.
    rewrite H. reflexivity.
  Qed.

  (** [interp_imp] commutes with [bind]. *)
  Lemma interp_imp_bind: forall {R S} (t: itree E R) (k: R -> itree E S) (g : env),
      (interp_imp (ITree.bind t k) g)
    ≅ (ITree.bind (interp_imp t g) (fun '(g',  x) => interp_imp (k x) g')).
  Proof.
    intros.
    unfold interp_imp.
    unfold interp_map.
    repeat rewrite interp_bind.
    repeat rewrite interp_state_bind.
    apply eqit_bind. red. intros.
    destruct a as [g'  x].
    simpl.
    reflexivity.
    reflexivity.
  Qed.

End InterpImpProperties.

 **)

(****************** copy-paste end **********************)
(****************** copy-paste end **********************)
(****************** copy-paste end **********************)
(****************** copy-paste end **********************)
(****************** copy-paste end **********************)

(**** ModSem ****)
Module ImpMod.
Section MODSEM.
  Context `{GRA: GRA.t}.
  Variable mn: mname.
  Variable prog: program.

  Set Typeclasses Depth 5.
  Instance Initial_void1 : @Initial (Type -> Type) IFun void1 := @elim_void1. (*** TODO: move to ITreelib ***)

  Definition modsem: ModSem.t := {|
    ModSem.fnsems := List.map (fun '(fn, st) => (fn, cfun (eval_function st))) prog;
    ModSem.initial_mrs := [(mn, (URA.unit, tt↑))];
  |}.

  Definition get_mod: Mod.t := {|
    Mod.get_modsem := fun _ => modsem;
    Mod.sk := List.map (fun '(fn, _) => (fn, Sk.Gfun)) prog;
  |}.

End MODSEM.
End ImpMod.


Section Example_Extract.

  Let Σ: GRA.t := fun _ => URA.of_RA RA.empty.
  Local Existing Instance Σ.

  Open Scope expr_scope.
  Open Scope stmt_scope.

  Definition factorial : stmt :=
    "output" =# 1%Z ;;#
    while# "input"
    do# "output" =# "output" * "input";;#
       "input"  =# "input" - 1%Z end#;;#
    "output".

  Definition factorial_fundef : function :=
    {| params := ["input"] ; body := factorial |}.

  Definition main : stmt :=
    "result" :=# (Fun "factorial") [4%Z : expr] ;;#
    "result".

  Definition main_fundef : function :=
    {| params := [] ; body := main |}.

  Definition ex_extract : program :=
    [("factorial", factorial_fundef); ("main", main_fundef)].

  Definition ex_prog: Mod.t := ImpMod.get_mod "Main" ex_extract.

  Definition imp_ex := ModSem.initial_itr_no_check (Mod.enclose ex_prog).

End Example_Extract.
