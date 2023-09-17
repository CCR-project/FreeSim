# Stuttering For Free && DTrees

This is the formalization for the paper "Stuttering For Free" (OOPSLA23).

## Mapping from the paper to the Coq development
Section 2
- State Transition System (Section 2 header): `Record semantics` in `sim/STS.v`
- Explicitly/Implicitly Stuttering Simulation (Section 2.1/2.2, also Fig 10): `Definition simg_alt_exp/simg_alt_imp` in `sim/SimGlobalAlts.v`

Section 3
- Fig 4: see Section 4 (Fig 7)
- REFL+/SEQ+: `Theorem simg_refl, Definition bindC` in `sim/SimGlobalIndexFacts.v`

SEQ+ is a special case of bindC. "a; b" is a syntactic sugar for "_ <- a; b" in ITrees.
- Fig 5: see Section 5 (Definition 5.1)
- Fig 6: see Section 4 (Fig 7)

Section 4
- Freely Stuttering Simulation (Section 4)
  + Fig 7: `Definition sim` in `sim/SimSTSIndex.v`
  + Theorem 4.1 (Adequacy): `Theorem adequacy` in `sim/SimSTSIndex.v`
  
Note that our development uses ordinals, whereas in the presentation
we used parameterized well-founded orders.  However, it is known that
every well-founded order can be embedded into ordinal numbers.  Such a
property is formalized in the Ordinal library we use, and can be found
[here](https://github.com/minkiminki/Ordinal/blob/fa610bb90912c81e0ef1371e6416c46a7540fcc5/src/Ordinal.v#L737).
It ensures that it is sufficient to work on ordinal numbers.

Section 5
- Definition 5.1: `Definition replay` in `sim/Replayability.v`
- Replaying ESim/ISim (Section 5.2): `Lemma psim_replay_esim/psim_replay_isim` in `sim/Replayability.v`
- Theorem 5.4 (Simulation Equivalence): `Theorem eq1_simg_implies_simg_alt_exp/eq2_simg_alt_exp_implies_simg_alt_imp/eq3_simg_alt_imp_implies_simg` in `sim/SimGlobalEquiv.v`
- Theorem 5.5 (Index Irrelevance): `simg_bot_flag_up` in `sim/SimGlobalEquiv.v`

Section 6.1 (CompCert)
- Section 6.1.1: `freesim_replay_bsim, freesim_replay_fdsim, freesim_replay_fsim` in `compcert/FreeSim.v`

CompCert's simulations (e.g., `forward_simulation` and
`backward_simulation`) comprise "functor" parts and other minor
conditions regarding initial states.  To state the replayability
result, we extract these "functor" parts out of these definitions and
name them `_fsim` and `_bsim` (you can see the correspondence to
`forward_simulation` and `backward_simulation` when `r` is renamed
into `match_states`). Note that these `_fsim` and `_bsim` are
independent of Paco, and our replayability result are stated with
respect to those.

There is one thing to note regarding FSim. 
While we consistently assumed determinism on the target in our
presentation, the assumption made in CompCert is slightly more
complicated that it assumes "determinate" (slightly weaker notion than
determinism) on the target and "receptiveness" on the source. Our
formalization provides replayability results for both FSim in our
presentation (assuming determinism on the target) and the precise
definition in CompCert (assuming determinate on the target and
receptiveness on the source). The paper's presentation corresponds
to `freesim_replay_fdsim`.

One may notice that our development for CompCert is entirely
orthogonal to the rest of the development.  The reason is as follows:
our main development is based on and compatible with another project,
CCR.  While, the notion of STS and behavior in both projects are
"theoretically" consistent, their formalization in Coq is quite
distant.  Specifically, the treatment of stuck states and the style in
formulating coinductive data types.  For that reason, we choose to
develop the theory separately for now.

- Section 6.1.2: `freesim_replay_xsim, freesim_replay_efsim` in `compcert/FreeSim.v`
- Rest of Fig.12: `free_simulation_behavior_improves, Section ADEQUACY_ALTS` in `compcert/FreeSim.v`
Section 6.2 (DTree)
- Fig. 13 (Definitions): `dtree` in `sim/Tutorial.v`, `eventE` in `sim/ModSemE.v`, `dualize` in `SimGlobalIndexFacts.v`

The rest (`iter`, `interp`, `stateT`, `interp_state`) originates from ITrees library.
- Simulation: `sim/SimGlobalIndex.v` and `sim/SimGlobalIndexFacts.v`
- upper rectangle in Fig. 14: `eutt_simg, bindC, euttC, simg_trans, dualizeC` in `sim/SimGlobalIndexFacts.v`
- lower rectangle in Fig. 14: `simg_iter, simg_interp, simg_interp_state, dualize_involution, dualize_bind, dualize_iter, dualize_interp` in `sim/SimGlobalIndexFacts.v`

Note that euttge (≳) is a stronger relation that eutt (≈).
- More examples (not in the paper): `sim/Tutorial.v`

## Axioms
The development uses the following non-constructive axioms (most of them are in `lib/Axioms.v`).
- Functional form of the (non extensional) Axiom of Choice.
  (technically, it appears as `relational_choice`
  [here](https://coq.inria.fr/library/Coq.Logic.RelationalChoice.html)
  and `dependent_unique_choice`
  [here](https://coq.inria.fr/library/Coq.Logic.ClassicalUniqueChoice.html).
  However, combination of these two axioms are known to be equivalent
  to Functional form of the (non extensional) Axiom of Choice.
  Specifically, see `Reification of dependent and non dependent
  functional relation are equivalent`, and `AC_rel + AC! = AC_fun`
  [here](https://coq.inria.fr/library/Coq.Logic.ChoiceFacts.html).)
- System call semantics, following the style of [CompCert](https://github.com/AbsInt/CompCert/blob/master/common/Events.v#L1483)
- Propositional Extensionality. (`prop_extensinality` [here](https://coq.inria.fr/library/Coq.Logic.ClassicalFacts.html))
- Proof Irrelevance. (`proof_irrelevance` [here](https://coq.inria.fr/library/Coq.Logic.ClassicalFacts.html))
- Functional Extensionality. (`functional_extensionality_dep` [here](https://coq.inria.fr/library/Coq.Logic.FunctionalExtensionality.html))
- Invariance by Substitution of Reflexive Equality Proofs, UIP. (`eq_rect_eq` [here](https://coq.inria.fr/library/Coq.Logic.Eqdep.html))
- Constructive form of definite description. `constructive_definite_description` [here](https://coq.inria.fr/library/Coq.Logic.Description.html)
- Excluded middle. (`classic` [here](https://coq.inria.fr/library/Coq.Logic.Classical_Prop.html))
- Bisimulation on itree implies Leibniz equality. (`bisimulation_is_eq` [here](https://github.com/DeepSpec/InteractionTrees/blob/master/theories/Eq/EqAxiom.v#L18))
