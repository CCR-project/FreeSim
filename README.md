# Stuttering For Free

This is the artifact for the paper "Conditional Contextual Refinement".

## List of Claims
We claim that the artifact provides Coq development for the results in
the paper (modulo small simplifications for expository purposes) and
compiles without any problem.

## Download, installation, and sanity-testing
The artifact is presented as a Docker image ("FreeSim-docker.tar"), but we
are also submitting the latest source code ("FreeSim.tar.gz") just in
case. Both of these are also publicly available
[here](https://github.com/alxest/FreeSim) and
[here](https://hub.docker.com/repository/docker/alxest/oopsla23ae).  If
there is a need to update our artifact in the middle of the review
process, we will make the latest version available on those links.

### Installing via Docker image
1. Install [Docker](https://www.docker.com/) (version 20.10.22 is
tested).

Now, you can either use the Docker image from the Docker Hub (make
sure you have internet connection):

2. Run `sudo docker run -it alxest/oopsla23ae /bin/bash`

or, you can use the Docker image that we submitted:

2. Run `sudo docker load < FreeSim.tar && sudo docker run -it alxest/oopsla23ae /bin/bash`.


### Installing manually with raw source code
1. Install opam in your system with the version at least 2.1.0.
2. Make a fresh directorcy, install a local opam switch and install the dependencies:
```
mkdir fresh_directory && cd fresh_directory &&
opam switch create . ocaml.4.13.0 &&
eval $(opam env) &&
opam repo add coq-released "https://coq.inria.fr/opam/released" &&
opam config env &&
opam pin add coq 8.15.2 -y &&
opam pin add coq-paco 4.1.2 -y &&
opam pin add coq-itree 4.0.0 -y &&
opam pin add coq-ordinal 0.5.2 -y &&
opam pin add coq-compcert 3.11 -y &&
opam pin add ocamlbuild 0.14.1 -y
```

Now, you can either use the source code from the Github (make sure you
have internet connection):

3. Run `git clone git@github.com:alxest/FreeSim.git && cd FreeSim && make`

or you can use the raw source code that we submitted:

3. Run `mv FreeSim.tar.gz fresh_directory && tar -xvf FreeSim.tar.gz && cd FreeSim && make`.

## Evaluation Instructions
To evaluate this artifact, we propose the following steps:
1. Confirm that the Coq development compiles without any problem.  To
   do so, type `git clean -xf .` in the project root directory if you
   have previously built the Coq development or are using the Docker
   image. Check that no `.vo` file remains (e.g., typing `find
   . -iname "*.vo"` in the project root should print nothing). Then,
   run `make -jN` where `N` is the number of cores you wish to use.
2. Check that the source code does not contain any `admit` or
   `Admitted.` (e.g., typing `grep -r "admit" --include="*.v" .`  in
   the project root should print nothing).
3. Read the Section "Mapping from the paper to the Coq development"
   and check that the Coq development indeed corresponds to the
   paper's presentation
4. Check that the project is hosted in the [public
   repository](https://github.com/alxest/FreeSim) (including an issue
   tracker) with [open source
   license](https://github.com/alxest/FreeSim/blob/popl23ae/LICENSE). We
   have also setup [public chat room](https://discord.gg/jQezqzJZ) to
   accommodate collaboration with others.
5. (optional) Check that the development is not using any more axioms
   than the ones specified in Section "Axioms". You can execute `Print
   Assumptions THEOREM` after a theorem. (e.g., try `Print Assumptions
   EXAMPLES_CCR2.flip_n_correct.` at the end of the `sim/Tutorial.v`.)


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

Section 5
- Definition 5.1: `Definition replay` in `sim/Replayability.v`
- Replaying ESim/ISim (Section 5.2): `Lemma psim_replay_esim/psim_replay_isim` in `sim/Replayability.v`
- Theorem 5.4 (Simulation Equivalence): `Theorem eq1_simg_implies_simg_alt_exp/eq2_simg_alt_exp_implies_simg_alt_imp/eq3_simg_alt_imp_implies_simg` in `sim/SimGlobalEquiv.v`
- Theorem 5.5 (Index Irrelevance): `simg_bot_flag_up` in `sim/SimGlobalEquiv.v`

Section 6.1 (CompCert)
- Section 6.1.1: `freesim_replay_bsim, freesim_replay_fdsim, freesim_replay_fsim` in `compcert/FreeSim.v`

CompCert's simulations (e.g., `forward_simulation` and
`backward_simulation`) comprise "functor" parts and other minor
conditions regarding initial states. To state the replayability result, we
extract these "functor" parts out of these definitions and name them
`_fsim` and `_bsim` (you can see the correspondence to
`forward_simulation` and `backward_simulation` when `r` is renamed
into `match_states`). Note that these `_fsim` and `_bsim` are independent of
Paco, and our replayability result are stated with respect to those.

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
