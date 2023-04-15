# Stuttering For Free

## Dependencies
Our development successfully compiles with following versions (in Linux, OS X):

- coq (= *8.15.0*)

- coq-ext-lib (= *0.11.3*)
- coq-paco (= *4.1.2*)
- coq-itree (= *4.0.0*)
- coq-ordinal (= *0.5.0*)

- ocamlbuild (= *0.14.0*)

All packages can be installed from [OPAM archive for Coq](https://github.com/coq/opam-coq-archive)

## How to build
- make -j[N] -k

## Code Structure

### Definitions and Theorems
- Freely Stuttering Simulation (Section 4.1)
  + Definition: `Definition sim` in `sim/SimSTSIndex.v`
  + Theorem 4.1 (ADEQUACY): `Theorem adequacy` in `sim/SimSTSIndex.v`
- Explicitly/Implicitly Stuttering Simulation (Section 2.1/2.2): `Definition simg_alt_exp/simg_alt_imp` in `sim/SimGlobalAlts.v`
  + Theorem 5.4 (Simulation Equivalence): `Theorem eq1_simg_implies_simg_alt_exp/eq2_simg_alt_exp_implies_simg_alt_imp/eq3_simg_alt_imp_implies_simg` in `sim/SimGlobalEquiv.v`
- DTree (Section 6.2)
  + Definitions: `sim/ModSemE.v`
  + Simulation: `sim/SimGlobalIndex.v` and `sim/SimGlobalIndexFacts.v`
  + Examples: `sim/Tutorial.v`
- Replayability (Section 5.2)
  + Definition: `Definition replay` in `sim/Replayability.v`
  + Replaying ESim/ISim: `Lemma psim_replay_esim/psim_replay_isim` in `sim/Replayability.v`
