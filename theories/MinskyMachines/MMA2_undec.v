(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*        Mozilla Public License Version 2.0, MPL-2.0         *)
(**************************************************************)

From Undecidability.Synthetic
  Require Import Undecidability ReducibilityFacts.

From Undecidability.FRACTRAN 
  Require Import FRACTRAN FRACTRAN_undec.

From Undecidability.MinskyMachines 
  Require Import MMA FRACTRAN_to_MMA2.

Lemma MMA2_HALTING_undec : undecidable MMA2_HALTING.
Proof.
  apply (undecidability_from_reducibility FRACTRAN_REG_undec).
  apply FRACTRAN_REG_MMA2_HALTING.
Qed.

Check MMA2_HALTING_undec.

Lemma MMA2_HALTING_compl_undec : undecidable (complement MMA2_HALTING).
Proof.
  apply (undecidability_from_reducibility FRACTRAN_REG_compl_undec).
  apply reduces_complement.
  apply FRACTRAN_REG_MMA2_HALTING.
Qed.

Lemma MMA2_HALTS_ON_ZERO_undec : undecidable MMA2_HALTS_ON_ZERO.
Proof.
  apply (undecidability_from_reducibility FRACTRAN_REG_undec).
  apply FRACTRAN_REG_MMA2_HALTS_ON_ZERO.
Qed.

Check MMA2_HALTS_ON_ZERO_undec.

