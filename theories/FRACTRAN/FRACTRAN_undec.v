(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*             Yannick Forster            [+]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(*                             [+] Affiliation Saarland Univ. *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*        Mozilla Public License Version 2.0, MPL-2.0         *)
(**************************************************************)

(** ** FRACTRAN_HALTING is undecidable *)

From Undecidability.Synthetic
  Require Import Undecidability ReducibilityFacts.

From Undecidability.MinskyMachines
  Require Import MM MM_undec.

From Undecidability.FRACTRAN
  Require Import FRACTRAN Reductions.MM_FRACTRAN FRACTRAN_sss.

Theorem FRACTRAN_REG_undec : undecidable FRACTRAN_REG_HALTING.
Proof.
  apply (undecidability_from_reducibility MM_HALTING_undec).
  apply MM_FRACTRAN_REG_HALTING.
Qed.

Check FRACTRAN_REG_undec.

Theorem FRACTRAN_REG_compl_undec : undecidable (complement FRACTRAN_REG_HALTING).
Proof.
  apply (undecidability_from_reducibility MM_HALTING_compl_undec).
  apply reduces_complement.
  apply MM_FRACTRAN_REG_HALTING.
Qed.

Theorem FRACTRAN_undec : undecidable Halt_FRACTRAN.
Proof.
  apply (undecidability_from_reducibility FRACTRAN_REG_undec).
  apply FRACTRAN_REG_FRACTRAN_HALTING.
Qed.

Theorem FRACTRAN_compl_undec : undecidable (complement Halt_FRACTRAN).
Proof.
  apply (undecidability_from_reducibility FRACTRAN_REG_compl_undec).
  apply reduces_complement.
  apply FRACTRAN_REG_FRACTRAN_HALTING.
Qed.
