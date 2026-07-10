(* Canonical model for [∃ ∧ ∀∃∀] formulas and their un-Skolemized form. *)

(* In this file, we prove that given quantifier-free formulas
   F(x, x', y) and Z(z), the following are equivalent:
   (i)  Z(0) ∧ ∀x y. F(x, x+1, y) is satisfiable over the natural numbers
   (ii) ∃z Z(z) ∧ ∀x ∃x' ∀y. F(x, x', y) is satisfiable over any model
*)

From Undecidability.FOL Require Import FullSyntax.


