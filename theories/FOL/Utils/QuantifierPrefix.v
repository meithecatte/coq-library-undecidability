From Undecidability.FOL Require Import FullSyntax PrenexNormalForm.
From Stdlib Require Import ssrbool.

Abbreviation quant := full_logic_quant.

Import List ListNotations.

Section QuantifierPrefix.
  Context {Σ_funcs : funcs_signature}.
  Context {Σ_preds : preds_signature}.
  Context {ff : falsity_flag}.

  Inductive quant_repeat :=
    | unlimited (q : quant)
    | once (q : quant).

  Definition quant_pattern := list quant_repeat.

  Declare Custom Entry qpat.
  Declare Custom Entry qrep.
  Declare Custom Entry quant.
  Notation "'All'" := All (in custom quant at level 0).
  Notation "'Ex'" := Ex (in custom quant at level 0).
  Notation "∀" := All (in custom quant at level 0).
  Notation "∃" := Ex (in custom quant at level 0).

  Notation "[ 'prefix' p ]" := p (p custom qpat, format "[ prefix  p ]").
  Notation "q *" := (unlimited q)
    (in custom qrep at level 1, q custom quant, format "q *").
  Notation "q" := (once q) (in custom qrep at level 1, q custom quant).
  (* specify the type explicitly to make the pretty-printer work correctly *)
  Notation "q qs" := (@cons quant_repeat q qs)
    (in custom qpat at level 2, right associativity, q custom qrep).
  Notation "q" := [q]
    (in custom qpat at level 2, right associativity, q custom qrep).

  Notation "( x )" := x (in custom qpat, x at level 10).
  Notation "{ x }" := x (in custom qpat, x constr).

  Check [prefix ∀].
  Check [prefix ∀* ∃].
  Check [prefix ∀* ∃ ∀*].
