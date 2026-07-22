From Undecidability.FOL Require Import FullSyntax PrenexNormalForm.
From Stdlib Require Import ssrbool.

Abbreviation Quant := full_logic_quant.

Import List ListNotations.

Section QuantifierPrefix.
  Context {Σ_funcs : funcs_signature}.
  Context {Σ_preds : preds_signature}.

  Inductive qrep :=
    | unlimited (q : Quant)
    | once (q : Quant).

  Definition qpat := list qrep.

  Fixpoint prefix {ff : falsity_flag} (phi : form) : list Quant :=
    match phi with
    | falsity => []
    | atom _ _ => []
    | bin _ _ _ => []
    | quant q phi' => q :: prefix phi'
    end.

  Inductive matches_qpat : list Quant -> qpat -> Prop :=
    | qNil           : matches_qpat nil nil
    | qSkip q qs pat :
        matches_qpat qs pat ->
        matches_qpat qs (q :: pat)
    | qOnce q qs pat :
        matches_qpat qs pat ->
        matches_qpat (q :: qs) (once q :: pat)
    | qUnlimited q qs pat :
        matches_qpat qs        (unlimited q :: pat) ->
        matches_qpat (q :: qs) (unlimited q :: pat).

  Definition PrefixClass {ff : falsity_flag} (pat : qpat) (phi : form) :=
    closed phi /\ PNF_ind phi /\ matches_qpat (prefix phi) pat.

  (* We generalize the notion of a quantifier prefix to the class to
   * specify classes of conjunctions whose each clause has a specified
   * quantifier prefix. This is useful for describing some of the intermediate
   * classes that crop up in the classification of prefix-vocabulary classes. *)
  Definition gpat := list qpat.

  Fixpoint matches_gpat (prefs : list (list Quant)) (pats : gpat) : Prop :=
    match prefs, pats with
    | qs :: prefs, pat :: pats => matches_qpat qs pat /\ matches_gpat prefs pats
    | _ :: _, [] => False
    | [], _ => True
    end.

  Definition GPrefixClass {ff : falsity_flag} (pat : gpat) (phi : form) :=
    closed phi /\ PNF_conj phi /\ matches_gpat (map prefix (unconj phi)) pat.
End QuantifierPrefix.

Declare Custom Entry quant.
Notation "'All'" := All (in custom quant at level 0).
Notation "'Ex'" := Ex (in custom quant at level 0).
Notation "∀" := All (in custom quant at level 0).
Notation "∃" := Ex (in custom quant at level 0).

Declare Custom Entry qrep.
Notation "q *" := (unlimited q)
  (in custom qrep at level 1, q custom quant, format "q *").
Notation "q" := (once q) (in custom qrep at level 1, q custom quant).

Declare Custom Entry qpat.
Notation "q ^ k qs" := (repeat q k ++ qs)
  (in custom qpat at level 2, right associativity, q custom qrep,
    k constr at level 100, format "q ^ k  qs").
(* specify the type explicitly to make the pretty-printer work correctly *)
Notation "q qs" := (@cons qrep q qs)
  (in custom qpat at level 2, right associativity, q custom qrep).
Notation "" := (@nil qrep)
  (in custom qpat at level 2, right associativity).

(* pretty-printer special cases to avoid extraneous whitespace at the end *)
Notation "q" := (@cons qrep q (@nil qrep))
  (in custom qpat at level 2, q custom qrep, only printing).
Notation "q ^ k" := (repeat q k ++ (@nil qrep))
  (in custom qpat at level 2, q custom qrep, k constr at level 100,
    format "q ^ k", only printing).

Declare Custom Entry gpat.
Notation "p" := (@cons qpat p (@nil qpat))
  (in custom gpat at level 1, p custom qpat).
Notation "p ∧ ps" := (@cons qpat p ps)
  (in custom gpat at level 1, right associativity, p custom qpat).
Notation "p /\ ps" := (@cons qpat p ps)
  (in custom gpat at level 1, right associativity, p custom qpat,
   only parsing).
Notation "[ 'prefix' p ]" := p (at level 0, p custom qpat, format "[ prefix  p ]").
Notation "[ 'gprefix' p ]" := p (at level 0, p custom gpat, format "[ gprefix  p ]").

(*
Check [prefix ∀].
Check [prefix ∀* ∃].
Check [prefix ∀* ∃^2 ∀*].
Check [prefix ∀* ∃^2].
Check []. (* make sure this doesn't get printed using the new notations *)

Check [gprefix ∀* ∃^2 ∀*].
Check [gprefix ∃ ∧ ∀∃∀].
 *)
