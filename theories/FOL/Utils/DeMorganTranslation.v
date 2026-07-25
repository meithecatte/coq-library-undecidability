(** Kolmogorov translation *)

(* A translation from full FOL to the forall-implicative fragment. Unlike
 * FiniteTarski.DoubleNegation, we obtain [rho ⊨ phi -> rho ⊨ Ko phi], even for
 * models whose predicates aren't decidable. Additionally, we don't bother
 * minimizing the amount of negations used, resulting in a feasible proof that
 * the translation preserves provability.
 *)

From Undecidability.FOL.Semantics.Tarski Require Import FullFacts FragmentFacts.

From Stdlib Require Import ssreflect.

Section translation. 
  Import FragmentSyntax.
  Existing Instance FragmentSyntax.frag_operators.
  Existing Instance falsity_on.
  Context {Σ_funcs : funcs_signature}.
  Context {Σ_preds : preds_signature}. 

  Abbreviation fragform := (@form _ _ frag_operators falsity_on).
  Abbreviation fullform f := (@form _ _ full_operators f).

  Definition dn (phi : form) := ¬ ¬ phi.

  Fixpoint Ko {f : falsity_flag} (phi : fullform f) : fragform :=
    match phi with
    | falsity => falsity
    | atom P v => dn (atom P v)
    | bin Conj l r => ¬ (Ko l → ¬ Ko r)
    | bin Disj l r => ¬ Ko l → Ko r
    | bin FullSyntax.Impl l r => dn (Ko l → Ko r)
    | quant FullSyntax.All phi => dn (∀ Ko phi)
    | quant Ex phi => ¬ ∀ ¬ Ko phi
    end.

  Context {D : Type}.
  Context {I : interp D}.

  (* XXX copying there definitions is probably not the greatest approach *)
  (* Define interpretations for full and frag syntax, which are equivalent. *)
  Definition tarski_full_tarski_interp (II:interp D) : FullCore.interp D.
  Proof.
  destruct II; split; easy.
  Defined.

  Definition full_tarski_tarski_interp (II:FullCore.interp D) : interp D.
  Proof.
  destruct II; split; easy.
  Defined.

  Definition full_interp_inverse_1 II : tarski_full_tarski_interp (full_tarski_tarski_interp II) = II.
  Proof. now destruct II. Qed.

  Definition full_interp_inverse_2 II : full_tarski_tarski_interp (tarski_full_tarski_interp II) = II.
  Proof. now destruct II. Qed.

  Notation "rho ⊨ phi" := (@sat _ _ D I falsity_on rho phi).
  Notation "rho 'f⊨' phi" := (@FullCore.sat _ _ D (tarski_full_tarski_interp I) _ rho phi) (at level 20).

  (* Terms are evaluated to equal results *)
  Lemma eval_same env trm : eval env trm = @FullCore.eval _ _ D (tarski_full_tarski_interp I) env trm.
  Proof.
  induction trm as [n|k v IH].
  - easy.
  - destruct I. cbn. erewrite VectorSpec.map_ext_in. 1:reflexivity.
    apply IH.
  Qed.

  Lemma eval_same_atom t (vt:Vector.t D (ar_preds t)) : i_atom vt <-> @FullCore.i_atom _ _ D (tarski_full_tarski_interp I) t vt.
  Proof.
  destruct I. cbn. easy.
  Qed.

  Lemma Ko_sat rho phi : (rho f⊨ phi -> rho ⊨ Ko phi) /\ (rho ⊨ Ko phi -> ~ ~ rho f⊨ phi).
  Proof.
    revert rho; induction phi as [| | ff [] | ff [] ] => rho //=.
    - (* atom *)
      rw -eval_same_atom.
      by under Vector.map_ext do rw -eval_same.
    - (* conj *) firstorder.
    - (* disj *) firstorder.
    - (* impl *) firstorder.
    - (* forall *) firstorder.
      split.
      + firstorder.
      + 
