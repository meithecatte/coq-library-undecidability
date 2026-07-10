(* Validity of Friedman translation of Prenex formulas in decidable models. *)

From Undecidability.FOL Require Import FullSyntax FriedmanTranslation PrenexNormalForm.
Require Import Undecidability.Synthetic.DecidabilityFacts.
Require Import Undecidability.Shared.Dec.


Section FixModel.
  Context {Σ_funcs : funcs_signature}.
  Context {Σ_preds : preds_signature}.
  Definition interp_dec {D} (I : interp D) := (forall p, decidable (fun v => i_atom (P:=p) v)).

  Context {D : Type} {I : interp D}.
  Hypothesis atom_dec : interp_dec I.

  Lemma noQuant_dec_sat `{ff : falsity_flag} (rho : env D) {phi : form} :
    noQuant_ind phi -> inhabited (dec (rho ⊨ phi)).
  Proof using atom_dec.
    intros H. induction H as [| | ff op phi1 phi2 H1 IH1 H2 IH2].
    - constructor. exact False_dec.
    - cbn.
      specialize (atom_dec P).
      apply decidable_iff in atom_dec.
      destruct atom_dec as [P_dec].
      constructor. apply P_dec.
    - destruct IH1 as [IH1]. destruct IH2 as [IH2].
      destruct op; constructor; cbn.
      + apply and_dec; easy.
      + apply or_dec; easy.
      + apply impl_dec; easy.
  Qed.

  Local Instance I' : @interp Σ_funcs extended_preds D := extend_interp I False.

  Lemma noQuant_Fr_iff `{ff : falsity_flag} (rho : env D) (phi : form) :
    noQuant_ind phi -> rho ⊨ phi <-> rho ⊨ Fr phi.
  Proof using atom_dec.
    intros H. induction H as [| | ff' op phi1 phi2 H1 IH1 H2 IH2].
    - (* falsity *) firstorder.
    - (* atom *)
      split; [firstorder|].
      specialize (atom_dec P).
      apply decidable_iff in atom_dec.
      destruct atom_dec as [P_dec].
      destruct (P_dec (Vector.map (eval rho) v)); firstorder.
    - destruct op.
      1,3: (* and, impl *) firstorder.
      split; [firstorder|].
      destruct (noQuant_dec_sat rho H1) as [[]];
        destruct (noQuant_dec_sat rho H2) as [[]];
        firstorder.
  Qed.

  Lemma PNF_Fr_sat `{ff : falsity_flag} (rho : env D) (phi : form) :
    PNF_ind phi -> rho ⊨ phi -> rho ⊨ Fr phi.
  Proof using atom_dec.
    intros H. revert rho. induction H as [| ff op phi H IH]; intros rho.
    - apply noQuant_Fr_iff, H.
    - destruct op; firstorder.
  Qed.

  Lemma PNF_conj_Fr_sat `{ff : falsity_flag} (rho : env D) (phi : form) :
    PNF_conj phi -> rho ⊨ phi -> rho ⊨ Fr phi.
  Proof using atom_dec.
    intros H. induction H.
    - auto using PNF_Fr_sat.
    - firstorder.
  Qed.

  Lemma PNF_conj_neg_Fr_sat (rho : env D) (phi : form) :
    PNF_conj phi -> rho ⊨ Fr (¬ phi) -> rho ⊨ ¬ phi.
  Proof using atom_dec.
    intros Hpnf Hfr Hphi.
    simpl in Hfr. apply Hfr.
    now apply PNF_conj_Fr_sat.
  Qed.
End FixModel.
