(*
  Satisfiability in [∃ ∧ ∀∃∀, (ω, 3)] is undecidable.
  The reduction class has been identified by Büchi, see:
  - Büchi, R. Turing-Machines and the Entscheidungsproblem, Math. Annalen 148, 201–203 (1962)
  - Börger, Grädel & Gurevich. The Classical Decision Problem. (2001) pp. 33–36
  
  We perform a novel reduction from 2-counter Minsky machines MM2.
  This sidesteps the need for developing Turing machines with the tape
  infinite in only one direction, and the undecidability of their halting
  problem from the all-0 tape.
*)
From Undecidability.FOL Require Import FullSyntax ReductionClass.
From Undecidability.MinskyMachines Require Import MM2 MM2_facts.
From Undecidability.Shared Require Import Vectors.
From Stdlib Require Import List ssreflect ssrfun ssrbool PeanoNat.

(* A(x, y) = Counter A has value y at time x. *)
(* B(x, y) = Counter B has value y at time x. *)
(* H(x, y) = Counter being modified had value y at time x-1 (helper predicate) *)
(* Q_i(x) = Machine is in state i at time x. *)
(* INC(x) = Machine ran an increment instruction at time x-1. *)
(* DEC(x) = Machine ran a successful decrement instruction at time x-1. *)
(* MA(x) = Machine ran an instruction on counter A at time x-1. *)
(*   (with MB = ¬ MA) *)
(* ZA(x) = Counter A is zero at time x. *)
(* ZB(x) = Counter B is zero at time x. *)
(* Z(x) = x is zero. *)
Inductive syms_pred := sA | sB | sH
  | sQ of nat | sINC | sDEC | sMA | sZA | sZB | sZ.

Definition ar_pred (s : syms_pred) : nat :=
  match s with
  | sA | sB | sH => 2
  | _ => 1
  end.

#[local]
Instance sig_pred : preds_signature :=
  {| preds := syms_pred; ar_preds := ar_pred |}.

#[local]
Instance sig_empty : funcs_signature :=
  {| syms := False; ar_syms := False_rect nat |}.

(*
  The reduction proceeds in two steps. First, we define formulas
  F(x, x', y) and G(x, x' y) such that ∀x y. F(x, x+1, 0) ∧ G(x, x+1, y)
  is satisfiable on the natural numbers iff the Minsky machine doesn't halt.

  Next, we adjoin a predicate Z(x) with the intended interpretation of
  "x is zero", and transform the formula into the form
  ∃z. Z(z) ∧ ∀x. ∃x'. ∀y. (Z(y) -> F(x, x', y)) ∧ G(x, x', y)
*)

Import VectorNotations2.
Local Open Scope vector_scope.
Section Reduction.
  Variable M : list mm2_instr.

  Abbreviation A x y := (atom sA ([| x; y |])).
  Abbreviation B x y := (atom sB ([| x; y |])).
  Abbreviation H x y := (atom sH ([| x; y |])).
  Abbreviation QQ i x := (atom (sQ i) ([| x |])).
  Abbreviation INC x := (atom sINC ([| x |])).
  Abbreviation DEC x := (atom sDEC ([| x |])).
  Abbreviation MA x := (atom sMA ([| x |])).
  Abbreviation MB x := (¬ MA x).
  Abbreviation ZA x := (atom sZA ([| x |])).
  Abbreviation ZB x := (atom sZB ([| x |])).
  Abbreviation Z x := (atom sZ ([| x |])).
  Abbreviation STAY x := (¬ INC x ∧ ¬ DEC x).

  Definition Q i (x : term) : form :=
    if (0 <? i) && (i <=? length M) then
      QQ i x
    else
      ⊥.

  (* If not modifying a counter, it's at the same position as the step before *)
  Definition GstayA : form := (MB $1 ∨ STAY $1) → (A $2 $0 ↔ A $1 $0).
  Definition GstayB : form := (MA $1 ∨ STAY $1) → (B $2 $0 ↔ B $1 $0).
  (* If incrementing a counter, do it by using the helper predicate *)
  Definition GincA : form := MA $0 → INC $0 → (H $0 $2 ↔ A $0 $1).
  Definition GincB : form := MB $0 → INC $0 → (H $0 $2 ↔ B $0 $1).
  (* Likewise for decrementing *)
  Definition GdecA : form := MA $0 → DEC $0 → (H $0 $1 ↔ A $0 $2).
  Definition GdecB : form := MB $0 → DEC $0 → (H $0 $1 ↔ B $0 $2).

  Definition G0 : form := (GstayA ∧ GstayB) ∧ (GincA ∧ GincB) ∧ (GdecA ∧ GdecB).

  (* At time 0, state is 1 and both counters are 0. *)
  Definition F1 : form := Q 1 $0 ∧ A $0 $0 ∧ B $0 $0 ∧ ¬ A $0 $1 ∧ ¬ B $0 $1.
  (* If incremented a counter, its value will not be 0. *)
  Definition F2 : form := MA $2 → INC $2 → ¬ A $2 $0.
  Definition F3 : form := MB $2 → INC $2 → ¬ B $2 $0.
  (* ZA and ZB correctly indicate whether counters are zero. *)
  Definition F4 : form := ZA $2 ↔ A $2 $0.
  Definition F5 : form := ZB $2 ↔ B $2 $0.

  Definition F0 : form := F1 ∧ F2 ∧ F3 ∧ F4 ∧ F5.

  Definition modA : form := MA $1 ∧ (A $2 $0 ↔ H $1 $0).
  Definition modB : form := MB $1 ∧ (B $2 $0 ↔ H $1 $0).
  (* Encode [inst] at position [i] *)
  Definition enc_instr (ni : nat * mm2_instr) : form :=
    match ni with
    | (i, mm2_inc_a) => Q i $2 → Q (S i) $1 ∧ INC $1 ∧ modA
    | (i, mm2_inc_b) => Q i $2 → Q (S i) $1 ∧ INC $1 ∧ modB
    | (i, mm2_dec_a j) => Q i $2 →
        (¬ ZA $2 → Q j $1 ∧ DEC $1 ∧ modA)
        ∧ (ZA $2 → Q (S i) $1 ∧ STAY $1)
    | (i, mm2_dec_b j) => Q i $2 →
        (¬ ZB $2 → Q j $1 ∧ DEC $1 ∧ modB)
        ∧ (ZB $2 → Q (S i) $1 ∧ STAY $1)
    end.

  Definition Ginstrs := map enc_instr (combine (seq 1 (length M)) M).
  Definition G : form := bigconj G0 Ginstrs.
  Definition F : form := (∃ Z $0) ∧ ∀ ∃ ∀ (Z $0 → F0) ∧ G.

  Definition conf_at t := odflt (0,(0,0)) (mm2_steps M t (1,(0,0))).
  Definition instr_at q := nth (Nat.pred q) M (mm2_inc_a).
  Abbreviation arg1 v := (Vector.hd v).
  Abbreviation arg2 v := (Vector.hd (Vector.tl v)).

  Import MM2Notations.
  Section NatModel.
    Definition modifiesA (instr : mm2_instr) :=
      match instr with
      | mm2_inc_a | mm2_dec_a _ => true
      | _ => false
      end.

    Definition isINC (instr : mm2_instr) :=
      match instr with
      | mm2_inc_a | mm2_inc_b => true
      | _ => false
      end.

    Definition i_atomN (P : preds) : Vector.t nat (ar_preds P) -> Prop :=
      match P with
      | sZ   => fun v => arg1 v = 0

      | sA   => fun v =>
          let '(q,(a,b)) := conf_at (arg1 v) in
          a = arg2 v
      | sB   => fun v =>
          let '(q,(a,b)) := conf_at (arg1 v) in
          b = arg2 v
      | sZA  => fun v =>
          let '(q,(a,b)) := conf_at (arg1 v) in
          a = 0
      | sZB  => fun v =>
          let '(q,(a,b)) := conf_at (arg1 v) in
          b = 0
      | sQ i => fun v =>
          let '(q,(a,b)) := conf_at (arg1 v) in
          q = i

      | sMA  => fun v =>
          let '(q,(a,b)) := conf_at (Nat.pred (arg1 v)) in
          let instr := instr_at q in
          modifiesA instr = true
      | sH   => fun v =>
          let '(q,(a,b)) := conf_at (Nat.pred (arg1 v)) in
          let instr := instr_at q in
          if modifiesA instr then
            a = arg2 v
          else
            b = arg2 v
      (* While MA and H can have any values we'd like at t=0, INC and DEC must be false *)
      | sINC => fun v =>
          match arg1 v with
          | 0 => False
          | S x =>
              let '(q,(a,b)) := conf_at x in
              let instr := instr_at q in
              isINC instr = true
          end
      | sDEC => fun v =>
          match arg1 v with
          | 0 => False
          | S x =>
              let '(q,(a,b)) := conf_at x in
              let instr := instr_at q in
              isINC instr = false /\
              if modifiesA instr then
                a <> 0
              else
                b <> 0
          end
      end.

    Instance INat : interp nat :=
      {| i_func f := False_rect _ f;
         i_atom := i_atomN |}.

    Hypothesis Hnohalt : ~ MM2_ZERO_HALTING M.

    Lemma conf_at_S t : mm2_step M (conf_at t) (conf_at (S t)).
    Proof using Hnohalt.
      rw -Nat.add_1_r /conf_at mm2_steps_plus'.
      case E: (mm2_steps M t _) => /=; last first.
        by have := mm2_steps_none E.
      case: mm2_sig_step_dec => [[y hy] |] //=.
      move=> /mm2_stop_terminates hterm.
      move=> /mm2_steps_reaches /mm2_steps_terminates_l in E.
      by have := Hnohalt (E hterm).
    Qed.

    Lemma instr_atE {q inst} : mm2_instr_at inst q M -> instr_at q = inst.
    Proof.
      move=> hinstr_at.
      have := mm2_instr_at_bounds hinstr_at.
      case: q => [| q] in hinstr_at *.
        case=> /Nat.lt_irrefl //.
      rw -nth_error_Some_mm2_instr_at_iff in hinstr_at.
      rw /instr_at (nth_error_nth _ _ _ hinstr_at) //.
    Qed.

    Lemma QE {q inst x} : mm2_instr_at inst q M -> Q q x = QQ q x.
    Proof.
      move/mm2_instr_at_bounds.
      rw/Q; case.
      move/Nat.ltb_lt => ->.
      move/Nat.leb_le => -> //.
    Qed.

    Inductive conf_at_spec (t : nat) : mm2_state -> mm2_state -> Prop :=
      | conf_at_specI q a b q' a' b' :
          mm2_step M (q, (a, b)) (q', (a', b')) ->
          (forall y rho, (y .: S t .: t .: rho) ⊨ Q q' $1) ->
          conf_at_spec t (q, (a, b)) (q', (a', b')).

    Lemma conf_at_inv t : conf_at_spec t (conf_at t) (conf_at (S t)).
    Proof using Hnohalt.
      move: (conf_at_S t) (conf_at_S (S t)).
      case: (conf_at t) => [q [a b]].
      case E: (conf_at (S t)) => [q' [a' b']] h1 [? [/= h2 _]].
      apply: conf_at_specI => // y rho.
      by rw (QE h2) /= E.
    Qed.

    Lemma INat_sat_F0 x rho : (0 .: S x .: x .: rho) ⊨ F0.
    Proof using Hnohalt.
      repeat split=> //.
        have [inst [hinst _]] := conf_at_S 0.
        by rw (QE hinst).
      all: case: x => [| x] //=.
      all: case: (conf_at_inv x) => q a b q' a' b' [/= inst [/instr_atE -> hatom]] _.
      all: case: inst => [||j|j] // in hatom *.
      all: move=> _ _.
      all: by inversion hatom.
    Qed.

    Lemma INat_sat_instr inst i x y rho :
      mm2_instr_at inst i M -> (y .: S x .: x .: rho) ⊨ enc_instr (i, inst).
    Proof using Hnohalt.
      case: inst => [||j|j] /= hinstr_at.
      all: rw (QE hinstr_at) /=.
      all: case: (conf_at_inv x) => q a b q' a' b' [inst [/= hinst hatom]] h' eqi.
      all: rw -{}eqi {i} in hinstr_at *.
      all: rw -{hinst inst}(mm2_instr_at_unique hinstr_at hinst) in hatom.
      all: rw {hinstr_at}(instr_atE hinstr_at) /=.
      1,2: by inversion hatom; subst.
      - case: a => [| a] in hatom *; split=> _ //=; last by inversion hatom.
        inversion hatom; subst; repeat split=> //; by case.
      - case: b => [| b] in hatom *; split=> _ //=; last by inversion hatom.
        inversion hatom; subst; repeat split=> //; by case.
    Qed.

    Lemma INat_sat_Gstay x y rho : (y .: S x .: x .: rho) ⊨ GstayA ∧ GstayB.
    Proof using Hnohalt.
      cbn; split.
      all: case: (conf_at_inv x) => q a b q' a' b' [/= inst [/instr_atE -> hatom]] _.
      all: case: inst => [||j|j] /= in hatom *; try by inversion hatom; try firstorder.
      1: case: a => [| a] // in hatom *; first by inversion hatom.
      2: case: b => [| b] // in hatom *; first by inversion hatom.
      all: by case=> [// | [_ []]].
    Qed.

    Lemma INat_sat_Ginc x y rho : (y .: S x .: x .: rho) ⊨ GincA ∧ GincB.
    Proof using Hnohalt.
      cbn; split; case: y => [| y] //=.
      all: case: (conf_at_inv y) => q a b q' a' b' [/= inst [/instr_atE -> hatom]] _.
      all: case: inst => [||j|j] //= in hatom *; inversion hatom; split; congruence.
    Qed.

    Lemma INat_sat_Gdec x y rho : (y .: S x .: x .: rho) ⊨ GdecA ∧ GdecB.
    Proof using Hnohalt.
      cbn; split; case: y => [| y] //=.
      all: case: (conf_at_inv y) => q a b q' a' b' [/= inst [/instr_atE -> hatom]] _.
      all: case: inst => [||j|j] //= in hatom *; move=> _; case=> //.
      1: case: a => [| a] // in hatom *.
      2: case: b => [| b] // in hatom *.
      all: inversion hatom; split; congruence.
    Qed.

    Lemma INat_sat : INat ⊨= F.
    Proof using Hnohalt.
      cbn -[G F0]=> rho.
      split=> [| x]; first eauto.
      exists (S x) => y.
      split=> [-> |].
      - exact: INat_sat_F0.
      - apply/bigconj_sat; split=> [psi /in_map_iff |].
          case=> [[i inst] [<- /mm2_inv_instr_at_in_combine hinstr_at]].
          exact: INat_sat_instr.
        split; last exact: INat_sat_Gdec.
        split; last exact: INat_sat_Ginc.
        exact: INat_sat_Gstay.
    Qed.
  End NatModel.

  Section Soundness.
    Context D (I : interp D) (rho : env D).
    Hypothesis Hsat : rho ⊨ F.

    Abbreviation iA x y := (@i_atom _ _ _ _ sA ([| x; y |])).
    Abbreviation iB x y := (@i_atom _ _ _ _ sB ([| x; y |])).
    Abbreviation iH x y := (@i_atom _ _ _ _ sH ([| x; y |])).
    Abbreviation iZ x := (@i_atom _ _ _ _ sZ ([| x |])).

    Definition codes_conf (f : nat -> D) (t : nat) : mm2_state -> Prop :=
      fun '(q,(a,b)) => (f t .: rho) ⊨ Q q $0 /\
        (f t .: f a .: rho) ⊨ A $0 $1 /\
        (f t .: f b .: rho) ⊨ B $0 $1.

    Definition initial_fragment (f : nat -> D) (n : nat) :=
      forall t, t <= n -> codes_conf f t (conf_at t).

    Inductive Qspec rho' q n : form -> Prop :=
      | QspecI : rho' ⊨ QQ q $n -> Qspec rho' q n (QQ q $n).

    Lemma QsatP rho' q n : rho' ⊨ Q q $n -> Qspec rho' q n (Q q $n).
    Proof.
      rw /Q. elim: (_ && _) => //=.
    Qed.

    Lemma has_fragment n : exists f, initial_fragment f n.
    Proof.
      elim: n => [| n [f IH]].
      - cbn -[F0 G] in Hsat. elim: Hsat => [[z hz] h].
        elim: {h}(h z) => [z' h].
        elim: {h}(h z) => [hF0 hG].
        cbn -[F1] in hF0.
        elim: {hF0}(hF0 hz) => [[[[hF1 _ ] _] _] _].
        cbn in hF1.
        elim: hF1 => [[[[hQ hA] hB] hnA] hnB].
        exists (fun=> z) => t /Nat.le_0_r {t}-> /=; repeat split=> //.
        by case: (QsatP hQ).
      -

    Lemma satis_nonhalt : ~ MM2_ZERO_HALTING M.
    Admitted.
  End Soundness.
End Reduction.

From Undecidability.Synthetic Require Import Definitions Undecidability ReducibilityFacts.
From Undecidability.MinskyMachines Require Import MM2_undec.

(* skip the quantifier prefix part of the definitions for now *)
Definition Buchi_satis := @satis _ _ falsity_on.
Definition Buchi_valid := @valid _ _ falsity_on.

Theorem satis_red : complement MM2_ZERO_HALTING ⪯ Buchi_satis.
Proof.
  exists F => M.
  split=> [/INat_sat h | [D [I [rho h]]]].
    by exists nat, (INat M), (fun _ => 0).
  exact: satis_nonhalt h.
Qed.

Theorem undecidable_Buchi_satis : undecidable Buchi_satis.
Proof.
  apply: (undecidability_from_reducibility MM2_ZERO_HALTING_compl_undec).
  exact: satis_red.
Qed.

Theorem valid_red : complement Buchi_satis ⪯ Buchi_valid.
Proof.
  exists (fun phi => ¬ phi) => phi.
  split=> [hnsatis D I rho | hvalid [D [I [rho hsat]]]]; last first.
    exact: (hvalid D I rho hsat).
  cbn=> hsat.
  apply: hnsatis.
  by exists D, I, rho.
Qed.

Theorem undecidable_Buchi_valid : undecidable Buchi_valid.
Proof.
  apply: undecidability_from_reducibility; last first.
    apply: (reduces_transitive _ valid_red).
    exact: reduces_complement satis_red.
  exact: undecidability_to_complement MM2_ZERO_HALTING_compl_undec.
Qed.
