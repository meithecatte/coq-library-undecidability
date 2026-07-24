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
From Undecidability.FOL Require Import FullSyntax ReductionClass QuantifierPrefix.
From Undecidability.MinskyMachines Require Import MM2 MM2_facts.
From Undecidability.Shared Require Import Vectors.
From Stdlib Require Import List Lia ssreflect ssrfun ssrbool PeanoNat.

(* A(x, y) = Counter A has value y at time x. *)
(* B(x, y) = Counter B has value y at time x. *)
(* H(x, y) = Counter being modified had value y at time x-1 (helper predicate) *)
(* Q_i(x) = Machine is in state i at time x. *)
(* INC(x) = Machine ran an increment instruction at time x-1. *)
(*   (with DEC = ¬ INC) *)
(* MA(x) = Machine ran an instruction on counter A at time x-1. *)
(*   (with MB = ¬ MA) *)
(* ZA(x) = Counter A is zero at time x. *)
(* ZB(x) = Counter B is zero at time x. *)
(* Z(x) = x is zero. *)
Inductive syms_pred := sA | sB | sH
  | sQ of nat | sINC | sMA | sZA | sZB | sZ.

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
  Abbreviation DEC x := (¬ INC x).
  Abbreviation MA x := (atom sMA ([| x |])).
  Abbreviation MB x := (¬ MA x).
  Abbreviation ZA x := (atom sZA ([| x |])).
  Abbreviation ZB x := (atom sZB ([| x |])).
  Abbreviation Z x := (atom sZ ([| x |])).

  Definition Q i (x : term) : form :=
    if (0 <? i) && (i <=? length M) then
      QQ i x
    else
      ⊥.

  (* At time 0, state is 1 and both counters are 0. *)
  Definition Finit : form := Q 1 $0 ∧ A $0 $0 ∧ B $0 $0.
  (* If decremented a counter that was already zero, its value will remain at 0. *)
  Definition FdecA : form := MA $2 → DEC $2 → H $2 $0 → A $2 $0.
  Definition FdecB : form := MB $2 → DEC $2 → H $2 $0 → B $2 $0.
  (* If a counter is 0, Zx indicates this.
   * Note: turning this into an equivalence is not enough to ensure that
   * ¬ Zx when the counter shouldn't be zero, because the model might be
   * representing 0 and some other number using the same element of the domain.
   * While we could modify the formula to explicitly require that ¬ Z(x') for
   * successors, that would require proving otherwise superfluous lemmas, such as
   * the configuration being unique at each particular point.
   *
   * Instead, we just add implications in the other direction to our formula: see
   * Gzero[AB].
   *)
  Definition FZA : form := A $2 $0 → ZA $2.
  Definition FZB : form := B $2 $0 → ZB $2.

  Definition F0 : form := Finit ∧ FdecA ∧ FdecB ∧ FZA ∧ FZB.

  (* If not modifying a counter, it's at the same position as the step before *)
  Definition GstayA : form := MB $1 → A $2 $0 → A $1 $0.
  Definition GstayB : form := MA $1 → B $2 $0 → B $1 $0.
  (* If incrementing a counter, do it by using the helper predicate *)
  Definition GincA  : form := MA $0 → INC $0 → H $0 $2 → A $0 $1.
  Definition GincB  : form := MB $0 → INC $0 → H $0 $2 → B $0 $1.
  (* Likewise for decrementing *)
  Definition GdecA  : form := MA $0 → DEC $0 → H $0 $1 → A $0 $2.
  Definition GdecB  : form := MB $0 → DEC $0 → H $0 $1 → B $0 $2.
  (* If a counter is non-zero, Zx doesn't report it as zero. *)
  Definition GzeroA : form := A $0 $1 → ¬ ZA $0.
  Definition GzeroB : form := B $0 $1 → ¬ ZB $0.

  Definition G0 : form := (GstayA ∧ GstayB) ∧ (GincA ∧ GincB) ∧ (GdecA ∧ GdecB) ∧ (GzeroA ∧ GzeroB).

  Definition modA : form := MA $1 ∧ (A $2 $0 → H $1 $0).
  Definition modB : form := MB $1 ∧ (B $2 $0 → H $1 $0).
  (* Encode [inst] at position [i] *)
  Definition enc_instr (ni : nat * mm2_instr) : form :=
    match ni with
    | (i, mm2_inc_a) => Q i $2 → Q (S i) $1 ∧ INC $1 ∧ modA
    | (i, mm2_inc_b) => Q i $2 → Q (S i) $1 ∧ INC $1 ∧ modB
    | (i, mm2_dec_a j) => Q i $2 → DEC $1 ∧ modA
        ∧ (¬ ZA $2 → Q j $1)
        ∧ (ZA $2 → Q (S i) $1)
    | (i, mm2_dec_b j) => Q i $2 → DEC $1 ∧ modB
        ∧ (¬ ZB $2 → Q j $1)
        ∧ (ZB $2 → Q (S i) $1)
    end.

  Definition Ginstrs := map enc_instr (combine (seq 1 (length M)) M).
  Definition G : form := bigconj G0 Ginstrs.
  Definition F : form := (∃ Z $0) ∧ ∀ ∃ ∀ (Z $0 → F0) ∧ G.

  Definition conf_at t := odflt (0,(0,0)) (mm2_steps M t (1,(0,0))).
  Definition instr_at q := nth (Nat.pred q) M (mm2_inc_a).
  Abbreviation arg1 v := (Vector.hd v).
  Abbreviation arg2 v := (Vector.hd (Vector.tl v)).

  Lemma F_closed : closed F.
  Proof.
    have bounded_Q k i t : bounded_t k t -> bounded k (Q i t).
      by rw /Q; case (_ && _) => h; solve_bounds.
    have bounded_enc_instr i inst : bounded 3 (enc_instr (i,inst)).
      by case: inst => [||j|j] /=; solve_bounds; apply: bounded_Q; solve_bounds.
  Admitted.

  Hint Constructors matches_qpat : core.
  Lemma F_qpat : GPrefixClass ([gprefix ∃ ∧ ∀∃∀]) F.
  Proof.
    split; first exact: F_closed.
    split; first admit.
    rw /=; auto 6.
  Admitted.

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

      (* For simplicity, set H(0,0) and DEC(0). MA(0) can be whatever *)
      | sINC => fun v =>
          match arg1 v with
          | 0 => False
          | S x => 
            let '(q,(a,b)) := conf_at x in
            let instr := instr_at q in
            isINC instr = true
          end
      | sH   => fun v =>
          match arg1 v with
          | 0 => arg2 v = 0
          | S x => 
            let '(q,(a,b)) := conf_at x in
            let instr := instr_at q in
            if modifiesA instr then
              a = arg2 v
            else
              b = arg2 v
          end
      | sMA  => fun v =>
          let '(q,(a,b)) := conf_at (Nat.pred (arg1 v)) in
          let instr := instr_at q in
          modifiesA instr = true
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
      - case: a => [| a] in hatom *; repeat split=> _ //=; last by inversion hatom.
        inversion hatom; subst; repeat split=> //; by case.
      - case: b => [| b] in hatom *; repeat split=> _ //=; last by inversion hatom.
        inversion hatom; subst; repeat split=> //; by case.
    Qed.

    Lemma INat_sat_Gstay x y rho : (y .: S x .: x .: rho) ⊨ GstayA ∧ GstayB.
    Proof using Hnohalt.
      cbn; split.
      all: case: (conf_at_inv x) => q a b q' a' b' [/= inst [/instr_atE -> hatom]] _.
      all: case: inst => [||j|j] /= in hatom *; try by inversion hatom; try firstorder.
    Qed.

    Lemma INat_sat_Ginc x y rho : (y .: S x .: x .: rho) ⊨ GincA ∧ GincB.
    Proof using Hnohalt.
      cbn; split; case: y => [| y] //=.
      all: case: (conf_at_inv y) => q a b q' a' b' [/= inst [/instr_atE -> hatom]] _.
      all: case: inst => [||j|j] //= in hatom *; inversion hatom; congruence.
    Qed.

    Lemma INat_sat_Gdec x y rho : (y .: S x .: x .: rho) ⊨ GdecA ∧ GdecB.
    Proof using Hnohalt.
      cbn; split; case: y => [| y] //=.
      all: case: (conf_at_inv y) => q a b q' a' b' [/= inst [/instr_atE -> hatom]] _.
      all: case: inst => [||j|j] //= in hatom *; move=> _ _.
      1: case: a => [| a] // in hatom *.
      2: case: b => [| b] // in hatom *.
      all: inversion hatom; congruence.
    Qed.

    Lemma INat_sat_Gzero x y rho : (y .: S x .: x .: rho) ⊨ GzeroA ∧ GzeroB.
    Proof.
      cbn; case: (conf_at y) => [q [a b]].
      split; congruence.
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
        split; last exact: INat_sat_Gzero.
        split; last exact: INat_sat_Gdec.
        split; last exact: INat_sat_Ginc.
        exact: INat_sat_Gstay.
    Qed.
  End NatModel.

  Section Soundness.
    Context D (I : interp D) (rho : env D).
    Hypothesis Hsat : rho ⊨ F.

    Abbreviation iA x y := (@i_atom _ _ _ I sA ([| x; y |])).
    Abbreviation iB x y := (@i_atom _ _ _ I sB ([| x; y |])).
    Abbreviation iH x y := (@i_atom _ _ _ I sH ([| x; y |])).
    Abbreviation iQQ i x := (@i_atom _ _ _ I (sQ i) ([| x |])).
    Abbreviation iINC x := (@i_atom _ _ _ I sINC ([| x |])).
    Abbreviation iMA x := (@i_atom _ _ _ I sMA ([| x |])).
    Abbreviation iZA x := (@i_atom _ _ _ I sZA ([| x |])).
    Abbreviation iZB x := (@i_atom _ _ _ I sZB ([| x |])).
    Abbreviation iZ x := (@i_atom _ _ _ I sZ ([| x |])).

    Definition iQ i (x : D) : Prop := 0 < i /\ i <= length M /\ iQQ i x.

    Lemma Qsat_iff_iQ i rho' n : rho' ⊨ Q i $n <-> iQ i (rho' n).
    Proof.
      clear Hsat rho.
      rw /Q /iQ.
      case: Nat.ltb_spec0; last by firstorder.
      case: Nat.leb_spec0; by firstorder.
    Qed.

    Lemma iQ_mm2_instr_at q x : iQ q x -> mm2_instr_at (instr_at q) q M.
    Proof.
      case=> [lt [le hq]].
      case: {hq} q => [|q] in lt le *.
        by move/Nat.lt_irrefl in lt.
      rw /instr_at /=.
      apply/nth_error_Some_mm2_instr_at_iff.
      exact: nth_error_nth'.
    Qed.

    Inductive Qspec rho' q n : form -> Prop :=
      | QspecI : rho' ⊨ QQ q $n -> Qspec rho' q n (QQ q $n).

    Lemma QsatP rho' q n : rho' ⊨ Q q $n -> Qspec rho' q n (Q q $n).
    Proof.
      rw /Q. elim E: (_ && _) => //=.
    Qed.

    Lemma F0_replace x y1 y2 z :
      (z .: y1 .: x .: rho) ⊨ F0 -> (z .: y2 .: x .: rho) ⊨ F0.
    Proof.
      cbn. elim=> [[[[[[hQ hA] hB] hF2] hF3] hF4] hF5].
      repeat split=> //.
      by case: (QsatP hQ).
    Qed.

    Definition codes_conf (f : nat -> D) (t : nat) : mm2_state -> Prop :=
      fun '(q,(a,b)) => iQ q (f t) /\ iA (f t) (f a) /\ iB (f t) (f b).

    Definition initial_fragment (f : nat -> D) (n : nat) :=
      iZ (f 0) /\
      (forall y, (f 0 .: f 0 .: y .: rho) ⊨ F0) /\
      forall x y, x < n -> (y .: f (S x) .: f x .: rho) ⊨ G.

    Lemma has_fragment n : exists f, initial_fragment f n.
    Proof using Hsat.
      cbn -[F0 G] in Hsat. elim: Hsat => [[z hz] h]. clear Hsat.
      elim: n => [| n [f [IHz [IHF0 IHG]]]].
      - exists (fun=> z). split=> //. split=> [y | x y /Nat.nlt_0_r] //.
        elim: {h}(h y) => [y' h].
        elim: {h}(h z) => [hF0 _].
        specialize (hF0 hz).
        apply: F0_replace hF0.
      - elim: {z hz}(h (f n)) => [x' hx'].
        exists (fun k => if k =? S n then x' else f k).
        split=> //; cbn -[F0].
        split=> [y | x y].
        + elim: {h}(h y) => [y' h].
          elim: {h}(h (f 0)) => [hF0 _].
          specialize (hF0 IHz).
          apply: F0_replace hF0.
        + case: (Nat.eqb_spec x (S n)) => [-> /Nat.lt_irrefl // | _].
          case: (Nat.eqb_spec x n) => [-> _ | ne_xn le_xSn]; last first.
            by apply: IHG; lia.
          by elim: (hx' y).
    Qed.

    Lemma codes_conf_S f t :
      codes_conf f t (conf_at t) -> mm2_step M (conf_at t) (conf_at (S t)).
    Proof.
      rw -Nat.add_1_r /conf_at mm2_steps_plus'.
      elim: (mm2_steps M t (1,(0,0))) => [[q [a b]]|]; last first.
        by rw /=; case; case=> /Nat.lt_irrefl.
      rw /=.
      elim=> [hQ _].
      case: mm2_sig_step_dec => [[y hy] | hstop] //.
      case: (mm2_progress (instr_at q) (q,(a,b))) => y Hatom.
      suff: False by []; apply: hstop.
      exists (instr_at q); split.
        exact: iQ_mm2_instr_at hQ.
      exact: Hatom.
    Qed.

    Lemma conf_at_bound t q a b :
      conf_at t = (q,(a,b)) -> a <= t /\ b <= t.
    Proof.
      elim: t => [| t IHt] in q a b *.
        by case=> _ <- <-.
      rw -Nat.add_1_r /conf_at mm2_steps_plus'.
      elim E: (mm2_steps M t (1,(0,0))) => [[q' [a' b']]|]; last by case; lia.
      have {E IHt} IH: a' <= t /\ b' <= t.
        by apply: IHt; rw /conf_at E.
      rw /=.
      case: mm2_sig_step_dec => [[y hy] | hstop]; last by case; lia.
      rw /= => E; rw {y}E in hy.
      elim: hy => [inst [hinst hatom]].
      inversion hatom; lia.
    Qed.

    Local Set Strict Implicit.

    (* Various projections out of initial_fragment, for convenience. *)
    Lemma initial_Finit f n :
      initial_fragment f n -> (f 0 .: f 0 .: f 0 .: rho) ⊨ Finit.
    Proof.
      elim=> [hz [hF0 hG]].
      have {hF0} /= := hF0 (f 0); intuition.
    Qed.

    Lemma initial_enc_instr f n y t q inst :
      initial_fragment f n -> t < n -> mm2_instr_at inst q M ->
      (y .: f (S t) .: f t .: rho) ⊨ enc_instr (q,inst).
    Proof.
      elim=> [hz [hF0 hG]] lt_tn /mm2_instr_at_in_combine /(in_map enc_instr).
      have {hG} /bigconj_sat hG := hG t y lt_tn.
      case: hG => hGinstrs hG0.
      by move/hGinstrs.
    Qed.

    Lemma initial_GstayA f n t a :
      initial_fragment f n -> t < n -> ~ iMA (f (S t)) ->
      iA (f t) (f a) -> iA (f (S t)) (f a).
    Proof.
      elim=> [hz [hF0 hG]] lt_xn.
      have {hG} /bigconj_sat hG := (hG t (f a) lt_xn).
      case: hG => hGinstrs /=; intuition.
    Qed.

    Lemma initial_GstayB f n t b :
      initial_fragment f n -> t < n -> iMA (f (S t)) ->
      iB (f t) (f b) -> iB (f (S t)) (f b).
    Proof.
      elim=> [hz [hF0 hG]] lt_xn.
      have {hG} /bigconj_sat hG := (hG t (f b) lt_xn).
      case: hG => hGinstrs /=; intuition.
    Qed.

    Lemma initial_GincA f n t a :
      initial_fragment f n -> a < n -> iMA (f t) -> iINC (f t) ->
      iH (f t) (f a) -> iA (f t) (f (S a)).
    Proof.
      elim=> [hz [hF0 hG]] lt_xn.
      have {hG} /bigconj_sat hG := (hG a (f t) lt_xn).
      case: hG => hGinstrs /=; intuition.
    Qed.

    Lemma initial_GincB f n t b :
      initial_fragment f n -> b < n -> ~ iMA (f t) -> iINC (f t) ->
      iH (f t) (f b) -> iB (f t) (f (S b)).
    Proof.
      elim=> [hz [hF0 hG]] lt_xn.
      have {hG} /bigconj_sat hG := (hG b (f t) lt_xn).
      case: hG => hGinstrs /=; intuition.
    Qed.

    Lemma initial_GdecA f n t a :
      initial_fragment f n -> a < n -> iMA (f t) -> ~ iINC (f t) ->
      iH (f t) (f a) -> iA (f t) (f (Nat.pred a)).
    Proof.
      elim=> [hz [hF0 hG]].
      case: a => [lt_0n | a lt_San].
        have {hF0} := hF0 (f t).
        by rw /=; intuition.
      have lt_an : a < n by lia.
      have {hG} /bigconj_sat hG := (hG a (f t) lt_an).
      case: hG => hGinstrs /=; intuition.
    Qed.

    Lemma initial_GdecB f n t b :
      initial_fragment f n -> b < n -> ~ iMA (f t) -> ~ iINC (f t) ->
      iH (f t) (f b) -> iB (f t) (f (Nat.pred b)).
    Proof.
      elim=> [hz [hF0 hG]].
      case: b => [lt_0n | b lt_San].
        have {hF0} := hF0 (f t).
        by rw /=; intuition.
      have lt_bn : b < n by lia.
      have {hG} /bigconj_sat hG := (hG b (f t) lt_bn).
      case: hG => hGinstrs /=; intuition.
    Qed.

    Lemma initial_GzeroA f n t a :
      initial_fragment f n -> a < n -> iA (f t) (f a) ->
      iZA (f t) <-> a = 0.
    Proof.
      elim=> [hz [hF0 hG]] lt_an ha.
      split.
        case: a => [|a] // in lt_an ha *.
        have lt_an' : a < n by lia.
        have {hG} /bigconj_sat hG := (hG a (f t) lt_an').
        case: hG => hGinstrs /=; intuition.
      move=> Ea. rw {}Ea in ha *.
      have /= [[h hZA] hZB] := hF0 (f t).
      intuition.
    Qed.

    Lemma initial_GzeroB f n t b :
      initial_fragment f n -> b < n -> iB (f t) (f b) ->
      iZB (f t) <-> b = 0.
    Proof.
      elim=> [hz [hF0 hG]] lt_bn hb.
      split.
        case: b => [|b] // in lt_bn hb *.
        have lt_bn' : b < n by lia.
        have {hG} /bigconj_sat hG := (hG b (f t) lt_bn').
        case: hG => hGinstrs /=; intuition.
      move=> Eb. rw {}Eb in hb *.
      have /= [[h hZA] hZB] := hF0 (f t).
      intuition.
    Qed.


    Lemma fragment_codes_conf f n t :
      initial_fragment f n -> t < n -> codes_conf f t (conf_at t).
    Proof.
      move=> frag.
      elim: t => [_ | t IHt le_Stn].
      - elim: (initial_Finit  frag) => [[/Qsat_iff_iQ hQ hA] hB].
        repeat split => //.
      - have lt_tn: t < n by lia.
        move: {IHt}(IHt lt_tn) => IHt.
        elim: (codes_conf_S IHt) => inst [Hinst Hatom].
        elim Hbound: (conf_at t) => [q [a b]] in Hinst Hatom IHt.
        elim: (conf_at (S t)) => [q' [a' b']] in Hatom *.
        move/conf_at_bound in Hbound.
        elim: IHt => [hQ [hA hB]].
        case: inst => [||j|j] in Hatom Hinst.
        + (* mm2_inc_a *)
          move/(initial_enc_instr (f a) frag lt_tn) in Hinst.
          have lt_an: a < n by lia.
          have hincA := (initial_GincA (S t) frag lt_an).
          have hstayB := (initial_GstayB b frag lt_tn).
          have hQt : (f a .: f (S t) .: f t .: rho) ⊨ Q q $2.
            exact/Qsat_iff_iQ.
          rw /= in Hinst.
          have {Hinst} := (Hinst hQt).
          repeat case. move/Qsat_iff_iQ => /= hQ' hINC [hMA hH].
          inversion Hatom; subst=> {Hatom}. intuition.
        + (* mm2_inc_b *)
          move/(initial_enc_instr (f b) frag lt_tn) in Hinst.
          have lt_bn: b < n by lia.
          have hincB := (initial_GincB (S t) frag lt_bn).
          have hstayA := (initial_GstayA a frag lt_tn).
          have hQt : (f b .: f (S t) .: f t .: rho) ⊨ Q q $2.
            exact/Qsat_iff_iQ.
          rw /= in Hinst.
          have {Hinst} := (Hinst hQt).
          repeat case. move/Qsat_iff_iQ => /= hQ' hINC [hMB hH].
          inversion Hatom; subst=> {Hatom}. intuition.
        + (* mm2_dec_a *)
          move/(initial_enc_instr (f a) frag lt_tn) in Hinst.
          have {Hbound} lt_an: a < n by lia.
          have hQt : (f a .: f (S t) .: f t .: rho) ⊨ Q q $2.
            exact/Qsat_iff_iQ.
          rw /= in Hinst.
          have {Hinst hQt} [[Hinst hnza] hza] := (Hinst hQt).
          suff {Hinst}: iQ q' (f (S t)).
            have hdecA := (initial_GdecA (S t) frag lt_an).
            have hstayB := (initial_GstayB b frag lt_tn).
            by inversion Hatom; subst=> {Hatom}; intuition.
          move/(initial_GzeroA t frag lt_an) in hA.
          case: a => [| a] in hA hza hnza Hatom lt_an *.
            have /hza/Qsat_iff_iQ : iZA (f t) by apply/hA.
            inversion Hatom; subst=> {Hatom}; intuition.
          have /hnza/Qsat_iff_iQ : ~ iZA (f t) by apply/hA.
          inversion Hatom; subst=> {Hatom}; intuition.
        + (* mm2_dec_b *)
          move/(initial_enc_instr (f b) frag lt_tn) in Hinst.
          have {Hbound} lt_bn: b < n by lia.
          have hQt : (f b .: f (S t) .: f t .: rho) ⊨ Q q $2.
            exact/Qsat_iff_iQ.
          rw /= in Hinst.
          have {Hinst hQt} [[Hinst hnzb] hzb] := (Hinst hQt).
          suff {Hinst}: iQ q' (f (S t)).
            have hdecB := (initial_GdecB (S t) frag lt_bn).
            have hstayA := (initial_GstayA a frag lt_tn).
            by inversion Hatom; subst=> {Hatom}; intuition.
          move/(initial_GzeroB t frag lt_bn) in hB.
          case: b => [| b] in hB hzb hnzb Hatom lt_bn *.
            have /hzb/Qsat_iff_iQ : iZB (f t) by apply/hB.
            inversion Hatom; subst=> {Hatom}; intuition.
          have /hnzb/Qsat_iff_iQ : ~ iZB (f t) by apply/hB.
          inversion Hatom; subst=> {Hatom}; intuition.
    Qed.

    Lemma satis_nonhalt : ~ MM2_ZERO_HALTING M.
    Proof using Hsat.
      move=> /= [s [/mm2_reaches_steps hsteps /mm2_stop_index_iff hstop]].
      case: hsteps => [k hsteps].
      have [f frag] := has_fragment (S k).
      have lt_kSk : k < S k by lia.
      have := fragment_codes_conf frag lt_kSk.
      rw /conf_at {}hsteps /= => hconf.
      case: s => [q [a b]] in hstop hconf.
      have: iQ q (f k) by cbn in hconf; intuition.
      rw /iQ.
      elim: hstop => /=; lia.
    Qed.
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
