import Proof.Wire_3_5.UnionMachine.FrontAtomRound

/-! # C6 front, U1b: the atom loop (P3:3670)

"It rejects malformed descriptions, oversized atoms" (P3:3670): the codec decodes every grid atom
(`decodeAtom m q`). The loop runs one round (`FrontAtomRound`) per validated entry of the guess rest `r`, while the
count `J` is positive and no atom was rejected, and ends with `BAD = 0` exactly when every atom passes the Theorem 2.5 repository's decoder.

Main statements: **`round_pass`**, **`round_fail`** (one round), **`atoms_loop`** (the loop). Paper quantity: the
rejection of malformed guessed atoms. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

namespace NearCubicWires.WireExponent3_5.UnionMachine.FrontAtomLoop
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.WireExponent3_5.FinalPass NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.UnionMachine.FrontAtomLayout NearCubicWires.WireExponent3_5.UnionMachine.FrontLoopKit
open NearCubicWires.WireExponent3_5.UnionMachine.FrontAtomRound

/-- **One round** of mode `m`: the erasers, the copy, the decoder, the verdict. -/
noncomputable def roundM (m : Mode) :=
  Composition.machine eraseH (Composition.machine eraseP (Composition.machine copyM
    (Composition.machine (decM m) tailM)))

/-- The round's step bound, with bounds `Kc` on the copy and `Kd` on the decoder. -/
def roundCost (P H Kc Kd : ℕ) : ℕ := (2 * H + 4) + 1 + ((2 * P + 4) + 1 + (Kc + 1 + (Kd + 1 + 12)))

section Round
variable (r : List Bool) (P H q W L cap : ℕ)

theorem heads_zero (out : List Bool) (i : Fin 1703) (h1 : i.val ≠ 1688) (h2 : i.val ≠ 1674) :
    CloseoutRowsCircuitColdEntry.heads out i = 0 := by
  simp only [CloseoutRowsCircuitColdEntry.heads, CloseoutRowsCircuit.heads, Fin.ext_iff]
  split_ifs <;> simp_all

theorem heads_priv (out : List Bool) (i : Fin 1703) (hi : isPub i = false) :
    CloseoutRowsCircuitColdEntry.heads out i = 0 := by
  simp only [isPub, Bool.or_eq_false_iff, beq_eq_false_iff_ne, ne_eq] at hi
  simp only [CloseoutRowsCircuitColdEntry.heads, CloseoutRowsCircuit.heads, Fin.ext_iff]
  split_ifs <;> simp_all

/-- The five stages of a round, chained, with the decoder's receipt named. -/
theorem round_steps (m : Mode) (one out : List Bool) (pv : Fin 1703 → List Bool) (J : ℕ) (cond : Bool)
    (P0 : ℕ) (b x : Bool) (p rest : List Bool)
    (hr : r.drop P0 = FrontEntriesRef.gridWord b x ++ (List.replicate p.length true ++ false :: p) ++ rest)
    (hk : 1 ≤ p.length) (hP : 2 * p.length + 1 ≤ P) (hC : CloseoutRowsCircuitCapacity.capacity p.length ≤ P)
    (hH : P + 1 ≤ H) (hcap : 2 * (P0 + 2 * p.length + 5) + 2 ≤ cap) (hJ : J ≤ cap) (hcap1 : 1 ≤ cap)
    (hone : one.length ≤ P) (hpv : ∀ i, isPub i = false → (pv i).length ≤ H)
    (Kc Kd : ℕ) (hKc : 70 * (p.length + 2) ≤ Kc) (hKd : CloseoutRowsCircuitWholeBudget.budget P p.length ≤ Kd) :
    ∃ r0 : ExecutionReceipt 1703 (FrontAtomDecoder.decS m),
      Step (roundM m) (roundCost P H Kc Kd)
        (bankH (CloseoutRowsCircuitColdEntry.heads out) (2 * P0) J 0)
        (bankA r P H q W L cap one out pv (2 * P0) J 0 cond)
        (bankGH r0.final.heads (smH (2 * (P0 + 2 * p.length + 5)) (J - 1) (FrontAtomTail.badNext (r0.final.tapes 1700) 0)))
        (bankG r0.final.tapes (smA r P H cap (2 * (P0 + 2 * p.length + 5)) (J - 1)
          (FrontAtomTail.badNext (r0.final.tapes 1700) 0)
          (FrontAtomTail.condOf (J - 1) (FrontAtomTail.badNext (r0.final.tapes 1700) 0)))) ∧
      r0.final.heads 1700 = 0 ∧ (readTapeBit (r0.final.tapes 1700) 0 = true ↔ FrontAtomDecoder.passedM m q W L p) ∧
      (FrontAtomDecoder.passedM m q W L p →
        r0.final.heads = CloseoutRowsCircuitColdEntry.heads (out ++ FrontAtomDecoder.nativeM m q p) ∧
        r0.final.tapes 1688 = out ++ FrontAtomDecoder.nativeM m q p ∧ r0.final.tapes 1674 = UnaryTemplate.tape q ∧
        r0.final.tapes 1694 = List.replicate P true ∧ r0.final.tapes 1698 = List.replicate W true ∧
        r0.final.tapes 1699 = List.replicate L true ∧ r0.final.tapes 1 = ZeroPadding.pad P (frame p) ∧
        ∀ i, i ≠ 1 → i ≠ 1674 → i ≠ 1694 → i ≠ 1698 → i ≠ 1699 → i ≠ 1688 → (r0.final.tapes i).length ≤ H) := by
  have hdh : ∀ i, isPub i = false → CloseoutRowsCircuitColdEntry.heads out i = 0 := heads_priv out
  have h1 : CloseoutRowsCircuitColdEntry.heads out 1 = 0 := heads_zero out 1 (by decide) (by decide)
  have h1694 : CloseoutRowsCircuitColdEntry.heads out 1694 = 0 := heads_zero out 1694 (by decide) (by decide)
  have s1 := eraseH_step r P H q W L cap one out pv (CloseoutRowsCircuitColdEntry.heads out) (2 * P0) J 0 cond hpv hdh
  have s2 := eraseP_step r P H q W L cap one out (fun _ => List.replicate H false)
    (CloseoutRowsCircuitColdEntry.heads out) (2 * P0) J 0 cond hone h1 h1694
  obtain ⟨nc, hnc, s3⟩ := copy_step r P H q W L cap out (fun _ => List.replicate H false)
    (CloseoutRowsCircuitColdEntry.heads out) J 0 cond P0 b x p rest hr hk hP hcap h1
  obtain ⟨r0, s4, hfh, hflag, hgood⟩ := dec_stepAt r P H q W L cap m p out (2 * (P0 + 2 * p.length + 5)) J 0 cond hC hH
  have s5 := tail_stepAt r P H cap r0.final.tapes r0.final.heads (2 * (P0 + 2 * p.length + 5)) J 0 cond hfh
    (by omega) hJ hcap1
  refine ⟨r0, ?_, hfh, hflag, hgood⟩
  have s4' := s4
  unfold bankH bankA at s4'
  have s45 := Step.seq s4 s5
  exact (Step.seq s1 (Step.seq s2 (Step.seq s3 s45))).enlarge (by unfold roundCost; omega)

theorem bankH_eqG (dh : Fin 1703 → ℕ) (pg J bad : ℕ) : bankH dh pg J bad = bankGH dh (smH pg J bad) := rfl
theorem bankA_eqG (one out : List Bool) (pv : Fin 1703 → List Bool) (pg J bad : ℕ) (cond : Bool) :
    bankA r P H q W L cap one out pv pg J bad cond = bankG (decA P q W L one out pv) (smA r P H cap pg J bad cond) :=
  rfl

/-- **A passing round**: the next round's start, with the native record appended and new private scratch. -/
theorem round_pass (m : Mode) (one out : List Bool) (pv : Fin 1703 → List Bool) (J : ℕ) (cond : Bool)
    (P0 : ℕ) (b x : Bool) (p rest : List Bool)
    (hr : r.drop P0 = FrontEntriesRef.gridWord b x ++ (List.replicate p.length true ++ false :: p) ++ rest)
    (hk : 1 ≤ p.length) (hP : 2 * p.length + 1 ≤ P) (hC : CloseoutRowsCircuitCapacity.capacity p.length ≤ P)
    (hH : P + 1 ≤ H) (hcap : 2 * (P0 + 2 * p.length + 5) + 2 ≤ cap) (hJ : J ≤ cap) (hcap1 : 1 ≤ cap)
    (hone : one.length ≤ P) (hpv : ∀ i, isPub i = false → (pv i).length ≤ H)
    (Kc Kd : ℕ) (hKc : 70 * (p.length + 2) ≤ Kc) (hKd : CloseoutRowsCircuitWholeBudget.budget P p.length ≤ Kd)
    (hpass : FrontAtomDecoder.passedM m q W L p) :
    ∃ pv' : Fin 1703 → List Bool, (∀ i, isPub i = false → (pv' i).length ≤ H) ∧
      Step (roundM m) (roundCost P H Kc Kd)
        (bankH (CloseoutRowsCircuitColdEntry.heads out) (2 * P0) J 0)
        (bankA r P H q W L cap one out pv (2 * P0) J 0 cond)
        (bankH (CloseoutRowsCircuitColdEntry.heads (out ++ FrontAtomDecoder.nativeM m q p))
          (2 * (P0 + 2 * p.length + 5)) (J - 1) 0)
        (bankA r P H q W L cap (ZeroPadding.pad P (frame p)) (out ++ FrontAtomDecoder.nativeM m q p) pv'
          (2 * (P0 + 2 * p.length + 5)) (J - 1) 0 (FrontAtomTail.condOf (J - 1) 0)) := by
  obtain ⟨r0, hs, hfh, hflag, hgood⟩ := round_steps r P H q W L cap m one out pv J cond P0 b x p rest hr hk hP hC hH
    hcap hJ hcap1 hone hpv Kc Kd hKc hKd
  obtain ⟨gh, g1688, g1674, g1694, g1698, g1699, g1, glen⟩ := hgood hpass
  have hb : FrontAtomTail.badNext (r0.final.tapes 1700) 0 = 0 := by
    simp [FrontAtomTail.badNext, hflag.2 hpass]
  rw [hb] at hs
  refine ⟨r0.final.tapes, ?_, ?_⟩
  · intro i hi
    simp only [isPub, Bool.or_eq_false_iff, beq_eq_false_iff_ne, ne_eq] at hi
    refine glen i ?_ ?_ ?_ ?_ ?_ ?_ <;> intro h <;> simp_all [Fin.ext_iff]
  · refine Step.congr_out hs ?_ ?_
    · rw [bankH_eqG, gh]
    · rw [bankA_eqG]
      congr 1
      funext i
      unfold decA
      split_ifs with e1 e2 e3 e4 e5 e6
      · rw [show i = 1 from Fin.ext e1, g1]
      · rw [show i = 1674 from Fin.ext e2, g1674]
      · rw [show i = 1688 from Fin.ext e3, g1688]
      · rw [show i = 1694 from Fin.ext e4, g1694]
      · rw [show i = 1698 from Fin.ext e5, g1698]
      · rw [show i = 1699 from Fin.ext e6, g1699]
      · rfl

/-- **A failing round**: the verdict `BAD = 1`, the condition clear. -/
theorem round_fail (m : Mode) (one out : List Bool) (pv : Fin 1703 → List Bool) (J : ℕ) (cond : Bool)
    (P0 : ℕ) (b x : Bool) (p rest : List Bool)
    (hr : r.drop P0 = FrontEntriesRef.gridWord b x ++ (List.replicate p.length true ++ false :: p) ++ rest)
    (hk : 1 ≤ p.length) (hP : 2 * p.length + 1 ≤ P) (hC : CloseoutRowsCircuitCapacity.capacity p.length ≤ P)
    (hH : P + 1 ≤ H) (hcap : 2 * (P0 + 2 * p.length + 5) + 2 ≤ cap) (hJ : J ≤ cap) (hcap1 : 1 ≤ cap)
    (hone : one.length ≤ P) (hpv : ∀ i, isPub i = false → (pv i).length ≤ H)
    (Kc Kd : ℕ) (hKc : 70 * (p.length + 2) ≤ Kc) (hKd : CloseoutRowsCircuitWholeBudget.budget P p.length ≤ Kd)
    (hfail : ¬ FrontAtomDecoder.passedM m q W L p) :
    ∃ H' A', Step (roundM m) (roundCost P H Kc Kd)
        (bankH (CloseoutRowsCircuitColdEntry.heads out) (2 * P0) J 0)
        (bankA r P H q W L cap one out pv (2 * P0) J 0 cond) H' A' ∧
      A' (sm 5) = [false] ∧ H' (sm 5) = 0 ∧ A' (sm 7) = regTape cap 1 ∧ H' (sm 7) = 1 := by
  obtain ⟨r0, hs, hfh, hflag, -⟩ := round_steps r P H q W L cap m one out pv J cond P0 b x p rest hr hk hP hC hH
    hcap hJ hcap1 hone hpv Kc Kd hKc hKd
  have hb : FrontAtomTail.badNext (r0.final.tapes 1700) 0 = 1 := by
    have : readTapeBit (r0.final.tapes 1700) 0 = false := by
      cases h : readTapeBit (r0.final.tapes 1700) 0
      · rfl
      · exact absurd (hflag.1 h) hfail
    simp [FrontAtomTail.badNext, this]
  rw [hb] at hs
  refine ⟨_, _, hs, ?_, ?_, ?_, ?_⟩
  · rw [bankG_sm]; simp [smA, FrontAtomTail.condOf]
  · rw [bankGH_sm]; simp [smH]
  · rw [bankG_sm]; simp [smA]
  · rw [bankGH_sm]; simp [smH]

/-- The loop's round count: up to and including the first rejected atom, or all `E`. -/
noncomputable def roundsOf (m : Mode) (E : ℕ) (pay : ℕ → List Bool) : ℕ := by
  classical
  exact if h : ∃ j, j < E ∧ ¬ FrontAtomDecoder.passedM m q W L (pay j) then Nat.find h + 1 else E

/-- The verdict: `0` when every atom passes. -/
noncomputable def verdictOf (m : Mode) (E : ℕ) (pay : ℕ → List Bool) : ℕ := by
  classical
  exact if ∀ j, j < E → FrontAtomDecoder.passedM m q W L (pay j) then 0 else 1

/-- **The atom loop**: from the first entry, the rounds run until the first rejected atom (or all `E`); the verdict
register `BAD` then holds `0` exactly when every atom passes the decoder. -/
theorem atoms_loop (m : Mode) (E : ℕ) (hE : 1 ≤ E) (pos : ℕ → ℕ) (pay : ℕ → List Bool)
    (hent : ∀ j, j < E → ∃ b x rest, r.drop (pos j) =
      FrontEntriesRef.gridWord b x ++ (List.replicate (pay j).length true ++ false :: pay j) ++ rest)
    (hk : ∀ j, j < E → 1 ≤ (pay j).length) (hpos : ∀ j, j < E → pos (j + 1) = pos j + 2 * (pay j).length + 5)
    (hP : ∀ j, j < E → 2 * (pay j).length + 1 ≤ P)
    (hC : ∀ j, j < E → CloseoutRowsCircuitCapacity.capacity (pay j).length ≤ P) (hH : P + 1 ≤ H)
    (hcap : ∀ j, j < E → 2 * (pos j + 2 * (pay j).length + 5) + 2 ≤ cap) (hEcap : E ≤ cap) (hcap1 : 1 ≤ cap)
    (Kc Kd : ℕ) (hKc : ∀ j, j < E → 70 * ((pay j).length + 2) ≤ Kc)
    (hKd : ∀ j, j < E → CloseoutRowsCircuitWholeBudget.budget P (pay j).length ≤ Kd)
    (one0 : List Bool) (pv0 : Fin 1703 → List Bool) (hone0 : one0.length ≤ P)
    (hpv0 : ∀ i, isPub i = false → (pv0 i).length ≤ H) :
    ∃ H' A', Step (StreamController.machine (roundM m) (sm 5))
        (roundsOf q W L m E pay * (roundCost P H Kc Kd + 2) + 1)
        (bankH (CloseoutRowsCircuitColdEntry.heads []) (2 * pos 0) E 0)
        (bankA r P H q W L cap one0 [] pv0 (2 * pos 0) E 0 true) H' A' ∧
      A' (sm 7) = regTape cap (verdictOf q W L m E pay) ∧ H' (sm 7) = verdictOf q W L m E pay := by
  classical
  set n := roundsOf q W L m E pay with hn
  set v := verdictOf q W L m E pay with hv
  -- the round count's facts
  have n_le : n ≤ E := by
    simp only [hn, roundsOf]; split_ifs with h
    · have := (Nat.find_spec h).1; omega
    · exact le_rfl
  have n_pass : ∀ j, j + 1 < n → FrontAtomDecoder.passedM m q W L (pay j) := by
    intro j hj
    simp only [hn, roundsOf] at hj; split_ifs at hj with h
    · by_contra hf; have := Nat.find_min' h ⟨by have := (Nat.find_spec h).1; omega, hf⟩; omega
    · by_contra hf; exact h ⟨j, by omega, hf⟩
  have n_fail : ∀ j, j < n → ¬ FrontAtomDecoder.passedM m q W L (pay j) → j + 1 = n ∧ v = 1 := by
    intro j hj hf
    have hjE : j < E := by omega
    have hex : ∃ j, j < E ∧ ¬ FrontAtomDecoder.passedM m q W L (pay j) := ⟨j, hjE, hf⟩
    refine ⟨?_, ?_⟩
    · simp only [hn, roundsOf, dif_pos hex] at hj ⊢
      have := Nat.find_min' hex ⟨hjE, hf⟩; omega
    · simp only [hv, verdictOf]; rw [if_neg]; intro hall; exact hf (hall j (by omega))
  have n_last : ∀ j, j + 1 = n → FrontAtomDecoder.passedM m q W L (pay j) → n = E ∧ v = 0 := by
    intro j hj hp
    by_cases hex : ∃ j, j < E ∧ ¬ FrontAtomDecoder.passedM m q W L (pay j)
    · exfalso
      simp only [hn, roundsOf, dif_pos hex] at hj
      have hjf : j = Nat.find hex := by omega
      exact (Nat.find_spec hex).2 (hjf ▸ hp)
    · refine ⟨by simp only [hn, roundsOf, dif_neg hex], ?_⟩
      simp only [hv, verdictOf]; rw [if_pos]; intro j hj; by_contra hf; exact hex ⟨j, hj, hf⟩
  -- the invariant
  let Start : ℕ → (Fin AT → ℕ) → (Fin AT → List Bool) → Prop := fun j Hb Ab =>
    ∃ (one out : List Bool) (pv : Fin 1703 → List Bool), one.length ≤ P ∧
      (∀ i, isPub i = false → (pv i).length ≤ H) ∧
      Hb = bankH (CloseoutRowsCircuitColdEntry.heads out) (2 * pos j) (E - j) 0 ∧
      Ab = bankA r P H q W L cap one out pv (2 * pos j) (E - j) 0 true
  let Fin' : (Fin AT → ℕ) → (Fin AT → List Bool) → Prop := fun Hb Ab =>
    Ab (sm 5) = [false] ∧ Hb (sm 5) = 0 ∧ Ab (sm 7) = regTape cap v ∧ Hb (sm 7) = v
  let Inv : ℕ → (Fin AT → ℕ) → (Fin AT → List Bool) → Prop := fun j Hb Ab =>
    if j < n then Start j Hb Ab else Fin' Hb Ab
  have hn1 : 1 ≤ n := by
    simp only [hn, roundsOf]; split_ifs <;> omega
  obtain ⟨Hn, An, hstep, hfin⟩ := whileInv (roundM m) (sm 5) n (roundCost P H Kc Kd) Inv
    (by
      intro j hj Hb Ab hI
      simp only [Inv, if_pos hj] at hI
      obtain ⟨one, out, pv, hone, hpv, rfl, rfl⟩ := hI
      have hjE : j < E := by omega
      obtain ⟨b, x, rest, hr⟩ := hent j hjE
      by_cases hp : FrontAtomDecoder.passedM m q W L (pay j)
      · obtain ⟨pv', hpv', hs⟩ := round_pass r P H q W L cap m one out pv (E - j) true (pos j) b x (pay j) rest hr
          (hk j hjE) (hP j hjE) (hC j hjE) hH (hcap j hjE) (by omega) hcap1 hone hpv Kc Kd (hKc j hjE) (hKd j hjE) hp
        refine ⟨_, _, hs, ?_⟩
        by_cases hj1 : j + 1 < n
        · simp only [Inv, if_pos hj1]
          refine ⟨ZeroPadding.pad P (frame (pay j)), out ++ FrontAtomDecoder.nativeM m q (pay j), pv', ?_, hpv', ?_, ?_⟩
          · simp; have := hP j hjE; omega
          · rw [hpos j hjE, show E - j - 1 = E - (j + 1) by omega]
          · rw [hpos j hjE, show E - j - 1 = E - (j + 1) by omega]
            have hc : FrontAtomTail.condOf (E - (j + 1)) 0 = true := by
              simp [FrontAtomTail.condOf]; omega
            rw [hc]
        · have hj1' : j + 1 = n := by omega
          obtain ⟨hnE, hv0⟩ := n_last j hj1' hp
          simp only [Inv, if_neg hj1]
          refine ⟨?_, ?_, ?_, ?_⟩
          · rw [bankA_sm]; simp [smA, FrontAtomTail.condOf]; omega
          · rw [bankH_sm]; simp [smH]
          · rw [bankA_sm, hv0]; simp [smA]
          · rw [bankH_sm, hv0]; simp [smH]
      · obtain ⟨H', A', hs, h5, h5h, h7, h7h⟩ := round_fail r P H q W L cap m one out pv (E - j) true (pos j) b x
          (pay j) rest hr (hk j hjE) (hP j hjE) (hC j hjE) hH (hcap j hjE) (by omega) hcap1 hone hpv Kc Kd
          (hKc j hjE) (hKd j hjE) hp
        obtain ⟨hj1, hv1⟩ := n_fail j hj hp
        refine ⟨H', A', hs, ?_⟩
        simp only [Inv, show ¬ (j + 1 < n) by omega, if_false]
        exact ⟨h5, h5h, by rw [h7, hv1], by rw [h7h, hv1]⟩)
    (by
      intro j hj Hb Ab hI
      simp only [Inv, if_pos hj] at hI
      obtain ⟨one, out, pv, -, -, rfl, rfl⟩ := hI
      rw [bankA_sm, bankH_sm]; rfl)
    (by
      intro Hb Ab hI
      simp only [Inv, lt_irrefl, if_false] at hI
      rw [hI.1, hI.2.1]; rfl)
    _ _ (by
      simp only [Inv, if_pos (show 0 < n by omega)]
      refine ⟨one0, [], pv0, hone0, hpv0, ?_, ?_⟩
      · rfl
      · rfl)
  simp only [Inv, lt_irrefl, if_false] at hfin
  exact ⟨Hn, An, hstep, hfin.2.2.1, hfin.2.2.2⟩

end Round

end NearCubicWires.WireExponent3_5.UnionMachine.FrontAtomLoop
