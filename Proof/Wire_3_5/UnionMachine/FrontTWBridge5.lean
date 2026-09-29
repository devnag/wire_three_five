import Proof.Wire_3_5.UnionMachine.FrontTWBridge4

/-! # C6 front, U5: the table writer writes `tableAll` and decides `schedule.all callOk` (P3:3685-3691)

**`accB_V_eq`**, **`accB_Q_eq`**, **`accB_Mu_eq`**: each pass's admissibility is its term list's; **`ok_eq`**: the
three together are `D.schedule.all okR` (the schedule is a permutation of the machine's lists). **`tblOf_tableAll`**:
the call table's word is the three lists' entries and the closing `0`. Together with `FrontTW.twT` and
`accW_V_eq/Q/Mu`, the table writer's output is `tblOf (tableAll D.s myV myQ myMu …)` and its `OK` is
`schedule.all okR`.

Paper quantity of the main statements: the call table of `(tr:tests)` and the calls' admissibility. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unnecessarySimpa false

namespace NearCubicWires.WireExponent3_5.UnionMachine.FrontTW
open NearCubicWires NearCubicWires.SourceInterfaces NearCubicWires.WireExponent3_5.Transfer
open NearCubicWires.WireExponent3_5.UnionMachine.FrontTableRef
open NearCubicWires.WireExponent3_5.UnionMachine.Bridge (entryOf tableOfTerms)

section Passes
variable (D : UnionCheckData) (d : TWData) (hr : TWRel D d) (fD : D.mode.Circuit D.q → Bool)
  (fE : Stars.Carrier D.q → Bool) (hf : TWFlags D d fD fE) (v0 : Fin NR → ℕ) (hC : decide (v0 rCDF ≠ 0) = fD D.const)
  (hSS : v0 rSS = D.s) (okR : PrimRequest → Bool)

include hr hf hC hSS in
/-- **The validity pass's admissibility is `myV`'s.** -/
theorem accB_V_eq (Λ : ℕ) (hmr : MagRegs D Λ v0) (hSYS : v0 rSYS = D.pcpp.systematicBits)
    (hok : ∀ (pos : Fin (2 ^ D.pcpp.clauseBits) × Fin 2) (pat : Fin 4 → FK) (t : Fin 4 → D.AtomIx),
      (∀ k, t k ∈ cand D (posVar D.pcpp pos.1 pos.2) (posVar D.pcpp pos.1 pos.2) (pat k)) →
      okR (D.vCall pos t) = okT D fD fE (posVar D.pcpp pos.1 pos.2) (posVar D.pcpp pos.1 pos.2) false t) :
    accB (litsD D) (bVof d v0) (2 ^ D.pcpp.clauseBits) = (myV D).all fun p => okR p.2 := by
  unfold litsD
  rw [accB_pairs]
  unfold myV posList
  rw [List.all_flatMap, List.all_flatMap]
  refine all_congr_mem _ _ _ fun i _ => ?_
  simp only [List.all_cons, List.all_nil, Bool.and_true, bVof, List.all_flatMap]
  set w1 := Function.update (Function.update v0 rL1 (RepairRepresentation.literalIndex (D.pcpp.clauses i).right)) rLIT
    (RepairRepresentation.literalIndex (D.pcpp.clauses i).left) with hw1
  set w2 := Function.update v0 rLIT (RepairRepresentation.literalIndex (D.pcpp.clauses i).right) with hw2
  obtain ⟨a1, a2, a3, a4, -⟩ := pos_facts D Λ v0 w1 hmr hSS hSYS
    (fun r h1 h2 => by simp only [w1]; rw [Function.update_of_ne h2, Function.update_of_ne h1]) (posVar D.pcpp i 0)
    (by simp [w1, litIdx_div])
  obtain ⟨b1, b2, b3, b4, -⟩ := pos_facts D Λ v0 w2 hmr hSS hSYS
    (fun r _ h2 => by simp only [w2]; rw [Function.update_of_ne h2]) (posVar D.pcpp i 1) (by simp [w2, litIdx_div])
  have c1 : decide (posRegs w1 rCDF ≠ 0) = fD D.const := by
    rw [posRegs_other _ _ (by decide) (by decide) (by decide) (by decide) (by decide)]
    have e : w1 rCDF = v0 rCDF := by simp only [w1]; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide)]
    simp only [e]; exact hC
  have c2 : decide (posRegs w2 rCDF ≠ 0) = fD D.const := by
    rw [posRegs_other _ _ (by decide) (by decide) (by decide) (by decide) (by decide)]
    have e : w2 rCDF = v0 rCDF := by simp only [w2]; rw [Function.update_of_ne (by decide)]
    simp only [e]; exact hC
  rw [okV_eq D d hr fD fE hf _ c1 (i, 0) a1 a2 a3 a4 okR (hok (i, 0)),
    okV_eq D d hr fD fE hf _ c2 (i, 1) b1 b2 b3 b4 okR (hok (i, 1))]

include hr hf hC hSS in
/-- **The second-moment pass's admissibility is `myQ`'s.** -/
theorem accB_Q_eq (Λ : ℕ) (hmr : MagRegs D Λ v0) (hSYS : v0 rSYS = D.pcpp.systematicBits)
    (hok : ∀ (pos : Fin (2 ^ D.pcpp.clauseBits) × Fin 2) (pat : Fin 4 → FK) (t : Fin 4 → D.AtomIx),
      (∀ k, t k ∈ cand D (posVar D.pcpp pos.1 pos.2) (posVar D.pcpp pos.1 pos.2) (pat k)) →
      okR (D.vCall pos t) = okT D fD fE (posVar D.pcpp pos.1 pos.2) (posVar D.pcpp pos.1 pos.2) false t) :
    accB (litsD D) (bQof d v0) (2 ^ D.pcpp.clauseBits) = (myQ D).all fun p => okR p.2 := by
  unfold litsD
  rw [accB_pairs]
  unfold myQ posList
  rw [List.all_flatMap, List.all_flatMap]
  refine all_congr_mem _ _ _ fun i _ => ?_
  simp only [List.all_cons, List.all_nil, Bool.and_true, bQof, List.all_flatMap]
  set w1 := Function.update (Function.update v0 rL1 (RepairRepresentation.literalIndex (D.pcpp.clauses i).right)) rLIT
    (RepairRepresentation.literalIndex (D.pcpp.clauses i).left) with hw1
  set w2 := Function.update v0 rLIT (RepairRepresentation.literalIndex (D.pcpp.clauses i).right) with hw2
  obtain ⟨a1, a2, a3, -, -⟩ := pos_facts D Λ v0 w1 hmr hSS hSYS
    (fun r h1 h2 => by simp only [w1]; rw [Function.update_of_ne h2, Function.update_of_ne h1]) (posVar D.pcpp i 0)
    (by simp [w1, litIdx_div])
  obtain ⟨b1, b2, b3, -, -⟩ := pos_facts D Λ v0 w2 hmr hSS hSYS
    (fun r _ h2 => by simp only [w2]; rw [Function.update_of_ne h2]) (posVar D.pcpp i 1) (by simp [w2, litIdx_div])
  have c1 : decide (posRegs w1 rCDF ≠ 0) = fD D.const := by
    rw [posRegs_other _ _ (by decide) (by decide) (by decide) (by decide) (by decide)]
    have e : w1 rCDF = v0 rCDF := by simp only [w1]; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide)]
    simp only [e]; exact hC
  have c2 : decide (posRegs w2 rCDF ≠ 0) = fD D.const := by
    rw [posRegs_other _ _ (by decide) (by decide) (by decide) (by decide) (by decide)]
    have e : w2 rCDF = v0 rCDF := by simp only [w2]; rw [Function.update_of_ne (by decide)]
    simp only [e]; exact hC
  rw [okQ_eq D d hr fD fE hf _ c1 (i, 0) a1 a2 a3 okR (hok (i, 0)),
    okQ_eq D d hr fD fE hf _ c2 (i, 1) b1 b2 b3 okR (hok (i, 1))]

include hr hf hC hSS in
/-- **The clause pass's admissibility is `myMu`'s.** -/
theorem accB_Mu_eq
    (hok : ∀ (i : Fin (2 ^ D.pcpp.clauseBits)) (pat : Fin 4 → FK) (t : Fin 4 → D.AtomIx),
      (∀ k, t k ∈ cand D (posVar D.pcpp i 0) (posVar D.pcpp i 1) (pat k)) →
      okR (D.muCall i t) = okT D fD fE (posVar D.pcpp i 0) (posVar D.pcpp i 1) true t) :
    accB (litsD D) (bMof d v0) (2 ^ D.pcpp.clauseBits) = (myMu D).all fun p => okR p.2 := by
  unfold litsD
  rw [accB_pairs]
  unfold myMu
  rw [List.all_flatMap]
  refine all_congr_mem _ _ _ fun i _ => ?_
  simp only [bMof]
  set a := RepairRepresentation.literalIndex (D.pcpp.clauses i).left with ha
  set b := RepairRepresentation.literalIndex (D.pcpp.clauses i).right with hb
  have hmo : ∀ r, r ≠ rX → r ≠ rN0 → r ≠ rXS → r ≠ rY → r ≠ rN1 → r ≠ rYS → muRegs v0 a b r = v0 r :=
    fun r h1 h2 h3 h4 h5 h6 => muRegs_other v0 a b r h1 h2 h3 h4 h5 h6
  have hSS' : muRegs v0 a b rSS = D.s := by
    rw [hmo _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hSS]
  have hC' : decide (muRegs v0 a b rCDF ≠ 0) = fD D.const := by
    rw [hmo _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hC
  rw [List.all_flatMap]
  exact okMu_eq D d hr fD fE hf _ hC' i (by simp +decide [muRegs, Function.update_apply, ha, litIdx_div])
    (by simp +decide [muRegs, Function.update_apply, hb, litIdx_div])
    (by simp +decide [muRegs, Function.update_apply, ha, litIdx_div, hSS])
    (by simp +decide [muRegs, Function.update_apply, hb, litIdx_div, hSS]) hSS'
    (by simp +decide [muRegs, Function.update_apply, ha, litIdx_mod])
    (by simp +decide [muRegs, Function.update_apply, hb, litIdx_mod]) okR (hok i)

end Passes

/-! ## The three passes together -/

theorem perm_all {α : Type} {l l' : List α} (h : l.Perm l') (p : α → Bool) : l.all p = l'.all p := by
  rw [Bool.eq_iff_iff]
  simp only [List.all_eq_true]
  exact ⟨fun H x hx => H x (h.mem_iff.2 hx), fun H x hx => H x (h.mem_iff.1 hx)⟩

/-- **The passes' admissibility is the schedule's**: `schedule.all okR`. -/
theorem ok_eq (D : UnionCheckData) (hm : D.mass ≠ 0) (hs : D.s ≠ 0) (okR : PrimRequest → Bool) :
    ((myV D).all (fun p => okR p.2) && (myQ D).all (fun p => okR p.2) && (myMu D).all (fun p => okR p.2)) =
      D.schedule.all okR := by
  unfold UnionCheckData.schedule
  rw [List.all_map, List.all_append, List.all_append, perm_all (termsV_perm D hm hs), perm_all (termsQ_perm D hm hs),
    perm_all (termsMu_perm D hm hs)]
  rfl

section Table
open NearCubicWires.WireExponent3_5.Cost NearCubicWires.WireExponent3_5.UnionMachine.DecisionBridge
variable {kclk : ℕ} {E : Envelope} {B : TimeBudget kclk E} {I : PrimitiveInputs B}

theorem tableOfTerms_e (k : Fin 3) (s : ℕ) (T : List (ℚ × PrimRequest)) (h : ∀ t ∈ T, I.Call t.2) :
    (tableOfTerms k s T h).map Sched.TEntry.e = T.map (entryOf k s) := by
  unfold tableOfTerms
  rw [List.map_pmap, List.pmap_eq_map]

/-- **The call table's word**: the three term lists' entries, then the closing `0`. -/
theorem tblOf_tableAll (s : ℕ) (LV LQ LM : List (ℚ × PrimRequest)) (hV : ∀ t ∈ LV, I.Call t.2)
    (hQ : ∀ t ∈ LQ, I.Call t.2) (hM : ∀ t ∈ LM, I.Call t.2) :
    Sched.tblOf (tableAll s LV LQ LM hV hQ hM) =
      LV.flatMap (fun t => Entry.entryWord (entryOf 0 s t)) ++ LQ.flatMap (fun t => Entry.entryWord (entryOf 1 s t)) ++
        LM.flatMap (fun t => Entry.entryWord (entryOf 2 s t)) ++ [false] := by
  unfold Sched.tblOf Entry.tableWord tableAll
  rw [List.map_append, List.map_append, tableOfTerms_e, tableOfTerms_e, tableOfTerms_e]
  simp [List.flatMap_append, List.flatMap_map, Function.comp_def]

end Table

/-! ## The table writer's semantics -/

section Sem
open NearCubicWires.WireExponent3_5.Cost NearCubicWires.WireExponent3_5.UnionMachine.DecisionBridge
open NearCubicWires.WireExponent3_5.FinalPass.Tm

end Sem

end NearCubicWires.WireExponent3_5.UnionMachine.FrontTW
