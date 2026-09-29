import Proof.Wire_3_5.Primitive.SeedFix.W6Z
import Proof.Wire_3_5.Primitive.ThresholdWriter.NumsPort4

/-! # W6, part 27: the body of the numbers machine

P3:2543-2558, 2573-2580, 2121-2157, 2220-2231 (the THR call's fourteen numbers, the prime rows, the level records, the
modulus word; `Joins.thrNumVals`): from the fill's state, the word phase and proof 1's programs (`body1_run`), the
arithmetic and the EW stage (`tail1_run`), the search and the outputs (`tail2_run`):
* `bodyM`, `portS` (the stream of each of the 21 ports), **`body_run`**: every port stream holds
  `Nums3.nums3OutPorts w ncar cap_T V (thrNumVals P Cs alg D ncar cap_T)`.

Paper quantities of the main type: the THR numbers on their ports. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedVariables false
set_option linter.style.longLine false

namespace NearCubicWires.WireExponent3_5.PrimT.W6
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairRepresentation NearCubicWires.SupplierPipeline NearCubicWires.SupplierPrime
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Shared
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimAsm
open NearCubicWires.RepairOrdinary.SignedSortKey (binary binary_length)

variable (alg : DecompositionAlgorithm)

/-- **The body**: the word phase, proof 1's programs, the arithmetic, the EW stage, the search, the outputs. -/
noncomputable def bodyM (Dexp : ℕ) := Composition.machine (Composition.machine body1M (tail1M Dexp)) tail2M

/-- The 21 ports on the streams: the request, `1^{ncar}`, `1^{cap_T}`, the fourteen numbers, the prime rows, the level
records, the modulus word, the count. -/
def portS (p : Fin 21) : Fin 192 :=
  ⟨if p.val = 0 then 0 else if p.val = 1 then 2 else if p.val = 2 then 3 else if p.val = 20 then 1 else p.val + 2,
    by split_ifs <;> omega⟩

theorem portS_inj : Function.Injective portS := by
  intro a b h
  have e := congrArg Fin.val h
  simp only [portS] at e
  apply Fin.ext
  split_ifs at e <;> omega

theorem ewL_sm_val (i : Fin 9) : (ewL.sm i).val = 20 ∨ (152 ≤ (ewL.sm i).val ∧ (ewL.sm i).val ≤ 159) := by
  fin_cases i <;> decide

/-- **The ports from the stream facts** (any numbers `v`). -/
theorem ports_of (τ : WL) (w : List Bool) (ncar capT V : ℕ) (v : PrimThrW.Joins.ThrNumVals)
    (h0 : τ.st 0 = frame w) (h2 : τ.st 2 = List.replicate ncar true) (h3 : τ.st 3 = List.replicate capT true)
    (hv : ∀ k : Fin 14, τ.st (sVal k) = List.replicate (v.get k) true)
    (h19 : τ.st 19 = Data.unaryList (PrimThrW.Joins.primesList v.cut))
    (h20 : τ.st 20 = PrimThrW.Joins.winRecs (PrimThrW.Joins.thrMP v.M v.A v.Bs v.den))
    (h21 : τ.st sMod = frame (binary v.ell0 (GF.firstPrimitive v.ell0))) (h1 : τ.st 1 = List.replicate V true)
    (hp : v.pMod = GF.firstPrimitive v.ell0) :
    ∀ p : Fin 21, τ.st (portS p) = PrimThrW.Nums3.nums3OutPorts w ncar capT V v p := by
  intro p
  fin_cases p
  · show τ.st 0 = _; rw [h0]; simp [PrimThrW.Nums3.nums3OutPorts, PrimThrW.NumsP.numsOutPorts]
  · show τ.st 2 = _; rw [h2]; simp [PrimThrW.Nums3.nums3OutPorts, PrimThrW.NumsP.numsOutPorts]
  · show τ.st 3 = _; rw [h3]; simp [PrimThrW.Nums3.nums3OutPorts, PrimThrW.NumsP.numsOutPorts]
  · show τ.st (sVal 0) = PrimThrW.Nums3.nums3OutPorts w ncar capT V v ⟨(0 : Fin 14).val + 3, by omega⟩
    rw [PrimThrW.Nums3.nums3Out_val]; exact hv 0
  · show τ.st (sVal 1) = PrimThrW.Nums3.nums3OutPorts w ncar capT V v ⟨(1 : Fin 14).val + 3, by omega⟩
    rw [PrimThrW.Nums3.nums3Out_val]; exact hv 1
  · show τ.st (sVal 2) = PrimThrW.Nums3.nums3OutPorts w ncar capT V v ⟨(2 : Fin 14).val + 3, by omega⟩
    rw [PrimThrW.Nums3.nums3Out_val]; exact hv 2
  · show τ.st (sVal 3) = PrimThrW.Nums3.nums3OutPorts w ncar capT V v ⟨(3 : Fin 14).val + 3, by omega⟩
    rw [PrimThrW.Nums3.nums3Out_val]; exact hv 3
  · show τ.st (sVal 4) = PrimThrW.Nums3.nums3OutPorts w ncar capT V v ⟨(4 : Fin 14).val + 3, by omega⟩
    rw [PrimThrW.Nums3.nums3Out_val]; exact hv 4
  · show τ.st (sVal 5) = PrimThrW.Nums3.nums3OutPorts w ncar capT V v ⟨(5 : Fin 14).val + 3, by omega⟩
    rw [PrimThrW.Nums3.nums3Out_val]; exact hv 5
  · show τ.st (sVal 6) = PrimThrW.Nums3.nums3OutPorts w ncar capT V v ⟨(6 : Fin 14).val + 3, by omega⟩
    rw [PrimThrW.Nums3.nums3Out_val]; exact hv 6
  · show τ.st (sVal 7) = PrimThrW.Nums3.nums3OutPorts w ncar capT V v ⟨(7 : Fin 14).val + 3, by omega⟩
    rw [PrimThrW.Nums3.nums3Out_val]; exact hv 7
  · show τ.st (sVal 8) = PrimThrW.Nums3.nums3OutPorts w ncar capT V v ⟨(8 : Fin 14).val + 3, by omega⟩
    rw [PrimThrW.Nums3.nums3Out_val]; exact hv 8
  · show τ.st (sVal 9) = PrimThrW.Nums3.nums3OutPorts w ncar capT V v ⟨(9 : Fin 14).val + 3, by omega⟩
    rw [PrimThrW.Nums3.nums3Out_val]; exact hv 9
  · show τ.st (sVal 10) = PrimThrW.Nums3.nums3OutPorts w ncar capT V v ⟨(10 : Fin 14).val + 3, by omega⟩
    rw [PrimThrW.Nums3.nums3Out_val]; exact hv 10
  · show τ.st (sVal 11) = PrimThrW.Nums3.nums3OutPorts w ncar capT V v ⟨(11 : Fin 14).val + 3, by omega⟩
    rw [PrimThrW.Nums3.nums3Out_val]; exact hv 11
  · show τ.st (sVal 12) = PrimThrW.Nums3.nums3OutPorts w ncar capT V v ⟨(12 : Fin 14).val + 3, by omega⟩
    rw [PrimThrW.Nums3.nums3Out_val]; exact hv 12
  · show τ.st (sVal 13) = PrimThrW.Nums3.nums3OutPorts w ncar capT V v ⟨(13 : Fin 14).val + 3, by omega⟩
    rw [PrimThrW.Nums3.nums3Out_val]; exact hv 13
  · show τ.st 19 = _; rw [h19]; simp [PrimThrW.Nums3.nums3OutPorts, PrimThrW.NumsP.numsOutPorts]
  · show τ.st 20 = _; rw [h20]; simp [PrimThrW.Nums3.nums3OutPorts, PrimThrW.NumsP.numsOutPorts]
  · show τ.st sMod = _; rw [h21, ← hp]; simp [PrimThrW.Nums3.nums3OutPorts, PrimThrW.NumsP.numsOutPorts]
  · show τ.st 1 = _; rw [h1]; exact (PrimThrW.Nums3.nums3Out_count w ncar capT V v).symm

theorem body_run (P : StarParams) {a' : ℕ} (Cs : Fin a' → NormalizedThresholdThresholdCircuit P.n) (codes : List ℕ)
    (tl : List Bool) (ncar capT V Dexp : ℕ) (ha : a' ≤ 4)
    (c1 : 2 ^ (natBitLength P.n + 1) ≤ (2 * V + 2)) (c2 : 2 ^ (natBitLength a' + 1) ≤ (2 * V + 2))
    (c3 : 2 * (payF alg Cs 0 ++ payF alg Cs 1 ++ payF alg Cs 2 ++ payF alg Cs 3).length + 4 ≤ (2 * V + 2))
    (c4 : 4 ≤ (2 * V + 2)) (c5 : fnw.length ≤ (2 * V + 2))
    (c6 : ∀ j, 2 ^ (natBitLength (szOf Cs j) + 1) + (Primitive.thrOccs P Cs).length ≤ (2 * V + 2))
    (c7 : ncar ≤ (2 * V + 2)) (c8 : capT ≤ (2 * V + 2))
    (hbA : MidBoundsA (2 * V + 2) P.n (PrimThrW.Joins.thrNumVals P Cs alg Dexp ncar capT).nG (familyMagnitudeExponent (Primitive.thrRealize P Cs alg)) Dexp (PrimThrW.Joins.thrNumVals P Cs alg Dexp ncar capT).cut)
    (hbC : MidBounds (2 * V + 2) (PrimThrW.Joins.thrNumVals P Cs alg Dexp ncar capT).nG (PrimThrW.Joins.thrNumVals P Cs alg Dexp ncar capT).nPr (PrimThrW.Joins.thrNumVals P Cs alg Dexp ncar capT).dig a' ncar capT (PrimThrW.Joins.thrNumVals P Cs alg Dexp ncar capT).den (PrimThrW.Joins.thrNumVals P Cs alg Dexp ncar capT).A (PrimThrW.Joins.thrNumVals P Cs alg Dexp ncar capT).Bs (PrimThrW.Joins.thrNumVals P Cs alg Dexp ncar capT).J (PrimThrW.Joins.thrNumVals P Cs alg Dexp ncar capT).M)
    (bE : (PrimThrW.Joins.thrNumVals P Cs alg Dexp ncar capT).ee ≤ (2 * V + 2)) (hneed : UnionMachine.EwSize.ewNeed ((PrimThrW.Joins.thrNumVals P Cs alg Dexp ncar capT).M + (PrimThrW.Joins.thrNumVals P Cs alg Dexp ncar capT).A + (PrimThrW.Joins.thrNumVals P Cs alg Dexp ncar capT).Bs + (PrimThrW.Joins.thrNumVals P Cs alg Dexp ncar capT).den) ≤ (2 * V + 2))
    (hbg : 2 ^ ((PrimThrW.Joins.thrNumVals P Cs alg Dexp ncar capT).ell0 + 1) + 2 * (PrimThrW.Joins.thrNumVals P Cs alg Dexp ncar capT).ell0 + 4 ≤ (2 * V + 2)) (hbv : ∀ k, 2 * (PrimThrW.Joins.thrNumVals P Cs alg Dexp ncar capT).get k + 4 ≤ (2 * V + 2)) :
    ∃ (τ : WL) (m : ℕ), Step (bodyM Dexp) m (wenc (2 * V + 2) (σ1 alg (Data.reqW P.n true (ReqBridge.thrCodes Cs) codes tl) ncar capT V Cs)).H (wenc (2 * V + 2) (σ1 alg (Data.reqW P.n true (ReqBridge.thrCodes Cs) codes tl) ncar capT V Cs)).A (wenc (2 * V + 2) τ).H (wenc (2 * V + 2) τ).A ∧
      m ≤ 30 * (opU (2 * V + 2) + 1) + 1 + pcC alg P Cs + 1 + pcE alg P Cs + 1 +
        (7 * (PrimThrW.Joins.thrNumVals P Cs alg Dexp ncar capT).nG + 7 * (familyMagnitudeExponent (Primitive.thrRealize P Cs alg)) + (Dexp + 1) * opU (2 * V + 2) + 40 * (opU (2 * V + 2) + 1) + 1 +
          ((PrimThrW.Joins.thrNumVals P Cs alg Dexp ncar capT).cut * ((PrimThrW.Joins.thrNumVals P Cs alg Dexp ncar capT).cut * (8 * (opU (2 * V + 2) + 1) + 4) + 14 * (opU (2 * V + 2) + 1) + 4) + 8 * (opU (2 * V + 2) + 1)) + 1 +
          100 * (opU (2 * V + 2) + 1) + 1 + (20 * (opU (2 * V + 2) + 1) + UnionMachine.EwSize.ewBound ((PrimThrW.Joins.thrNumVals P Cs alg Dexp ncar capT).M + (PrimThrW.Joins.thrNumVals P Cs alg Dexp ncar capT).A + (PrimThrW.Joins.thrNumVals P Cs alg Dexp ncar capT).Bs + (PrimThrW.Joins.thrNumVals P Cs alg Dexp ncar capT).den))) + 1 +
        ((20 * (4 * (opU (2 * V + 2) + 1) + 1) + 1 + GF2.searchCost (PrimThrW.Joins.thrNumVals P Cs alg Dexp ncar capT).ell0 + 1 +
          (opU (2 * V + 2) + 2 * ((PrimThrW.Joins.thrNumVals P Cs alg Dexp ncar capT).ell0 + 2) * (40 * 2 ^ (PrimThrW.Joins.thrNumVals P Cs alg Dexp ncar capT).ell0 + 40))) + 1 + 14 * (4 * (opU (2 * V + 2) + 1) + 1)) ∧
      ∀ p : Fin 21, τ.st (portS p) = PrimThrW.Nums3.nums3OutPorts (Data.reqW P.n true (ReqBridge.thrCodes Cs) codes tl) ncar capT V (PrimThrW.Joins.thrNumVals P Cs alg Dexp ncar capT) p := by
  have hL0 : ((PrimThrW.Joins.thrNumVals P Cs alg Dexp ncar capT).J + 1 + (Nat.clog 2 (PrimThrW.Joins.thrNumVals P Cs alg Dexp ncar capT).M - ((PrimThrW.Joins.thrNumVals P Cs alg Dexp ncar capT).J + 1))) = (PrimThrW.Joins.thrNumVals P Cs alg Dexp ncar capT).ell0 := aL_max _ _
  refine (body1_run alg P Cs codes tl ncar capT V ha c1 c2 c3 c4 c5 c6 c7 c8).elim fun τ3 h3 => h3.elim fun m3 h3' => ?_
  have f48 := h3'.2.2.1
  have f49 := h3'.2.2.2.1
  have f50 := h3'.2.2.2.2.1
  have f51 := h3'.2.2.2.2.2.1
  have f52 := h3'.2.2.2.2.2.2.1
  have fz := h3'.2.2.2.2.2.2.2.1
  have fC := h3'.2.2.2.2.2.2.2.2.1
  have fCh := h3'.2.2.2.2.2.2.2.2.2.1
  have fE := h3'.2.2.2.2.2.2.2.2.2.2.1
  have fEh := h3'.2.2.2.2.2.2.2.2.2.2.2.1
  have fst := h3'.2.2.2.2.2.2.2.2.2.2.2.2.1
  have fsh := h3'.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hnB : ∀ s : Fin 192, (s.val < 30 ∨ 152 ≤ s.val) → (∀ k, s ≠ sBC k) ∧ (∀ k, s ≠ sBE k) := fun s hs =>
    ⟨fun k h => by rw [h] at hs; simp [sBC] at hs; omega, fun k h => by rw [h] at hs; simp [sBE] at hs; omega⟩
  have hnL : ∀ s : Fin 192, (5 ≤ s.val ∧ s.val < 22 ∨ 152 ≤ s.val) → s ≠ sReq ∧ s ≠ sNc ∧ s ≠ sCap ∧ ∀ i, s ≠ sPay i :=
    fun s hs => ⟨fun h => by rw [h] at hs; simp [sReq] at hs, fun h => by rw [h] at hs; simp [sNc] at hs,
      fun h => by rw [h] at hs; simp [sCap] at hs, fun i h => by rw [h] at hs; simp [sPay] at hs; omega⟩
  have blank3 : ∀ s : Fin 192, (5 ≤ s.val ∧ s.val < 22 ∨ 152 ≤ s.val) → τ3.st s = [] ∧ τ3.sh s = 0 := fun s hs => by
    have hb := hnB s (by omega)
    have hl := hnL s hs
    exact ⟨(fst s hb.1 hb.2).trans (σ1_blank alg (Data.reqW P.n true (ReqBridge.thrCodes Cs) codes tl) ncar capT V Cs s (by omega)),
      fsh s hb.1 hb.2 hl.1 hl.2.1 hl.2.2.1 hl.2.2.2⟩
  have fz0 : ∀ r : Fin 80, r.val < 48 → τ3.val r = 0 := fun r hr =>
    fz r (fun h => by rw [h] at hr; simp at hr) (fun h => by rw [h] at hr; simp at hr)
      (fun h => by rw [h] at hr; simp at hr) (fun h => by rw [h] at hr; simp at hr) (fun h => by rw [h] at hr; simp at hr)
  have fzH : ∀ r : Fin 80, 53 ≤ r.val → τ3.val r = 0 := fun r hr =>
    fz r (fun h => by rw [h] at hr; simp at hr) (fun h => by rw [h] at hr; simp at hr)
      (fun h => by rw [h] at hr; simp at hr) (fun h => by rw [h] at hr; simp at hr) (fun h => by rw [h] at hr; simp at hr)
  refine (tail1_run (2 * V + 2) τ3 P.n a' (PrimThrW.Joins.thrNumVals P Cs alg Dexp ncar capT).M ncar capT (PrimThrW.Joins.thrNumVals P Cs alg Dexp ncar capT).nG (familyMagnitudeExponent (Primitive.thrRealize P Cs alg)) Dexp (PrimThrW.Joins.thrNumVals P Cs alg Dexp ncar capT).den (PrimThrW.Joins.thrNumVals P Cs alg Dexp ncar capT).cut (PrimThrW.Joins.thrNumVals P Cs alg Dexp ncar capT).dig (PrimThrW.Joins.thrNumVals P Cs alg Dexp ncar capT).nPr (PrimThrW.Joins.thrNumVals P Cs alg Dexp ncar capT).pSum
    (PrimThrW.Joins.thrNumVals P Cs alg Dexp ncar capT).A (PrimThrW.Joins.thrNumVals P Cs alg Dexp ncar capT).Bs (PrimThrW.Joins.thrNumVals P Cs alg Dexp ncar capT).J (PrimThrW.Joins.thrNumVals P Cs alg Dexp ncar capT).tt f48 f49 f50 f51 f52 fz0 fzH
    fC fCh fE fEh (blank3 sPr (by left; decide)).1 (blank3 sPr (by left; decide)).2
    (fun i => blank3 _ (by fin_cases i <;> decide)) (blank3 160 (by right; decide))
    rfl rfl rfl rfl rfl rfl rfl rfl rfl hbA hbC bE hneed).elim fun τ5 h5 => h5.elim fun m5 h5' => ?_
  have g5val := h5'.2.2.1
  have g5pr := h5'.2.2.2.1
  have g5win := h5'.2.2.2.2.1
  have g5st := h5'.2.2.2.2.2.1
  have g5sh := h5'.2.2.2.2.2.2.1
  have hsT : ∀ s : Fin 192, (5 ≤ s.val ∧ s.val < 22 ∨ 160 < s.val) → s ≠ sPr → s ≠ 20 → τ5.st s = [] ∧ τ5.sh s = 0 :=
    fun s hs h19 h20 => by
      have h20' : s.val ≠ 20 := fun e => h20 (Fin.ext e)
      have hi : ∀ i, ewL.sm i ≠ s := fun i h => by
        have hv := ewL_sm_val i
        rw [h] at hv
        omega
      have h160 : s ≠ 160 := fun h => by rw [h] at hs; simp at hs
      have hb1 : s ≠ sBC 1 := fun h => by rw [h] at hs; simp [sBC] at hs
      have hb2 : s ≠ sBE 1 := fun h => by rw [h] at hs; simp [sBE] at hs
      rw [g5st s hi h160 h19, g5sh s hi h160 h19 hb1 hb2]
      exact blank3 s (by omega)
  have t2 := tail2_run (2 * V + 2) τ5 (PrimThrW.Joins.thrNumVals P Cs alg Dexp ncar capT).ell0 (PrimThrW.Joins.thrNumVals P Cs alg Dexp ncar capT).get (by rw [g5val]; simp only [Function.update_apply, Fin.isValue, Fin.reduceEq, ↓reduceIte, ite_true, ite_false, Nat.zero_add]; exact hL0) (by rw [← hL0]; omega)
    (by rw [g5val]; simp only [Function.update_apply, Fin.isValue, Fin.reduceEq, ↓reduceIte, ite_true, ite_false, Nat.zero_add]; exact fz 66 (by decide) (by decide) (by decide) (by decide) (by decide)) (by rw [g5val]; simp only [Function.update_apply, Fin.isValue, Fin.reduceEq, ↓reduceIte, ite_true, ite_false, Nat.zero_add]; exact fz 75 (by decide) (by decide) (by decide) (by decide) (by decide)) (by rw [g5val]; simp only [Function.update_apply, Fin.isValue, Fin.reduceEq, ↓reduceIte, ite_true, ite_false, Nat.zero_add]; exact fz 76 (by decide) (by decide) (by decide) (by decide) (by decide)) (by rw [g5val]; simp only [Function.update_apply, Fin.isValue, Fin.reduceEq, ↓reduceIte, ite_true, ite_false, Nat.zero_add]; exact fz 77 (by decide) (by decide) (by decide) (by decide) (by decide)) (by rw [g5val]; simp only [Function.update_apply, Fin.isValue, Fin.reduceEq, ↓reduceIte, ite_true, ite_false, Nat.zero_add]; exact fz 78 (by decide) (by decide) (by decide) (by decide) (by decide)) (by rw [g5val]; simp only [Function.update_apply, Fin.isValue, Fin.reduceEq, ↓reduceIte, ite_true, ite_false, Nat.zero_add]; exact fz 79 (by decide) (by decide) (by decide) (by decide) (by decide)) (by rw [g5val]; simp only [Function.update_apply, Fin.isValue, Fin.reduceEq, ↓reduceIte, ite_true, ite_false, Nat.zero_add]; exact fz 68 (by decide) (by decide) (by decide) (by decide) (by decide))
    (fun j => hsT _ (by fin_cases j <;> decide) (by fin_cases j <;> decide) (by fin_cases j <;> decide))
    (fun k => hsT _ (by fin_cases k <;> decide) (by fin_cases k <;> decide) (by fin_cases k <;> decide)) hbg
    (fun k hk => by
      fin_cases k
      · show τ5.val 53 = _
        rw [g5val]; simp only [Function.update_apply, Fin.isValue, Fin.reduceEq, ↓reduceIte, ite_true, ite_false, Nat.zero_add]; rfl
      · show τ5.val 55 = _
        rw [g5val]; simp only [Function.update_apply, Fin.isValue, Fin.reduceEq, ↓reduceIte, ite_true, ite_false, Nat.zero_add]; rfl
      · show τ5.val 56 = _
        rw [g5val]; simp only [Function.update_apply, Fin.isValue, Fin.reduceEq, ↓reduceIte, ite_true, ite_false, Nat.zero_add]; rfl
      · show τ5.val 58 = _
        rw [g5val]; simp only [Function.update_apply, Fin.isValue, Fin.reduceEq, ↓reduceIte, ite_true, ite_false, Nat.zero_add]; rfl
      · show τ5.val 59 = _
        rw [g5val]; simp only [Function.update_apply, Fin.isValue, Fin.reduceEq, ↓reduceIte, ite_true, ite_false, Nat.zero_add]; rfl
      · show τ5.val 57 = _
        rw [g5val]; simp only [Function.update_apply, Fin.isValue, Fin.reduceEq, ↓reduceIte, ite_true, ite_false, Nat.zero_add]; rfl
      · show τ5.val 50 = _
        rw [g5val]; simp only [Function.update_apply, Fin.isValue, Fin.reduceEq, ↓reduceIte, ite_true, ite_false, Nat.zero_add]; exact f50
      · show τ5.val 60 = _
        rw [g5val]; simp only [Function.update_apply, Fin.isValue, Fin.reduceEq, ↓reduceIte, ite_true, ite_false, Nat.zero_add]; rfl
      · show τ5.val 61 = _
        rw [g5val]; simp only [Function.update_apply, Fin.isValue, Fin.reduceEq, ↓reduceIte, ite_true, ite_false, Nat.zero_add]; rfl
      · show τ5.val 62 = _
        rw [g5val]; simp only [Function.update_apply, Fin.isValue, Fin.reduceEq, ↓reduceIte, ite_true, ite_false, Nat.zero_add]; rfl
      · show τ5.val 63 = _
        rw [g5val]; simp only [Function.update_apply, Fin.isValue, Fin.reduceEq, ↓reduceIte, ite_true, ite_false, Nat.zero_add]; rfl
      · show τ5.val 64 = _
        rw [g5val]; simp only [Function.update_apply, Fin.isValue, Fin.reduceEq, ↓reduceIte, ite_true, ite_false, Nat.zero_add]; rfl
      · show τ5.val 65 = _
        rw [g5val]; simp only [Function.update_apply, Fin.isValue, Fin.reduceEq, ↓reduceIte, ite_true, ite_false, Nat.zero_add]; exact hL0
      · exact absurd rfl hk)
    rfl hbv
  have keepT : ∀ s : Fin 192, (∀ j, srT j ≠ s) → (∀ k, sVal k ≠ s) → (∀ i, ewL.sm i ≠ s) → s ≠ 160 → s ≠ sPr →
      (∀ k, s ≠ sBC k) → (∀ k, s ≠ sBE k) → (outSt (⟨Function.update (gfQ τ5 (PrimThrW.Joins.thrNumVals P Cs alg Dexp ncar capT).ell0).sh sMod (2 * (PrimThrW.Joins.thrNumVals P Cs alg Dexp ncar capT).ell0), (gfQ τ5 (PrimThrW.Joins.thrNumVals P Cs alg Dexp ncar capT).ell0).st, Function.update τ5.val 66 (GF.firstPrimitive (PrimThrW.Joins.thrNumVals P Cs alg Dexp ncar capT).ell0), τ5.cell⟩ : WL) (PrimThrW.Joins.thrNumVals P Cs alg Dexp ncar capT).get).st s = (σ1 alg (Data.reqW P.n true (ReqBridge.thrCodes Cs) codes tl) ncar capT V Cs).st s := fun s h1 h2 h3 h4 h5 h6 h7 => by
    rw [tail2_st_other τ5 (PrimThrW.Joins.thrNumVals P Cs alg Dexp ncar capT).ell0 (PrimThrW.Joins.thrNumVals P Cs alg Dexp ncar capT).get s h1 h2, g5st s h3 h4 h5, fst s h6 h7]
  refine ⟨(outSt (⟨Function.update (gfQ τ5 (PrimThrW.Joins.thrNumVals P Cs alg Dexp ncar capT).ell0).sh sMod (2 * (PrimThrW.Joins.thrNumVals P Cs alg Dexp ncar capT).ell0), (gfQ τ5 (PrimThrW.Joins.thrNumVals P Cs alg Dexp ncar capT).ell0).st, Function.update τ5.val 66 (GF.firstPrimitive (PrimThrW.Joins.thrNumVals P Cs alg Dexp ncar capT).ell0), τ5.cell⟩ : WL) (PrimThrW.Joins.thrNumVals P Cs alg Dexp ncar capT).get), _, ((h3'.1).seq h5'.1).seq t2,
    Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add h3'.2.1 (le_refl 1)) h5'.2.1) (le_refl 1)) le_rfl, ?_⟩
  exact ports_of (outSt (⟨Function.update (gfQ τ5 (PrimThrW.Joins.thrNumVals P Cs alg Dexp ncar capT).ell0).sh sMod (2 * (PrimThrW.Joins.thrNumVals P Cs alg Dexp ncar capT).ell0), (gfQ τ5 (PrimThrW.Joins.thrNumVals P Cs alg Dexp ncar capT).ell0).st, Function.update τ5.val 66 (GF.firstPrimitive (PrimThrW.Joins.thrNumVals P Cs alg Dexp ncar capT).ell0), τ5.cell⟩ : WL) (PrimThrW.Joins.thrNumVals P Cs alg Dexp ncar capT).get) (Data.reqW P.n true (ReqBridge.thrCodes Cs) codes tl) ncar capT V (PrimThrW.Joins.thrNumVals P Cs alg Dexp ncar capT)
    (by rw [(keepT 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))]; exact σ1_req alg (Data.reqW P.n true (ReqBridge.thrCodes Cs) codes tl) ncar capT V Cs)
    (by rw [(keepT 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))]; exact σ1_nc alg (Data.reqW P.n true (ReqBridge.thrCodes Cs) codes tl) ncar capT V Cs)
    (by rw [(keepT 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))]; exact σ1_cap alg (Data.reqW P.n true (ReqBridge.thrCodes Cs) codes tl) ncar capT V Cs)
    (fun k => tail2_st_val τ5 (PrimThrW.Joins.thrNumVals P Cs alg Dexp ncar capT).ell0 (PrimThrW.Joins.thrNumVals P Cs alg Dexp ncar capT).get k)
    (by rw [tail2_st_other τ5 (PrimThrW.Joins.thrNumVals P Cs alg Dexp ncar capT).ell0 (PrimThrW.Joins.thrNumVals P Cs alg Dexp ncar capT).get 19 (by decide) (by decide)]; exact g5pr)
    (by rw [tail2_st_other τ5 (PrimThrW.Joins.thrNumVals P Cs alg Dexp ncar capT).ell0 (PrimThrW.Joins.thrNumVals P Cs alg Dexp ncar capT).get 20 (by decide) (by decide)]; exact g5win)
    (tail2_st_mod τ5 (PrimThrW.Joins.thrNumVals P Cs alg Dexp ncar capT).ell0 (PrimThrW.Joins.thrNumVals P Cs alg Dexp ncar capT).get)
    (by rw [(keepT 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))]; exact σ1_cnt alg (Data.reqW P.n true (ReqBridge.thrCodes Cs) codes tl) ncar capT V Cs) rfl

end NearCubicWires.WireExponent3_5.PrimT.W6
