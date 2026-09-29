import Proof.Wire_3_5.Primitive.SeedFix.GeoPack
import Proof.Wire_3_5.Primitive.Writers.SBTypes

/-! # The SB identifications, proved — `SBIdentStmts l` and `SBOutsStmt l`

* the filter's widths at `(2(n+1)^{26}, cap, e)`: **`fieldBits_s`**, **`labelBits_s`** (`⌈log₂ V⌉ = natBitLength (V−1)`,
  `FiltNum.clog_eq_nbl`), **`thr_s`** (the walk's majority `e/4 + 1`), **`seedWidth_s`**;
* **`geo_s`** (`hL`, `dRow`, `dR` in the registers' shapes), **`filterParams_s`**, **`starR_s`**, **`slots_s`** (S4's words
  `4 … 7` of `frontWordsW2` are `s4Core2`'s), **`sbIdent`** : `SBIdentStmts l`;
* **`sbOuts`** : `SBOutsStmt l` (SB's register-shaped words are S4's words `4 … 7`).

Paper quantity of the main types: S4's words `4 … 7` (`s4Core2`, P3:3170-3181; the filter's field, P3:2039-2055; the
walk's threshold; `s4Small2`). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace NearCubicWires.WireExponent3_5.PrimT.SBId
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Split NearCubicWires.WireExponent3_5.Transfer
open NearCubicWires.WireExponent3_5.FinalPass NearCubicWires.WireExponent3_5.FinalPass.PlanFP
open NearCubicWires.WireExponent3_5.PrimAsm.Plan
open NearCubicWires.RepairOrdinary.SignedSortKey (binary)

theorem len_ge (n : ℕ) : 2 ≤ 2 * (n + 1) ^ 26 := by
  have := Nat.one_le_pow 26 (n + 1) (by omega); omega

theorem fieldBits_s : PrimAsm.SBIdent.FieldBitsStmt := fun n cap e => by
  show Nat.clog 2 (2 * (n + 1) ^ 26) + 4 = _
  rw [PrimAsm.FiltNum.clog_eq_nbl _ (len_ge n), Nat.mul_comm 2]

theorem labelBits_s : PrimAsm.SBIdent.LabelBitsStmt := fun n cap e hc => by
  show max (Nat.clog 2 (32 * cap)) (Nat.clog 2 (2 * (n + 1) ^ 26)) = _
  rw [PrimAsm.FiltNum.clog_eq_nbl (32 * cap) (by omega), PrimAsm.FiltNum.clog_eq_nbl _ (len_ge n), Nat.mul_comm 32,
    Nat.mul_comm 2]

theorem thr_s : PrimAsm.SBIdent.ThrStmt := fun n cap e => by
  show (2 * (e / 4) + 1 + 1) / 2 = e / 4 + 1
  omega

theorem seedWidth_s : PrimAsm.SBIdent.SeedWidthStmt := fun n cap e hc => by
  have h1 := fieldBits_s n cap e
  have h2 := labelBits_s n cap e hc
  show 160 * (2 * (e / 4)) + 2 * (Filt.wOf (Filters.GapParams.fieldBits ⟨2 * (n + 1) ^ 26, cap, e⟩)
    (Filters.GapParams.labelBits ⟨2 * (n + 1) ^ 26, cap, e⟩) * 128) = _
  rw [h1, h2]
  unfold Filt.wOf
  generalize natBitLength ((n + 1) ^ 26 * 2 - 1) = A
  generalize max (natBitLength (cap * 32 - 1)) A = L
  omega

theorem geo_s : PrimAsm.SBIdent.GeoStmt := fun P =>
  ⟨rfl, by unfold PrimT.C4Geo.hL; omega,
    by show P.r / 2 * (P.b - P.s) + (P.n - P.r * P.b + 1) / 2 = _; rw [Nat.mul_comm],
    by show P.r / 2 * (P.b - P.s) + (P.n - P.r * P.b) / 2 = _; rw [Nat.mul_comm]⟩

theorem filterParams_s (l : Literals) : PrimAsm.SBIdent.FilterParamsStmt l :=
  fun F kclk coef A a ha m n => rfl

theorem starR_s (l : Literals) : PrimAsm.SBIdent.StarRStmt l :=
  fun F kclk coef A a ha n hs => ⟨PrimT.GeoPack.starParams_r l F kclk coef A a ha n hs, rfl⟩

theorem slots_s (l : Literals) : PrimAsm.SBIdent.SlotsStmt l := by
  intro F kclk coef A a ha r hs k
  obtain ⟨⟨n, mode, a', ha', Cs, carriers, translation⟩, hc⟩ := r
  have hk := k.isLt
  have h8 : (Finish.s4SlotB k).val < 8 := by simp [Finish.s4SlotB]; omega
  cases mode <;>
  · simp only [Seams.frontWordsW2, Seams.frontWordsOfW2]
    rw [dif_pos hs, dif_pos h8]
    fin_cases k <;> rfl

/-- **The SB identifications**, proved. -/
theorem sbIdent (l : Literals) : PrimAsm.SBIdent.SBIdentStmts l :=
  ⟨fieldBits_s, labelBits_s, thr_s, seedWidth_s, geo_s, filterParams_s l, starR_s l, slots_s l⟩

/-- **`sb_outs`**: SB's register-shaped words are S4's words `4 … 7` at every star call. -/
theorem sbOuts (l : Literals) : PrimAsm.SBTypes.SBOutsStmt l := by
  intro hI F kclk coef A a ha r hs k
  rw [slots_s l F kclk coef A a ha r hs k]
  obtain ⟨⟨n, mode, a', ha', Cs, carriers, translation⟩, hc⟩ := r
  have hPr := PrimT.GeoPack.starParams_r l F kclk coef A a ha n hs
  have hFP := filterParams_s l F kclk coef A a ha mode n
  have hcap : PrimAsm.SBTypes.capAt l mode ((callInputs l F kclk coef A a ha).starParams n hs) =
      Ledger.rowBCap (gateCap l) mode (Ledger.rowBr F.cr n)
        (Ledger.rowBSparse (gateZeta_pos l) (gateZeta_lt l) 2 (gateCδ1 l) n) n := by
    unfold PrimAsm.SBTypes.capAt; rw [hPr]; rfl
  have hC1 : 1 ≤ Ledger.rowBCap (gateCap l) mode (Ledger.rowBr F.cr n)
      (Ledger.rowBSparse (gateZeta_pos l) (gateZeta_lt l) 2 (gateCδ1 l) n) n :=
    ((gate0 l F).budget kclk coef A a ha).capOf_pos mode n
  show PrimAsm.SBTypes.sbWords ((callInputs l F kclk coef A a ha).starParams n hs)
      (PrimAsm.SBTypes.capAt l mode ((callInputs l F kclk coef A a ha).starParams n hs))
      (F.filterErrDeg * Nat.clog 2 (n + 2)) (Out.Car.carCnt carriers 0) (Out.Car.carCnt carriers 1) carriers.length k =
    (![Filt.tauWord ((callInputs l F kclk coef A a ha).filterParams mode n),
      Filt.modWord ((callInputs l F kclk coef A a ha).filterParams mode n),
      ListEval.unary (SupplierWalk.majorityThreshold ((callInputs l F kclk coef A a ha).filterParams mode n).walkLen),
      PrimAsm.Data.unaryList (Seams.s4Small2 ((callInputs l F kclk coef A a ha).starParams n hs) carriers
        ((callInputs l F kclk coef A a ha).filterParams mode n))] : Fin 4 → List Bool) k
  rw [hFP, hcap]
  have hPn : ((callInputs l F kclk coef A a ha).starParams n hs).n = n := rfl
  have hE := fieldBits_s n (Ledger.rowBCap (gateCap l) mode (Ledger.rowBr F.cr n)
    (Ledger.rowBSparse (gateZeta_pos l) (gateZeta_lt l) 2 (gateCδ1 l) n) n) (F.filterErrDeg * Nat.clog 2 (n + 2))
  fin_cases k
  · show frame (binary (PrimAsm.SBTypes.ellOf ((callInputs l F kclk coef A a ha).starParams n hs).n) _) = _
    unfold Filt.tauWord PrimAsm.SBTypes.ellOf
    rw [hE, hPn]
    rfl
  · show frame (binary (PrimAsm.SBTypes.ellOf ((callInputs l F kclk coef A a ha).starParams n hs).n) _) = _
    unfold Filt.modWord PrimAsm.SBTypes.ellOf
    rw [hE, hPn]
    rfl
  · show ListEval.unary (F.filterErrDeg * Nat.clog 2 (n + 2) / 4 + 1) = _
    rw [thr_s]
    rfl
  · show PrimAsm.Data.unaryList (PrimAsm.SBTypes.sbList _ _ _ _ _ _) = PrimAsm.Data.unaryList (Seams.s4Small2 _ _ _)
    congr 1
    obtain ⟨g1, g2, g3, g4⟩ := geo_s ((callInputs l F kclk coef A a ha).starParams n hs)
    have hsw := seedWidth_s n (Ledger.rowBCap (gateCap l) mode (Ledger.rowBr F.cr n)
      (Ledger.rowBSparse (gateZeta_pos l) (gateZeta_lt l) 2 (gateCδ1 l) n) n) (F.filterErrDeg * Nat.clog 2 (n + 2)) hC1
    unfold PrimAsm.SBTypes.sbList Seams.s4Small2 Seams.s4Small
    rw [g2, g1, g3, g4, Out.Car.carLen_eq, Out.Car.carLen_eq, hsw]
    unfold PrimAsm.SBTypes.swOf PrimAsm.SBTypes.ellOf PrimAsm.SBTypes.lbOf
    rw [hPn]
    simp only [List.cons_append, List.nil_append, Nat.mul_comm]

end NearCubicWires.WireExponent3_5.PrimT.SBId
