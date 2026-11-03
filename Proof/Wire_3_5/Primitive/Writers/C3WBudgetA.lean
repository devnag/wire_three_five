import Lean
import Proof.Wire_3_5.Primitive.Writers.C3WClass
import W3.Proof.Foundations.SourceRegistry
import Statement_Wire_3_5
import Proof.Wire_3_5.Assembly.Gate0
import Proof.Wire_3_5.Transfer.LiteralSources
import Proof.Wire_3_5.Primitive.Writers.Plan
import Proof.Wire_3_5.Primitive.SeedFix.GeoIface2
import Proof.Wire_3_5.Assembly.Split
import Proof.Wire_3_5.Primitive.Writers.C3WBudgetABase


noncomputable section
set_option maxRecDepth 4096


/-! # C3 request writer, part 22: the budget at a call

The writers' envelopes (`EGs`: the geometry writers at `n^{geoD}`; the gate-field writers at `n^{gsD}`, `n^{gtD}`),
the fill polynomial `CvF·(n+1)^{DvC}` (**`call_hpoly`**), and the writer's steps within
`c_W·classBound (EW l) .preprocessing` (**`call_budget`**).

Paper quantity: the request writer's steps within the preprocessing class `2^{O(Ψ)}` (P3:3108). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false

namespace NearCubicWires.WireExponent3_5.PrimAsm.C3Cost
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Shared
open NearCubicWires.SupplierPipeline NearCubicWires.LocalBitMultitape NearCubicWires.BlockPlatform
open NearCubicWires.WireExponent3_5.PrimAsm.C3Mach NearCubicWires.WireExponent3_5.PrimAsm.C3Field
open NearCubicWires.RepairOrdinary (frame frame_length)
open NearCubicWires.RepairRepresentation (natWord)

section Consts
open NearCubicWires.WireExponent3_5.Cost

/-- **The writer's coefficient.** -/
noncomputable def cWF (l : Literals) (cN cr : ℕ) : ℕ :=
  cGm (Classical.choice l.eightSources.decomposition) DvC *
    (KF cN cr + 1) ^ dGm (Classical.choice l.eightSources.decomposition) DvC

end Consts

section Call
open NearCubicWires.WireExponent3_5.Cost NearCubicWires.WireExponent3_5.Split NearCubicWires.WireExponent3_5.Primitive
open NearCubicWires.WireExponent3_5.PrimAsm.Plan
variable (l : Literals) (F : GateFree l) (kclk coef A a : ℕ) (ha : a ≤ kclk + 1)

/-- The sizes of the writers' outputs at a call. -/
theorem call_sizes (Gs : WriterIface.WriterStage)
    (sA : PrimT.GeoIface2.SideWriterAt l F EGs (cGs (gate0 l F).row.cr) kclk coef A a ha)
    (wA : PrimT.GeoIface2.WidthWriterAt l F EGs (cGs (gate0 l F).row.cr) kclk coef A a ha)
    (cA : PrimT.GeoIface2.ColsWriterAt l F EGs (cGs (gate0 l F).row.cr) kclk coef A a ha) (req : PrimRequest)
    (hcall : (callInputs l F kclk coef A a ha).Call req) (hs : (callInputs l F kclk coef A a ha).StarAt req.n)
    (gates : List (NormalizedThresholdGate ((callInputs l F kclk coef A a ha).starParams req.n hs).n)) (BG : ℕ)
    (hG : WriterIfaceJ.WriterRun Gs.M BG Gs.inS Gs.outS req.word (PrimT.C4Geo.gateField gates)) :
    (gates.map PrimT.C4Geo.suppG).length ≤ BG ∧
      PrimT.C4Geo.width ((callInputs l F kclk coef A a ha).starParams req.n hs) ≤ cGs (gate0 l F).row.cr * req.n ^ PrimT.GeoPack.geoD ∧
      (PrimT.C4Geo.cols ((callInputs l F kclk coef A a ha).starParams req.n hs)).length ≤
        cGs (gate0 l F).row.cr * req.n ^ PrimT.GeoPack.geoD := by
  have oG := wr_out_le Gs.hio hG
  have oW := wr_out_le wA.hio (wA.ready req hcall hs)
  have oC := wr_out_le cA.hio (cA.ready req hcall hs)
  unfold EGs at oW oC
  rw [classBound_EGp] at oW oC
  rw [gateField_eq, frame_length, List.length_append] at oG
  rw [List.length_replicate] at oW
  simp only [PrimT.C4Geo.colsField, RepairOrdinary.MatrixScorePhi.columnsWord, frame_length, List.length_append] at oC
  have hgy := flatMap_frame_len' (gates.map PrimT.C4Geo.suppG) RepairOrdinary.CloseoutRowsCircuitBottom.nativeWord
  have hgyr : (gates.map PrimT.C4Geo.suppG).length ≤ (gyrOf gates).length := by
    unfold gyrOf; rw [List.length_append]; omega
  have hcl := flatMap_frame_len' (PrimT.C4Geo.cols ((callInputs l F kclk coef A a ha).starParams req.n hs))
    fun x => RepairOrdinary.SignedSortKey.binary (PrimT.C4Geo.width ((callInputs l F kclk coef A a ha).starParams req.n hs)) x
  exact ⟨by omega, oW, by omega⟩

/-- **The fill polynomial covers the first program's numbers.** -/
theorem call_hpoly (req : PrimRequest) (hs : (callInputs l F kclk coef A a ha).StarAt req.n)
    (gates : List (NormalizedThresholdGate ((callInputs l F kclk coef A a ha).starParams req.n hs).n))
    (Ag cGx : ℕ) (hAg : Ag ≤ DvC) (hcGx : cGx ≤ cGg + cGt)
    (hg : (gates.map PrimT.C4Geo.suppG).length ≤ cGx * req.n ^ Ag)
    (hw : PrimT.C4Geo.width ((callInputs l F kclk coef A a ha).starParams req.n hs) ≤
      cGs (gate0 l F).row.cr * req.n ^ PrimT.GeoPack.geoD)
    (hc : (PrimT.C4Geo.cols ((callInputs l F kclk coef A a ha).starParams req.n hs)).length ≤
      cGs (gate0 l F).row.cr * req.n ^ PrimT.GeoPack.geoD) :
    PrimT.C4Geo.width ((callInputs l F kclk coef A a ha).starParams req.n hs) +
      (gates.map PrimT.C4Geo.suppG).length + 4 * PrimT.C4Geo.width ((callInputs l F kclk coef A a ha).starParams req.n hs) +
      2 + (PrimT.C4Geo.cols ((callInputs l F kclk coef A a ha).starParams req.n hs)).length + 1 +
      2 ^ (natBitLength (gates.map PrimT.C4Geo.suppG).length + 1) +
      2 ^ (natBitLength (PrimT.C4Geo.width ((callInputs l F kclk coef A a ha).starParams req.n hs)) + 1) +
      21 * (PrimT.C4Geo.cols ((callInputs l F kclk coef A a ha).starParams req.n hs)).length + 61 ≤
        UnaryCalc.value DvC (CvF (gate0 l F).row.cr) req.n := by
  have p1 := PrimAsm.CopyNat.two_pow_natBitLength_le (gates.map PrimT.C4Geo.suppG).length
  have p2 := PrimAsm.CopyNat.two_pow_natBitLength_le (PrimT.C4Geo.width ((callInputs l F kclk coef A a ha).starParams req.n hs))
  rw [pow_succ] at *
  obtain ⟨X, hX⟩ : ∃ X, X = (req.n + 1) ^ DvC := ⟨_, rfl⟩
  have hX1 : 1 ≤ X := by rw [hX]; exact Nat.one_le_pow _ _ (by omega)
  have e1 : req.n ^ PrimT.GeoPack.geoD ≤ X :=
    hX ▸ le_trans (Nat.pow_le_pow_left (by omega) _) (Nat.pow_le_pow_right (by omega) geoD_le)
  have e2 : req.n ^ Ag ≤ X := hX ▸ le_trans (Nat.pow_le_pow_left (by omega) _) (Nat.pow_le_pow_right (by omega) hAg)
  have f1 : cGs (gate0 l F).row.cr * req.n ^ PrimT.GeoPack.geoD ≤ cGs (gate0 l F).row.cr * X := Nat.mul_le_mul_left _ e1
  have f2 : cGx * req.n ^ Ag ≤ (cGg + cGt) * X := Nat.mul_le_mul hcGx e2
  have ev : UnaryCalc.value DvC (CvF (gate0 l F).row.cr) req.n = 31 * (cGs (gate0 l F).row.cr * X) +
      9 * ((cGg + cGt) * X) + 80 * X := by
    unfold UnaryCalc.value CvF; rw [← hX]; ring
  rw [ev]
  omega

end Call

end NearCubicWires.WireExponent3_5.PrimAsm.C3Cost

end
