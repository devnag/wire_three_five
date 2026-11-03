import Proof.Packets.BudgetCycParts

section
set_option autoImplicit false
set_option maxRecDepth 120000
set_option maxHeartbeats 250000
set_option warningAsError true

open NearCubicWires LocalBitMultitape ExtDecompositionBatch
open RepairOrdinary RepairOrdinary.RecoveryRootRound
open RepairRepresentation SupplierEstimator SupplierPipeline SourceInterfaces
open NearCubicWires.P1Closure
open PCJ9eff70d512234a4c_Fixed PCJd4d1d9d7d1fa4313_Production PCJc4297ab269d8423a_Source
open NearCubicWires.RepairSource NearCubicWires.RepairSource.CloseoutFinal
namespace NearCubicWires.SourceBudget
open NearCubicWires.Admission NearCubicWires.RuntimeShape NearCubicWires.SourceConstruction
noncomputable section

/-- The metadata bits are linear in the metadata values and the four caps. -/
theorem metaBits_le (w deg C : ℕ) (caps : RowCaps) :
    (SLoad.Setup.metaBits w deg C caps).length ≤
      6*(w + deg + C) + 8*(caps.headerFuel + caps.copyCap + caps.descriptorReserve + caps.rawReserve) + 41 := by
  have h1 := natListWord_le [w, deg, C] (w + deg + C) (by
    intro x hx; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl <;> omega)
  have h2 := natListWord_le [caps.headerFuel, caps.copyCap, caps.descriptorReserve, caps.rawReserve]
    (caps.headerFuel + caps.copyCap + caps.descriptorReserve + caps.rawReserve) (by
    intro x hx; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl <;> omega)
  unfold SLoad.Setup.metaBits RowCaps.word
  simp only [List.length_append, List.length_cons, List.length_nil] at h1 h2 ⊢
  omega

/-- **The row initializer in the classes**: `rowBudget` (class `rb`, AD `rowBudget_inClasses`) plus
`coefficient·(rawReserve + descriptorReserve + |rows| + |metadata word| + 1)`. -/
theorem rowInit_inClasses (a : DecompositionAlgorithm) (c d : ℕ) (r : Request) (w deg C : ℕ) (caps : RowCaps)
    {dP hT hS m L n qn : ℕ} {cbP cbT cbS c1P c1T c1S c2P c2T c2S rowsC : ℕ}
    (hrb : InClasses dP hT hS m L n qn cbP cbT cbS (rowBudget a c d r C caps))
    (hB1 : InClasses dP hT hS m L n qn c1P c1T c1S (w + deg + C))
    (hB2 : InClasses dP hT hS m L n qn c2P c2T c2S
      (caps.headerFuel + caps.copyCap + caps.descriptorReserve + caps.rawReserve))
    (hrows : (r.family a).rows.length ≤ rowsC*(n+1)^dP) :
    InClasses dP hT hS m L n qn (cbP + c*(12*c1P + 17*c2P + rowsC + 84)) (cbT + c*(12*c1T + 17*c2T))
      (cbS + c*(12*c1S + 17*c2S)) (rowInitBudget a c d r w deg C caps) := by
  have hR : InClasses dP hT hS m L n qn rowsC 0 0 (r.family a).rows.length := InClasses.poly hrows le_rfl
  have hin := ((((hB1.smul 12).add (hB2.smul 17)).add hR).add_const 84).smul c
  have hs := hrb.add hin
  refine InClasses.mono ?_ (hs.coeff_mono (by ring_nf; omega) (by ring_nf; omega) (by ring_nf; omega))
  have hmb := metaBits_le w deg C caps
  unfold rowInitBudget
  rw [SLoad.Setup.meta_frame, RepairOrdinary.frame_length]
  have hc : c*(caps.rawReserve + caps.descriptorReserve + (r.family a).rows.length +
      (2*(SLoad.Setup.metaBits w deg C caps).length + 1) + 1) ≤
      c*(12*(w + deg + C) + 17*(caps.headerFuel + caps.copyCap + caps.descriptorReserve + caps.rawReserve) +
        (r.family a).rows.length + 84) := Nat.mul_le_mul_left _ (by omega)
  omega

/-- **The row family in the classes**, from the row producer's own `cost` field (`rowFuel ≤ rowBudget` under
`RowCaps.Good`) and `rowBudget`'s class; the row count raises every exponent by `nE`. -/
theorem family_inClasses {selector : CyclicChoice.Laws} {a : DecompositionAlgorithm} {printer : WilliamsAlgorithm}
    (rows : RowProducer selector a printer) (r : Request) (layout : Packets.Layout a (r.family a) (geometryOf selector a r))
    (facts : ∀ row ∈ (r.family a).rows, Packets.PacketFacts a (r.family a) (geometryOf selector a r) row)
    (caps : RowCaps) (hgood : RowCaps.Good selector a printer r layout facts caps)
    {dP hT hS m L n qn cP cT cS nC nE : ℕ}
    (hrb : InClasses dP hT hS m L n qn cP cT cS (rowBudget a rows.coefficient rows.degree r layout.C caps))
    (hNn : (r.family a).rows.length ≤ nC*(n+1)^nE) (hNq : (r.family a).rows.length ≤ nC*(qn+1)^nE) :
    InClasses (nE+dP) (nE+hT) (nE+hS) m L n qn (nC*(cP+3) + 3) (nC*cT) (nC*cS)
      (PCJ38fbfed565f64139_Family.budget printer (r.family a) (rows.state r layout facts caps)) :=
  familyBudget_inClasses (r.family a) (rows.state r layout facts caps) (rows.cost r layout facts caps hgood) hrb hNn hNq

end
end NearCubicWires.SourceBudget
end

