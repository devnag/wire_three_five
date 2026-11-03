import Proof.Packets.BudgetFamilyCost
import Proof.SourceAssembly.SourceRefillJoin

section
set_option autoImplicit false
set_option maxRecDepth 120000
set_option maxHeartbeats 250000
set_option warningAsError true

open NearCubicWires LocalBitMultitape ExtDecompositionBatch
open RepairOrdinary RepairOrdinary.RecoveryRootRound
open RepairRepresentation SupplierEstimator SupplierPipeline SourceInterfaces
open RepairSource.VerifierDecoding
open NearCubicWires.P1Closure
open PCJ9eff70d512234a4c_Fixed PCJd4d1d9d7d1fa4313_Production PCJc4297ab269d8423a_Source
open PCJ1fef9807c6954e94_Native PCJ515eaa990d75455b_FamilyInit
open NearCubicWires.RepairSource NearCubicWires.RepairSource.CloseoutFinal
namespace NearCubicWires.SourceBudget
open NearCubicWires.Admission NearCubicWires.RuntimeShape NearCubicWires.SourceConstruction
noncomputable section
attribute [local irreducible] P1TopDownPaidPayload.tapes

section cyc
variable (mask : MaskProducer) {selector : CyclicChoice.Laws} {a : DecompositionAlgorithm}
  {printer : WilliamsAlgorithm} (packet : PacketWriter selector a) (rows : RowProducer selector a printer)
  (r : Request) (layout : Packets.Layout a (r.family a) (geometryOf selector a r))
  (facts : ∀ row ∈ (r.family a).rows, Packets.PacketFacts a (r.family a) (geometryOf selector a r) row)
  (caps : RowCaps) (M2 U0 S Rw B v : Nat)

/-- The row-width scalar of the family init (as `cycFuel` states it). -/
abbrev rwOf (a : DecompositionAlgorithm) (r : Request) (M2 U0 : Nat) : Nat :=
  RowWidth.rw M2 U0 (exactListWord (PCJ38fbfed565f64139_Cached.cacheArgs a (r.family a)).gs).length

/-- The row count of the family init. -/
abbrev nOf (selector : CyclicChoice.Laws) (a : DecompositionAlgorithm) (r : Request)
    (layout : Packets.Layout a (r.family a) (geometryOf selector a r))
    (facts : ∀ row ∈ (r.family a).rows, Packets.PacketFacts a (r.family a) (geometryOf selector a r) row) : Nat :=
  (dataList a (r.family a) (geometryOf selector a r) layout facts).length

/-- **The cycle's summands**, `n`-free. -/
def cycBody : Nat :=
  SourceRequest.seedFuel mask packet r +
    BinaryCacheColdRun.budget (PCJ38fbfed565f64139_Cached.cacheArgs a (r.family a)) +
    SLoad.Setup.cost (r.input a).length (SLoad.Setup.metaBits layout.w layout.degree layout.C caps).length +
    rowInitBudget a rows.coefficient rows.degree r layout.w layout.degree layout.C caps +
    PCJ38fbfed565f64139_Family.budget printer (r.family a) (rows.state r layout facts caps) +
    2 * caps.descriptorReserve +
    RowWidth.cost (exactListWord (PCJ38fbfed565f64139_Cached.cacheArgs a (r.family a)).gs).length M2 U0
      (nOf selector a r layout facts) +
    initFuel printer ⟨S, Rw, B, rwOf a r M2 U0, v, nOf selector a r layout facts⟩

/-- **`cycFuel` is the prologue cost plus the cycle's summands plus `10`.** -/
theorem cycFuel_eq (n : Nat) :
    Rest.cycFuel mask packet rows r layout facts caps M2 U0 S Rw B v n =
      n + (cycBody mask packet rows r layout facts caps M2 U0 S Rw B v + 10) := by
  unfold Rest.cycFuel cycBody rwOf nOf
  omega

/-- **`cycFuel_inClasses`.** One class fact per summand (the prologue's included) puts the whole cycle fuel in the classes,
coefficients summed. -/
theorem cycFuel_inClasses {dP hT hS m L nn qn : Nat} (n : Nat)
    {c0P c0T c0S c1P c1T c1S c2P c2T c2S c3P c3T c3S c4P c4T c4S c5P c5T c5S c6P c6T c6S c7P c7T c7S
      c8P c8T c8S : Nat}
    (hn : InClasses dP hT hS m L nn qn c0P c0T c0S n)
    (hseed : InClasses dP hT hS m L nn qn c1P c1T c1S (SourceRequest.seedFuel mask packet r))
    (hcold : InClasses dP hT hS m L nn qn c2P c2T c2S
      (BinaryCacheColdRun.budget (PCJ38fbfed565f64139_Cached.cacheArgs a (r.family a))))
    (hsetup : InClasses dP hT hS m L nn qn c3P c3T c3S
      (SLoad.Setup.cost (r.input a).length (SLoad.Setup.metaBits layout.w layout.degree layout.C caps).length))
    (hrinit : InClasses dP hT hS m L nn qn c4P c4T c4S
      (rowInitBudget a rows.coefficient rows.degree r layout.w layout.degree layout.C caps))
    (hfam : InClasses dP hT hS m L nn qn c5P c5T c5S
      (PCJ38fbfed565f64139_Family.budget printer (r.family a) (rows.state r layout facts caps)))
    (hdR : InClasses dP hT hS m L nn qn c6P c6T c6S caps.descriptorReserve)
    (hrwc : InClasses dP hT hS m L nn qn c7P c7T c7S
      (RowWidth.cost (exactListWord (PCJ38fbfed565f64139_Cached.cacheArgs a (r.family a)).gs).length M2 U0
        (nOf selector a r layout facts)))
    (hinit : InClasses dP hT hS m L nn qn c8P c8T c8S
      (initFuel printer ⟨S, Rw, B, rwOf a r M2 U0, v, nOf selector a r layout facts⟩)) :
    InClasses dP hT hS m L nn qn
      (c0P + (c1P + c2P + c3P + c4P + c5P + 2*c6P + c7P + c8P + 10))
      (c0T + (c1T + c2T + c3T + c4T + c5T + 2*c6T + c7T + c8T))
      (c0S + (c1S + c2S + c3S + c4S + c5S + 2*c6S + c7S + c8S))
      (Rest.cycFuel mask packet rows r layout facts caps M2 U0 S Rw B v n) := by
  rw [cycFuel_eq]
  have hbody := (((((((hseed.add hcold).add hsetup).add hrinit).add hfam).add (hdR.smul 2)).add hrwc).add hinit).add_const 10
  have h := hn.add hbody
  unfold cycBody
  refine InClasses.mono (le_of_eq ?_) (h.coeff_mono ?_ ?_ ?_)
  · ring
  · omega
  · omega
  · omega

end cyc

/-! ## Two summands from `V`'s class -/

/-- The family init's fuel `1000(T+1)(S+R+B+rw+v+N+N·rw+1)` with `S R B` workspace/rewind/buffer of `V` (table) and the
row scalars polynomial. -/
theorem initFuel_inClasses (printer : WilliamsAlgorithm) {dP hT hS m L n qn : Nat} {V cP cT cS : Nat}
    (hV : InClasses dP hT hS m L n qn cP cT cS V) (rw v N xC : Nat)
    (hx : rw + v + N + N*rw + 1 ≤ xC*(n+1)^dP) :
    InClasses dP hT hS m L n qn
      (1000*(r_tapes printer + 1)*(((2*P1TopDownPaidReusableReserves.coefficient printer+20)*(cP+1) +
        (P1TopDownPaidReusableReserves.coefficient printer+2)*(cP+1) + (cP+1)) + xC))
      (1000*(r_tapes printer + 1)*((2*P1TopDownPaidReusableReserves.coefficient printer+20)*cT +
        (P1TopDownPaidReusableReserves.coefficient printer+2)*cT + cT))
      (1000*(r_tapes printer + 1)*((2*P1TopDownPaidReusableReserves.coefficient printer+20)*cS +
        (P1TopDownPaidReusableReserves.coefficient printer+2)*cS + cS))
      (initFuel printer ⟨P1TopDownPaidReusableReserves.workspace printer V, P1TopDownPaidReusableReserves.rewind printer V,
        P1TopDownPaidReusableReserves.buffer V, rw, v, N⟩) := by
  have hW := workspace_inClasses printer hV
  have hR := rewind_inClasses printer hV
  have hB := buffer_inClasses hV
  have hP : InClasses dP hT hS m L n qn xC 0 0 (rw + v + N + N*rw + 1) := InClasses.poly hx le_rfl
  have hsum := ((hW.add hR).add hB).add hP
  have hsc := hsum.smul (1000*(r_tapes printer + 1))
  unfold initFuel
  refine InClasses.mono (le_of_eq ?_) (hsc.coeff_mono le_rfl (by simp) (by simp))
  ring

end
end NearCubicWires.SourceBudget
end

