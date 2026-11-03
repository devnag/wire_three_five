import Proof.SourceAssembly.SourceProloguePro3
import Proof.SourceAssembly.SourceRefillJoin

section
set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true

open NearCubicWires LocalBitMultitape ExtDecompositionBatch
open RepairOrdinary RepairOrdinary.RecoveryRootRound
open RepairRepresentation SupplierEstimator SupplierPipeline SourceInterfaces
open RepairSource.VerifierDecoding
open NearCubicWires.P1Closure
open PCJ9eff70d512234a4c_Fixed PCJd4d1d9d7d1fa4313_Production PCJc4297ab269d8423a_Source
open PCJ1fef9807c6954e94_Native PCJ515eaa990d75455b_FamilyInit
open NearCubicWires.RepairSource NearCubicWires.RepairSource.CloseoutFinal
open NearCubicWires.SourceRequest NearCubicWires.SourceRequest.FactorLoop
namespace NearCubicWires.SourceConstruction
noncomputable section
attribute [local irreducible] P1TopDownPaidPayload.tapes

namespace Dims

end Dims

/-! ### Layout facts (small contexts) -/

namespace Rest

section layout

end layout

/-- **The loop invariant of the repaired seam** at loop point `j`, on the unpadded view `(H, A)`: `Inv3`'s residents,
masters and outer driver/log; the dirt split — off `Z`: length and head `≤ Rc`; on the family bank `[F, F+rt)`:
head `+ fuel + 1 ≤ Rc` (B1 (2): the ONLY place the family fuel enters); on `Z`: length and head `≤ Rk`; and the four
`enc` heads `rest` reads are `0`. `K` may hold tapes below `F` and high residents. -/
structure InvR {d : SourceConstruction.Dims} {eX pX gW : Nat} (e : d.RestExt3 eX pX gW) {V : Nat} (hV : d.U ≤ V)
    (Rc Rk : Nat) (K : Fin V → Prop) (K0 : Fin V → List Bool) (KH0 : Fin V → Nat)
    (j w q Mb Ms cW cQ cB cS S Rw B v U0 fuel : Nat) (H : Fin V → Nat) (A : Fin V → List Bool) : Prop where
  kept : ∀ x, K x → A x = K0 x ∧ H x = KH0 x
  curT : A (d.rsT e.ext2.ext1 hV 2) = ZeroPadding.pad Rc (UnaryTemplate.tape j)
  big : A (d.rsT e.ext2.ext1 hV 0) = ZeroPadding.pad cB (List.replicate Mb true)
  small : A (d.rsT e.ext2.ext1 hV 1) = ZeroPadding.pad cS (List.replicate Ms true)
  wv : A (d.rsT e.ext2.ext1 hV 3) = ZeroPadding.pad cW (List.replicate w true)
  qv : A (d.rsT e.ext2.ext1 hV 4) = ZeroPadding.pad cQ (List.replicate q true)
  rsH : ∀ i, H (d.rsT e.ext2.ext1 hV i) = 0
  mU : A (Dims.mT e.ext2 hV 0) = ZeroPadding.pad Rc (List.replicate U0 true)
  mS : A (Dims.mT e.ext2 hV 1) = ZeroPadding.pad Rc (UnaryTemplate.tape S)
  mR : A (Dims.mT e.ext2 hV 2) = ZeroPadding.pad Rc (UnaryTemplate.tape Rw)
  mB : A (Dims.mT e.ext2 hV 3) = ZeroPadding.pad Rc (UnaryTemplate.tape B)
  mv : A (Dims.mT e.ext2 hV 4) = ZeroPadding.pad Rc (UnaryTemplate.tape v)
  mH : ∀ i, H (Dims.mT e.ext2 hV i) = 0
  drv : A (d.scr hV 11) = List.replicate Rc true
  drvH : H (d.scr hV 11) = 0
  lg : A (d.scr hV 12) = List.replicate (Rc+2) false
  lgH : H (d.scr hV 12) = 0
  zD : A (Dims.hrT e hV 10) = List.replicate Rk true
  zDH : H (Dims.hrT e hV 10) = 0
  zL : A (Dims.hrT e hV 11) = List.replicate (Rk+2) false
  zLH : H (Dims.hrT e hV 11) = 0
  dirtA : ∀ x : Fin V, d.InDirt eX pX gW x.val → ¬ d.InZ eX pX x.val → (A x).length ≤ Rc
  dirtH : ∀ x : Fin V, d.InDirt eX pX gW x.val → ¬ d.InZ eX pX x.val → H x ≤ Rc
  famH : ∀ x : Fin V, d.F ≤ x.val → x.val < d.F + d.rt → H x + fuel + 1 ≤ Rc
  zA : ∀ x : Fin V, d.InZ eX pX x.val → (A x).length ≤ Rk
  zH : ∀ x : Fin V, d.InZ eX pX x.val → H x ≤ Rk
  encH : ∀ kk : Fin 13, (kk.val < 3 ∨ kk.val = 4) → H (Dims.encT (d := d) hV kk) = 0

section concrete
variable (mask : MaskProducer) {selector : CyclicChoice.Laws}
  (packets : PCJc4297ab269d8423a_Source.PacketLibrary selector)
  (rows : PCJc4297ab269d8423a_Source.RowLibrary selector) (sources : EightSources) (res : Nat)
  {gamma : Real} (p : Parameters sources gamma) (k r : Nat)

set_option hygiene false in
local notation "𝔇" => dimsOf mask packets rows sources res p k r

end concrete

end Rest
end
end NearCubicWires.SourceConstruction
end
