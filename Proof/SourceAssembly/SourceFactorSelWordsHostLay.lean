import Proof.SourceAssembly.SourceFactorSelWordsLayout

set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedVariables false

namespace NearCubicWires.SourceFactorSel.WordsHost
open NearCubicWires LocalBitMultitape ExtDecompositionBatch
open RepairOrdinary RepairOrdinary.RecoveryRootRound RepairRepresentation
open P1Closure SupplierPipeline SupplierEstimator RepairSource RepairSource.CloseoutFinal
open PCJ9eff70d512234a4c_Fixed PCJd4d1d9d7d1fa4313_Production
open PCJc4297ab269d8423a_Source PCJ6fbdd6f776f6447d_Source
noncomputable section
attribute [local irreducible] NearCubicWires.P1TopDownPaidPayload.tapes

structure HostLay (mask : MaskProducer) {selector : CyclicChoice.Laws} {a : DecompositionAlgorithm}
    {printer : WilliamsAlgorithm} (packet : PacketWriter selector a) (rows : RowProducer selector a printer) (V : Nat) where
  maskSlots : Fin (5 + mask.work) → Fin V
  pslots : Fin packet.ordinary.program.tapeCount → Fin V
  slot : Fin 13 → Fin V
  ret : Fin 4 → Fin V
  retDrv : Fin V
  log : Fin V
  familySlots : Fin (rowTapes printer rows.privateWork + 1) → Fin V
  poolSlots : Fin 373 → Fin V
  rewindSlots : Fin 3 → Fin V
  s1 : Fin V
  d1 : Fin V
  l1 : Fin V
  s2 : Fin V
  d2 : Fin V
  l2 : Fin V
  lenTape : Fin V
  F : Nat
  rt : Nat
  sp : Nat
  G : Nat
  R1 : Nat
  descV : Nat
  outV : Nat
  Pc : Nat
  gB : Nat
  wB : Nat
  hG : G = F + rt + 13
  hsp : sp < rt
  hF : 285 < F
  hdesc : descV < R1
  hdesc440 : 440 ≤ descV
  hout0 : outV ≠ 0
  hslot : ∀ j, (slot j).val = G + R1 + 375 + j.val
  hmask : ∀ j, (maskSlots j).val = if j.val = 4 then G + R1 + 375 else G + R1 + 388 + j.val
  hpsl : ∀ j, (pslots j).val = if j.val = outV then G + 262 else if j.val = 0 then G + R1 + 386
    else G + R1 + 393 + mask.work + j.val
  hret : ∀ k, (ret k).val = G + R1 + 393 + mask.work + packet.ordinary.program.tapeCount + k.val
  hretDrv : retDrv.val = G + R1 + 397 + mask.work + packet.ordinary.program.tapeCount
  hlog : log.val = G + R1 + 398 + mask.work + packet.ordinary.program.tapeCount
  hs1 : s1.val = G + R1 + 402 + mask.work + packet.ordinary.program.tapeCount
  hd1 : d1.val = G + R1 + 403 + mask.work + packet.ordinary.program.tapeCount
  hl1 : l1.val = G + R1 + 404 + mask.work + packet.ordinary.program.tapeCount
  hs2 : s2.val = G + R1 + 405 + mask.work + packet.ordinary.program.tapeCount
  hd2 : d2.val = G + R1 + 406 + mask.work + packet.ordinary.program.tapeCount
  hl2 : l2.val = G + R1 + 407 + mask.work + packet.ordinary.program.tapeCount
  hfam : ∀ j, (familySlots j).val = if j.val = descV then F + sp else G + j.val
  hpool : ∀ i, (poolSlots i).val = if i.val = 34 then G else G + R1 + i.val
  hrw1 : (rewindSlots 1).val = 278
  hrw2 : (rewindSlots 2).val = 279
  hlen : lenTape.val = G + R1 + 410 + mask.work + packet.ordinary.program.tapeCount
  
  hgB : G + R1 + 410 + mask.work + packet.ordinary.program.tapeCount + 19 < gB
  hwB : gB ≤ wB

section lay
variable {mask : MaskProducer} {selector : CyclicChoice.Laws} {a : DecompositionAlgorithm} {printer : WilliamsAlgorithm}
  {packet : PacketWriter selector a} {rows : RowProducer selector a printer} {V : Nat}
  (L : HostLay mask packet rows V)

/-- The reserved region's start `B` (= `lenTape`). -/
def HostLay.B : Nat := L.G + L.R1 + 410 + mask.work + packet.ordinary.program.tapeCount
/-- The family bank's end `P0 = G + R1`. -/
def HostLay.P0 : Nat := L.G + L.R1
/-- The packet program's tape count. -/
def HostLay.tc (L : HostLay mask packet rows V) : Nat := packet.ordinary.program.tapeCount

/-- **The target values** (what the words stage writes on the loader layout). -/
def HostLay.IsTgt (v : Nat) : Prop :=
  v = L.P0 + 98 ∨ (L.P0 + 224 ≤ v ∧ v < L.P0 + 227) ∨ (L.P0 + 378 ≤ v ∧ v < L.P0 + 382) ∨
  (L.P0 + 393 + mask.work + L.tc ≤ v ∧ v < L.P0 + 398 + mask.work + L.tc) ∨
  (L.P0 + 402 + mask.work + L.tc ≤ v ∧ v < L.P0 + 404 + mask.work + L.tc) ∨
  (L.P0 + 405 + mask.work + L.tc ≤ v ∧ v < L.P0 + 407 + mask.work + L.tc) ∨ v = L.B

/-- **The nil view** (the `Resident`'s `[]` tapes: `maskSlots j<4`, `slot 1`, `slot 7`, `slot 9..12`). -/
def HostLay.NSv (v : Nat) : Prop :=
  (L.P0 + 388 ≤ v ∧ v < L.P0 + 392) ∨ v = L.P0 + 376 ∨ v = L.P0 + 382 ∨ (L.P0 + 384 ≤ v ∧ v < L.P0 + 388)

def HostLay.Blank (gw : Nat) (v : Nat) : Prop :=
  (L.F ≤ v ∧ v < L.F + L.rt) ∨ (L.G ≤ v ∧ v < L.P0 + 408 + mask.work + L.tc) ∨ v = L.B ∨ (L.wB ≤ v ∧ v < L.wB + gw)

end lay

end
end NearCubicWires.SourceFactorSel.WordsHost

