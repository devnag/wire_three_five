import Proof.SourceAssembly.SourceFactorSelWordsHostWR
import Proof.SourceAssembly.SourceRestIn4

section
set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedVariables false

open NearCubicWires LocalBitMultitape ExtDecompositionBatch
open RepairOrdinary RepairOrdinary.RecoveryRootRound
open RepairRepresentation SupplierEstimator SupplierPipeline SourceInterfaces
open RepairSource.VerifierDecoding
open NearCubicWires.P1Closure
open PCJ9eff70d512234a4c_Fixed PCJd4d1d9d7d1fa4313_Production PCJc4297ab269d8423a_Source
open NearCubicWires.RepairSource NearCubicWires.RepairSource.CloseoutFinal
open NearCubicWires.SourceRequest NearCubicWires.SourceRequest.FactorLoop
open NearCubicWires.SourceConstruction NearCubicWires.SourceConstruction.Rest
open NearCubicWires.SourceFactorSel.Words NearCubicWires.SourceFactorSel.WordsHost
namespace NearCubicWires.SourceFactorSel.AtS
noncomputable section
attribute [local irreducible] NearCubicWires.P1TopDownPaidPayload.tapes

section S
variable (mask : MaskProducer) {selector : CyclicChoice.Laws}
  (packets : PCJc4297ab269d8423a_Source.PacketLibrary selector)
  (rows : PCJc4297ab269d8423a_Source.RowLibrary selector) (sources : EightSources) (res : Nat)
  {gamma : Real} (p : Parameters sources gamma) (k r : Nat)

set_option hygiene false in
local notation "𝔇" => dimsOf mask packets rows sources res p k r

def layS {eX pX gW : Nat} (e : (𝔇).RestExt3 eX pX gW) {V : Nat} (hV : (𝔇).U ≤ V) (gG7 : Nat) :
    HostLay mask (packets (decompositionOf sources)) (rows (decompositionOf sources) (printerOf sources)) V where
  maskSlots := (𝔇).maskSlots hV
  pslots := (𝔇).pslots hV
  slot := (𝔇).slot hV
  ret := (𝔇).ret hV
  retDrv := (𝔇).scr hV 0
  log := (𝔇).scr hV 1
  familySlots := (𝔇).familySlots hV
  poolSlots := (𝔇).poolSlots hV
  rewindSlots := Dims.rewind2Slots e.ext2.ext1.ext hV
  s1 := (𝔇).scr hV 5
  d1 := (𝔇).scr hV 6
  l1 := (𝔇).scr hV 7
  s2 := (𝔇).scr hV 8
  d2 := (𝔇).scr hV 9
  l2 := (𝔇).scr hV 10
  lenTape := Dims.lenTape e.ext2.ext1.ext hV
  F := (𝔇).F
  rt := (𝔇).rt
  sp := (𝔇).sp
  G := (𝔇).G
  R1 := (𝔇).R1
  descV := (𝔇).descV
  outV := (𝔇).outV
  Pc := restPc eX pX gW
  gB := (𝔇).B + 90 + eX + pX
  wB := (𝔇).B + 90 + eX + pX + gG7
  hG := rfl
  hsp := (𝔇).hsp
  hF := e.ext2.ext1.ext.hF
  hdesc := (𝔇).hdesc
  hdesc440 := (𝔇).hdesc440
  hout0 := (𝔇).hout0
  hslot := fun _ => rfl
  hmask := fun _ => rfl
  hpsl := fun _ => rfl
  hret := fun _ => rfl
  hretDrv := by show (𝔇).G + (𝔇).R1 + 397 + (𝔇).w + (𝔇).tc + 0 = (𝔇).G + (𝔇).R1 + 397 + (𝔇).w + (𝔇).tc; omega
  hlog := by show (𝔇).G + (𝔇).R1 + 397 + (𝔇).w + (𝔇).tc + 1 = (𝔇).G + (𝔇).R1 + 398 + (𝔇).w + (𝔇).tc; omega
  hs1 := by show (𝔇).G + (𝔇).R1 + 397 + (𝔇).w + (𝔇).tc + 5 = (𝔇).G + (𝔇).R1 + 402 + (𝔇).w + (𝔇).tc; omega
  hd1 := by show (𝔇).G + (𝔇).R1 + 397 + (𝔇).w + (𝔇).tc + 6 = (𝔇).G + (𝔇).R1 + 403 + (𝔇).w + (𝔇).tc; omega
  hl1 := by show (𝔇).G + (𝔇).R1 + 397 + (𝔇).w + (𝔇).tc + 7 = (𝔇).G + (𝔇).R1 + 404 + (𝔇).w + (𝔇).tc; omega
  hs2 := by show (𝔇).G + (𝔇).R1 + 397 + (𝔇).w + (𝔇).tc + 8 = (𝔇).G + (𝔇).R1 + 405 + (𝔇).w + (𝔇).tc; omega
  hd2 := by show (𝔇).G + (𝔇).R1 + 397 + (𝔇).w + (𝔇).tc + 9 = (𝔇).G + (𝔇).R1 + 406 + (𝔇).w + (𝔇).tc; omega
  hl2 := by show (𝔇).G + (𝔇).R1 + 397 + (𝔇).w + (𝔇).tc + 10 = (𝔇).G + (𝔇).R1 + 407 + (𝔇).w + (𝔇).tc; omega
  hfam := fun _ => rfl
  hpool := fun _ => rfl
  hrw1 := rfl
  hrw2 := rfl
  hlen := rfl
  hgB := by show (𝔇).G + (𝔇).R1 + 410 + (𝔇).w + (𝔇).tc + 19 < (𝔇).B + 90 + eX + pX; unfold Dims.B; omega
  hwB := Nat.le_add_right _ _

/-- W's region fits below the high residents. -/
theorem layS_hN {eX pX gW : Nat} (e : (𝔇).RestExt3 eX pX gW) {V : Nat} (hV : (𝔇).U ≤ V) (gG7 : Nat) (kb : Nat)
    (hroom : gG7 + gwW mask.work (Cold.tapes (decompositionOf sources)) kb ≤ gW) :
    (layS mask packets rows sources res p k r e hV gG7).wB + (nW mask.work (Cold.tapes (decompositionOf sources)) kb - 29) ≤
      (layS mask packets rows sources res p k r e hV gG7).B + 43 + (layS mask packets rows sources res p k r e hV gG7).Pc := by
  have h := nW_eq mask.work (Cold.tapes (decompositionOf sources)) kb
  show (𝔇).B + 90 + eX + pX + gG7 + (nW mask.work (Cold.tapes (decompositionOf sources)) kb - 29) ≤
    (𝔇).B + 43 + restPc eX pX gW
  unfold restPc
  omega

/-- The high residents lie in the universe. -/
theorem layS_hVB {eX pX gW : Nat} (e : (𝔇).RestExt3 eX pX gW) {V : Nat} (hV : (𝔇).U ≤ V) (gG7 : Nat)
    (hres48 : 48 + restPc eX pX gW ≤ (𝔇).res) :
    (layS mask packets rows sources res p k r e hV gG7).B + 48 + (layS mask packets rows sources res p k r e hV gG7).Pc ≤ V := by
  show (𝔇).B + 48 + restPc eX pX gW ≤ V
  have hU : (𝔇).U = (𝔇).B + (𝔇).res := by unfold Dims.U Dims.prepT Dims.B; omega
  omega

end S

end
end NearCubicWires.SourceFactorSel.AtS
end
