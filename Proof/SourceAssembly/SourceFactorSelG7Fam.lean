import Proof.SourceAssembly.SourceFactorSelItem4AtS
import Proof.SourceAssembly.SourceRequestSelDockSym
import Proof.Packets.SrcStartBankInst

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
open NearCubicWires.SourceFactorSel.Words NearCubicWires.SourceFactorSel.WordsHost NearCubicWires.SourceFactorSel.AtS
namespace NearCubicWires.SourceFactorSel.G7Fam
noncomputable section
attribute [local irreducible] NearCubicWires.P1TopDownPaidPayload.tapes

/-! ## 1. The loop and the words-stage sources without the producer's PCPP -/

def cs (t : Nat) (i : Fin 4) (j : Fin t) : Fin (19 + 4 * t) :=
  ⟨19 + i.val * t + j.val, by
    have hi := i.isLt
    have hj := j.isLt
    have h := Nat.mul_le_mul_right t (show i.val + 1 ≤ 4 by omega)
    rw [Nat.succ_mul] at h
    omega⟩

def fs (t : Nat) (oN oS oT : Fin t) (j : Fin 31) : Fin (19 + 4 * t) :=
  if h0 : j.val = 0 then ⟨0, by omega⟩
  else if h1 : j.val < 5 then cs t ⟨j.val - 1, by omega⟩ oN
  else if h2 : j.val < 9 then cs t ⟨j.val - 5, by omega⟩ oS
  else if h3 : j.val < 13 then cs t ⟨j.val - 9, by omega⟩ oT
  else ⟨j.val - 12, by omega⟩

/-- **The factor loop from the producer's machine and output ports.** -/
def loopOf {t s : Nat} (M : Machine t s) (oN oS oT : Fin t) :=
  Composition.machine (RecoveryFocus.machine (cs t 0) M)
    (Composition.machine (RecoveryFocus.machine (cs t 1) M)
      (Composition.machine (RecoveryFocus.machine (cs t 2) M)
        (Composition.machine (RecoveryFocus.machine (cs t 3) M)
          (RecoveryFocus.machine (fs t oN oS oT) NearCubicWires.SourceRequest.Fields.machine))))

/-- **A family member from its three pieces**, generic in the producer's tape count (a closed numeral tape count here makes the kernel's
type check of the docked loop time out, so each mode instantiates this definition instead). -/
def memberOf {V t sS sL sW : Nat} (selM : Machine V sS) (M : Machine t sL) (oN oS oT : Fin t)
    (reg : Fin (19 + 4 * t) → Fin V) (W : Machine V sW) :=
  Composition.machine selM (Composition.machine (RecoveryFocus.machine reg (loopOf M oN oS oT)) W)

section pcpp
variable {q : Nat} {circuit : BooleanCircuit q} {pcpp : PointwisePCPP circuit} {mode : Bool} {a : DecompositionAlgorithm}

def srcOfT (t : Nat) (oN oS oT : Fin t) {V : Nat} (reg : Fin (19 + 4 * t) → Fin V) : Fin 6 → Fin V :=
  fun i => reg (fs t oN oS oT (srcIdx i))

end pcpp

/-! ## 2. The family -/

section S
variable (mask : MaskProducer) {selector : CyclicChoice.Laws}
  (packets : PCJc4297ab269d8423a_Source.PacketLibrary selector)
  (rows : PCJc4297ab269d8423a_Source.RowLibrary selector) (sources : EightSources) (res : Nat)
  {gamma : Real} (p : Parameters sources gamma) (k r : Nat)

set_option hygiene false in
local notation "𝔇" => dimsOf mask packets rows sources res p k r

/-- The start bank's scratch count (`kOf a = 194`). -/
abbrev kb (sources : EightSources) : Nat := NearCubicWires.SourceStart.Bank.kOf (decompositionOf sources)

theorem res48 {eX pX gW : Nat} (hres : 49 + restPc eX pX gW ≤ (𝔇).res) : 48 + restPc eX pX gW ≤ (𝔇).res := by omega

def wM {eX pX gW : Nat} (e : (𝔇).RestExt3 eX pX gW) {V : Nat} (hV : (𝔇).U ≤ V) (gG7 : Nat)
    (hroom : gG7 + gwW mask.work (Cold.tapes (decompositionOf sources)) (kb sources) ≤ gW)
    (hres : 49 + restPc eX pX gW ≤ (𝔇).res) (src : Fin 6 → Fin V) :=
  wordsHostM (layS mask packets rows sources res p k r e hV gG7) (NearCubicWires.SourceStart.Bank.sb (decompositionOf sources)) src
    ((layS mask packets rows sources res p k r e hV gG7).hostV_lt _
      (layS_hN mask packets rows sources res p k r e hV gG7 (kb sources) hroom)
      (layS_hVB mask packets rows sources res p k r e hV gG7 (res48 mask packets rows sources res p k r hres)))

/-- **The THR member** (mode `false`). -/
def thrM {eX pX gW : Nat} (e : (𝔇).RestExt3 eX pX gW) {V : Nat} (hV : (𝔇).U ≤ V) (gG7 : Nat)
    (cacheT : Fin 19 → Fin V) (terminal : Fin V) (hres : 49 + restPc eX pX gW ≤ (𝔇).res)
    (hN : SelFront.NF + (19 + 4 * SelLocal.tT (decompositionOf sources)) ≤ gW)
    (hroom : gG7 + gwW mask.work (Cold.tapes (decompositionOf sources)) (kb sources) ≤ gW) (ph : CloseoutRowsOriginalSchedule.Phase) :=
  memberOf (RecoveryFocus.machine (SelLocal.gS e hV (decompositionOf sources) cacheT terminal hres hN)
      (SelLocal.selThrM ph (decompositionOf sources)))
    (ThrSwitch.machine (decompositionOf sources)) (ThrSwitch.outN (decompositionOf sources))
    (ThrSwitch.outS (decompositionOf sources)) (ThrSwitch.outT (decompositionOf sources))
    (fun x => SelLocal.gS e hV (decompositionOf sources) cacheT terminal hres hN (Fin.natAdd SelFront.NF x))
    (wM mask packets rows sources res p k r e hV gG7 hroom hres
      (srcOfT (SelLocal.tT (decompositionOf sources)) (ThrSwitch.outN (decompositionOf sources))
        (ThrSwitch.outS (decompositionOf sources)) (ThrSwitch.outT (decompositionOf sources))
        (fun x => SelLocal.gS e hV (decompositionOf sources) cacheT terminal hres hN (Fin.natAdd SelFront.NF x))))

/-- **The SYM member** (mode `true`). -/
def symM {eX pX gW : Nat} (e : (𝔇).RestExt3 eX pX gW) {V : Nat} (hV : (𝔇).U ≤ V) (gG7 : Nat)
    (cacheT : Fin 19 → Fin V) (terminal : Fin V) (hres : 49 + restPc eX pX gW ≤ (𝔇).res)
    (hN : SelFront.NF + (19 + 4 * SelLocal.tS) ≤ gW)
    (hroom : gG7 + gwW mask.work (Cold.tapes (decompositionOf sources)) (kb sources) ≤ gW) (ph : CloseoutRowsOriginalSchedule.Phase) :=
  memberOf (RecoveryFocus.machine (SelLocal.gSS e hV (decompositionOf sources) cacheT terminal hres hN) (SelLocal.selSymM ph))
    SymSwitch.machine SymSwitch.outN SymSwitch.outS SymSwitch.outT
    (fun x => SelLocal.gSS e hV (decompositionOf sources) cacheT terminal hres hN (Fin.natAdd SelFront.NF x))
    (wM mask packets rows sources res p k r e hV gG7 hroom hres
      (srcOfT SelLocal.tS SymSwitch.outN SymSwitch.outS SymSwitch.outT
        (fun x => SelLocal.gSS e hV (decompositionOf sources) cacheT terminal hres hN (Fin.natAdd SelFront.NF x))))

def g7At {eX pX gW : Nat} (e : (𝔇).RestExt3 eX pX gW) {V : Nat} (hV : (𝔇).U ≤ V) (gG7 : Nat)
    (cacheT : Bool → Fin 19 → Fin V) (terminal : Fin V) (hres : 49 + restPc eX pX gW ≤ (𝔇).res)
    (hNT : SelFront.NF + (19 + 4 * SelLocal.tT (decompositionOf sources)) ≤ gW) (hNS : SelFront.NF + (19 + 4 * SelLocal.tS) ≤ gW)
    (hroom : gG7 + gwW mask.work (Cold.tapes (decompositionOf sources)) (kb sources) ≤ gW) :
    Bool → CloseoutRowsOriginalSchedule.Phase → Σ s, Machine V s
  | false, ph => ⟨_, thrM mask packets rows sources res p k r e hV gG7 (cacheT false) terminal hres hNT hroom ph⟩
  | true, ph => ⟨_, symM mask packets rows sources res p k r e hV gG7 (cacheT true) terminal hres hNS hroom ph⟩

/-! ## 3. The bridge to `AtS.hG7_of` -/

end S

end
end NearCubicWires.SourceFactorSel.G7Fam
end

