import Proof.Packets.SrcMetaProg
import Proof.Packets.SrcMetaIface2

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedSimpArgs false

open NearCubicWires LocalBitMultitape ExtDecompositionBatch
open RepairOrdinary RepairOrdinary.RecoveryRootRound
open RepairRepresentation SupplierEstimator SupplierPipeline SourceInterfaces
open NearCubicWires.P1Closure
open PCJ9eff70d512234a4c_Fixed PCJd4d1d9d7d1fa4313_Production PCJc4297ab269d8423a_Source
open NearCubicWires.RepairSource NearCubicWires.RepairSource.CloseoutFinal
namespace NearCubicWires.SourceStart.MetaRun
open NearCubicWires.SourceBudget NearCubicWires.SourceBudget.Params NearCubicWires.SourceBudget.Pow2
open NearCubicWires.Admission NearCubicWires.SourceConstruction
open NearCubicWires.SourceStart.MetaTM NearCubicWires.SourceStart.MetaWords NearCubicWires.SourceStart.Regs
open NearCubicWires.SourceStart.MetaAsm NearCubicWires.SourceStart.MetaProg
noncomputable section

/-! ## 1. Word facts -/

theorem bitlen_clog (m : ℕ) (hm : 1 ≤ m) : natBitLength m = Nat.clog 2 (m + 1) := by
  unfold natBitLength
  apply le_antisymm
  · have h := Nat.pow_log_le_self 2 (show m ≠ 0 by omega)
    have := (Nat.lt_clog_iff_pow_lt (b := 2) (by norm_num) (x := m + 1) (y := Nat.log 2 m)).mpr (by omega)
    omega
  · apply Nat.clog_le_of_le_pow
    have := Nat.lt_pow_succ_log_self (b := 2) (by norm_num) m
    exact this

theorem natWord_zero : natWord 0 = [true, false, false] := by
  rw [natWord_eq]
  simp [natBitLength, SignedSortKey.binary]

theorem bits_zero : CloseoutRowsCountBinary.bits 0 = [] := by
  simp [CloseoutRowsCountBinary.bits]

theorem wA_le (q L : ℕ) : wA q L ≤ q := by
  unfold wA wU
  exact (Nat.div_le_self _ _).trans ((Nat.sub_le _ _).trans ((Nat.div_le_self _ _).trans (Nat.sub_le _ _)))

theorem deg_le (q L : ℕ) : uniformDeg q L ≤ q := by
  unfold uniformDeg
  exact Nat.div_le_self _ _

theorem finRange_flatMap_getD (l : List (List Bool)) (g : List Bool → List Bool) :
    (List.finRange l.length).flatMap (fun i => g (l.getD i.val [])) = l.flatMap g := by
  have hm : (List.finRange l.length).map (fun i => l.getD i.val []) = l := by
    apply List.ext_getElem (by simp)
    intro i h1 h2
    simp [List.getD_eq_getElem?_getD]
  have h := congrArg (fun l' => l'.flatMap g) hm
  simp only [List.flatMap_map] at h
  exact h

/-! ## 2. The pieces -/

/-- The meta word (decision 80b's caps). -/
def MBof (selector : CyclicChoice.Laws) (s : EightSources) {gamma : Real} (p : Parameters s gamma)
    (packets : PCJc4297ab269d8423a_Source.PacketLibrary selector) (L q : ℕ) : List Bool :=
  SLoad.Setup.metaBits (wA q L) (uniformDeg q L) (COf selector s p q)
    (⟨hFOf2 selector s p L q, cCOf2 selector s p L q, VvOf selector s p L q, rROf2 selector s p packets q⟩ :
      PCJd4d1d9d7d1fa4313_Production.RowCaps)

/-- `C`'s leading ones (`1` in the degenerate case `mC = 0`). -/
def BC (selector : CyclicChoice.Laws) (s : EightSources) {gamma : Real} (p : Parameters s gamma) (cz : Bool) (q : ℕ) : ℕ :=
  if cz then 1 else Nat.clog 2 (Meta.mC selector s p q + 1) + q/4
/-- `C`'s shift zeros. -/
def XC (cz : Bool) (q : ℕ) : ℕ := if cz then 1 else q/4
/-- `Vv`'s leading ones. -/
def BV (selector : CyclicChoice.Laws) (s : EightSources) {gamma : Real} (p : Parameters s gamma) (L : ℕ) (vz : Bool) (q : ℕ) : ℕ :=
  if vz then 1 else Nat.clog 2 (Meta.mV selector s p q + 1) + (q - normalizedLiveCount q L)
/-- `Vv`'s shift zeros. -/
def XV (L : ℕ) (vz : Bool) (q : ℕ) : ℕ := if vz then 1 else q - normalizedLiveCount q L
/-- `cCOf2`'s exponent. -/
def yCC (selector : CyclicChoice.Laws) (s : EightSources) {gamma : Real} (p : Parameters s gamma) (L q : ℕ) : ℕ :=
  max (yA selector s p L q) (yB selector s p q) + 1

/-- **The 25 pieces of `MB`**, in order. -/
def pw (selector : CyclicChoice.Laws) (s : EightSources) {gamma : Real} (p : Parameters s gamma)
    (packets : PCJc4297ab269d8423a_Source.PacketLibrary selector) (L : ℕ) (cz vz : Bool) (q : ℕ) : List (List Bool) :=
  [natWord 3, natWord (wA q L), natWord (uniformDeg q L),
   List.replicate (BC selector s p cz q) true, [false], List.replicate (XC cz q) false, CloseoutRowsCountBinary.bits (Meta.mC selector s p q),
   natWord 4 ++ [true],
   List.replicate (yH selector s p L q) true, [false], List.replicate (yH selector s p L q) false, [true, true],
   List.replicate (yCC selector s p L q) true, [false], List.replicate (yCC selector s p L q) false, [true],
   List.replicate (BV selector s p L vz q) true, [false], List.replicate (XV L vz q) false, CloseoutRowsCountBinary.bits (Meta.mV selector s p q),
   [true], List.replicate (yR selector s p packets q) true, [false], List.replicate (yR selector s p packets q) false, [true]]

def pwF (selector : CyclicChoice.Laws) (s : EightSources) {gamma : Real} (p : Parameters s gamma)
    (packets : PCJc4297ab269d8423a_Source.PacketLibrary selector) (L : ℕ) (cz vz : Bool) (q : ℕ) (k : Fin 25) : List Bool :=
  (pw selector s p packets L cz vz q).getD k.val []

theorem bdC (selector : CyclicChoice.Laws) (s : EightSources) {gamma : Real} (p : Parameters s gamma) (cz : Bool) (q : ℕ)
    (hcz : cz = true ↔ Meta.mC selector s p q = 0) :
    bd (natWord (COf selector s p q)) = bd (List.replicate (BC selector s p cz q) true) ++ bd [false] ++
      bd (List.replicate (XC cz q) false) ++ bd (CloseoutRowsCountBinary.bits (Meta.mC selector s p q)) := by
  rw [Meta.COf_eq]
  cases cz with
  | true =>
    have h0 := hcz.mp rfl
    rw [h0, zero_mul, natWord_zero, bits_zero]
    simp [BC, XC, bd, body, dat]
  | false =>
    have h1 : 1 ≤ Meta.mC selector s p q := Nat.one_le_iff_ne_zero.mpr (fun h => absurd (hcz.mpr h) (by simp))
    rw [bd_shift _ _ h1, bitlen_clog _ h1]
    simp [BC, XC]

theorem bdV (selector : CyclicChoice.Laws) (s : EightSources) {gamma : Real} (p : Parameters s gamma) (L : ℕ) (vz : Bool) (q : ℕ)
    (hvz : vz = true ↔ Meta.mV selector s p q = 0) :
    bd (natWord (VvOf selector s p L q)) = bd (List.replicate (BV selector s p L vz q) true) ++ bd [false] ++
      bd (List.replicate (XV L vz q) false) ++ bd (CloseoutRowsCountBinary.bits (Meta.mV selector s p q)) := by
  rw [Meta.VvOf_eq]
  cases vz with
  | true =>
    have h0 := hvz.mp rfl
    rw [h0, zero_mul, natWord_zero, bits_zero]
    simp [BV, XV, bd, body, dat]
  | false =>
    have h1 : 1 ≤ Meta.mV selector s p q := Nat.one_le_iff_ne_zero.mpr (fun h => absurd (hvz.mpr h) (by simp))
    rw [bd_shift _ _ h1, bitlen_clog _ h1]
    simp [BV, XV]

theorem bdP (y : ℕ) : bd (natWord (2^y)) =
    bd [true] ++ bd (List.replicate y true) ++ bd [false] ++ bd (List.replicate y false) ++ bd [true] := by
  rw [bd_pow2, List.replicate_succ]
  simp only [bd, ← body_append, List.cons_append, List.nil_append, List.append_assoc]

/-- **`frame MB` from the pieces.** -/
theorem pieces_frame (selector : CyclicChoice.Laws) (s : EightSources) {gamma : Real} (p : Parameters s gamma)
    (packets : PCJc4297ab269d8423a_Source.PacketLibrary selector) (L : ℕ) (cz vz : Bool) (q : ℕ)
    (hcz : cz = true ↔ Meta.mC selector s p q = 0) (hvz : vz = true ↔ Meta.mV selector s p q = 0) :
    (List.finRange 25).flatMap (fun i => body false (pwF selector s p packets L cz vz q i)) ++ [false] =
      RepairOrdinary.frame (MBof selector s p packets L q) := by
  have e := finRange_flatMap_getD (pw selector s p packets L cz vz q) (body false)
  rw [show (pw selector s p packets L cz vz q).length = 25 from rfl] at e
  unfold pwF
  rw [e, MBof, meta_frame, bdC selector s p cz q hcz, bdV selector s p L vz q hvz]
  unfold hFOf2 cCOf2 rROf2
  rw [bdP, bdP, bdP]
  simp only [pw, yCC, List.flatMap_cons, List.flatMap_nil, List.append_nil, bd, body_append, List.append_assoc]
  rfl

/-! ## 3. The pipeline stage -/

variable {selector : CyclicChoice.Laws} {s : EightSources} {gamma : Real} {p : Parameters s gamma}
  {packets : PCJc4297ab269d8423a_Source.PacketLibrary selector} {L : ℕ}

/-- The pipeline's thirteen ports, in the order of registers `0..12`. -/
def vports (V : Meta.MetaVals2 selector s p packets L) : List (Fin V.NP) :=
  [V.iq, V.iK, V.oW, V.oD, V.oX, V.oXK, V.oM, V.oB, V.oH, V.oC, V.oMV, V.oBV, V.oR]

theorem idx_lt (V : Meta.MetaVals2 selector s p packets L) (j : Fin V.NP) (h : j ∈ vports V) : (vports V).idxOf j < 13 :=
  List.idxOf_lt_length_iff.mpr h

/-- Port `j` is register `idxOf j`; the pipeline's other tapes are scratch. -/
def nmV (V : Meta.MetaVals2 selector s p packets L) {NL : ℕ} (hNL : 13 ≤ NL) (j : Fin V.NP) : Option (Fin NL) :=
  if h : j ∈ vports V then some ⟨(vports V).idxOf j, by have := idx_lt V j h; omega⟩ else none

/-! ## 4. The program -/

/-- A register of the program's universe. -/
def rg (V : Meta.MetaVals2 selector s p packets L) (i : ℕ) (h : i < 41 := by decide) : Fin (191 + V.NP) := ⟨i, by omega⟩

/-- **The meta program** (ONE fixed machine; `cz`/`vz` select the degenerate `mC = 0` / `mV = 0` sources, fixed before any input). -/
def progM (V : Meta.MetaVals2 selector s p packets L) (cz vz : Bool) :=
  Composition.machine (Composition.machine (Composition.machine (Composition.machine (Composition.machine (Composition.machine (Composition.machine (Composition.machine (Composition.machine (Composition.machine (Composition.machine (Composition.machine (Composition.machine (Composition.machine (Composition.machine (Composition.machine (Composition.machine (Composition.machine (Composition.machine (Composition.machine (Composition.machine (Composition.machine (Composition.machine (Composition.machine (Composition.machine (Composition.machine (Composition.machine (Composition.machine (RecoveryFocus.machine (nslot (nmV V (by omega : 13 ≤ 191 + V.NP)) 41 (by omega)) V.machine)
    (fixM ([true]) (rg V 15) (41 + V.NP + 0) (by omega)))
    (fixM (RepairOrdinary.frame (natWord 3)) (rg V 16) (41 + V.NP + 2) (by omega)))
    (natM (rg V 2) (rg V 17) (41 + V.NP + 4) (by omega)))
    (natM (rg V 3) (rg V 18) (41 + V.NP + 26) (by omega)))
    (fruM (if cz then rg V 15 else rg V 7) (rg V 19) (41 + V.NP + 48) (by omega)))
    (fixM (RepairOrdinary.frame [false]) (rg V 20) (41 + V.NP + 51) (by omega)))
    (zerM (if cz then rg V 15 else rg V 4) (rg V 21) (41 + V.NP + 53) (by omega)))
    (cntM (rg V 6) (rg V 22) (41 + V.NP + 56) (by omega)))
    (fixM (RepairOrdinary.frame (natWord 4 ++ [true])) (rg V 23) (41 + V.NP + 66) (by omega)))
    (fruM (rg V 8) (rg V 24) (41 + V.NP + 68) (by omega)))
    (fixM (RepairOrdinary.frame [false]) (rg V 25) (41 + V.NP + 71) (by omega)))
    (zerM (rg V 8) (rg V 26) (41 + V.NP + 73) (by omega)))
    (fixM (RepairOrdinary.frame [true, true]) (rg V 27) (41 + V.NP + 76) (by omega)))
    (fruM (rg V 9) (rg V 28) (41 + V.NP + 78) (by omega)))
    (fixM (RepairOrdinary.frame [false]) (rg V 29) (41 + V.NP + 81) (by omega)))
    (zerM (rg V 9) (rg V 30) (41 + V.NP + 83) (by omega)))
    (fixM (RepairOrdinary.frame [true]) (rg V 31) (41 + V.NP + 86) (by omega)))
    (fruM (if vz then rg V 15 else rg V 11) (rg V 32) (41 + V.NP + 88) (by omega)))
    (fixM (RepairOrdinary.frame [false]) (rg V 33) (41 + V.NP + 91) (by omega)))
    (zerM (if vz then rg V 15 else rg V 5) (rg V 34) (41 + V.NP + 93) (by omega)))
    (cntM (rg V 10) (rg V 35) (41 + V.NP + 96) (by omega)))
    (fixM (RepairOrdinary.frame [true]) (rg V 36) (41 + V.NP + 106) (by omega)))
    (fruM (rg V 12) (rg V 37) (41 + V.NP + 108) (by omega)))
    (fixM (RepairOrdinary.frame [false]) (rg V 38) (41 + V.NP + 111) (by omega)))
    (zerM (rg V 12) (rg V 39) (41 + V.NP + 113) (by omega)))
    (fixM (RepairOrdinary.frame [true]) (rg V 40) (41 + V.NP + 116) (by omega)))
    (phAM 25 16 (by omega) (rg V 13) (41 + V.NP + 118) (by omega)))
    (phBM (rg V 13) (rg V 14) (41 + V.NP + 146) (by omega))

/-- Its cost. -/
def progCost (V : Meta.MetaVals2 selector s p packets L) (cz vz : Bool) (q : ℕ) : ℕ :=
  (((((((((((((((((((((((((((V.cost q + 1 + (2*([true]).length+2)) + 1 + (2*(RepairOrdinary.frame (natWord 3)).length+2)) + 1 + CloseoutRowsEstimatorParity.Natural.budget (wA q L)) + 1 + CloseoutRowsEstimatorParity.Natural.budget (uniformDeg q L)) + 1 + (2*(2*(BC selector s p cz q)+1)+2)) + 1 + (2*(RepairOrdinary.frame [false]).length+2)) + 1 + (2*(2*(XC cz q)+1)+2)) + 1 + CloseoutRowsCountBinary.budget (Meta.mC selector s p q)) + 1 + (2*(RepairOrdinary.frame (natWord 4 ++ [true])).length+2)) + 1 + (2*(2*(yH selector s p L q)+1)+2)) + 1 + (2*(RepairOrdinary.frame [false]).length+2)) + 1 + (2*(2*(yH selector s p L q)+1)+2)) + 1 + (2*(RepairOrdinary.frame [true, true]).length+2)) + 1 + (2*(2*(yCC selector s p L q)+1)+2)) + 1 + (2*(RepairOrdinary.frame [false]).length+2)) + 1 + (2*(2*(yCC selector s p L q)+1)+2)) + 1 + (2*(RepairOrdinary.frame [true]).length+2)) + 1 + (2*(2*(BV selector s p L vz q)+1)+2)) + 1 + (2*(RepairOrdinary.frame [false]).length+2)) + 1 + (2*(2*(XV L vz q)+1)+2)) + 1 + CloseoutRowsCountBinary.budget (Meta.mV selector s p q)) + 1 + (2*(RepairOrdinary.frame [true]).length+2)) + 1 + (2*(2*(yR selector s p packets q)+1)+2)) + 1 + (2*(RepairOrdinary.frame [false]).length+2)) + 1 + (2*(2*(yR selector s p packets q)+1)+2)) + 1 + (2*(RepairOrdinary.frame [true]).length+2)) + 1 + costA 25 (pwF selector s p packets L cz vz q)) + 1 + (2*((2*(MBof selector s p packets L q).length+1) + 1 + (2*0+1)) + 2)

end
end NearCubicWires.SourceStart.MetaRun

