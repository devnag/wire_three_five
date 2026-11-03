import Proof.SourceAssembly.SourceRequestSymOriginal
import Proof.SourceAssembly.SourceRequestSymParity

set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedVariables false
open NearCubicWires LocalBitMultitape ExtDecompositionBatch RepairOrdinary RepairRepresentation
open RecoveryRootRound RepairSource.VerifierDecoding RepairSource.ProjectionNormalization
open SupplierPipeline CanonicalWitnessCodec RadixSemantics SourceInterfaces CompilerSemantics
noncomputable section

namespace NearCubicWires.SourceRequest.SymSwitch
open PCJd4d1d9d7d1fa4313_Production
open PCJ6e421fabe2aa4155_SourceSymmetricMeaning (bitmap)
open ThrSwitch (install_pull read_true read_blank stop_step frame_nil_pad sysDescAt origDescAt)

/-! ## Layout -/

def origVal (j : Nat) : Nat :=
  if j = 1711 then 177 else if j = 3419 then 351 else if j = 3421 then 353 else 354 + j

def sysSlot (j : Fin 354) : Fin 3778 := ⟨j.val, by omega⟩
def origSlot (j : Fin 3422) : Fin 3778 := ⟨origVal j.val, by have := j.isLt; unfold origVal; split_ifs <;> omega⟩

theorem sysSlot_inj : Function.Injective sysSlot := by
  intro i j h
  have hv : (sysSlot i).val = (sysSlot j).val := congrArg Fin.val h
  exact Fin.ext hv

theorem origSlot_inj : Function.Injective origSlot := by
  intro i j h
  have hv : origVal i.val = origVal j.val := congrArg Fin.val h
  have hi := i.isLt
  have hj := j.isLt
  apply Fin.ext
  unfold origVal at hv
  split_ifs at hv <;> omega

def flagS : Fin 3778 := ⟨3776, by omega⟩
def flagO : Fin 3778 := ⟨3777, by omega⟩

def descVal (k : Nat) : Nat :=
  if k < 4 then SymSystematic.descVal k else if k < 14 then 354 + SymOriginal.descVal (k - 4) else 3776 + (k - 14)

theorem sysDesc_range (k : Nat) :
    SymSystematic.descVal k = 3 ∨ SymSystematic.descVal k = 13 ∨ SymSystematic.descVal k = 182 ∨
      SymSystematic.descVal k = 192 := by
  unfold SymSystematic.descVal
  split_ifs <;> simp

theorem origDesc_range (k : Nat) :
    (1 ≤ SymOriginal.descVal k ∧ SymOriginal.descVal k ≤ 1699) ∨
      (1714 ≤ SymOriginal.descVal k ∧ SymOriginal.descVal k ≤ 3412) := by
  have r1 := ThrOriginal.posVal_range k
  have r2 := ThrOriginal.posVal_range (k - 5)
  unfold SymOriginal.descVal
  split_ifs
  · exact Or.inl r1
  · exact Or.inr ⟨by omega, by omega⟩

theorem origDesc_val (k : Nat) : origVal (SymOriginal.descVal k) = 354 + SymOriginal.descVal k := by
  have hr := origDesc_range k
  unfold origVal
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]

def descSlots (k : Fin 16) : Fin 3778 :=
  ⟨descVal k.val, by
    have hk := k.isLt
    have r1 := sysDesc_range k.val
    have r2 := origDesc_range (k.val - 4)
    unfold descVal; split_ifs <;> omega⟩

theorem descSlots_inj : Function.Injective descSlots := by
  intro i j h
  have hv : descVal i.val = descVal j.val := congrArg Fin.val h
  have hi := i.isLt
  have hj := j.isLt
  have s1 := sysDesc_range i.val
  have s2 := sysDesc_range j.val
  have o1 := origDesc_range (i.val - 4)
  have o2 := origDesc_range (j.val - 4)
  apply Fin.ext
  unfold descVal at hv
  split_ifs at hv with h1 h2 h3 h4 h5 h6 h7
  · have e := congrArg Fin.val (SymSystematic.descSlots_inj (a₁ := ⟨i.val, h1⟩) (a₂ := ⟨j.val, h2⟩) (Fin.ext hv))
    exact e
  all_goals first
    | omega
    | (have e := congrArg Fin.val (SymOriginal.descSlots_inj (a₁ := ⟨i.val - 4, by omega⟩)
          (a₂ := ⟨j.val - 4, by omega⟩) (Fin.ext (by
            show SymOriginal.descVal (i.val - 4) = SymOriginal.descVal (j.val - 4)
            omega)))
       simp only at e
       omega)

def sysIdx (k : Fin 4) : Fin 16 := ⟨k.val, by omega⟩
def origIdx (k : Fin 10) : Fin 16 := ⟨k.val + 4, by omega⟩

theorem sys_he (k : Fin 4) : descSlots (sysIdx k) = sysSlot (SymSystematic.descSlots k) := by
  apply Fin.ext
  show descVal k.val = SymSystematic.descVal k.val
  unfold descVal
  rw [if_pos k.isLt]

theorem sys_cov (k : Fin 16) (j : Fin 354) (h : descSlots k = sysSlot j) :
    ∃ k', SymSystematic.descSlots k' = j := by
  have hv : descVal k.val = j.val := congrArg Fin.val h
  have hj := j.isLt
  have hk := k.isLt
  have o := origDesc_range (k.val - 4)
  by_cases h4 : k.val < 4
  · refine ⟨⟨k.val, h4⟩, Fin.ext ?_⟩
    show SymSystematic.descVal k.val = j.val
    rw [← hv]
    unfold descVal
    rw [if_pos h4]
  · exfalso
    unfold descVal at hv
    rw [if_neg h4] at hv
    split_ifs at hv <;> omega

theorem orig_he (k : Fin 10) : descSlots (origIdx k) = origSlot (SymOriginal.descSlots k) := by
  apply Fin.ext
  show descVal (k.val + 4) = origVal (SymOriginal.descVal k.val)
  rw [origDesc_val]
  unfold descVal
  rw [if_neg (by omega), if_pos (by omega), show k.val + 4 - 4 = k.val by omega]

theorem orig_cov (k : Fin 16) (j : Fin 3422) (h : descSlots k = origSlot j) :
    ∃ k', SymOriginal.descSlots k' = j := by
  have hv : descVal k.val = origVal j.val := congrArg Fin.val h
  have hj := j.isLt
  have hk := k.isLt
  have sr := sysDesc_range k.val
  have o := origDesc_range (k.val - 4)
  by_cases h4 : k.val < 4
  · exfalso
    unfold descVal origVal at hv
    rw [if_pos h4] at hv
    split_ifs at hv <;> omega
  · by_cases h14 : k.val < 14
    · refine ⟨⟨k.val - 4, by omega⟩, Fin.ext ?_⟩
      show SymOriginal.descVal (k.val - 4) = j.val
      unfold descVal at hv
      rw [if_neg h4, if_pos h14] at hv
      unfold origVal at hv
      split_ifs at hv <;> omega
    · exfalso
      unfold descVal origVal at hv
      rw [if_neg h4, if_neg h14] at hv
      split_ifs at hv <;> omega

/-! ## The producer -/

section producer
open SupplierEstimator NearCubicWires.RepairSource NearCubicWires.RepairSource.CloseoutFinal
variable {q : Nat} {circuit : BooleanCircuit q} {pcpp : PointwisePCPP circuit}

/-- What factor selection writes for a SYM-mode slot holding `o`. -/
def descAt (P W L : Nat) : Option (C10TotalDecode.Atom pcpp) → Nat → List Bool
  | none, _ => []
  | some (.systematic idx), n =>
      if n < 4 then sysDescAt (q := q) (bitmap (pcpp.systematicSupport idx)) n
      else if n = 14 then [true] else []
  | some (.symmetric c), n =>
      if n < 4 then [] else if n < 14 then origDescAt (q := q) P W L (SymOriginal.symCodeBits L c) (n - 4)
      else if n = 15 then [true] else []
  | some (.threshold _), _ => []

def ok (P W L : Nat) : Option (C10TotalDecode.Atom pcpp) → Prop
  | none => True
  | some (.systematic _) => True
  | some (.symmetric c) =>
      4 ≤ L ∧ c.descriptionBits ≤ L ∧ c.wireCount ≤ W ∧
        CloseoutRowsCircuitCapacity.capacity (SymOriginal.symCodeWidth L) ≤ P
  | some (.threshold _) => False

def cost (P L : Nat) : Option (C10TotalDecode.Atom pcpp) → Nat
  | none => 0 + 2 + 2
  | some (.systematic idx) => SymSystematic.cost (pcpp.systematicSupport idx) + 2
  | some (.symmetric c) => SymOriginal.cost c P (SymOriginal.symCodeBits L c) + 2 + 2
  | some (.threshold _) => 0

def sysM := RecoveryFocus.machine sysSlot SymSystematic.machine
def origM := RecoveryFocus.machine origSlot SymOriginal.machine
def inner := CloseoutRowsOriginalSwitch.machine origM (CloseoutRowsOriginalSwitch.stop 3778) flagO
/-- The SYM kind switch: flag S → parity; else flag O → original; else stop. -/
def machine := CloseoutRowsOriginalSwitch.machine sysM inner flagS

def outN : Fin 3778 := ⟨177, by omega⟩
def outS : Fin 3778 := ⟨351, by omega⟩
def outT : Fin 3778 := ⟨353, by omega⟩

theorem outN_sys : outN = sysSlot SymSystematic.outN := rfl
theorem outS_sys : outS = sysSlot SymSystematic.outS := rfl
theorem outT_sys : outT = sysSlot SymSystematic.outT := rfl
theorem outN_orig : outN = origSlot SymOriginal.outN := rfl
theorem outS_orig : outS = origSlot SymOriginal.outS := rfl
theorem outT_orig : outT = origSlot SymOriginal.outT := rfl

theorem flagS_desc : flagS = descSlots 14 := rfl
theorem flagO_desc : flagO = descSlots 15 := rfl

theorem out_blank (x : Fin 3778) (hx : x.val = 177 ∨ x.val = 351 ∨ x.val = 353) : ∀ k, descSlots k ≠ x := by
  intro k e
  have hv : descVal k.val = x.val := congrArg Fin.val e
  have hk := k.isLt
  have sr := sysDesc_range k.val
  have o := origDesc_range (k.val - 4)
  unfold descVal at hv
  split_ifs at hv <;> omega

/-- **The SYM-mode factor producer**: the kind switch over the SYM parity and original producers. -/
theorem run (a : DecompositionAlgorithm) (P W L : Nat) (o : Option (C10TotalDecode.Atom pcpp)) (R : Nat)
    (hok : ok P W L o) (hR : 1 ≤ R) :
    ∃ A' : Fin 3778 → List Bool,
      Step machine (cost P L o) (fun _ => 0)
        (install descSlots (fun _ => List.replicate R false)
          (fun k => ZeroPadding.pad R (descAt P W L o k.val)))
        (fun _ => 0) A' ∧
      A' outN = ZeroPadding.pad R (RepairOrdinary.frame (FactorLoop.segN true o)) ∧
      A' outS = ZeroPadding.pad R (RepairOrdinary.frame (FactorLoop.segS true o)) ∧
      A' outT = ZeroPadding.pad R (RepairOrdinary.frame (FactorLoop.segT a true o)) := by
  set Ab := install descSlots (fun _ => List.replicate R false)
    (fun k => ZeroPadding.pad R (descAt P W L o k.val)) with hAb
  have fS : Ab flagS = ZeroPadding.pad R (descAt P W L o 14) := by
    rw [flagS_desc, hAb, install_slot _ descSlots_inj]
    rfl
  have fO : Ab flagO = ZeroPadding.pad R (descAt P W L o 15) := by
    rw [flagO_desc, hAb, install_slot _ descSlots_inj]
    rfl
  have blank : ∀ x : Fin 3778, (x.val = 177 ∨ x.val = 351 ∨ x.val = 353) →
      Ab x = List.replicate R false := fun x hx => by
    rw [hAb, install_other _ _ _ _ (out_blank x hx)]
  match o, hok with
  | none, _ =>
    have hs := CloseoutRowsOriginalSwitch.false_run sysM inner flagS
      (CloseoutRowsOriginalSwitch.false_run origM (CloseoutRowsOriginalSwitch.stop 3778)
        flagO (stop_step (fun _ => 0) Ab) (by rw [fO]; exact read_blank R)) (by rw [fS]; exact read_blank R)
    refine ⟨Ab, hs, ?_, ?_, ?_⟩
    · rw [blank _ (Or.inl rfl)]; exact frame_nil_pad R hR
    · rw [blank _ (Or.inr (Or.inl rfl))]; exact frame_nil_pad R hR
    · rw [blank _ (Or.inr (Or.inr rfl))]; exact frame_nil_pad R hR
  | some (.systematic idx), _ =>
    obtain ⟨F, hF, hN, hS, hT⟩ := SymSystematic.produce (pcpp := pcpp) a idx R hR
    have dk := hF.dock sysSlot sysSlot_inj (fun _ => 0) Ab (fun _ => rfl) (fun j => by
      rw [hAb, install_pull descSlots descSlots_inj sysSlot SymSystematic.descSlots
        SymSystematic.descSlots_inj sysIdx sys_he sys_cov]
      congr 1
      funext k
      show ZeroPadding.pad R (if k.val < 4 then sysDescAt (q := q) (bitmap (pcpp.systematicSupport idx)) k.val
        else if k.val = 14 then [true] else []) = _
      rw [if_pos k.isLt]
      rfl)
    rw [ThrSystematic.zeroH] at dk
    have hs := CloseoutRowsOriginalSwitch.true_run sysM inner flagS dk (by rw [fS]; exact read_true R)
    refine ⟨_, hs, ?_, ?_, ?_⟩
    · rw [outN_sys, install_slot _ sysSlot_inj, hN]
    · rw [outS_sys, install_slot _ sysSlot_inj, hS]
    · rw [outT_sys, install_slot _ sysSlot_inj, hT]
  | some (.symmetric c), ⟨h4, hL, hW, hcap⟩ =>
    obtain ⟨F, hF, hN, hS, hT⟩ := SymOriginal.produce (pcpp := pcpp) a c P W L (SymOriginal.symCodeBits L c)
      (by rw [SymOriginal.symCodeBits_length]; exact hcap) (SymOriginal.symCodeBits_decode L c h4 hL) hW hL R hR
    have dk := hF.dock origSlot origSlot_inj (fun _ => 0) Ab (fun _ => rfl) (fun j => by
      rw [hAb, install_pull descSlots descSlots_inj origSlot SymOriginal.descSlots
        SymOriginal.descSlots_inj origIdx orig_he orig_cov]
      congr 1
      funext k
      show ZeroPadding.pad R (if k.val + 4 < 4 then [] else if k.val + 4 < 14 then
        origDescAt (q := q) P W L (SymOriginal.symCodeBits L c) (k.val + 4 - 4)
        else if k.val + 4 = 15 then [true] else []) = _
      rw [if_neg (by omega), if_pos (by omega), show k.val + 4 - 4 = k.val by omega]
      rfl)
    rw [ThrSystematic.zeroH] at dk
    have hs := CloseoutRowsOriginalSwitch.false_run sysM inner flagS
      (CloseoutRowsOriginalSwitch.true_run origM (CloseoutRowsOriginalSwitch.stop 3778) flagO dk
        (by rw [fO]; exact read_true R)) (by rw [fS]; exact read_blank R)
    refine ⟨_, hs, ?_, ?_, ?_⟩
    · rw [outN_orig, install_slot _ origSlot_inj, hN]
    · rw [outS_orig, install_slot _ origSlot_inj, hS]
    · rw [outT_orig, install_slot _ origSlot_inj, hT]
  | some (.threshold _), h => exact h.elim

/-- **The SYM-mode `FactorProducer`** (queue (d)3): caps `P W L` are the call's admission caps. -/
def producer (a : DecompositionAlgorithm) (P W L : Nat) : FactorLoop.FactorProducer true a pcpp where
  t := 3778
  s := _
  machine := machine
  d := 16
  descSlots := descSlots
  descInjective := descSlots_inj
  outN := outN
  outS := outS
  outT := outT
  hNS := by decide
  hNT := by decide
  hST := by decide
  Desc := fun o k => descAt P W L o k.val
  Ok := ok P W L
  cost := cost P L
  need := fun _ => 1
  run := fun o R hok hR => run a P W L o R hok hR

end producer
end NearCubicWires.SourceRequest.SymSwitch

