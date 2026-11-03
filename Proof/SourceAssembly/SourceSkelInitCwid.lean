import Proof.SourceAssembly.SourceSkelInitHorner
import Proof.SourceAssembly.SourceRequestSymOriginal

section
set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true

open NearCubicWires LocalBitMultitape ExtDecompositionBatch RepairOrdinary
open RepairOrdinary.RecoveryRootRound RepairSource.VerifierDecoding RepairSource.ProjectionNormalization
open NearCubicWires.SupplierEstimator RepairRepresentation
open PCJ1fef9807c6954e94_Native
open NearCubicWires.SourceConstruction NearCubicWires.SourceConstruction.InitRun
namespace NearCubicWires.SourceSkeleton.InitS
noncomputable section

/-! ## 1. The two widths as Horner coefficient lists -/

/-- THR (`codeWidth`): coefficients of `Ld^14 .. Ld^0` (the leading `Ld^15` coefficient is `4096`). -/
def thrCs : List Nat := [4096, 0, 0, 0, 36864, 33792, 0, 0, 0, 82472, 51568, 560, 640, 360, 50596]
/-- SYM (`symCodeWidth`). -/
def symCs : List Nat := [4096, 0, 0, 0, 28672, 25600, 0, 0, 0, 25640, 880, 560, 640, 360, 676]

def cwCs (mode : Bool) : List Nat := if mode then symCs else thrCs

def cwidOf (mode : Bool) (L : Nat) : Nat :=
  if mode then SourceRequest.SymOriginal.symCodeWidth L else SourceRequest.ThrSwitch.codeWidth L

theorem thr_eq (p : Nat) : hVal p thrCs 4096 = SourceRequest.ThrSwitch.codeWidth p := by
  simp only [hVal, thrCs, SourceRequest.ThrSwitch.codeWidth,
    RecoveryWitnessPolicy.canonicalThresholdCircuitCodeBitBound, RecoveryWitnessPolicy.taggedListBitBound,
    RecoveryWitnessPolicy.canonicalNatCodeBitBound, CanonicalBinary.encodeNatBitsBound,
    RecoveryWitnessPolicy.canonicalBalancedCodeBitBound, RecoveryWitnessPolicy.canonicalSupportedGateCodeBitBound,
    RecoveryWitnessPolicy.canonicalIntCodeBitBound]
  ring

theorem sym_eq (p : Nat) : hVal p symCs 4096 = SourceRequest.SymOriginal.symCodeWidth p := by
  simp only [hVal, symCs, SourceRequest.SymOriginal.symCodeWidth,
    RecoveryWitnessPolicy.canonicalSymmetricCircuitCodeBitBound, RecoveryWitnessPolicy.taggedListBitBound,
    RecoveryWitnessPolicy.canonicalNatCodeBitBound, CanonicalBinary.encodeNatBitsBound,
    RecoveryWitnessPolicy.canonicalBalancedCodeBitBound, RecoveryWitnessPolicy.canonicalSupportedGateCodeBitBound,
    RecoveryWitnessPolicy.canonicalIntCodeBitBound]
  ring

/-- **The width identity.** -/
theorem cwid_eq (mode : Bool) (p : Nat) : hVal p (cwCs mode) 4096 = cwidOf mode p := by
  cases mode
  · exact thr_eq p
  · exact sym_eq p

/-! ## 2. The stage on the init's invariant -/

variable {d : Dims} {eX pX gW eR eV X T : Nat} (pl : Place d eX pX gW eR eV X T) {NS : Nat}
  (hh : HeadExt d eX pX gW X NS)

include pl in
theorem T_pos : 0 < T := by
  obtain ⟨hF0, hB0, h11, h12, hU, hJB, hjk, hP⟩ := lay pl.ext
  have := pl.hT; omega

/-- A total extension-tape map (the value is `eb + k` whenever that is a tape). -/
def extF (k : Nat) : Fin T := ⟨(eb d eX pX gW X NS + k) % T, Nat.mod_lt _ (T_pos pl)⟩

theorem extF_val {NE : Nat} (hE : ResExt d eX pX gW X NS NE) (k : Nat) (hk : k < NE) :
    (extF (NS := NS) pl k).val = eb d eX pX gW X NS + k :=
  Nat.mod_eq_of_lt (ext_lt pl hE k hk)

/-- The stage: template of `Ld` onto `u`, log `u+1`; `1^4096` onto `u+3` (word log `u+2`); Horner on `[u+4, u+79)`; copy onto `hrT 8`
(blank `u+79`, log `u+80`). -/
def cwM (mode : Bool) (u : Nat) :=
  Composition.machine
    (RecoveryFocus.machine (![Dims.hrT (ext3 pl hh) pl.hT 3, extF (NS := NS) pl u, extF (NS := NS) pl (u+1)] : Fin 3 → Fin T)
      (DimensionTemplate.machine false))
  (Composition.machine
    (RecoveryFocus.machine (![extF (NS := NS) pl (u+3), extF (NS := NS) pl (u+2)] : Fin 2 → Fin T)
      (HierarchyFixedWord.machine (List.replicate 4096 true)))
  (Composition.machine
    (hChain (extF (NS := NS) pl) (extF (NS := NS) pl u) (extF (NS := NS) pl (u+2)) (cwCs mode)
      (extF (NS := NS) pl (u+3)) (u+4)).2
    (RecoveryFocus.machine (![extF (NS := NS) pl (u+77), extF (NS := NS) pl (u+79), stripT pl hh 8 (by decide),
      extF (NS := NS) pl (u+80)] : Fin 4 → Fin T) ClockUnarySum.machine)))

def cwCost (mode : Bool) (Ld : Nat) : Nat :=
  (2*Ld+8) + 1 + ((2 * (List.replicate 4096 true).length + 2) + 1 +
    (hCost Ld (cwCs mode) 4096 + 1 + (2 * cwidOf mode Ld + 6)))

end
end NearCubicWires.SourceSkeleton.InitS
end
