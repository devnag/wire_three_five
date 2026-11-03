import Proof.SourceAssembly.SourceInitEnc

section
set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true

open NearCubicWires LocalBitMultitape ExtDecompositionBatch RepairOrdinary
open RepairOrdinary.RecoveryRootRound RepairSource.VerifierDecoding RepairSource.ProjectionNormalization
open NearCubicWires.SupplierEstimator
namespace NearCubicWires.SourceConstruction.InitPost
noncomputable section

/-! ## 1. The docks -/

def rw7 : Fin 7 → Fin 323 := ![2, 8, 6, 9, 10, 7, 11]
def rc79 : Fin 79 → Fin 323 := fun j =>
  ⟨if j.val = 0 then 0 else if j.val = 47 then 18 else if j.val = 77 then 12 else 32 + j.val, by
    have := j.isLt; split_ifs <;> omega⟩
def sl57 : Fin 57 → Fin 323 := fun j =>
  ⟨if j.val = 0 then 0 else if j.val = 1 then 18 else if j.val = 49 then 21 else if j.val = 55 then 17
    else 111 + j.val, by have := j.isLt; split_ifs <;> omega⟩
def en119 : Fin 119 → Fin 323 := fun j =>
  ⟨if j.val = 0 then 1 else if j.val = 17 then 22 else if j.val = 40 then 25 else if j.val = 43 then 26
    else if j.val = 37 then 27 else if j.val = 77 then 28 else if j.val = 116 then 29
    else if j.val = 97 then 30 else if j.val = 117 then 31 else 168 + j.val, by
    have := j.isLt; split_ifs <;> omega⟩
def cp4 : Fin 4 → Fin 323 := ![1, 287, 20, 288]
def un43 : Fin 43 → Fin 323 := fun j =>
  ⟨if j.val = 0 then 2 else if j.val = 1 then 3 else if j.val = 2 then 1 else if j.val ≤ 6 then 10 + j.val
    else if j.val ≤ 40 then 282 + j.val else if j.val = 41 then 4 else 5, by
    have := j.isLt; split_ifs <;> omega⟩


macro "injv2" : tactic => `(tactic| (
  intro a b hab
  have hv := congrArg Fin.val hab
  have ha := a.isLt
  have hb := b.isLt
  simp only [rc79, sl57, un43] at hv
  apply Fin.ext
  split_ifs at hv <;> omega))



/-! ## 2. The machine, the input, the cost -/

def machine (L cS cR : ℕ) :=
  Composition.machine (Composition.machine (Composition.machine (Composition.machine (Composition.machine
    (RecoveryFocus.machine rw7 RewindOnce.machine)
    (RecoveryFocus.machine rc79 (RowConst.machine L 2)))
    (RecoveryFocus.machine sl57 (InitSlopes.machine L)))
    (RecoveryFocus.machine en119 InitEnc.machine))
    (RecoveryFocus.machine cp4 ClockUnarySum.machine))
    (RecoveryFocus.machine un43 (Uniform.machine cS cR))

/-- The small slope `Ms = 2(K+1)`. -/
abbrev Ms (L q : ℕ) : ℕ := 2*(normalizedLiveCount q L+1)

def cost (L cS cR q b V Rc : ℕ) : ℕ :=
  ((((RewindOnce.cost V+1+RowConst.cost L 2 q)+1+InitSlopes.cost L q (Ms L q))+1+InitEnc.cost b)+1+
    (2*b+6))+1+Uniform.cost cS cR V b Rc

/-! ## 3. The copy of `1^b`, padded off its source -/

/-! ## 4. The run -/

end
end NearCubicWires.SourceConstruction.InitPost
end
