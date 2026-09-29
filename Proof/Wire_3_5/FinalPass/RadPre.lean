import Proof.Wire_3_5.UnionMachine.RadSpec
import Proof.Wire_3_5.Primitive.Writers.ThrSide7

/-! # The RADIX row's admissibility at every THR call (the stage 7 (b))

row:radix P3:2585-2623 at a THR call of the gate: the RADIX request `radReqOf … g pr s row` (the fixed hash's list
data `D = thrCallD`, the digit lists `thrDigs`, the prime `p`, `b₀ = 2`, the residue `s`) is admissible
(`RadReq.Pre`): every digit list has exactly four labels per occurrence (`labsOf`'s corner atoms, `DigsOk`), the
fixed hash's levels are nested (`𝓛_{j+1} ⊆ 𝓛_j`: vanishing of the first `j+1` bits implies vanishing of the first
`j`, `inLevelBits`), there is at least one digit (`τ₀ = ⌈log₂ cutoff⌉ ≥ 1`, the cutoff is at least `563`), and the
residue is below the prime.

* `inLevelBits_nest`, **`radPre`**.

Paper quantity of the main type: the RADIX row's admissibility at a THR call. -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.FinalPass.RadB
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Shared
open NearCubicWires.WireExponent3_5.Cost NearCubicWires.WireExponent3_5.Primitive NearCubicWires.SupplierPipeline
open NearCubicWires.WireExponent3_5.PrimAsm NearCubicWires.WireExponent3_5.PrimThrW.RadSetup
open NearCubicWires.WireExponent3_5.Split NearCubicWires.WireExponent3_5.PrimAsm.Plan NearCubicWires.WireExponent3_5.Stars

/-- **The fixed hash's levels are nested** (`𝓛_{j+1} ⊆ 𝓛_j`). -/
theorem inLevelBits_nest (MP : Filters.MajorantParams) (s : Fin (2 * MP.t * MP.ell0) → Bool) (j i : ℕ)
    (h : FinalPass.MajorantBits.inLevelBits MP s (j + 1) i = true) : FinalPass.MajorantBits.inLevelBits MP s j i = true := by
  unfold FinalPass.MajorantBits.inLevelBits at h ⊢
  split_ifs at h ⊢ with hi
  · simp only [decide_eq_true_eq] at h ⊢
    exact fun b hb hbj => h b hb (by omega)
  · rfl

/-- **The RADIX row is admissible at every THR call** (`RadPreStmt`). -/
theorem radPre (l : Literals) (F : GateFree l) : UnionMachine.RadSpec.RadPreStmt l F := by
  intro kclk coef A a ha n hs a' ha' Cs carriers translation _ g pr s row _
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro dg hdg
    obtain ⟨d, rfl⟩ := List.mem_ofFn.mp hdg
    show 4 * _ ≤ (CompilerMachine.Pool.labsOf _ _ _).length
    rw [Records.labsOf_length]
  · intro j i h
    exact inLevelBits_nest _ _ j i h
  · show 1 ≤ (List.ofFn _).length
    rw [List.length_ofFn]
    exact ThrSide.dig_pos l F kclk coef A a ha Cs hs
  · have hp : Nat.Prime pr.val := (Finset.mem_filter.mp pr.2).2
    haveI : NeZero pr.val := ⟨hp.pos.ne'⟩
    exact ZMod.val_lt s

end NearCubicWires.WireExponent3_5.FinalPass.RadB
