import Proof.Packets.BudgetRestParts
import Proof.Packets.PacketsMetaSeedCount
import Proof.Packets.PacketsMetaCutoffSpec

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

namespace NearCubicWires.SourceBudget
open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation NearCubicWires.SupplierPipeline
open NearCubicWires.RepairSource NearCubicWires.RepairSource.CloseoutFinal NearCubicWires.RuntimeShape
open PCJ9eff70d512234a4c_Fixed PCJd4d1d9d7d1fa4313_Production

theorem smallSize_pos (a : DecompositionAlgorithm) (r : Request) : 1 ≤ r.smallSize a := by
  have key : ∀ x1 x2 x3 x4 x5 x6 x7 x8 : ℕ, 1 ≤ x1 + x2 + x3 + x4 + x5 + x6 + x7 + x8 + 1 := by
    intros; omega
  unfold Request.smallSize
  exact key _ _ _ _ _ _ _ _

/-- **PG's prime count is below `40001·smallSize^3`** (the THR cutoff, PM `cut_le_small`; `1` otherwise). -/
theorem primeCount_le_small (a : DecompositionAlgorithm) (r : Request) :
    PacketsGlue.RequestMeta.primeCountOf a r ≤ 40001 * (r.smallSize a)^3 := by
  have hS := smallSize_pos a r
  have hS3 : 1 ≤ (r.smallSize a)^3 := Nat.one_le_pow _ _ hS
  rw [PacketsGlue.RequestMeta.primeCountOf_eq]
  have hpc := PacketsGlue.RequestMeta.pc_le (PacketsGlue.RequestMeta.cutoffOf a r)
  cases r with
  | terminal =>
    simp only [PacketsGlue.RequestMeta.cutoffOf] at hpc ⊢
    omega
  | sym r four L target =>
    simp only [PacketsGlue.RequestMeta.cutoffOf] at hpc ⊢
    omega
  | thr r four L target =>
    have hc := PacketsMeta.Stage.cut_le_small a r four L target
    rw [PacketsMeta.Spec.cut_eq a r four target] at hc
    simp only [PacketsGlue.RequestMeta.cutoffOf] at hpc ⊢
    omega

/-- **The F6 binary counts at a call are small class** (`hcb` of `restFree_inClasses`). -/
theorem counts_at (a : DecompositionAlgorithm) (r : Request) (m sC sE : ℕ)
    (hsm : (r.smallSize a)^(2*(163+3)) ≤ sC*smallClass m sE r.q) :
    CloseoutRowsCountBinary.budget (PacketsGlue.RequestMeta.seedCount a r) +
        CloseoutRowsCountBinary.budget (PacketsGlue.RequestMeta.primeCountOf a r) ≤
      (992*(8+40001+1)^2*sC) * smallClass m sE r.q :=
  counts_small _ _ (r.smallSize a) 8 163 40001 3 (smallSize_pos a r) (PacketsMeta.Seed.seedCount_le_small a r)
    (primeCount_le_small a r) m sC sE r.q hsm

end NearCubicWires.SourceBudget

