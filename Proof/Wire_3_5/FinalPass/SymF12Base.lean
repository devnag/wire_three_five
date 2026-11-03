import Proof.Wire_3_5.FinalPass.SymF8
import Proof.Wire_3_5.FinalPass.SymF5
import Proof.Wire_3_5.Foundations.OutMachineJoinGBase
import Proof.Wire_3_5.Primitive.Writers.CallIndexRBase

/-! # SWf (the SYM words writer's flat tables), part 12: the flat tables writer at a SYM request

At a SYM request `r` of the family (on-star, carriers `≤ 2`, circuit descriptions `≤ (n+1)^{26}`), the flat list's
numbers are below `X = K₀·(n+2)^{E₀}` with `E₀ = E0P l` on `l` alone and `K₀ = K0P c_r` (PA's `CallIndexR`:
`flatSeed_leR`, `cap_leR`; `M ≤ 4(n+1)^{26}`, `L_c ≤ M`, `errExp = ⌈log₂(n+2)⌉ + 5`), and `n + 2 ≤ 2^m + 1` at the
writer's dimension `m = mOf P`. **`writer_runP`**: the flat tables writer `tabMP W c_r (9E₀) (CWP K₀) E₀ K₀` runs
(`tabP_writer` with `tabP_hyps`) from `frame (reqP n (symPl r) (symL r c))` to `flatWord (symPl r) (symL r c)` within
the shell's budget `budP`.

Paper quantity of the main type: circuit `c`'s flat tables word (`tablesJ`, list:flatten P3:1508-1520) at the
request, on the writer's output. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace NearCubicWires.WireExponent3_5.FinalPass.SymF
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Split
open NearCubicWires.WireExponent3_5.Lists NearCubicWires.WireExponent3_5.Primitive NearCubicWires.WireExponent3_5.Shared
open NearCubicWires.WireExponent3_5.FinalPass.PlanFP NearCubicWires.WireExponent3_5.PrimAsm.Plan
open NearCubicWires.WireExponent3_5.PrimAsm NearCubicWires.WireExponent3_5.PrimT.WalkBank
open NearCubicWires.BlockPlatform NearCubicWires.SupplierPipeline

/-- The atoms' coefficient (on `c_r`). -/
def K0P (cr : ℕ) : ℕ := CallIndexR.flatK cr + 8192 * CallIndexR.capK cr + 1000

theorem n2_le_mP (P : StarParams) : P.n + 2 ≤ 2 ^ NumsX.mOf P + 1 := by
  have h1 : P.n + 2 ≤ 2 ^ Nat.clog 2 (P.n + 2) := Nat.le_pow_clog (by norm_num) _
  have h2 : 2 ^ Nat.clog 2 (P.n + 2) ≤ 2 ^ NumsX.mOf P :=
    Nat.pow_le_pow_right (by norm_num) (by unfold NumsX.mOf; omega)
  omega

variable (W : WalkBankProducer)

/-- **The flat tables writer's budget** at a star call (the shell's cost). -/
noncomputable def budP (cr E0 K0 : ℕ) (P : StarParams) (Pl : FlatListParams) (L : ℕ) : ℕ :=
  2 * ShellT.shellCostG (reqP P.n Pl L) P.n (9 * E0) (CWP K0) 1 64
    (ThrData.thrDataStage2.cost 0 (TabW.noCs P.n) [] (UnaryCalc.value 1 64 P.n) (UnaryCalc.value 1 64 P.n)) 1
    (cr + 18) (TabW.c2Of cr P.n) (NumsX.mOf P) E0 K0 (A2P K0 * (2 ^ NumsX.mOf P + 1) ^ (9 * E0)) + 2

/-- **The flat tables writer's run at the flat list's numbers `≤ K₀·(n+2)^{E₀}`.** -/
theorem writer_atP (cr : ℕ) (P : StarParams) (hrP : P.r = Ledger.rowBr cr P.n) (Pl : FlatListParams) (L K0 E0 : ℕ)
    (hK0 : 1 ≤ K0) (hE0 : 1 ≤ E0) (hM : Pl.M ≤ K0 * (P.n + 2) ^ E0) (hB : Pl.B ≤ K0 * (P.n + 2) ^ E0)
    (hE : Pl.errExp ≤ K0 * (P.n + 2) ^ E0) (hL : L ≤ K0 * (P.n + 2) ^ E0)
    (hK : Fintype.card Pl.FlatSeed ≤ K0 * (P.n + 2) ^ E0) :
    WriterIfaceJ.WriterRun (tabMP W cr (9 * E0) (CWP K0) E0 K0) (budP cr E0 K0 P Pl L)
      (ShellX.shellInX W.x (9 * E0) 1 1 E0) (ShellX.shellOutX W.x (9 * E0) 1 1 E0) (reqP P.n Pl L)
      (flatWord Pl L) := by
  have hQ := n2_le_mP P
  have lift : ∀ v, v ≤ K0 * (P.n + 2) ^ E0 → v ≤ K0 * (2 ^ NumsX.mOf P + 1) ^ E0 := fun v h =>
    h.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hQ _))
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ := tabP_hyps (NumsX.mOf P) Pl P.n L K0 E0 hQ hK0 hE0
    (lift _ hM) (lift _ hB) (lift _ hE) (lift _ hL) (lift _ hK)
  exact tabP_writer W cr P hrP Pl L (9 * E0) (CWP K0) E0 K0 (A1P K0 * (2 ^ NumsX.mOf P + 1) ^ (3 * E0))
    (A2P K0 * (2 ^ NumsX.mOf P + 1) ^ (9 * E0)) _ h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 le_rfl

section Req

end Req

end NearCubicWires.WireExponent3_5.FinalPass.SymF
