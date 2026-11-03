import Lean
import Proof.Wire_3_5.Primitive.Writers.PreLink
import Statement_Wire_3_5
import Proof.Wire_3_5.Assembly.Gate0
import Proof.Wire_3_5.Primitive.Writers.Plan
import Proof.Wire_3_5.Assembly.Split
import Proof.Wire_3_5.UnionMachine.PreProofBase


noncomputable section
set_option maxRecDepth 4096


/-! # PA (e), proved: the writers' class link `∀ l, PreLinkT l`

"The additive preprocessing of a call costs `2^{O(Ψ)}q^{O(1)}`" (P3:3108, 3112-3114) at the load
`Ψ = max{Ψ_T, Ψ_S, Ψ_aux}` (P3:3094-3102), `Ψ_aux = C_D[k + L² + (k+L³)L²(k+L)]`. The batch writers run over the star
cells, `2^{k+L}·poly(n)` units, with the writers' fixed polynomial `C·(2^{k+L} + n + 1)^D` (PA's `PreLinkT`).
With the floor envelope `2^{D·Ψ}` (**`envW D`**: `cpsi = D`, `Apre = 0`), the load-constant floor `C_D ≥ 1` and
`c_W = C·2^D`: `Ψ ≥ Ψ_aux ≥ k + L` (**`kL_le_loadPsi`**) and `n + 2 ≤ 2^L`, so `2^{k+L} + n + 1 ≤ 2^{Ψ+1}` and
`C·(2^{k+L} + n + 1)^D ≤ C·2^D·2^{D·Ψ}` (**`link_le`**); **`preLink`**: `∀ l, PreLinkT l`.

Paper quantity of the main type: the preprocessing class `2^{cpsi·Ψ}q^{Apre}` at the load `Ψ` against the star cells'
count `2^{k+L}`. -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.UnionMachine.PreProof
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Shared
open NearCubicWires.WireExponent3_5.Cost NearCubicWires.WireExponent3_5.Split
open NearCubicWires.WireExponent3_5.PrimAsm.Plan NearCubicWires.WireExponent3_5.PrimAsm.WriterIfaceJ
open NearCubicWires.WireExponent3_5.PrimAsm.PreLink

/-- **PA's (e), proved** (the `pre` child of the writer node): at every endpoint exponent `fe` and writers'
polynomial `(D, C)`: the floor envelope `envW D`, the load-constant floor `1`, and `c_W = C·2^D`. -/
def preLink (l : Literals) : PreLinkT l := fun _fe D C =>
  ⟨envW D, 1, fun F _ _ hCD => ⟨C * 2 ^ D, fun kclk coef A a ha n _ => by
    have e : ((gate0 l F).budget kclk coef A a ha).psiOf n =
        loadPsi F.CD (((gate0 l F).budget kclk coef A a ha).kOf n) (Nat.clog 2 (n + 2))
          (((gate0 l F).budget kclk coef A a ha).capOf .thr n) (((gate0 l F).budget kclk coef A a ha).capOf .sym n) :=
      rfl
    rw [e]
    exact link_le D C F.CD _ n _ _ hCD⟩⟩

end NearCubicWires.WireExponent3_5.UnionMachine.PreProof

end
