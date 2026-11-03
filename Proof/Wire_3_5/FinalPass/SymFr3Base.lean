import Proof.Wire_3_5.FinalPass.FreeGen9
import Proof.Wire_3_5.FinalPass.SymSz1Base

/-! # The SYM free numbers (root #145 (ii)), part 4: the SYM constants and the pad and load bounds

At a SYM call the free numbers are `freeVal2 (symK2 c) (symX …)` (`FreeGen.freeProg2`): `m = max(8·nc + 16·a·W, 8)`
(the degenerate call's padded batch has one constant row), `Q' = dQ(2kh+β)`, `h = dH(n+1)^{eH}`,
`pr = dP(n+1)^{eP}` (P3:1886-1906; P3:1596-1615 for `h`), and the requests' degree bound is
`dF c x = dD·(⌊√B_S⌋ + β)`, the paper's `d_S = C_D(√B + L)` (P3:3094-3100).
* `SymC`, **`symK2`**, **`symDF`**;
* `kL_le_loadPsi` (`k + L ≤ ψ` once `C_D ≥ 1`, through `Ψ_aux`, P3:3101-3102);
* **`pad_sym2`** (`SymFreeOk4.pad_le`), `c3K2`, **`c3_sym2`** (`SymFreeOk4.c3_le` at `K3 = c3K2 c`, `D3 = eH + eP`).
Paper quantities of the main types: the pad `2^ρ` against `2^{n−k}poly(n)`, `h + Q' + m + pr` against `(ψ+1)·poly(n)`. -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.FinalPass.SymFr
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.PrimT.C4Set
open NearCubicWires.RepairOrdinary NearCubicWires.WireExponent3_5.PrimAsm
open NearCubicWires.WireExponent3_5.Shared NearCubicWires.WireExponent3_5.Cost NearCubicWires.WireExponent3_5.Primitive
open NearCubicWires.SupplierPipeline NearCubicWires.WireExponent3_5.Stars NearCubicWires.WireExponent3_5.Split
open NearCubicWires.WireExponent3_5.PrimAsm.Plan NearCubicWires.WireExponent3_5.PrimAsm.WriterIface
open NearCubicWires.WireExponent3_5.FinalPass.FreeGen

/-- The SYM exponents and coefficients. -/
structure SymC where
  dT : ℕ
  dC : ℕ
  dQ : ℕ
  dH : ℕ
  eH : ℕ
  dP : ℕ
  eP : ℕ
  dA : ℕ
  dR : ℕ
  dD : ℕ

/-- **The SYM constants**: `m = max(8·nc + 16·a·W, 8)`. -/
def symK2 (c : SymC) : FreeK2 := ⟨⟨c.dT, c.dC, c.dQ, c.dH, 8, 16, 0, 0, 0, 0, c.dP, c.dA, c.dR⟩, c.eH, c.eP, 8⟩

/-- **The requests' degree bound** `dD·(⌊√B_S⌋ + β)`: the paper's `d_S = C_D(√B + L)` (P3:3094-3100). -/
def symDF (c : SymC) (x : FreeIn) : ℕ := c.dD * (Nat.sqrt x.capS + β x)

/-- **`k + L ≤ ψ` once `C_D ≥ 1`**, through `Ψ_aux = C_D[k + L² + (k+L³)L²(k+L)]` (P3:3101-3102). -/
theorem kL_le_loadPsi (CD k L BT BS : ℕ) (hCD : 1 ≤ CD) : k + L ≤ loadPsi CD k L BT BS := by
  have h1 : loadAux CD k L ≤ loadPsi CD k L BT BS := by
    unfold loadPsi; exact le_trans (le_max_right _ _) (le_max_right _ _)
  have h2 : L ≤ L ^ 2 := Nat.le_self_pow (by norm_num) L
  have h3 : k + L ^ 2 + (k + L ^ 3) * L ^ 2 * (k + L) ≤ loadAux CD k L := by
    unfold loadAux
    exact Nat.le_mul_of_pos_left _ hCD
  omega

section Gate
variable (l : Literals) 

/-- The load bound's coefficient. -/
def c3K2 (c : SymC) : ℕ := c.dH + c.dQ + 400 + c.dP

end Gate

end NearCubicWires.WireExponent3_5.FinalPass.SymFr

