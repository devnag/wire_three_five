import Proof.Wire_3_5.Primitive.Writers.ThrSide6Base

/-! # PA2 c4 THR block, piece 6 part 8: `hpre` and `CoefFit` at a THR call

The THR twin of the SymHp1–3 and SymOcc4: the request's `h·Q'·d ≤ pr` (**`hqd_thr`**, at the THR degree
`d_D(⌊√(B_T L)⌋ + L²)`), `N^{16}·2^{8ℓ}·2^{Q'} ≤ 2^{pr}` (**`coef_thr`**), the printer's budget within the rectangle
(**`occ_thr`**, under the THR printer floor `occCDT ≤ C_D`: the linear part through `C_D(k+L) ≤ Ψ` and
`C_D·L² ≤ Ψ`, the quadratic part through the THR load `C_D²(k+L)²(⌊√(B_T L)⌋ + L²) ≤ Ψ`), and hence alg:compiler's
precondition at every THR child prefix (**`hpre_thr`**, `pre_of`), with the pool's `CoefFit` (**`thrHcf`**).

* `ThrHpreC`, `hqd_thr`, `coef_thr`, `occCDT`, `occ_thr`, **`hpre_thr`**, **`thrHcf`**.

Paper quantity of the main type: alg:compiler's precondition at a THR call (P3:1882-1900). -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.PrimAsm.ThrSide
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.PrimT.C4Set
open NearCubicWires.RepairOrdinary NearCubicWires.WireExponent3_5.PrimAsm
open NearCubicWires.WireExponent3_5.Shared NearCubicWires.WireExponent3_5.Cost NearCubicWires.WireExponent3_5.Primitive
open NearCubicWires.SupplierPipeline NearCubicWires.WireExponent3_5.Stars NearCubicWires.WireExponent3_5.Split
open NearCubicWires.WireExponent3_5.PrimAsm.Plan NearCubicWires.WireExponent3_5.PrimAsm.WriterIface
open NearCubicWires.WireExponent3_5.CompilerMachine NearCubicWires.WireExponent3_5.FinalPass.FreeGen
open NearCubicWires.WireExponent3_5.FinalPass.SymFr (SymC symBud symBud_le cDa n2_le_L one_le_L pow_mono_mul kL_mul_le L2_mul_le two_dRow_ge occ_num pow_N_le)

section Gate
variable (l : Literals) 

/-- **The THR printer's load floor** (fixed before `F`: the algorithm is the literals'). -/
def occCDT (a : RepairRepresentation.DecompositionAlgorithm) (c : SymC) (A1 cd : ℕ) : ℕ :=
  160 * (A1 + 1392 * cd + 16 + 16 * cd + c.dQ + 1) + 160 * (c.dQ * c.dD * cDa a) + 2

end Gate

end NearCubicWires.WireExponent3_5.PrimAsm.ThrSide
