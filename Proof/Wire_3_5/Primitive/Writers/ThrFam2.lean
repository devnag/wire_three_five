import Proof.Wire_3_5.Primitive.Writers.ThrFam1
import Proof.Wire_3_5.Primitive.SeedFix.C4SF

/-! # c4 THR block, the THR free numbers' side part: `thrX`, **`ThrEAt2`** (types only)

"`ℓ ≥ max(k, ⌈log₂(Q+1)⌉)`" and `Q` (P3:2929-2941, 2994-3000); "For each candidate child prefix, print its signed
equation expression, reduce modulo the chosen power of two at each column, and sum the recovered integers" (P3:3034-3036:
the precision `Q'`, the power `2^{m−1}`, the compiler's `h`, `pr`); "The processor writes the pool, the enumeration's
rulers and constants [...] before the loop" (P3:3011-3016: the rulers `TWd`, `Cap`, the pad `ρ`). The THR twin of `C4SymW.symX`/`SymEAt2` (C4SymKB2: the child requests' degree bound `d := h`), at the THR batch (`thrSP`, `thrExprs`, `thrNT`, `thrEnts`, `thrR0`, `thrFam`):
* **`thrX`**: the THR call's numbers (`C4Set.FreeIn`, the registers `bigT_spec` leaves before C4.K's program);
* **`ThrEAt2`**: at one THR call, the enumeration's conditions (`hok`), the compiler's precondition (`hpre`), `Q' ≤ pr`,
  the child's step bound (`hcost`), the exact recovery range, the pad (`cellCost + 1 ≤ 2^ρ`), the THR pool's
  coefficients within `h` bits (`CoefFit`), `1 ≤ h`.

Paper quantities of the main type: the free numbers `TWd, Cap, Q', h, m, pr, ρ` of a THR call. -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.PrimAsm.ThrFam
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.PrimT NearCubicWires.WireExponent3_5.PrimT.C4Set
open NearCubicWires.RepairOrdinary NearCubicWires.WireExponent3_5.PrimAsm
open NearCubicWires.WireExponent3_5.Shared NearCubicWires.WireExponent3_5.Cost NearCubicWires.WireExponent3_5.Primitive
open NearCubicWires.SupplierPipeline NearCubicWires.WireExponent3_5.Stars
open NearCubicWires.WireExponent3_5.PrimAsm.WriterIface

section Call
variable {kclk : ℕ} {E : Envelope} {B : TimeBudget kclk E} (I : PrimitiveInputs B)
  (alg : RepairRepresentation.DecompositionAlgorithm) (wa : RepairRepresentation.WilliamsAlgorithm) {n a : ℕ}
  (Cs : Fin a → NormalizedThresholdThresholdCircuit n) (carriers : List (Carrier n)) (translation : List ℕ)
  (hs : I.StarAt n)

/-- **The THR call's numbers** (`C4Set.FreeIn`: `n`, `kh`, `L`, the THR filter's cap, `a'`, `|carriers|`, the digit count
`dig` (in the field `M`: the RADIX rows' factor count is `2·dig`),
the THR count `Q`, `ℓ`, `n_T`, `w`, `dRow`). -/
noncomputable def thrX : FreeIn :=
  ⟨n, SeedFix.callKh (I.starParams n hs), Ledger.Lq n, B.capOf .thr n, a, carriers.length,
    Primitive.thrDigits (I.starParams n hs) Cs alg (Primitive.thrCallDen alg I hs Cs), SeedFix.thrCount alg I hs Cs,
    max (SeedFix.callKh (I.starParams n hs) + SeedFix.callKh (I.starParams n hs))
      (Nat.clog 2 (SeedFix.thrCount alg I hs Cs)),
    PrimAsm.Enum.thrNT alg I hs Cs, wOf (SeedFix.callKh (I.starParams n hs)) (SeedFix.thrCount alg I hs Cs),
    C4Geo.dRow (I.starParams n hs)⟩

end Call

end NearCubicWires.WireExponent3_5.PrimAsm.ThrFam
