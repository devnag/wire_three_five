import Proof.Wire_3_5.Primitive.SeedFix.C4SymKA
import Proof.Wire_3_5.Primitive.Writers.SymDecCall

/-! # C4.K SYM, the contract of the free numbers (builds (e) + (g) to it)

"`ℓ ≥ max(k, ⌈log₂(Q+1)⌉)`" and `Q` (P3:2929-2941, 2994-3000); "For each candidate child prefix, print its signed
equation expression, reduce modulo the chosen power of two at each column, and sum the recovered integers" (P3:3034-3036:
the precision `Q'`, the power `2^{m−1}`, the compiler's `h`, `pr`); "The processor writes the pool, the enumeration's
rulers and constants [...] before the loop" (P3:3011-3016: the rulers `TWd`, `Cap`, the pad `ρ`). The SYM stage
(`sym_call_run`) runs at the free numbers `fr = Fp.val x` of C4.K's program (`C4Set.FreeProg`), `x` the call's
numbers (**`symX`**). This file fixes what the free numbers must satisfy:
* **`SymEAt`**: at one call, the enumeration's conditions (`hok`: `C4Dock.EnumOk` at every prefix), the compiler's
  precondition (`hpre`), `Q' ≤ pr` (`hQp`), the child's step bound (`hcost`, `coreCost ≤ Kch`), the exact recovery
  range (`hrange`), the pad (`hR`: `cellCost + 1 ≤ 2^ρ`), the pool's coefficients within `h` bits (`CoefFit`), `1 ≤ h`;
* **`SymFreeOk l F`**: the program `Fp`, the bounds `K`, `Kch` (functions of `n`), the compiler's envelope `E3`, the
  global bounds (`ok_le`, `cost_le`, `val_le`, `rho_le`, `pad_le`, `c3_le`) and `SymEAt` at every SYM call of every
  family of the gate `F`.

Paper quantities of the main type: the free numbers `TWd, Cap, Q', h, m, pr, ρ` of a SYM call. -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.PrimT.C4SymW
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.PrimT.C4Set
open NearCubicWires.RepairOrdinary NearCubicWires.WireExponent3_5.PrimAsm
open NearCubicWires.WireExponent3_5.Shared NearCubicWires.WireExponent3_5.Cost NearCubicWires.WireExponent3_5.Primitive
open NearCubicWires.SupplierPipeline NearCubicWires.WireExponent3_5.Stars NearCubicWires.WireExponent3_5.Split
open NearCubicWires.WireExponent3_5.PrimAsm.Plan NearCubicWires.WireExponent3_5.PrimAsm.WriterIface

section Call
variable {kclk : ℕ} {E : Envelope} {B : TimeBudget kclk E} (I : PrimitiveInputs B)
  (alg : RepairRepresentation.DecompositionAlgorithm) (wa : RepairRepresentation.WilliamsAlgorithm) {n a : ℕ}
  (Cs : Fin a → NormalizedSymmetricThresholdCircuit n) (carriers : List (Carrier n)) (translation : List ℕ)
  (hs : I.StarAt n)

/-- **The SYM call's numbers** (`C4Set.FreeIn`, the numbers program's registers before C4.K's program). -/
noncomputable def symX : FreeIn :=
  ⟨n, SeedFix.callKh (I.starParams n hs), Ledger.Lq n, B.capOf .sym n, a, carriers.length,
    (SymDec.cyOf Cs).sum, SeedFix.symCount I hs Cs carriers,
    max (SeedFix.callKh (I.starParams n hs) + SeedFix.callKh (I.starParams n hs)) (Nat.clog 2 (SeedFix.symCount I hs Cs carriers)),
    PrimAsm.Enum.symNT I hs Cs carriers, wOf (SeedFix.callKh (I.starParams n hs)) (SeedFix.symCount I hs Cs carriers),
    C4Geo.dRow (I.starParams n hs)⟩

end Call

end NearCubicWires.WireExponent3_5.PrimT.C4SymW
