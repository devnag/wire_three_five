import Proof.Wire_3_5.Primitive.SeedFix.C4SF

/-! # The free numbers of a call, generic: the formulas and the record

"The processor writes the pool, the enumeration's rulers and constants [...] before the loop" (P3:3011-3016); "print its
signed equation expression, reduce modulo the chosen power of two at each column" (P3:3034-3036). C4.K's program
(`PrimT.C4Set.FreeProg`) computes the seven free numbers `TWd, Cap, Q', h, m, pr, ρ` of a call from the call's
numbers (`FreeIn`). One program family serves every mode (SYM, THR, HASH); a mode fixes the constants `κ : FreeK`:

* `β x = ⌈log₂(n+2)⌉`, `W x = 2⌊(β+5)/4⌋ + 1` (the list walk's length at `D = 1`);
* **`freeVal κ x`**: `TWd = dT·β²`, `Cap = 2^{dC·β²}`, `Q' = dQ·β²`, `h = dH·β²`,
  `m = mA·nc + mB·a·W + mC·W + mD·a + mF·M + mE` (the exact factor count of the printed terms), `pr = dP·β⁶`,
  `ρ = max(n − 2kh + dA·β, dR·β²)`;
* **`FreeSmall Ds x`**: the fields the program reads (`kh`, `nc`, `a`, `M`) are at most `2^{Ds·(B+1)²}`;
* **`FreeOk`**: the program and its bounds (the mode-independent part of `SymFreeOk`'s contract): `ok_le`, `val_le`
  (with `FreeSmall`), `cost_le`, `rho_le`, the pad **`padX`** (`2^ρ ≤ Kp·(2^{n−2kh}(n+1)^{Dp} + 2^{n/2}·2^{Dp(B+1)²})`)
  and **`c3X`** (`h + Q' + m + pr ≤ K3·(nc + a + M + 1)·(β + 1)⁶`).

Paper quantities of the main types: the free numbers of a call (the rulers, the constants, the precision, the pad). -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.FinalPass.FreeGen
open NearCubicWires NearCubicWires.WireExponent3_5.PrimT.C4Set

/-- **The mode's constants** of the free numbers. -/
structure FreeK where
  dT : ℕ
  dC : ℕ
  dQ : ℕ
  dH : ℕ
  mA : ℕ
  mB : ℕ
  mC : ℕ
  mD : ℕ
  mE : ℕ
  mF : ℕ
  dP : ℕ
  dA : ℕ
  dR : ℕ

/-- `β = ⌈log₂(n+2)⌉` (the ledger's `L`). -/
def β (x : FreeIn) : ℕ := Nat.clog 2 (x.n + 2)

/-- The list walk's length at `D = 1`: `2⌊(β+5)/4⌋ + 1`. -/
def W (x : FreeIn) : ℕ := 2 * ((β x + 5) / 4) + 1

/-- **The free numbers**: `TWd, Cap, Q', h, m, pr, ρ`. -/
def freeVal (κ : FreeK) (x : FreeIn) : Fin 7 → ℕ :=
  ![κ.dT * (β x * β x), 2 ^ (κ.dC * (β x * β x)), κ.dQ * (β x * β x), κ.dH * (β x * β x),
    κ.mA * x.nc + κ.mB * (x.a * W x) + κ.mC * W x + κ.mD * x.a + κ.mF * x.M + κ.mE,
    κ.dP * (β x * β x * (β x * β x) * (β x * β x)),
    max (x.n - (x.kh + x.kh) + κ.dA * β x) (κ.dR * (β x * β x))]

/-- **The read fields are small** (`kh`, `nc`, `a`, `M` at most `2^{Ds·(B+1)²}`). -/
def FreeSmall (Ds : ℕ) (x : FreeIn) : Prop :=
  x.kh ≤ 2 ^ (Ds * (natBitLength x.n + 1) ^ 2) ∧ x.nc ≤ 2 ^ (Ds * (natBitLength x.n + 1) ^ 2) ∧
    x.a ≤ 2 ^ (Ds * (natBitLength x.n + 1) ^ 2) ∧ x.M ≤ 2 ^ (Ds * (natBitLength x.n + 1) ^ 2)

end NearCubicWires.WireExponent3_5.FinalPass.FreeGen

