import Proof.Wire_3_5.Primitive.SeedFix.NwBTBase
import Proof.Wire_3_5.UnionMachine.NumsW1Base
import Proof.Wire_3_5.Primitive.Writers.ThrCap1
import Proof.Wire_3_5.FinalPass.S5TNum3Base

/-! # NW phase (b)'s value link and capacity need (#257, the `PrimT.NwB` types): **`vLinkB`**, **`needB`**

Phase (b) computes, at a THR call on the star, `vB = 2^{⌊(5k_h+3)/4⌋}·B·2^{sb}·#primes` from W6's numbers. The paper's
value is `V = |PrimeIndex(cut)|·|E|·Q` (P3:3044-3048) with `Q = 2^e·B` (the THR sample count, `thrQ_link`),
`|E| = 2^{sb}` (`card_gapSeed` at the THR filter `gP n cap_T (f_e·L)`) and `|PrimeIndex(cut)| = #primes`:

* **`vLinkB l : NwB.VLinkB l`** (`vB = vOf` at every THR call on the star).

Every number phase (b)'s register programs hold is polynomial in `X = |fpIn| + 1` (P3:3170-3181): the need
(`needT_le`), `cap_T` (`capTL_le1`), `(n+1)^{26}`, W6's power, W6's fourteen numbers (`S5T.vals_le`), the gap numbers
(`gapSeed_leR`, `lfw_le`), `V` (`vLinkB` and `vOf_le`), `T_f = K_T·(n+2)^{Z_T}`, and `#primes ≥ 1`
(`cut ≥ 563`):

* `Kn`, `Dn`, `atom_le`, **`needB l : NwB.NeedB l`**.

Paper quantities of the main types: the final pass's unshifted denominator `V = |PrimeIndex(cut)|·|E|·Q` at a THR
request (P3:3044-3048) and the polynomial size of (b)'s numbers in the input (P3:3170-3181). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearCubicWires.WireExponent3_5.FinalPass.Out.NwBV
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Split
open NearCubicWires.WireExponent3_5.PrimAsm.Plan NearCubicWires.SupplierPipeline
open NearCubicWires.WireExponent3_5.PrimT.NwB

theorem atom_le {K Ki X d D : ℕ} (hK : Ki ≤ K) (hd : d ≤ D) (hX : 1 ≤ X) : Ki * X ^ d ≤ K * X ^ D :=
  Nat.mul_le_mul hK (Nat.pow_le_pow_right hX hd)

theorem pow2_le {n X : ℕ} (hX : n + 1 ≤ X) (K d : ℕ) : K * (n + 2) ^ d ≤ K * 2 ^ d * X ^ d := by
  have h : (n + 2) ^ d ≤ (2 * X) ^ d := Nat.pow_le_pow_left (by omega) d
  rw [mul_pow] at h
  calc K * (n + 2) ^ d ≤ K * (2 ^ d * X ^ d) := Nat.mul_le_mul_left _ h
    _ = K * 2 ^ d * X ^ d := by ring

theorem pow_atom_le {n X c K Z D : ℕ} (hX : n + 1 ≤ X) (hc : c ≤ K * (n + 1) ^ Z) :
    (n + c + 1) ^ D ≤ (K + 1) ^ D * X ^ ((Z + 1) * D) := by
  have hX1 : 1 ≤ X := by omega
  have h1 : c ≤ K * X ^ (Z + 1) :=
    hc.trans (Nat.mul_le_mul_left _ ((Nat.pow_le_pow_left hX Z).trans (Nat.pow_le_pow_right hX1 (by omega))))
  have h2 : n + 1 ≤ X ^ (Z + 1) := hX.trans (Nat.le_self_pow (by omega) X)
  have h3 : n + c + 1 ≤ (K + 1) * X ^ (Z + 1) := by
    have : (K + 1) * X ^ (Z + 1) = K * X ^ (Z + 1) + X ^ (Z + 1) := by ring
    omega
  calc (n + c + 1) ^ D ≤ ((K + 1) * X ^ (Z + 1)) ^ D := Nat.pow_le_pow_left h3 D
    _ = (K + 1) ^ D * X ^ ((Z + 1) * D) := by rw [mul_pow, ← pow_mul]

theorem gap_arith {sb lfw g : ℕ} (hl : lfw ≤ sb + 1) (hg : 2 ^ sb ≤ g) : 2 ^ (sb + 1) + lfw ≤ 4 * g := by
  have h := Nat.lt_two_pow_self (n := sb)
  rw [pow_succ]
  omega


end NearCubicWires.WireExponent3_5.FinalPass.Out.NwBV
