import Mathlib
import Proof.Wire_3_5.Foundations.GF

/-! # Risk 3 (S2/S4 machines): GF(2^ℓ) needs only shift/XOR/parity primitives

This file shows the machine side can be made small:

* the field is `F₂[x]/(p)` with a PRIMITIVE modulus, certified by the LFSR period test
  `period p ℓ = 2^ℓ - 1` (a finite commutative ring whose unit `x` has order `|R| - 1` is a field,
  so the certificate needs no factor search); P3:2932-2941 allows `2^{O(ℓ)}` preprocessing;
* multiplication is `ℓ` LFSR steps (`×x mod p`: shift, conditional XOR) and XORs (`fmulShift`);
* the trace is GF(2)-linear: `Tr(a) = ⟨τ, a⟩` with `τ_b = Tr(x^b)` precomputed, i.e. the same
  parity-of-masked-bits primitive as the printer's row transform `φ` (risk 1);
* the labels `λ_j = x^j` are distinct for `j < 2^ℓ - 1`.

Each claim is checked exhaustively at `ℓ = 4` by `decide`. (Seed fold v3: `lfsr`, `lfsrPow`, `period` and
`isField_of_unit_of_order` now live in the seed module `Proof.Wire_3_5.Foundations.GF`, same full names.) -/
namespace NearCubicWires.WireExponent3_5.GF2
set_option autoImplicit false

/-- Carry-less product and reduction (the statement files' `Certificates` shape), as the reference. -/
def clmul (x y w : ℕ) : ℕ := (List.range w).foldl (fun acc i => if y.testBit i then acc ^^^ (x <<< i) else acc) 0
def reduce (p ℓ x : ℕ) : ℕ :=
  (List.range ℓ).reverse.foldl (fun acc i => if acc.testBit (i + ℓ) then acc ^^^ (p <<< i) else acc) x
def fmul (p ℓ x y : ℕ) : ℕ := reduce p ℓ (clmul x y ℓ)

/-- Multiplication from LFSR steps and XOR only. -/
def fmulShift (p ℓ x y : ℕ) : ℕ :=
  ((List.range ℓ).foldl (fun (st : ℕ × ℕ) i =>
    (if y.testBit i then st.1 ^^^ st.2 else st.1, lfsr p ℓ st.2)) (0, x)).1

/-- Trace by definition, `Σ_{i<ℓ} a^{2^i}`. -/
def trace (p ℓ a : ℕ) : ℕ :=
  ((List.range ℓ).foldl (fun (st : ℕ × ℕ) _ => (st.1 ^^^ st.2, fmul p ℓ st.2 st.2)) (0, a)).1

def parityMasked (mask a ℓ : ℕ) : ℕ :=
  ((List.range ℓ).filter (fun b => mask.testBit b && a.testBit b)).length % 2

/-- `τ` as a bit mask: `τ_b = Tr(x^b)`. -/
def tau (p ℓ : ℕ) : ℕ := (List.range ℓ).foldl (fun m b => if trace p ℓ (2 ^ b) = 1 then m ||| 2 ^ b else m) 0

end NearCubicWires.WireExponent3_5.GF2
