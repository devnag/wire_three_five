import Mathlib

/-! # G-ARCH pilot: the two components' executable references (S1 twins, P19/P25)

Pattern P1 (enumerate + evaluate + sort + join; the kernel shared by C1 and C3):
`joinBrute a b dL dR = #{(z_L, z_R) : a(z_L) + b(z_R) = 0}` (P3:1339-1356, 1734-1738), and the
count-product form `joinByCounts` that a sort-then-merge machine computes.

Pattern P2 (GF(2^ℓ) + binary Gaussian elimination; the kernel of S4 and C4):
`condProbGauss` = the exact conditional probability that the `2h`-wise polynomial generator puts
every listed sample label at its listed projected position, given a fixed seed prefix, computed by
elimination (P3:2950-2957, 2268-2271); `condProbBrute` counts completions directly.

Both are checked against brute force at tiny parameters by `decide`. Field elements and GF(2)
polynomials are bit masks in `ℕ` (the encoding of the statement files' `WireProof/Certificates.lean`). -/
namespace NearCubicWires.WireExponent3_5.JoinElimination
set_option autoImplicit false

/-! ## P1 -/



/-! ## P2 -/

/-- Carry-less product of GF(2) polynomials (bit masks). -/
def clmul (x y : ℕ) (w : ℕ) : ℕ :=
  (List.range w).foldl (fun acc i => if y.testBit i then acc ^^^ (x <<< i) else acc) 0

/-- Reduction modulo a degree-`ℓ` modulus `p` (bit mask with bit `ℓ` set), for inputs below `2^(2ℓ)`. -/
def reduce (p ℓ x : ℕ) : ℕ :=
  (List.range ℓ).reverse.foldl (fun acc i => if acc.testBit (i + ℓ) then acc ^^^ (p <<< i) else acc) x

def fmul (p ℓ x y : ℕ) : ℕ := reduce p ℓ (clmul x y ℓ)

def fpow (p ℓ x : ℕ) : ℕ → ℕ
  | 0 => 1
  | n + 1 => fmul p ℓ (fpow p ℓ x n) x

/-- The generator: `f(λ) = Σ_{i<2h} a_i λ^i`, seed = the `2h·ℓ` coefficient bits, `a_i` = bits
`[iℓ, (i+1)ℓ)` of the seed (P3:2932-2938). -/
def gen (p ℓ twoH seed lam : ℕ) : ℕ :=
  (List.range twoH).foldl (fun acc i =>
    acc ^^^ fmul p ℓ ((seed >>> (i * ℓ)) % 2 ^ ℓ) (fpow p ℓ lam i)) 0

def proj (k v : ℕ) : ℕ := v % 2 ^ k

/-- Brute force: the fraction of completions of `prefix` (its low `plen` bits fixed) satisfying all
constraints, as (count, total). -/
def condProbBrute (p ℓ twoH k plen pre : ℕ) (cons : List (ℕ × ℕ)) : ℕ × ℕ :=
  let S := twoH * ℓ
  let rest := S - plen
  (((List.range (2 ^ rest)).filter (fun r =>
      let seed := pre % 2 ^ plen + (r <<< plen)
      cons.all (fun c => decide (proj k (gen p ℓ twoH seed c.1) = c.2)))).length, 2 ^ rest)

/-- One GF(2) row: variable bits (mask over the remaining seed bits) and the right-hand side. -/
abbrev Row := ℕ × Bool

/-- The linear system: output bit `c` of `proj(f(λ))` equals `Σ_{i,b} seedbit(i,b)·bit_c(x^b·λ^i)`;
fixed prefix bits move to the right-hand side (P3:2950-2952). -/
def system (p ℓ twoH k plen pre : ℕ) (cons : List (ℕ × ℕ)) : List Row :=
  cons.flatMap (fun con => (List.range k).map (fun c =>
    let coeff : ℕ → Bool := fun j => (fmul p ℓ (2 ^ (j % ℓ)) (fpow p ℓ con.1 (j / ℓ))).testBit c
    let fixed := (List.range plen).foldl (fun acc j => xor acc (coeff j && pre.testBit j)) false
    let mask := (List.range (twoH * ℓ - plen)).foldl
      (fun acc j => if coeff (plen + j) then acc ||| (1 <<< j) else acc) 0
    (mask, xor (con.2.testBit c) fixed)))

/-- Gaussian elimination over GF(2): returns `(consistent, rank)`. -/
def gauss (nvars : ℕ) (rows : List Row) : Bool × ℕ :=
  let step := fun (st : List Row × ℕ) (col : ℕ) =>
    let (rs, rank) := st
    match rs.find? (fun r => r.1.testBit col) with
    | none => (rs, rank)
    | some piv =>
      let rs' := (rs.erase piv).map (fun r => if r.1.testBit col then (r.1 ^^^ piv.1, xor r.2 piv.2) else r)
      (rs', rank + 1)
  let (rest, rank) := (List.range nvars).foldl step (rows, 0)
  (rest.all (fun r => !(r.1 == 0 && r.2)), rank)

/-- Elimination form: probability `2^{-rank}` if consistent, else 0, as (count, total). -/
def condProbGauss (p ℓ twoH k plen pre : ℕ) (cons : List (ℕ × ℕ)) : ℕ × ℕ :=
  let rest := twoH * ℓ - plen
  let (ok, rank) := gauss rest (system p ℓ twoH k plen pre cons)
  (if ok then 2 ^ (rest - rank) else 0, 2 ^ rest)


end NearCubicWires.WireExponent3_5.JoinElimination
