import Proof.Wire_3_5.Selection.MathDefs

/-! # C1.4: the machine's order of the halves and error rows (P3:1339-1345, 1195-1197)

Paper: "Enumerate its `2^k` error rows. For each gate and row, the four threshold predicates have integer scores of the
form `a_j(z_L) + b_j(z_R)` [...] Enumerate each half's score vectors" (P3:1339-1345); "The center bits can be divided
into two halves differing in size by at most one while keeping each code block on its assigned side" (P3:1196-1197).

The machine enumerates each half as a counter over its bits and each side's errors as a counter over `s`-bit codes.
This module fixes that order, all computable:
* the machine position `p` of a half's bit and its coordinate: `coordL`, `coordR` (the blocks in DESCENDING block order,
  `b` bits each, then the free coordinates), and their inverses `posL`, `posR`;
* `decX`, `decY`: a counter value as a half; `decU`: a counter value as a side's errors (segment `t` of `s` bits is the
  code of block `h − 1 − t`: `0` is no error, `c` is `e_{c−1}`);
* `enumL`, `enumR`: the machine's lists of `(errors, half)` pairs (errors outer, half inner).
The descending block order makes every walk of a point routine forward: block `h − 1 − t` of the left half meets the
coset counter's segment `h + t` (its code `c_{h−1−t}`), and of the right half the segment `t`.
Paper quantity: the enumeration of each half's score vectors. -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.SelectionMachine.Gate
open NearCubicWires NearCubicWires.WireExponent3_5.Shared NearCubicWires.WireExponent3_5.Stars
open NearCubicWires.WireExponent3_5.SelectionMachine.Math

variable (P : StarParams)

/-- Blocks per side. -/
def hh : ℕ := P.r / 2

/-- Free coordinates on the left: `⌈(n − rb)/2⌉`. -/
def fL : ℕ := (P.n - P.r * P.b + 1) / 2

/-- Free coordinates on the right: `⌊(n − rb)/2⌋`. -/
def fR : ℕ := (P.n - P.r * P.b) / 2

/-- Bits of the left half. -/
def lw : ℕ := hh P * P.b + fL P

/-- Bits of the right half. -/
def rw : ℕ := hh P * P.b + fR P

/-- The coordinate of left machine position `p`: block `h − 1 − p/b`, index `p mod b`; then the free coordinates. -/
def coordL (p : ℕ) : ℕ :=
  if p < hh P * P.b then (hh P - 1 - p / P.b) * P.b + p % P.b else P.r * P.b + (p - hh P * P.b)

/-- The coordinate of right machine position `p`: block `h + (h − 1 − p/b)`; then the free coordinates. -/
def coordR (p : ℕ) : ℕ :=
  if p < hh P * P.b then (hh P + (hh P - 1 - p / P.b)) * P.b + p % P.b
  else P.r * P.b + fL P + (p - hh P * P.b)

/-- The machine position of a left coordinate. -/
def posL (c : ℕ) : ℕ :=
  if c < hh P * P.b then (hh P - 1 - c / P.b) * P.b + c % P.b else hh P * P.b + (c - P.r * P.b)

/-- The machine position of a right coordinate. -/
def posR (c : ℕ) : ℕ :=
  if c < P.r * P.b then (hh P - 1 - (c / P.b - hh P)) * P.b + c % P.b
  else hh P * P.b + (c - P.r * P.b - fL P)

/-- A left counter value as a left half: coordinate `c` reads bit `posL c`. -/
def decX (x : ℕ) : P.SideL → Bool := fun i => x.testBit (posL P i.1.val)

/-- A right counter value as a right half. -/
def decY (y : ℕ) : P.SideR → Bool := fun i => y.testBit (posR P i.1.val)

/-- The code of block `j` in an errors counter: segment `h − 1 − j`. -/
def errCode (u : ℕ) (j : ℕ) : ℕ := u / 2 ^ (P.s * (hh P - 1 - j)) % 2 ^ P.s

/-- An errors counter value as the errors of one side: code `0` is no error, code `c ≥ 1` is `e_{c−1}`. -/
def decU (u : ℕ) : P.Errors := fun j =>
  if hc : errCode P u j.val = 0 then none
  else some ⟨errCode P u j.val - 1, by
    have h1 := Nat.mod_lt (u / 2 ^ (P.s * (hh P - 1 - j.val))) (Nat.two_pow_pos P.s)
    have h2 := P.b_succ
    unfold errCode at hc ⊢
    omega⟩

/-- **The machine's left points' order**: errors outer, half inner. -/
def enumL : List (P.Errors × (P.SideL → Bool)) :=
  (List.range (2 ^ (P.s * hh P))).flatMap fun u => (List.range (2 ^ lw P)).map fun x => (decU P u, decX P x)

/-- **The machine's right points' order.** -/
def enumR : List (P.Errors × (P.SideR → Bool)) :=
  (List.range (2 ^ (P.s * hh P))).flatMap fun v => (List.range (2 ^ rw P)).map fun y => (decU P v, decY P y)

end NearCubicWires.WireExponent3_5.SelectionMachine.Gate
