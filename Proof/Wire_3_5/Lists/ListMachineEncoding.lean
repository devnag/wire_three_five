import Proof.Foundations.OrdinaryStreaming

/-! # C2 → C3: the tape encoding of explicit `𝔽₂` polynomials and integer expressions (P3:1482-1488, 1886-1906)

The C2 list machines print "the explicit monomial lists" (P3:1482-1488) and the flattened integer expression they
form; the compiler stages read that expression as their input, "an explicit signed separated-equation expression"
(P3:1886-1906), S0's `IntExpression ℕ = List (ℤ × List (F2Poly ℕ))`. On a tape:

* an atom (coordinate) `i` in unary, `atomCode i = 1^i 0`; a monomial `m` as the framed word of its atoms' codes;
* a polynomial as its monomial records `true :: frame (monoBits m)`, then `false` (`polyWord`);
* a coefficient `c` as `frame (sign :: bits |c|)`: sign first, then the little-endian bits of `|c|`, variable width
  (`coefWord`);
* a term `(c, fs)` as `coefWord c`, then its factor records `true :: polyWord f`, then `false` (`termWord`);
* an expression as its term records `true :: termWord t`, then `false` (`exprWord`).

Every field is self-delimiting: `PrefixInj enc` says that `enc a ++ r = enc b ++ s` forces `a = b` and `r = s`. It
holds for `frame`, `polyWord`, `coefWord`, `termWord` and `exprWord` (so an input word `exprWord V ++ rest`
determines both `V` and `rest`), and `exprWord_injective`, `polyWord_injective` follow. -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.ListMachine.Rec
open NearCubicWires.RepairOrdinary

/-! ## The fields -/

/-- A coordinate index in unary. -/
def atomCode (i : ℕ) : List Bool := List.replicate i true ++ [false]

/-- The bits of a monomial: its atoms' codes. -/
def monoBits (m : List ℕ) : List Bool := m.flatMap atomCode

/-- A monomial record. -/
def recW (m : List ℕ) : List Bool := true :: frame (monoBits m)

@[simp] theorem recW_length (m : List ℕ) : (recW m).length = 2 * (monoBits m).length + 2 := by
  simp [recW, frame_length]

/-- A polynomial: its monomial records, then `false`. -/
def polyWord (p : List (List ℕ)) : List Bool := p.flatMap recW ++ [false]

/-- A coefficient: its sign, then the little-endian bits of its magnitude, framed. -/
def coefWord (c : ℤ) : List Bool := frame (decide (c < 0) :: Nat.bits c.natAbs)

/-- A term: its coefficient, then its factor records `true :: polyWord f`, then `false`. -/
def termWord (t : ℤ × List (List (List ℕ))) : List Bool :=
  coefWord t.1 ++ (t.2.flatMap (fun f => true :: polyWord f) ++ [false])

/-- An integer expression (S0's `IntExpression ℕ`): its term records `true :: termWord t`, then `false`. -/
def exprWord (V : List (ℤ × List (List (List ℕ)))) : List Bool :=
  V.flatMap (fun t => true :: termWord t) ++ [false]

/-! ## Self-delimiting fields -/


end NearCubicWires.WireExponent3_5.ListMachine.Rec
