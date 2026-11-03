import Proof.Wire_3_5.Primitive.SeedFix.HbLink
import Proof.Wire_3_5.Primitive.SeedFix.C4WA
import Proof.Wire_3_5.Primitive.SeedFix.C4SymKB7Base
import Proof.Wire_3_5.Primitive.SeedFix.SeedFixTypesBase
import Proof.Wire_3_5.Primitive.SeedFix.SeedFixHashObjective

/-! # C4H: the HASH stage's contract (types only)

`filt:soft`, P3:2221-2336: "Let `p` be a prefix of the `s_h`-bit hash seed [...] At prefix `p` print
`V_p(z) = Δ₀Σ_yΣ_e F_aux(e,x(y,z))·E_h[H_h(x(y,z)) | p]` [...] Reduce the printed signed score modulo `2^{Q_aux}`
separately at each column [...] Only then sum over columns [...] Greedily choose a child with no larger value, using at
most two printer calls per hash bit." The HASH stage (consumer `C4At.hash`: `frame (thrIn …)` from the THR request and
the HASH tape) is the C4 wrapper (`C4Wrap.wrapM`, `wrap_run`) around four owned parts:

* (i): **`HashFamAt`**, the HASH child family: a `C4Loop.ChildFam` over the `s_h = 2t·ℓ₀` hash seed bits whose loop
  decisions are the fixed hash's bits (`bits`, at the call `List.ofFn thrHashBits`), at the fixed interface below:
  its tapes (`CTH`, the assembler's, the Hb unit's `HU`, the printer child's), kept tapes `hKeepN`, kept words `hKN`
  (the compiler's fields, the Hb printer's 94 static words `KW`, `1^{Q'}`, the mask), prefix tape `A.t + 94`, sum tape.
  The Hb printer's static words at a call are `hb0 (hbX D c 0 0)` (`hbX`: the call's data `D`, capacities `c`).
* (ii) (setup) and (docking): **`HBank`**, the HASH setup's exit bank on its big bank: the request, the HASH
  tape on port `1`, the compiler's fields, `1^{uu}`, `1^{2^ρ}`, the log, the loop's cells blank (SymBank's fields on
  the layout `L`), and the 94 kept words `KW` and `1^{Q'}` on tapes `hkT`, `hqT` of the setup's choice.
* (iii): **`HashFinSpec`**, the HASH finisher: from `frame w` and the loop's `frame bits`, `frame (w ++ frame bits)`.
* (iv): **`HashEAt`**, the side conditions at a HASH call: the Hb printer's run conditions at every child, the
  compiler's precondition and cost (`hCoreCost`), `Q ≤ pr`, the exact recovery range, the pad `2^ρ`, `CoefFit`,
  `1 ≤ h`.

Paper quantity of the main types: the HASH stage's loop (the fixed hash's bits) and its inputs. -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.PrimT.C4H
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.RepairOrdinary NearCubicWires.LocalBitMultitape
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimT.C4Set
open NearCubicWires.RepairOrdinary.SignedSortKey (binary)

noncomputable section

/-! ## The Hb printer's data at a HASH call -/

/-- The Hb printer's free capacities (register and log capacities, the elimination's constants). -/
structure HbCaps where
  cap : ℕ
  capL : ℕ
  m : ℕ
  c1 : ℕ
  c2 : ℕ
  c3 : ℕ
  c4 : ℕ
  RV : ℕ
  cL : ℕ
  cE : ℕ
  cK : ℕ
  cC : ℕ

/-- **The HASH call's printed-objective data**: the majorant's parameters, the pool's gate count `G`, the star's
`N = 2^{k_h}`, the aux seeds `nE`, the HASH tape's rows `Fs` (as F₂ polynomials, row `q·nE + e`), the populations. -/
structure HashData where
  MP : Filters.MajorantParams
  G : ℕ
  N : ℕ
  nE : ℕ
  Fs : List (List (List ℕ))
  pops : List (Bool × List ℕ)

/-- The Hb printer's data record at `D`, `c`, at the child prefix `(plen, pfx)`. -/
def hbX (D : HashData) (c : HbCaps) (plen pfx : ℕ) : HbM.HbX :=
  ⟨D.Fs, D.pops, HbM.wsOf D.MP, D.G, D.N ^ 2, D.nE, D.MP.J, 2 * D.MP.t, D.MP.ell0, D.MP.refMod, plen, pfx, c.m,
    c.c1, c.c2, c.c3, c.c4, c.RV, c.cL, c.cE, c.cK, c.cC, c.cap, c.capL⟩

/-- The Hb printer's streams before cell `0` (`HbX.Streams 0`, the flags `GF`, `VAL` clear). -/
def st0 (X : HbM.HbX) : Fin 24 → List Bool := fun i =>
  if i.val = 2 then HbM.htWord X.Fs
  else if i.val = 3 then HbM.popsWord X.pops
  else if i.val = 4 then HbM.wtWord X.Ws
  else if i.val = 5 then binary X.L 0
  else if i.val = 6 then HbM.unary 0 (X.J + 1)
  else if i.val = 7 then HbM.unary 0 X.P
  else if i.val = 8 then HbM.unary 0 X.nE
  else if i.val = 9 then HbM.unary 0 X.N2
  else if i.val = 11 then [false]
  else if i.val = 13 then [false]
  else if i.val = 14 then [decide (0 < X.n)]
  else if i.val = 15 then List.replicate X.T2 true
  else if i.val = 16 then List.replicate X.ℓ true
  else if i.val = 17 then List.replicate X.J true
  else if i.val = 18 then List.replicate X.G true
  else if i.val = 19 then List.replicate (X.N2 - 1) true
  else if i.val = 20 then List.replicate (X.nE - 1) true
  else if i.val = 21 then List.replicate (X.P - 1) true
  else if i.val = 22 then List.replicate X.L true
  else []

/-- The elimination's initial registers. -/
def R0 (X : HbM.HbX) : SeedFix.Regs := ⟨0, 0, 0, 0, 0, [], false, [], List.replicate (X.T2 * (X.ℓ * (2 * X.ℓ + 1))) false⟩

/-- **The Hb printer's 94-tape bank before cell `0`** (the kept words `KW` are `hb0 (hbX D c 0 0)`). -/
def hb0 (X : HbM.HbX) : Fin 94 → List Bool := HbM.hbBank X.cap X.capL (HbM.bnd (st0 X)) (X.ex (R0 X) [] [] [])

/-- The printed objective at the child prefix `p'`: `hashTermsM` (the machine prints it). -/
def hV (D : HashData) (p' : List Bool) : SeedFix.SExpr :=
  HashB.hashTermsM D.MP D.G D.N D.nE D.Fs D.pops p'.length (SeedFix.listNum p')

/-- The compiler's request of the child prefix `p'`: the call's request with the child's expression. -/
def hR (R0 : CompilerMachine.Req.C3Req) (D : HashData) (p' : List Bool) : CompilerMachine.Req.C3Req :=
  { R0 with V := hV D p' }

/-! ## (i) The HASH child family's interface -/

/-- The Hb unit's tapes: the 94 kept static words, the prefix, the working Hb bank (94), 64 scratch tapes. -/
def HU : ℕ := 94 + 1 + 94 + 64

/-- The child's tapes (before the masked reset's log): the assembler's, the Hb unit's, the printer child's. -/
abbrev CTH (A : C4Iface.AsmStage) (wa : RepairRepresentation.WilliamsAlgorithm) : ℕ := A.t + (HU + C4Pipe.CN wa)

/-- The kept tapes, by index: the assembler's two field words, the unit's 94 words and the prefix, the printer child's
`1^{Q'}` and mask. -/
def hKeepN (A : C4Iface.AsmStage) (wa : RepairRepresentation.WilliamsAlgorithm) (v : ℕ) : Bool :=
  if v < A.t then decide (v = A.pA.val ∨ v = A.pB.val)
  else if v < A.t + HU then decide (v - A.t ≤ 94)
  else if v < CTH A wa then decide (v - A.t - HU = (C4Pipe.childQQ wa).val ∨ v - A.t - HU = (C4Pipe.childUU wa).val)
  else false

/-! ## (ii) The HASH setup's exit bank -/

/-! ## (iii) The HASH finisher -/

/-- **(iii) The HASH finisher**: from the request's `frame w` on its input `iW` and the loop's `frame bits` on its input
`iP` (every other tape blank), within `nf w bits` steps, `frame (w ++ frame bits)` on its output `o`. -/
def HashFinSpec {tf sf : ℕ} (Mf : Machine tf sf) (iW iP o : Fin tf) (nf : List Bool → List Bool → ℕ) : Prop :=
  iW ≠ iP ∧ ∀ w bits : List Bool, ∃ tout : Fin tf → List Bool,
    ExtDecompositionBatch.Step Mf (nf w bits) (fun _ => 0)
      (fun i => if i = iW then frame w else if i = iP then frame bits else []) (fun _ => 0) tout ∧
      tout o = frame (w ++ frame bits)

/-! ## (iv) The side conditions at a HASH call -/

/-- The Hb unit's prep (the working bank from the kept words and the prefix) and read-out steps (builds within). -/
def hbPrepCost (X : HbM.HbX) : ℕ := 64 * ((List.ofFn (hb0 X)).flatten.length + 94) + 64 * (X.T2 * X.ℓ + 64) + 4096

/-- The child's steps at the prefix `p'`, the Hb printer's cell bound `Kc` and the printer's request `r`. -/
def hCoreCost (wa : RepairRepresentation.WilliamsAlgorithm) (a : RepairRepresentation.DecompositionAlgorithm)
    (R0 : CompilerMachine.Req.C3Req) (D : HashData) (c : HbCaps) (Kc : ℕ) (p' : List Bool)
    (r : MatrixScoreBatch.Request) : ℕ :=
  hbPrepCost (hbX D c p'.length (SeedFix.listNum p')) +
    ((hbX D c p'.length (SeedFix.listNum p')).n * (Kc + 2) + 1) + 64 * ((ListMachine.Rec.exprWord (hV D p')).length + 64) +
    C4Iface.asmCost (C4Child.pre a R0) (C4Child.post a R0) (hV D p') + C4Pipe.childCost wa a (hR R0 D p') r

/-- **(iv) The side conditions at a HASH call** (C1b's, instances of its batch-generic SymEAt): at the free numbers
`fr` (`TWd, Cap, Q', h, m, pr, ρ`), the data `D`, the capacities `c`, the Hb cell bound `Kc`, the child bound `Kch`,
the compiler's request `R0` (the call's THR pool at `h = fr 3`, `Q' = fr 2`, `m = fr 4`, `pr = fr 5`), and `s_h`:
the Hb printer's conditions at every child, the compiler's precondition, `Q' ≤ pr`, the cost, the exact recovery
range, the pad `2^ρ` over the family's cell, `CoefFit` and `1 ≤ h`. -/
def HashEAt (wa : RepairRepresentation.WilliamsAlgorithm) (a : RepairRepresentation.DecompositionAlgorithm)
    (R0 : CompilerMachine.Req.C3Req) (D : HashData) (c : HbCaps) (fr : Fin 7 → ℕ) (Kc Kch sh : ℕ) : Prop :=
  (∀ (p : List Bool) (b : Bool), p.length < sh →
      (hbX D c (p ++ [b]).length (SeedFix.listNum (p ++ [b]))).HbOk ∧
      (∀ cc < (hbX D c (p ++ [b]).length (SeedFix.listNum (p ++ [b]))).n,
        (hbX D c (p ++ [b]).length (SeedFix.listNum (p ++ [b]))).CellOk cc ∧
        (hbX D c (p ++ [b]).length (SeedFix.listNum (p ++ [b]))).cellCost cc ≤ Kc)) ∧
  (∀ (p : List Bool) (b : Bool), p.length < sh → (hR R0 D (p ++ [b])).Pre a) ∧
  R0.P.Q ≤ R0.p ∧
  (∀ (p : List Bool) (b : Bool) (r : MatrixScoreBatch.Request), p.length < sh →
    MatrixScoreBatch.word r = CompilerMachine.Req.reqWord R0.dRow (R0.p + 1) R0.P.width R0.cols
      (CompilerMachine.Req.c3v2Ref a (hR R0 D (p ++ [b]))) →
    hCoreCost wa a R0 D c Kc (p ++ [b]) r ≤ Kch) ∧
  (∀ p' : List Bool, p'.length ≤ sh → ∀ ρ : ℕ → Bool,
    0 ≤ Shared.IntExpression.eval (hV D p') ρ ∧ (2 : ℤ) ^ (R0.m - 1) * Shared.IntExpression.eval (hV D p') ρ < 2 ^ R0.P.Q) ∧
  (2 * Kch + 2) + 1 + ((2 * Kch + 2) + 1 + (2 * C4Loop.cmpCost (R0.P.Q + (2 * R0.dRow + 2 * (R0.p + 1) + 4))
    (List.replicate sh false) + 2)) + 1 ≤ 2 ^ fr 6 ∧
  CompilerMachine.Pool.CoefFit a R0.P ∧
  1 ≤ R0.P.h

end

end NearCubicWires.WireExponent3_5.PrimT.C4H
