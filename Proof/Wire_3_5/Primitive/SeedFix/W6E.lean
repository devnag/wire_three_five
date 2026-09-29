import Proof.Wire_3_5.Primitive.SeedFix.W6D

/-! # W6, part 5: the first word phase

P3:2543-2558: after the front end and the fill, the numbers machine reads `n` and `a'` from the request, writes the
top word `frame tw` into both programs' blocks (tape `0`) and the native word `frame nw0` (tape `2`), and reads `M`,
`ncar`, `cap_T`. **`p1W`** and **`p1_spec`**: from the filled state, the two blocks ready for proof 1's program
(tapes `0`, `2` filled, head `0`), the registers `rN = n`, `rA = a'`, `rM = M`, `rNc = ncar`, `rCap = cap_T`, every
other register as found, every other stream's word as found.

Paper quantities of the main type: `n`, `a'`, `M = Σᵢ |supp(topᵢ)|`, `ncar`, `cap_T`, the top word. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedVariables false

namespace NearCubicWires.WireExponent3_5.PrimT.W6
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairRepresentation
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimAsm
open NearCubicWires.WireExponent3_5.FinalPass.Hash4 (wcopyR wcopyR_spec)

variable (cap : ℕ)

attribute [local simp] rN rA rM rNc rCap qa qOP qSP qf qc qp qt

/-- The native word `frame nw0`. -/
abbrev fnw : List Bool := frame PrimThrW.W6Meta.nw0

/-- **The first word phase.** -/
def p1W : WP :=
  .seq readReq (.seq (wcopyR rA qa qt) (.seq (twW (sBC 0) qOP qSP qa) (.seq (wcopyR rA qa qt)
    (.seq (twW (sBE 0) qOP qSP qa) (.seq (nwW (sBC 2) fnw) (.seq (nwW (sBE 2) fnw) (.seq (wcopyR rA qa qt)
      (.seq readM (.seq (SymDec.readUW sNc rNc) (SymDec.readUW sCap rCap))))))))))

/-- **After the first word phase.** -/
structure P1Post (σ τ : WL) (TW : List Bool) (n a' M ncar capT : ℕ) : Prop where
  twC : τ.st (sBC 0) = frame TW ∧ τ.sh (sBC 0) = 0
  twE : τ.st (sBE 0) = frame TW ∧ τ.sh (sBE 0) = 0
  nwC : τ.st (sBC 2) = fnw ∧ τ.sh (sBC 2) = 0
  nwE : τ.st (sBE 2) = fnw ∧ τ.sh (sBE 2) = 0
  st : ∀ s, s ≠ sBC 0 → s ≠ sBE 0 → s ≠ sBC 2 → s ≠ sBE 2 → τ.st s = σ.st s
  sh : ∀ s, s ≠ sReq → s ≠ sNc → s ≠ sCap → (∀ i, s ≠ sPay i) → τ.sh s = σ.sh s
  vN : τ.val rN = n
  vA : τ.val rA = a'
  vM : τ.val rM = M
  vNc : τ.val rNc = ncar
  vCap : τ.val rCap = capT
  v0 : ∀ r, r ≠ rN → r ≠ rA → r ≠ rM → r ≠ rNc → r ≠ rCap → τ.val r = σ.val r
  cell : τ.cell = σ.cell

theorem sPay_ne_blk (i : Fin 4) (k : Fin 61) : sPay i ≠ sBC k ∧ sPay i ≠ sBE k := by
  constructor <;> intro h <;> have := congrArg Fin.val h <;> simp only [sPay, sBC, sBE] at this <;> omega

end NearCubicWires.WireExponent3_5.PrimT.W6
