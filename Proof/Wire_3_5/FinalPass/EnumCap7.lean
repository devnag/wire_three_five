import Proof.Wire_3_5.FinalPass.EnumCap4
import Proof.Wire_3_5.FinalPass.EnumCap6

/-! # The child's cost at a call, generic in the batch, part 3: `hcost`

P3:3011-3016, 1905-1906: one child of the call's family runs the enumeration unit, C6's assembler and the printer
child (metadata, compiler, framer, printer); `coreCost_le` bounds its steps by `210000(q+1)^3 + Y + T` when every
number the child reads is `≤ q` and the compiler's cost is `≤ Y`, `T` the printer's table term. Here: the child
expression's word from `qG` (`chV_word_le`), the fixed fields from `256·B³` (`prepost_le`), the request's cuts from the
charged occurrence count `O` (`cuts_le`), and `Y = 52802·(O·(256B³ + 2qG + 1)·B_n)^8` (`c3Cost_le_B`, `c3Input_len`).
Mode-generic (SYM, THR, HASH and the padded batch are instances).

* `tabT`, **`hcost_of`**.

Paper quantity of the main type: one child's step count at the call. -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.FinalPass.EnumCap
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.SeedFix
open NearCubicWires.WireExponent3_5.Sampler
open NearCubicWires.WireExponent3_5.CompilerMachine NearCubicWires.WireExponent3_5.CompilerMachine.Pool
open NearCubicWires.WireExponent3_5.CompilerMachine.Req NearCubicWires.WireExponent3_5.CompilerMachine.Top
open NearCubicWires.RepairRepresentation NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.ListMachine.Rec (exprWord)

/-- The printer's table term of `coreCost_le`. -/
noncomputable def tabT (wa : WilliamsAlgorithm) (R0 : C3Req) : ℕ :=
  (CompetitorCountTable.coefficient wa + 1034014) * (2 ^ R0.dRow + 1) ^ 2 *
    (R0.dRow + R0.p + 2) ^ CompetitorCrossScheduler.exponent wa

/-- **One child's steps at every prefix** (the child family's `hcost`), generic in the batch. -/
theorem hcost_of (wa : WilliamsAlgorithm) (a : DecompositionAlgorithm) (R0 : C3Req) (P : SeedParams)
    (TWd Cap nT Rn K : ℕ) (batch : List SExpr) (q O Bn : ℕ)
    (hpm : ∀ V ∈ batch, ∀ t ∈ V, t.1 = 1 ∨ t.1 = -1) (hQ1 : 1 ≤ P.Q) (hQp : R0.P.Q ≤ R0.p)
    (hpre : ∀ (p : List Bool) (b : Bool), p.length < 8 * P.ell →
      (PrimT.C4Child.chR R0 P nT Rn batch (p ++ [b])).Pre a)
    (hO : ∀ (p : List Bool) (b : Bool), p.length < 8 * P.ell →
      (PrimT.C4Child.chR R0 P nT Rn batch (p ++ [b])).occBoundP a ≤ O)
    (hB1 : 1 ≤ Bn) (hBp : R0.p ≤ Bn) (hBw : R0.P.width ≤ Bn)
    (hBP : (poolChildren a R0.P.gates R0.P.flips).length ≤ Bn) (hBh : R0.P.h ≤ Bn) (hBQ : R0.P.Q ≤ Bn)
    (hBd : R0.d ≤ Bn)
    (hl : P.ell ≤ q) (hkh : P.kh ≤ q) (hT : TWd ≤ q) (hC : Cap ≤ q) (hn : nT * 2 ^ (8 + 8 * P.ell + 8 * P.kh) ≤ q)
    (hK : K ≤ q) (hfix : 256 * fixB a R0 ^ 3 ≤ q)
    (hG : PrimT.C4Grp.qG P nT Rn (PrimT.C4Grp.bsz batch) TWd (8 * P.ell) ≤ q) (hdq : R0.dRow ≤ q)
    (hpq : R0.p + 1 ≤ q) (hwq : R0.P.width ≤ q) (hOq : 2 * O ≤ q) (hQq : R0.P.Q ≤ q) :
    ∀ (p : List Bool) (b : Bool) (r : MatrixScoreBatch.Request), p.length < 8 * P.ell →
      MatrixScoreBatch.word r = reqWord R0.dRow (R0.p + 1) R0.P.width R0.cols
        (c3v2Ref a (PrimT.C4Child.chR R0 P nT Rn batch (p ++ [b]))) →
      PrimT.C4Child.coreCost wa a R0 P TWd Cap nT Rn K batch (p ++ [b]) r ≤
        210000 * (q + 1) ^ 3 + 52802 * (O * (256 * fixB a R0 ^ 3 + 2 * PrimT.C4Grp.qG P nT Rn (PrimT.C4Grp.bsz batch) TWd
          (8 * P.ell) + 1) * Bn) ^ 8 + tabT wa R0 := by
  intro p b r hp hw
  have hplen : (p ++ [b]).length ≤ 8 * P.ell := by
    rw [List.length_append, List.length_singleton]; omega
  have hR := hpre p b hp
  have hOp := hO p b hp
  -- the child expression's word
  have hV0 : (exprWord (PrimT.C4Child.chV P nT Rn batch (p ++ [b]))).length ≤
      PrimT.C4Grp.qG P nT Rn (PrimT.C4Grp.bsz batch) TWd (8 * P.ell) :=
    (chV_word_le P nT Rn batch TWd Cap (p ++ [b]) hpm hQ1).trans (qG_mono P nT Rn _ TWd _ _ hplen)
  have hV : (exprWord (PrimT.C4Child.chV P nT Rn batch (p ++ [b]))).length ≤ q := hV0.trans hG
  -- the fixed fields
  have hpp := prepost_le a R0
  have hpre' : (PrimT.C4Child.pre a R0).length ≤ q := by omega
  have hpost' : (PrimT.C4Child.post a R0).length ≤ q := by omega
  -- the cuts
  have hcs : (c3v2Ref a (PrimT.C4Child.chR R0 P nT Rn batch (p ++ [b]))).length ≤ q := by
    rw [c3v2Ref, EquationRow.doubled_length]
    have := cuts_le a _ hR
    omega
  -- the compiler's cost
  have hin := c3Input_len a (PrimT.C4Child.chR R0 P nT Rn batch (p ++ [b]))
  have hin' : (c3Input a (PrimT.C4Child.chR R0 P nT Rn batch (p ++ [b]))).length ≤
      256 * fixB a R0 ^ 3 + 2 * PrimT.C4Grp.qG P nT Rn (PrimT.C4Grp.bsz batch) TWd (8 * P.ell) + 1 := by
    have e1 : (PrimT.C4Child.pre a (PrimT.C4Child.chR R0 P nT Rn batch (p ++ [b]))).length =
        (PrimT.C4Child.pre a R0).length := rfl
    have e2 : (PrimT.C4Child.post a (PrimT.C4Child.chR R0 P nT Rn batch (p ++ [b]))).length =
        (PrimT.C4Child.post a R0).length := rfl
    have e3 : (PrimT.C4Child.chR R0 P nT Rn batch (p ++ [b])).V = PrimT.C4Child.chV P nT Rn batch (p ++ [b]) := rfl
    rw [e1, e2, e3] at hin
    omega
  have hc3 := c3Cost_le_B a (PrimT.C4Child.chR R0 P nT Rn batch (p ++ [b])) hR Bn hB1 hBp hBw hBP hBh hBQ hBd
  have hY : c3Cost a (PrimT.C4Child.chR R0 P nT Rn batch (p ++ [b])) ≤ 52802 * (O * (256 * fixB a R0 ^ 3 +
      2 * PrimT.C4Grp.qG P nT Rn (PrimT.C4Grp.bsz batch) TWd (8 * P.ell) + 1) * Bn) ^ 8 :=
    hc3.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left
      (Nat.mul_le_mul_right _ (Nat.mul_le_mul hOp hin')) 8))
  have := PrimAsm.SFCost.coreCost_le wa a R0 P TWd Cap nT Rn K batch (p ++ [b]) r q _ R0.cols _ hw hQp hl hkh hT hC hn hK
    hpre' hpost' hV hdq hpq hwq hcs hQq hY
  unfold tabT
  exact this

end NearCubicWires.WireExponent3_5.FinalPass.EnumCap
