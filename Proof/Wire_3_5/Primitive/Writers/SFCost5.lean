import Proof.Wire_3_5.Primitive.SeedFix.C4Child
import Proof.Hierarchy.CompetitorCountTableBounds
import Proof.Hierarchy.CompetitorCountRecordRequestBounds
import Proof.Hierarchy.CompetitorSameBucketDenseBounds
import Proof.CaseAnalysis.FinalRoundCursor

/-! # polynomial bounds, part 5: one child's step bound `C4Child.coreCost`

"For each candidate child prefix, print its signed equation expression, reduce modulo the chosen power of two at each
column, and sum the recovered integers" (P3:3034-3036). One child is the enumeration unit (`C4Dock.euCost`), the
assembler (`C4Iface.asmCost`) and the printer child (`C4Pipe.childCost`: the metadata, the compiler, the framer and
base's printer with its sum). The bound keeps the three kinds of terms apart, so that the free numbers' pad can cover
each by its own class:
* a polynomial in one bound `q` of the call's numbers (the rulers `ℓ, kh, TWd, Cap`, the enumeration's `nT·2^w` and
  `K`, the compiler's pre/post words and the child's expression word, `Q'`, `dRow`, `p`, the width, the cut count);
* the compiler's cost `c3Cost` (bounded by `CompilerMachine.Top.c3Cost_le_gB`, P3:1905-1906), as a parameter `Y`;
* the printer's table work `(U+1)²·(dRow+p+2)^e`, `U = 2^dRow` (base's `CompetitorCountTable.budget_bound` and
  `CompetitorCountRecordRequest.budget_bound`), with the Williams algorithm's constant and exponent.
The printer's request is read off its word (`reqWord_fields`), exactly the premise of the child family's `hcost`.

Paper quantity of the main type: the step bound of one child (print, assemble, compile, sum; P3:3034-3037). -/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace NearCubicWires.WireExponent3_5.PrimAsm.SFCost
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.PrimT
open NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation NearCubicWires.WireExponent3_5.Sampler
open NearCubicWires.WireExponent3_5.ListMachine.Rec (exprWord)

/-! ## The request's header -/

theorem rep_false_cancel : ∀ (a b : ℕ) (x y : List Bool),
    List.replicate a true ++ false :: x = List.replicate b true ++ false :: y → a = b ∧ x = y
  | 0, 0, x, y, h => by simpa using h
  | 0, b + 1, x, y, h => by simp [List.replicate_succ] at h
  | a + 1, 0, x, y, h => by simp [List.replicate_succ] at h
  | a + 1, b + 1, x, y, h => by
    simp only [List.replicate_succ, List.cons_append, List.cons.injEq, true_and] at h
    obtain ⟨e, h'⟩ := rep_false_cancel a b x y h
    exact ⟨by rw [e], h'⟩

/-- **`natWord` is self-delimiting**: a common prefix of two concatenations determines the number and the rest. -/
theorem natWord_append_cancel {a b : ℕ} {x y : List Bool} (h : natWord a ++ x = natWord b ++ y) : a = b ∧ x = y := by
  unfold natWord WilliamsPublishedForm.framedNatBits at h
  simp only [List.append_assoc, List.cons_append] at h
  obtain ⟨e, h'⟩ := rep_false_cancel _ _ _ _ h
  have hl : (WilliamsPublishedForm.fixedWidthNatBits (natBitLength a) a).length =
      (WilliamsPublishedForm.fixedWidthNatBits (natBitLength b) b).length := by
    simp [WilliamsPublishedForm.fixedWidthNatBits, e]
  obtain ⟨hf, hxy⟩ := List.append_inj h' hl
  rw [e] at hf
  have ha : a < 2 ^ natBitLength b := by
    rw [← e]; unfold natBitLength; exact Nat.lt_pow_succ_log_self (by norm_num) a
  have hb : b < 2 ^ natBitLength b := by unfold natBitLength; exact Nat.lt_pow_succ_log_self (by norm_num) b
  exact ⟨CloseoutFinalC10RoundCursor.fixedWidthNatBits_inj ha hb hf, hxy⟩

/-- **The printer's request from its word**: the header's four numbers. -/
theorem reqWord_fields (r : MatrixScoreBatch.Request) (d p w : ℕ) (cols : List ℕ) (cs : List MatrixScoreBatch.Cut)
    (h : MatrixScoreBatch.word r = CompilerMachine.Req.reqWord d p w cols cs) :
    r.d = d ∧ r.p = p ∧ r.Gates = cs.length ∧ r.width = w := by
  unfold MatrixScoreBatch.word MatrixScoreBatch.header CompilerMachine.Req.reqWord at h
  simp only [List.append_assoc] at h
  obtain ⟨h1, h⟩ := natWord_append_cancel h
  obtain ⟨h2, h⟩ := natWord_append_cancel h
  obtain ⟨h3, h⟩ := natWord_append_cancel h
  obtain ⟨h4, -⟩ := natWord_append_cancel h
  exact ⟨h1, h2, h3, h4⟩

/-! ## The enumeration unit -/

/-- The arm's cost is linear in its rulers. -/
theorem armCost_le (N : C4Arm.Nums) : C4Arm.armCost N ≤ 1000 * N.mx + 10000 := by
  simp only [C4Arm.armCost, C4Arm.loadCost, C4Arm.armWrs, C4Arm.costWr, C4Arm.wrConst, C4Arm.wrFrame,
    C4Arm.wrFrames8, C4Arm.wrZeros, C4Arm.frameZCost, C4Arm.frames8Cost, C4Arm.Nums.mx, List.length_cons,
    List.length_nil, frame_length, List.length_replicate]
  omega

theorem nums_mx_le (P : SeedParams) (TWd Cap q : ℕ) (hl : P.ell ≤ q) (hk : P.kh ≤ q) (hT : TWd ≤ q) (hC : Cap ≤ q) :
    (C4Dock.nums P TWd Cap).mx ≤ 60 * (q + 1) ^ 2 := by
  simp only [C4Dock.nums, C4Arm.Nums.mx]
  have h2 : P.ell * (2 * P.ell + 1) ≤ q * (2 * q + 1) := Nat.mul_le_mul hl (by omega)
  nlinarith

/-- **The enumeration unit's cost** at every number `≤ q`. -/
theorem euCost_le (P : SeedParams) (TWd Cap nT K q : ℕ) (hl : P.ell ≤ q) (hk : P.kh ≤ q) (hT : TWd ≤ q)
    (hC : Cap ≤ q) (hn : nT * 2 ^ (8 + 8 * P.ell + 8 * P.kh) ≤ q) (hK : K ≤ q) :
    C4Dock.euCost P TWd Cap nT K ≤ 150000 * (q + 1) ^ 2 := by
  unfold C4Dock.euCost
  have ha := armCost_le (C4Dock.nums P TWd Cap)
  have hm := nums_mx_le P TWd Cap q hl hk hT hC
  have hp : nT * 2 ^ (8 + 8 * P.ell + 8 * P.kh) * (K + 3) ≤ q * (q + 3) := Nat.mul_le_mul hn (by omega)
  nlinarith

/-! ## The assembler, the metadata, the framer -/

theorem asmCost_le (PRE POST : List Bool) (V : List (ℤ × List (List (List ℕ)))) (q : ℕ) (h1 : PRE.length ≤ q)
    (h2 : POST.length ≤ q) (h3 : (exprWord V).length ≤ q) : C4Iface.asmCost PRE POST V ≤ 12288 * (q + 1) := by
  unfold C4Iface.asmCost; omega

theorem prepCost_eq (q u : ℕ) : C4Pipe.prepCost q u = 14 * q + 14 * u + 12 := by unfold C4Pipe.prepCost; omega

theorem nbl_le (x : ℕ) : natBitLength x ≤ x + 1 := by
  unfold natBitLength; have := Nat.log_le_self 2 x; omega

theorem two_pow_nbl_le (x : ℕ) : 2 ^ natBitLength x ≤ 2 * x + 2 := by
  unfold natBitLength
  rw [pow_succ]
  rcases Nat.eq_zero_or_pos x with h | h
  · subst h; simp
  · have := Nat.pow_log_le_self 2 (Nat.pos_iff_ne_zero.mp h); omega

theorem rdC_le (x q : ℕ) (hx : x ≤ q) : C4Frame.rdC x ≤ 360 * (q + 1) ^ 2 := by
  unfold C4Frame.rdC
  have h1 := nbl_le x
  have h2 := two_pow_nbl_le x
  calc (natBitLength x + 2) * (40 * 2 ^ natBitLength x + 40) ≤ (3 * (q + 1)) * (120 * (q + 1)) :=
        Nat.mul_le_mul (by omega) (by omega)
    _ = 360 * (q + 1) ^ 2 := by ring

theorem wtC_le (x q : ℕ) (hx : x ≤ q) : C4Frame.wtC x ≤ 2200 * (q + 1) ^ 2 := by
  unfold C4Frame.wtC
  have h1 := nbl_le x
  calc (natBitLength x + 10) * (100 * x + 200) ≤ (11 * (q + 1)) * (200 * (q + 1)) :=
        Nat.mul_le_mul (by omega) (by omega)
    _ = 2200 * (q + 1) ^ 2 := by ring

theorem lenC_le (d p G w q : ℕ) (hd : d ≤ q) (hp : p ≤ q) (hG : G ≤ q) (hw : w ≤ q) :
    C4Frame.lenC d p G w ≤ 2000 * (q + 1) ^ 3 := by
  have hm : C4Frame.lenC d p G w ≤ C4Frame.lenC (q + 1) (q + 1) (q + 1) (q + 1) := by
    unfold C4Frame.lenC
    have e1 : d ≤ q + 1 := by omega
    have e2 : p ≤ q + 1 := by omega
    have e3 : G ≤ q + 1 := by omega
    have e4 : w ≤ q + 1 := by omega
    gcongr
  refine hm.trans ?_
  obtain ⟨Q, hQ1, hQe⟩ : ∃ Q, 1 ≤ Q ∧ q + 1 = Q := ⟨q + 1, by omega, rfl⟩
  rw [hQe]
  unfold C4Frame.lenC
  have h2 : Q ≤ Q ^ 2 := Nat.le_self_pow (by norm_num) Q
  have h3 : Q ^ 2 ≤ Q ^ 3 := Nat.pow_le_pow_right hQ1 (by norm_num)
  have h4 : 1 ≤ Q ^ 2 := le_trans hQ1 h2
  ring_nf
  nlinarith

theorem restLen_le (d p G w q : ℕ) (hd : d ≤ q) (hp : p ≤ q) (hG : G ≤ q) (hw : w ≤ q) :
    C4Frame.restLen d p G w ≤ 8 * (q + 1) ^ 3 := by
  unfold C4Frame.restLen
  have h1 : d * (2 * w + 1) ≤ (q + 1) * (2 * (q + 1)) := Nat.mul_le_mul (by omega) (by omega)
  have h2 : G * ((2 * w + 2) * (2 * p + 3)) ≤ (q + 1) * ((2 * (q + 1)) * (3 * (q + 1))) :=
    Nat.mul_le_mul (by omega) (Nat.mul_le_mul (by omega) (by omega))
  have e1 : (q + 1) * (2 * (q + 1)) = 2 * (q + 1) ^ 2 := by ring
  have e2 : (q + 1) * ((2 * (q + 1)) * (3 * (q + 1))) = 6 * (q + 1) ^ 3 := by ring
  have h3 : (q + 1) ^ 2 ≤ (q + 1) ^ 3 := Nat.pow_le_pow_right (by omega) (by norm_num)
  omega

/-- **The framer's cost** at a request whose four header numbers are `≤ q`. -/
theorem frameCost_le (r : MatrixScoreBatch.Request) (q : ℕ) (hd : r.d ≤ q) (hp : r.p ≤ q) (hG : r.Gates ≤ q)
    (hw : r.width ≤ q) : C4Frame.frameCost r ≤ 20000 * (q + 1) ^ 3 := by
  unfold C4Frame.frameCost C4Frame.hdrCost
  have a1 := rdC_le r.d q hd
  have a2 := rdC_le r.p q hp
  have a3 := rdC_le r.Gates q hG
  have a4 := rdC_le r.width q hw
  have b1 := wtC_le r.d q hd
  have b2 := wtC_le r.p q hp
  have b3 := wtC_le r.Gates q hG
  have b4 := wtC_le r.width q hw
  have c1 := lenC_le r.d r.p r.Gates r.width q hd hp hG hw
  have c2 := restLen_le r.d r.p r.Gates r.width q hd hp hG hw
  have h1 : 1 ≤ q + 1 := by omega
  have h2 : (q + 1) ^ 2 ≤ (q + 1) ^ 3 := Nat.pow_le_pow_right h1 (by norm_num)
  have h0 : 1 ≤ (q + 1) ^ 3 := Nat.one_le_pow _ _ (by omega)
  omega

/-! ## Base's printer -/

/-- **The printer's steps** (`P1Plan.DirectCount`): the Williams table plus the selected count, at `Q ≤ p`. -/
theorem dcBudget_le (wa : WilliamsAlgorithm) (r : MatrixScoreBatch.Request) (Q : ℕ) (hQ : Q ≤ r.p) :
    P1Plan.DirectCount.budget wa r Q + 1 ≤ (CompetitorCountTable.coefficient wa + 1034000) * (r.U + 1) ^ 2 *
      (r.d + r.p + 1) ^ CompetitorCrossScheduler.exponent wa := by
  have h1 := CompetitorCountTable.budget_bound wa r Q (by rw [CompetitorSameBucketColdDense.width_eq]; omega)
  have h2 := CompetitorCountRecordRequest.budget_bound r Q hQ
  have h3 : CompetitorSelectedRequestCount.budget r Q + 1 ≤ CompetitorCountRecordRequest.budget r Q := by
    unfold CompetitorCountRecordRequest.budget; omega
  have hp : (r.d + r.p + 1) ^ 2 ≤ (r.d + r.p + 1) ^ CompetitorCrossScheduler.exponent wa :=
    Nat.pow_le_pow_right (by omega) (by unfold CompetitorCrossScheduler.exponent; omega)
  have h4 : 1034000 * (r.U + 1) ^ 2 * (r.d + r.p + 1) ^ 2 ≤
      1034000 * (r.U + 1) ^ 2 * (r.d + r.p + 1) ^ CompetitorCrossScheduler.exponent wa :=
    Nat.mul_le_mul_left _ hp
  unfold CompetitorCountTable.envelope at h1
  unfold P1Plan.DirectCount.budget
  calc CompetitorCountTable.budget wa r Q + 1 + CompetitorSelectedRequestCount.budget r Q + 1
      ≤ CompetitorCountTable.coefficient wa * (r.U + 1) ^ 2 *
          (r.d + r.p + 1) ^ CompetitorCrossScheduler.exponent wa +
        1034000 * (r.U + 1) ^ 2 * (r.d + r.p + 1) ^ CompetitorCrossScheduler.exponent wa := by omega
    _ = _ := by ring

/-! ## One child -/

/-- **The printer child's cost** (metadata, compiler, framer, printer), the compiler's cost as `Y`. -/
theorem childCost_le (wa : WilliamsAlgorithm) (a : DecompositionAlgorithm) (R : CompilerMachine.Req.C3Req)
    (r : MatrixScoreBatch.Request) (q Y : ℕ) (hd : r.d = R.dRow) (hp : r.p = R.p + 1) (hQp : R.P.Q ≤ R.p)
    (hdq : R.dRow ≤ q) (hpq : R.p + 1 ≤ q) (hG : r.Gates ≤ q) (hw : r.width ≤ q) (hQ : R.P.Q ≤ q)
    (hc3 : CompilerMachine.Top.c3Cost a R ≤ Y) :
    C4Pipe.childCost wa a R r ≤ 40100 * (q + 1) ^ 3 + Y + (CompetitorCountTable.coefficient wa + 1034014) *
      (2 ^ R.dRow + 1) ^ 2 * (R.dRow + R.p + 2) ^ CompetitorCrossScheduler.exponent wa := by
  unfold C4Pipe.childCost
  rw [prepCost_eq]
  have hf := frameCost_le r q (by omega) (by omega) hG hw
  have hb := dcBudget_le wa r R.P.Q (by omega)
  have hU : r.U = 2 ^ R.dRow := by unfold MatrixScoreBatch.Request.U; rw [hd]
  rw [hU, hd, hp] at hb
  have e : R.dRow + (R.p + 1) + 1 = R.dRow + R.p + 2 := by omega
  rw [e] at hb
  set M := (R.dRow + R.p + 2) ^ CompetitorCrossScheduler.exponent wa with hM
  set U := 2 ^ R.dRow with hU'
  have hM1 : 1 ≤ M := Nat.one_le_pow _ _ (by omega)
  have hUU : U * U ≤ (U + 1) ^ 2 := by nlinarith
  have hUM : (U + 1) ^ 2 ≤ (U + 1) ^ 2 * M := Nat.le_mul_of_pos_right _ hM1
  have h1 : 1 ≤ q + 1 := by omega
  have h3 : q + 1 ≤ (q + 1) ^ 3 := Nat.le_self_pow (by norm_num) _
  calc 14 * R.P.Q + 14 * (U * U) + 12 + 1 + (CompilerMachine.Top.c3Cost a R + 1 +
        (2 * C4Frame.frameCost r + 2 + 1 + P1Plan.DirectCount.budget wa r R.P.Q))
      ≤ 40100 * (q + 1) ^ 3 + Y + (CompetitorCountTable.coefficient wa + 1034000) * (U + 1) ^ 2 * M +
          14 * ((U + 1) ^ 2 * M) := by nlinarith
    _ = _ := by ring

/-- **One child's step bound** (`C4Child.coreCost`) at the premise of the child family's `hcost`: the printer's
request word is a request word at the call's `dRow`, `p + 1` and width (any columns, any cuts `cs`; the child family
has the compiler's reference `c3v2Ref`). Every number of the call is `≤ q`, the compiler's cost `≤ Y`. -/
theorem coreCost_le (wa : WilliamsAlgorithm) (a : DecompositionAlgorithm) (R0 : CompilerMachine.Req.C3Req)
    (P : SeedParams) (TWd Cap nT Rn K : ℕ) (batch : List SeedFix.SExpr) (p' : List Bool)
    (r : MatrixScoreBatch.Request) (q Y : ℕ) (cols : List ℕ) (cs : List MatrixScoreBatch.Cut)
    (hw : MatrixScoreBatch.word r = CompilerMachine.Req.reqWord R0.dRow (R0.p + 1) R0.P.width cols cs)
    (hQp : R0.P.Q ≤ R0.p) (hl : P.ell ≤ q) (hkh : P.kh ≤ q) (hT : TWd ≤ q) (hC : Cap ≤ q)
    (hn : nT * 2 ^ (8 + 8 * P.ell + 8 * P.kh) ≤ q) (hK : K ≤ q) (hpre : (C4Child.pre a R0).length ≤ q)
    (hpost : (C4Child.post a R0).length ≤ q) (hV : (exprWord (C4Child.chV P nT Rn batch p')).length ≤ q)
    (hdq : R0.dRow ≤ q) (hpq : R0.p + 1 ≤ q) (hwq : R0.P.width ≤ q)
    (hG : cs.length ≤ q) (hQ : R0.P.Q ≤ q)
    (hc3 : CompilerMachine.Top.c3Cost a (C4Child.chR R0 P nT Rn batch p') ≤ Y) :
    C4Child.coreCost wa a R0 P TWd Cap nT Rn K batch p' r ≤ 210000 * (q + 1) ^ 3 + Y +
      (CompetitorCountTable.coefficient wa + 1034014) * (2 ^ R0.dRow + 1) ^ 2 *
        (R0.dRow + R0.p + 2) ^ CompetitorCrossScheduler.exponent wa := by
  obtain ⟨e1, e2, e3, e4⟩ := reqWord_fields r _ _ _ _ _ hw
  unfold C4Child.coreCost
  have h1 := euCost_le P TWd Cap nT K q hl hkh hT hC hn hK
  have h2 := asmCost_le (C4Child.pre a R0) (C4Child.post a R0) (C4Child.chV P nT Rn batch p') q hpre hpost hV
  have h3 := childCost_le wa a (C4Child.chR R0 P nT Rn batch p') r q Y e1 e2 hQp hdq hpq (by rw [e3]; exact hG)
    (by rw [e4]; exact hwq) hQ hc3
  have hq1 : 1 ≤ q + 1 := by omega
  have hq2 : (q + 1) ^ 2 ≤ (q + 1) ^ 3 := Nat.pow_le_pow_right hq1 (by norm_num)
  have hq3 : q + 1 ≤ (q + 1) ^ 3 := Nat.le_self_pow (by norm_num) _
  change C4Dock.euCost P TWd Cap nT K + 1 + (C4Iface.asmCost (C4Child.pre a R0) (C4Child.post a R0)
    (C4Child.chV P nT Rn batch p') + 1 + C4Pipe.childCost wa a (C4Child.chR R0 P nT Rn batch p') r) ≤ _
  have h3' : C4Pipe.childCost wa a (C4Child.chR R0 P nT Rn batch p') r ≤ 40100 * (q + 1) ^ 3 + Y +
      (CompetitorCountTable.coefficient wa + 1034014) * (2 ^ R0.dRow + 1) ^ 2 *
        (R0.dRow + R0.p + 2) ^ CompetitorCrossScheduler.exponent wa := h3
  omega

end NearCubicWires.WireExponent3_5.PrimAsm.SFCost
