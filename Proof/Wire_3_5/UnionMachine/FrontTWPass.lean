import Proof.Wire_3_5.UnionMachine.FrontTWPos

/-! # C6 front, U5: the clause loop and the three passes (P3:3685-3691)

The PCPP output word lists the clauses' literal pairs (`natListWord` of `literalIndex (±i)`: `2i`, `2i + 1`; base
`pcppOutput`). Each pass of the table writer streams them: per clause it reads the two literal indices into `L₀`,
`L₁` (PA's `readNatM`) and runs the pass's clause body: the validity or second-moment test at both positions
(`bodyV`, `bodyQ`), or the clause test (`bodyMu`).

Main statements: **`bodyVT`**, **`bodyQT`**, **`bodyMuT`** (one clause), the clause loop **`clLoopT`**.
Paper quantity: the calls of `(tr:tests)`, clause by clause. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unnecessarySimpa false

namespace NearCubicWires.WireExponent3_5.UnionMachine.FrontTW
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimAsm.WriteNat NearCubicWires.WireExponent3_5.PrimAsm.ParseNat
open NearCubicWires.WireExponent3_5.PrimAsm.UnaryArith
open NearCubicWires.WireExponent3_5.UnionMachine.FrontTWKit
open NearCubicWires.WireExponent3_5.UnionMachine.FrontTableRef (FK lexProd patV patQ patMu)

variable (cap : ℕ) (src : Fin 11 → List Bool)

/-! ## Moving a plain register -/

theorem moveT (h : ℕ) (o : List Bool) (cl : Bool) (w : Fin NR → ℕ) (ok : ℕ) (a b : Fin NR) (ha : Plain a) (hb : Plain b)
    (hao : a ≠ rOP) (hbo : b ≠ rOP) (hab : a ≠ b) (hcap : w a + w b ≤ cap) :
    WExec cap (WM.move a b) (ts src h o (regsOf w Z4 Z4 Z4 ok) cl)
      (ts src h o (regsOf (Function.update (Function.update w a 0) b (w b + w a)) Z4 Z4 Z4 ok) cl) (7 * w a + 1) := by
  have e := wmove_spec cap a b hab (w a) (ts src h o (regsOf w Z4 Z4 Z4 ok) cl)
    (tsR_val src h o cl w _ _ _ ok a ha hao) (by rw [tsR_val src h o cl w _ _ _ ok a ha hao]; omega)
    (by rw [tsR_val src h o cl w _ _ _ ok a ha hao, tsR_val src h o cl w _ _ _ ok b hb hbo]; omega)
  rw [tsR_val src h o cl w _ _ _ ok a ha hao, tsR_val src h o cl w _ _ _ ok b hb hbo,
    tsR_setv src h o cl w _ _ _ ok a ha hao, tsR_setv src h o cl _ _ _ _ ok b hb hbo] at e
  exact e

theorem pL0 : Plain rL0 := ⟨by decide, by decide⟩
theorem pL1 : Plain rL1 := ⟨by decide, by decide⟩
theorem pLIT : Plain rLIT := ⟨by decide, by decide⟩

/-- A variable's index facts: its grid entries, parity and carrier exist, within the capacity. -/
structure XOK (d : TWData) (s x : ℕ) : Prop where
  es : x * s + s ≤ d.es.length
  pc : x < d.pcs.length
  pf : x < d.pf.length
  cr : x < d.crs.length
  ef : x < d.ef.length
  cx : x * s + s + 1 ≤ cap

theorem varOK_pos (d : TWData) (w : Fin NR → ℕ) (hx : XOK cap d (w rSS) (w rLIT / 2))
    (hys : w rYS + w rSS ≤ d.es.length) (hyc : w rY < d.crs.length ∧ w rY < d.ef.length)
    (hcy : w rYS + w rSS + 1 ≤ cap) : VarOK cap d (posRegs w) := by
  have oSS : posRegs w rSS = w rSS := posRegs_other w _ (by decide) (by decide) (by decide) (by decide) (by decide)
  have oY : posRegs w rY = w rY := posRegs_other w _ (by decide) (by decide) (by decide) (by decide) (by decide)
  have oYS : posRegs w rYS = w rYS := posRegs_other w _ (by decide) (by decide) (by decide) (by decide) (by decide)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [posRegs_XS, oSS]; exact hx.es
  · rw [oYS, oSS]; exact hys
  · rw [posRegs_X]; exact ⟨hx.pc, hx.pf⟩
  · rw [posRegs_X]; exact ⟨hx.cr, hx.ef⟩
  · rw [oY]; exact hyc
  · rw [posRegs_XS, oSS]; exact hx.cx
  · rw [oYS, oSS]; exact hcy

/-- The validity test at both positions of a clause. -/
def bodyV : WM 10 NR := .seq (WM.move rL0 rLIT) (.seq (posP vBlocks) (.seq (WM.move rL1 rLIT) (posP vBlocks)))

/-- The second-moment test at both positions of a clause. -/
def bodyQ : WM 10 NR := .seq (WM.move rL0 rLIT) (.seq (posP qBlocks) (.seq (WM.move rL1 rLIT) (posP qBlocks)))

/-- A position test's block contract, from its registers. -/
def PosBlocks (blocks : WM 10 NR) (h : ℕ) (cl : Bool) (d : TWData) (B : ℕ)
    (W : (Fin NR → ℕ) → List Bool) (b : (Fin NR → ℕ) → Bool) (c : (Fin NR → ℕ) → ℕ) : Prop :=
  ∀ v : Fin NR → ℕ, GInv cap d B v → VarOK cap d v → PSpec cap src blocks h cl v (30 * B + 40) (W v) (b v) (c v)

/-- **Both positions of a clause** (literal indices `a`, `b` in `L₀`, `L₁`). -/
theorem bodyPT (blocks : WM 10 NR) (h : ℕ) (cl : Bool) (d : TWData) (B : ℕ) (W : (Fin NR → ℕ) → List Bool)
    (bf : (Fin NR → ℕ) → Bool) (c : (Fin NR → ℕ) → ℕ) (hbl : PosBlocks cap src blocks h cl d B W bf c)
    (v0 : Fin NR → ℕ) (hg : GInv cap d B v0) (hL0 : v0 rL0 = 0) (hL1 : v0 rL1 = 0) (hLIT : v0 rLIT = 0)
    (hX0 : v0 rX = 0) (hN0 : v0 rN0 = 0) (hXS0 : v0 rXS = 0) (hSY0 : v0 rSYSX = 0)
    (hys : v0 rYS + v0 rSS ≤ d.es.length) (hyc : v0 rY < d.crs.length ∧ v0 rY < d.ef.length)
    (hcy : v0 rYS + v0 rSS + 1 ≤ cap) (a b : ℕ) (ha : XOK cap d (v0 rSS) (a / 2)) (hb : XOK cap d (v0 rSS) (b / 2))
    (hca : a + a * v0 rSS + v0 rSS + v0 rSYS + b + 1 ≤ cap) (hcb : b + b * v0 rSS + v0 rSS + v0 rSYS + 1 ≤ cap)
    (o : List Bool) (ok : ℕ) (hok : ok ≤ 1)
    (hlen : o.length + (W (posRegs (Function.update (Function.update v0 rL1 b) rLIT a))).length +
      (W (posRegs (Function.update v0 rLIT b))).length + (30 * B + 40) ≤ cap) :
    WExec cap (.seq (WM.move rL0 rLIT) (.seq (posP blocks) (.seq (WM.move rL1 rLIT) (posP blocks))))
      (ts src h o (regsOf (Function.update (Function.update v0 rL0 a) rL1 b) Z4 Z4 Z4 ok) cl)
      (ts src h (o ++ (W (posRegs (Function.update (Function.update v0 rL1 b) rLIT a)) ++
          W (posRegs (Function.update v0 rLIT b))))
        (regsOf v0 Z4 Z4 Z4 (if (bf (posRegs (Function.update (Function.update v0 rL1 b) rLIT a)) &&
          bf (posRegs (Function.update v0 rLIT b))) then ok else 0)) cl)
      (7 * a + 1 + 1 + (110 * (a * v0 rSS) + 110 * a + 110 * v0 rSS + 30 * v0 rSYS +
        c (posRegs (Function.update (Function.update v0 rL1 b) rLIT a)) + 120) + 1 +
        (7 * b + 1 + 1 + (110 * (b * v0 rSS) + 110 * b + 110 * v0 rSS + 30 * v0 rSYS +
          c (posRegs (Function.update v0 rLIT b)) + 120))) := by
  set w1 := Function.update (Function.update v0 rL1 b) rLIT a with hw1
  set w2 := Function.update v0 rLIT b with hw2
  have gw : ∀ w : Fin NR → ℕ, (∀ r, r ≠ rL0 → r ≠ rL1 → r ≠ rLIT → w r = v0 r) → GInv cap d B w := by
    intro w hw
    have e : ∀ r : Fin NR, (r = rT ∨ r = rF ∨ r = rC ∨ r = rZ ∨ r = rFL ∨ r = rNEG ∨ r = rBIG ∨ r = rNZ ∨ r = rMAG ∨
        r = rS1 ∨ r = rS2 ∨ r = rS3 ∨ r = rMa ∨ r = rMb ∨ r = rMc ∨ r = rMd ∨ r = rMe ∨ r = rMf) → w r = v0 r := by
      intro r hr
      apply hw <;> rcases hr with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;> subst h <;>
        decide
    refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, hg.df, hg.capB, ?_⟩
    · rw [e _ (by simp)]; exact hg.scr.t
    · rw [e _ (by simp)]; exact hg.scr.f
    · rw [e _ (by simp)]; exact hg.scr.c
    · rw [e _ (by simp)]; exact hg.scr.z
    · rw [e _ (by simp)]; exact hg.scr.fl
    · rw [e _ (by simp)]; exact hg.scr.neg
    · rw [e _ (by simp)]; exact hg.big
    · rw [e _ (by simp)]; exact hg.nz
    · rw [e _ (by simp)]; exact hg.mag
    · rw [e _ (by simp)]; exact hg.s1
    · rw [e _ (by simp)]; exact hg.s2
    · rw [e _ (by simp)]; exact hg.s3
    · intro M hM
      rw [e _ (by rcases hM with h | h | h | h | h | h <;> simp [h])]
      exact hg.capM M hM
  have w1o : ∀ r, r ≠ rL0 → r ≠ rL1 → r ≠ rLIT → w1 r = v0 r := fun r h1 h2 h3 => by
    simp only [w1]; rw [Function.update_of_ne h3, Function.update_of_ne h2]
  have w2o : ∀ r, r ≠ rL0 → r ≠ rL1 → r ≠ rLIT → w2 r = v0 r := fun r h1 h2 h3 => by
    simp only [w2]; rw [Function.update_of_ne h3]
  -- first move
  have m1 := moveT cap src h o cl (Function.update (Function.update v0 rL0 a) rL1 b) ok rL0 rLIT pL0 pLIT (by decide)
    (by decide) (by decide) (by simp +decide [Function.update_apply, hLIT]; omega)
  have e1 : Function.update (Function.update (Function.update (Function.update v0 rL0 a) rL1 b) rL0 0) rLIT
      ((Function.update (Function.update v0 rL0 a) rL1 b) rLIT + (Function.update (Function.update v0 rL0 a) rL1 b) rL0)
      = w1 := by
    funext r
    by_cases a1 : r = rLIT
    · subst a1; simp +decide [w1, hLIT]
    by_cases a2 : r = rL0
    · subst a2; simp +decide [w1, hL0]
    by_cases a3 : r = rL1
    · subst a3; simp +decide [w1]
    simp only [w1]; rw [Function.update_of_ne a1, Function.update_of_ne a2, Function.update_of_ne a1,
      Function.update_of_ne a3, Function.update_of_ne a3, Function.update_of_ne a2]
  rw [e1] at m1
  have hb1 := hbl (posRegs w1) (ginv_pos cap d B w1 (gw w1 w1o))
    (varOK_pos cap d w1 (by rw [w1o _ (by decide) (by decide) (by decide)]; simpa [w1] using ha)
      (by rw [w1o _ (by decide) (by decide) (by decide), w1o _ (by decide) (by decide) (by decide)]; exact hys)
      (by rw [w1o _ (by decide) (by decide) (by decide)]; exact hyc)
      (by rw [w1o _ (by decide) (by decide) (by decide), w1o _ (by decide) (by decide) (by decide)]; exact hcy))
  have p1 := posT cap src h cl w1 blocks _ _ _ _ hb1 (by rw [w1o _ (by decide) (by decide) (by decide)]; exact hX0)
    (by rw [w1o _ (by decide) (by decide) (by decide)]; exact hN0)
    (by rw [w1o _ (by decide) (by decide) (by decide)]; exact hXS0)
    (by rw [w1o _ (by decide) (by decide) (by decide)]; exact hSY0)
    (by rw [w1o _ (by decide) (by decide) (by decide)]; exact hg.s1)
    (by rw [w1o _ (by decide) (by decide) (by decide)]; exact hg.s2)
    (by rw [w1o _ (by decide) (by decide) (by decide)]; exact hg.s3)
    (by simp +decide [w1, Function.update_apply]; omega) o ok hok (by omega)
  have e2 : Function.update w1 rLIT 0 = Function.update v0 rL1 b := by
    funext r
    by_cases a1 : r = rLIT
    · subst a1; simp +decide [w1, hLIT]
    simp only [w1]; rw [Function.update_of_ne a1, Function.update_of_ne a1]
  rw [e2] at p1
  set ok1 := if bf (posRegs w1) then ok else 0 with hok1
  -- second move
  have m2 := moveT cap src h (o ++ W (posRegs w1)) cl (Function.update v0 rL1 b) ok1 rL1 rLIT pL1 pLIT (by decide)
    (by decide) (by decide) (by simp +decide [Function.update_apply, hLIT]; omega)
  have e3 : Function.update (Function.update (Function.update v0 rL1 b) rL1 0) rLIT
      ((Function.update v0 rL1 b) rLIT + (Function.update v0 rL1 b) rL1) = w2 := by
    funext r
    by_cases a1 : r = rLIT
    · subst a1; simp +decide [w2, hLIT]
    by_cases a3 : r = rL1
    · subst a3; simp +decide [w2, hL1]
    simp only [w2]; rw [Function.update_of_ne a1, Function.update_of_ne a3, Function.update_of_ne a3,
      Function.update_of_ne a1]
  rw [e3] at m2
  have hb2 := hbl (posRegs w2) (ginv_pos cap d B w2 (gw w2 w2o))
    (varOK_pos cap d w2 (by rw [w2o _ (by decide) (by decide) (by decide)]; simpa [w2] using hb)
      (by rw [w2o _ (by decide) (by decide) (by decide), w2o _ (by decide) (by decide) (by decide)]; exact hys)
      (by rw [w2o _ (by decide) (by decide) (by decide)]; exact hyc)
      (by rw [w2o _ (by decide) (by decide) (by decide), w2o _ (by decide) (by decide) (by decide)]; exact hcy))
  have p2 := posT cap src h cl w2 blocks _ _ _ _ hb2 (by rw [w2o _ (by decide) (by decide) (by decide)]; exact hX0)
    (by rw [w2o _ (by decide) (by decide) (by decide)]; exact hN0)
    (by rw [w2o _ (by decide) (by decide) (by decide)]; exact hXS0)
    (by rw [w2o _ (by decide) (by decide) (by decide)]; exact hSY0)
    (by rw [w2o _ (by decide) (by decide) (by decide)]; exact hg.s1)
    (by rw [w2o _ (by decide) (by decide) (by decide)]; exact hg.s2)
    (by rw [w2o _ (by decide) (by decide) (by decide)]; exact hg.s3)
    (by simp +decide [w2, Function.update_apply]; omega) (o ++ W (posRegs w1)) ok1 (by simp only [ok1]; split_ifs <;> omega)
    (by simp only [List.length_append]; omega)
  have e4 : Function.update w2 rLIT 0 = v0 := by
    funext r
    by_cases a1 : r = rLIT
    · subst a1; simp +decide [w2, hLIT]
    simp only [w2]; rw [Function.update_of_ne a1, Function.update_of_ne a1]
  rw [e4] at p2
  have e5 : (if bf (posRegs w2) then ok1 else 0) = if (bf (posRegs w1) && bf (posRegs w2)) then ok else 0 := by
    simp only [ok1]; cases bf (posRegs w1) <;> cases bf (posRegs w2) <;> simp
  rw [e5, List.append_assoc] at p2
  have hw1L : w1 rLIT = a := by simp [w1]
  have hw1S : w1 rSS = v0 rSS := w1o _ (by decide) (by decide) (by decide)
  have hw1Y : w1 rSYS = v0 rSYS := w1o _ (by decide) (by decide) (by decide)
  have hw2L : w2 rLIT = b := by simp [w2]
  have hw2S : w2 rSS = v0 rSS := w2o _ (by decide) (by decide) (by decide)
  have hw2Y : w2 rSYS = v0 rSYS := w2o _ (by decide) (by decide) (by decide)
  rw [hw1L, hw1S, hw1Y] at p1
  rw [hw2L, hw2S, hw2Y] at p2
  have hm1 : (Function.update (Function.update v0 rL0 a) rL1 b) rL0 = a := by simp +decide [Function.update_apply]
  have hm2 : (Function.update v0 rL1 b) rL1 = b := by simp
  rw [hm1] at m1
  rw [hm2] at m2
  exact WExec.mono (WExec.seq m1 (WExec.seq p1 (WExec.seq m2 p2))) (by omega)

/-! ## The clause test at one clause -/

/-- Clear the clause's registers. -/
def muClr : WM 10 NR :=
  .seq (WM.clear rX) (.seq (WM.clear rN0) (.seq (WM.clear rXS) (.seq (WM.clear rY) (.seq (WM.clear rN1) (WM.clear rYS)))))

/-- The clause test at one clause: both variables, the blocks, the cleanup. -/
def bodyMu : WM 10 NR :=
  .seq (WM.move rL0 rLIT) (.seq (varSet rN0 mX) (.seq (WM.move rL1 rLIT) (.seq (varSet rN1 mY) (.seq muBlocks muClr))))

/-- The registers at a clause of literal indices `a`, `b`. -/
def muRegs (v0 : Fin NR → ℕ) (a b : ℕ) : Fin NR → ℕ :=
  Function.update (Function.update (Function.update (Function.update (Function.update (Function.update v0
    rX (a / 2)) rN0 (a % 2)) rXS (a / 2 * v0 rSS)) rY (b / 2)) rN1 (b % 2)) rYS (b / 2 * v0 rSS)

theorem muRegs_other (v0 : Fin NR → ℕ) (a b : ℕ) (r : Fin NR) (h1 : r ≠ rX) (h2 : r ≠ rN0) (h3 : r ≠ rXS)
    (h4 : r ≠ rY) (h5 : r ≠ rN1) (h6 : r ≠ rYS) : muRegs v0 a b r = v0 r := by
  simp only [muRegs]
  rw [Function.update_of_ne h6, Function.update_of_ne h5, Function.update_of_ne h4, Function.update_of_ne h3,
    Function.update_of_ne h2, Function.update_of_ne h1]

theorem bodyMuT (h : ℕ) (cl : Bool) (d : TWData) (hd : d.Holds src) (B : ℕ) (hB : d.Bnd B) (v0 : Fin NR → ℕ)
    (hg : GInv cap d B v0) (hL0 : v0 rL0 = 0) (hL1 : v0 rL1 = 0) (hLIT : v0 rLIT = 0)
    (hX0 : v0 rX = 0) (hN0 : v0 rN0 = 0) (hXS0 : v0 rXS = 0) (hY0 : v0 rY = 0) (hN10 : v0 rN1 = 0) (hYS0 : v0 rYS = 0)
    (a b : ℕ) (ha : XOK cap d (v0 rSS) (a / 2)) (hb : XOK cap d (v0 rSS) (b / 2))
    (hca : a + a * v0 rSS + v0 rSS + b + b * v0 rSS + 1 ≤ cap)
    (o : List Bool) (ok : ℕ) (hok : ok ≤ 1)
    (hlen : o.length + (outMu d (muRegs v0 a b)).length + (30 * B + 40) ≤ cap) :
    WExec cap bodyMu (ts src h o (regsOf (Function.update (Function.update v0 rL0 a) rL1 b) Z4 Z4 Z4 ok) cl)
      (ts src h (o ++ outMu d (muRegs v0 a b)) (regsOf v0 Z4 Z4 Z4 (if okMu d (muRegs v0 a b) then ok else 0)) cl)
      (100 * (a + 1) * (v0 rSS + 1) + 100 * (b + 1) * (v0 rSS + 1) + costMu B (muRegs v0 a b) + 100) := by
  have pX : Plain rX := ⟨by decide, by decide⟩
  have hmX : ∀ i, Plain (mX i) := by intro i; fin_cases i <;> exact ⟨by decide, by decide⟩
  have hmXo : ∀ i, mX i ≠ rOP := by intro i; fin_cases i <;> decide
  have hmY : ∀ i, Plain (mY i) := by intro i; fin_cases i <;> exact ⟨by decide, by decide⟩
  have hmYo : ∀ i, mY i ≠ rOP := by intro i; fin_cases i <;> decide
  -- L₀ → LIT
  have m1 := moveT cap src h o cl (Function.update (Function.update v0 rL0 a) rL1 b) ok rL0 rLIT pL0 pLIT (by decide)
    (by decide) (by decide) (by simp +decide [Function.update_apply, hLIT]; omega)
  set u1 := Function.update (Function.update v0 rL1 b) rLIT a with hu1
  have e1 : Function.update (Function.update (Function.update (Function.update v0 rL0 a) rL1 b) rL0 0) rLIT
      ((Function.update (Function.update v0 rL0 a) rL1 b) rLIT + (Function.update (Function.update v0 rL0 a) rL1 b) rL0)
      = u1 := by
    funext r
    by_cases a1 : r = rLIT
    · subst a1; simp +decide [u1, hLIT]
    by_cases a2 : r = rL0
    · subst a2; simp +decide [u1, hL0]
    by_cases a3 : r = rL1
    · subst a3; simp +decide [u1]
    simp only [u1]; rw [Function.update_of_ne a1, Function.update_of_ne a2, Function.update_of_ne a1,
      Function.update_of_ne a3, Function.update_of_ne a3, Function.update_of_ne a2]
  rw [e1] at m1
  -- X from a
  have s1 := varSetT' cap src h o cl u1 ok rN0 mX ⟨by decide, by decide⟩ (by decide) hmX hmXo rfl (by decide) (by decide)
    (by intro i; fin_cases i <;> decide) (by intro i; fin_cases i <;> decide)
    (by simp only [u1, show mX 0 = rX from rfl]; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide)];
        exact hX0)
    (by simp only [u1, show mX 2 = rXS from rfl]; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide)];
        exact hXS0)
    (by simp only [u1]; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide)]; exact hN0)
    (by simp only [u1]; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide)]; exact hg.s1)
    (by simp only [u1, show mX 4 = rS2 from rfl]; rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide)];
        exact hg.s2)
    (by simp only [u1, show mX 1 = rSS from rfl]
        rw [Function.update_self, Function.update_of_ne (by decide), Function.update_of_ne (by decide)]; nlinarith)
  set u2 := varSetVec u1 rN0 mX with hu2
  have u1LIT : u1 rLIT = a := by simp [u1]
  have u1o : ∀ r, r ≠ rLIT → r ≠ rL1 → u1 r = v0 r := fun r h1 h2 => by
    simp only [u1]; rw [Function.update_of_ne h1, Function.update_of_ne h2]
  have u2LIT : u2 rLIT = 0 := varSetVec_LIT _ _ _ (by decide) (by decide) (by decide)
  have u2o : ∀ r, r ≠ rLIT → r ≠ rN0 → r ≠ rX → r ≠ rXS → u2 r = u1 r := fun r h1 h2 h3 h4 =>
    varSetVec_other _ _ _ r h1 h2 h3 h4
  have u2L1 : u2 rL1 = b := by
    rw [u2o _ (by decide) (by decide) (by decide) (by decide)]; simp +decide [u1, Function.update_apply]
  -- L₁ → LIT
  have m2 := moveT cap src h o cl u2 ok rL1 rLIT pL1 pLIT (by decide) (by decide) (by decide)
    (by rw [u2L1, u2LIT]; omega)
  rw [u2L1, u2LIT] at m2
  set u3 := Function.update (Function.update u2 rL1 0) rLIT (0 + b) with hu3
  have u3LIT : u3 rLIT = b := by simp [u3]
  have u3o : ∀ r, r ≠ rLIT → r ≠ rL1 → u3 r = u2 r := fun r h1 h2 => by
    simp only [u3]; rw [Function.update_of_ne h1, Function.update_of_ne h2]
  -- Y from b
  have s2 := varSetT' cap src h o cl u3 ok rN1 mY ⟨by decide, by decide⟩ (by decide) hmY hmYo rfl (by decide) (by decide)
    (by intro i; fin_cases i <;> decide) (by intro i; fin_cases i <;> decide)
    (by rw [show mY 0 = rY from rfl, u3o _ (by decide) (by decide), u2o _ (by decide) (by decide) (by decide) (by decide),
        u1o _ (by decide) (by decide)]; exact hY0)
    (by rw [show mY 2 = rYS from rfl, u3o _ (by decide) (by decide), u2o _ (by decide) (by decide) (by decide) (by decide),
        u1o _ (by decide) (by decide)]; exact hYS0)
    (by rw [u3o _ (by decide) (by decide), u2o _ (by decide) (by decide) (by decide) (by decide),
        u1o _ (by decide) (by decide)]; exact hN10)
    (by rw [u3o _ (by decide) (by decide), u2o _ (by decide) (by decide) (by decide) (by decide),
        u1o _ (by decide) (by decide)]; exact hg.s1)
    (by rw [show mY 4 = rS2 from rfl, u3o _ (by decide) (by decide), u2o _ (by decide) (by decide) (by decide) (by decide),
        u1o _ (by decide) (by decide)]; exact hg.s2)
    (by rw [show mY 1 = rSS from rfl, u3LIT, u3o _ (by decide) (by decide),
        u2o _ (by decide) (by decide) (by decide) (by decide), u1o _ (by decide) (by decide)]; nlinarith)
  have e4 : varSetVec u3 rN1 mY = muRegs v0 a b := by
    have hS : u3 rSS = v0 rSS := by
      rw [u3o _ (by decide) (by decide), u2o _ (by decide) (by decide) (by decide) (by decide), u1o _ (by decide) (by decide)]
    have hS1 : u1 rSS = v0 rSS := u1o _ (by decide) (by decide)
    have y2 : varSetVec u3 rN1 mY rYS = b / 2 * v0 rSS := by
      have := varSetVec_m2 u3 rN1 mY; rw [show mY 1 = rSS from rfl, u3LIT, hS] at this; exact this
    have y0 : varSetVec u3 rN1 mY rY = b / 2 := by
      have := varSetVec_m0 u3 rN1 mY; rw [u3LIT] at this; exact this
    have yN : varSetVec u3 rN1 mY rN1 = b % 2 := by
      have := varSetVec_N u3 rN1 mY (by decide) (by decide); rw [u3LIT] at this; exact this
    have x2 : u2 rXS = a / 2 * v0 rSS := by
      have := varSetVec_m2 u1 rN0 mX; rw [show mX 1 = rSS from rfl, u1LIT, hS1] at this; exact this
    have x0 : u2 rX = a / 2 := by
      have := varSetVec_m0 u1 rN0 mX; rw [u1LIT] at this; exact this
    have xN : u2 rN0 = a % 2 := by
      have := varSetVec_N u1 rN0 mX (by decide) (by decide); rw [u1LIT] at this; exact this
    have mO : ∀ r, r ≠ rX → r ≠ rN0 → r ≠ rXS → r ≠ rY → r ≠ rN1 → r ≠ rYS → muRegs v0 a b r = v0 r :=
      fun r h1 h2 h3 h4 h5 h6 => muRegs_other v0 a b r h1 h2 h3 h4 h5 h6
    funext r
    by_cases a1 : r = rYS
    · subst a1; rw [y2]; simp [muRegs]
    by_cases a2 : r = rY
    · subst a2; rw [y0]; simp +decide [muRegs, Function.update_apply]
    by_cases a3 : r = rN1
    · subst a3; rw [yN]; simp +decide [muRegs, Function.update_apply]
    by_cases a4 : r = rLIT
    · subst a4; rw [varSetVec_LIT _ _ _ (by decide) (by decide) (by decide)]
      rw [mO _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hLIT]
    rw [varSetVec_other _ _ _ r a4 a3 a2 a1]
    by_cases a5 : r = rL1
    · subst a5; simp only [u3, Function.update_of_ne (show rL1 ≠ rLIT by decide), Function.update_self]
      rw [mO _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hL1]
    rw [u3o r a4 a5]
    by_cases a6 : r = rXS
    · subst a6; rw [x2]; simp +decide [muRegs, Function.update_apply]
    by_cases a7 : r = rX
    · subst a7; rw [x0]; simp +decide [muRegs, Function.update_apply]
    by_cases a8 : r = rN0
    · subst a8; rw [xN]; simp +decide [muRegs, Function.update_apply]
    rw [u2o r a4 a8 a7 a6, u1o r a4 a5, mO r a7 a8 a6 a2 a3 a1]
  rw [e4] at s2
  -- the blocks
  have gm : GInv cap d B (muRegs v0 a b) := by
    have e : ∀ r : Fin NR, (r = rT ∨ r = rF ∨ r = rC ∨ r = rZ ∨ r = rFL ∨ r = rNEG ∨ r = rBIG ∨ r = rNZ ∨ r = rMAG ∨
        r = rS1 ∨ r = rS2 ∨ r = rS3 ∨ r = rMa ∨ r = rMb ∨ r = rMc ∨ r = rMd ∨ r = rMe ∨ r = rMf) →
        muRegs v0 a b r = v0 r := by
      intro r hr
      apply muRegs_other <;> rcases hr with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;>
        subst h <;> decide
    refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, hg.df, hg.capB, ?_⟩
    · rw [e _ (by simp)]; exact hg.scr.t
    · rw [e _ (by simp)]; exact hg.scr.f
    · rw [e _ (by simp)]; exact hg.scr.c
    · rw [e _ (by simp)]; exact hg.scr.z
    · rw [e _ (by simp)]; exact hg.scr.fl
    · rw [e _ (by simp)]; exact hg.scr.neg
    · rw [e _ (by simp)]; exact hg.big
    · rw [e _ (by simp)]; exact hg.nz
    · rw [e _ (by simp)]; exact hg.mag
    · rw [e _ (by simp)]; exact hg.s1
    · rw [e _ (by simp)]; exact hg.s2
    · rw [e _ (by simp)]; exact hg.s3
    · intro M hM
      rw [e _ (by rcases hM with h | h | h | h | h | h <;> simp [h])]
      exact hg.capM M hM
  have vm : VarOK cap d (muRegs v0 a b) := by
    have hSS : muRegs v0 a b rSS = v0 rSS := muRegs_other v0 a b _ (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide)
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp +decide only [hSS, muRegs, Function.update_apply, if_true, if_false]
    · exact ha.es
    · exact hb.es
    · exact ⟨ha.pc, ha.pf⟩
    · exact ⟨ha.cr, ha.ef⟩
    · exact ⟨hb.cr, hb.ef⟩
    · exact ha.cx
    · exact hb.cx
  have bl := muBlocksP cap src d hd B hB h cl (muRegs v0 a b) gm vm o ok hok hlen
  set okm := if okMu d (muRegs v0 a b) then ok else 0 with hokm
  -- cleanup
  have cl6 : WExec cap muClr (ts src h (o ++ outMu d (muRegs v0 a b)) (regsOf (muRegs v0 a b) Z4 Z4 Z4 okm) cl)
      (ts src h (o ++ outMu d (muRegs v0 a b)) (regsOf v0 Z4 Z4 Z4 okm) cl) (3 * (a + b) * (v0 rSS + 1) + 100) := by
    set O := o ++ outMu d (muRegs v0 a b) with hO
    have c1 := wclear_spec cap rX (a / 2) (ts src h O (regsOf (muRegs v0 a b) Z4 Z4 Z4 okm) cl)
      (by rw [tsR_val src _ _ _ _ _ _ _ _ _ pX (by decide)]; simp +decide [muRegs, Function.update_apply])
      (by rw [tsR_val src _ _ _ _ _ _ _ _ _ pX (by decide)]; simp +decide [muRegs, Function.update_apply]; omega)
    rw [tsR_setv src _ _ _ _ _ _ _ _ _ pX (by decide)] at c1
    have c2 := wclear_spec cap rN0 (a % 2) (ts src h O (regsOf (Function.update (muRegs v0 a b) rX 0) Z4 Z4 Z4 okm) cl)
      (by rw [tsR_val src _ _ _ _ _ _ _ _ _ ⟨by decide, by decide⟩ (by decide)]; simp +decide [muRegs, Function.update_apply])
      (by rw [tsR_val src _ _ _ _ _ _ _ _ _ ⟨by decide, by decide⟩ (by decide)]; simp +decide [muRegs, Function.update_apply]
          have := Nat.mod_lt a (show 2 > 0 by omega); omega)
    rw [tsR_setv src _ _ _ _ _ _ _ _ _ ⟨by decide, by decide⟩ (by decide)] at c2
    have c3 := wclear_spec cap rXS (a / 2 * v0 rSS)
      (ts src h O (regsOf (Function.update (Function.update (muRegs v0 a b) rX 0) rN0 0) Z4 Z4 Z4 okm) cl)
      (by rw [tsR_val src _ _ _ _ _ _ _ _ _ ⟨by decide, by decide⟩ (by decide)]; simp +decide [muRegs, Function.update_apply])
      (by rw [tsR_val src _ _ _ _ _ _ _ _ _ ⟨by decide, by decide⟩ (by decide)]; simp +decide [muRegs, Function.update_apply]
          have : a / 2 * v0 rSS ≤ a * v0 rSS := Nat.mul_le_mul_right _ (Nat.div_le_self _ _); omega)
    rw [tsR_setv src _ _ _ _ _ _ _ _ _ ⟨by decide, by decide⟩ (by decide)] at c3
    have c4 := wclear_spec cap rY (b / 2)
      (ts src h O (regsOf (Function.update (Function.update (Function.update (muRegs v0 a b) rX 0) rN0 0) rXS 0) Z4 Z4 Z4
        okm) cl)
      (by rw [tsR_val src _ _ _ _ _ _ _ _ _ ⟨by decide, by decide⟩ (by decide)]; simp +decide [muRegs, Function.update_apply])
      (by rw [tsR_val src _ _ _ _ _ _ _ _ _ ⟨by decide, by decide⟩ (by decide)]; simp +decide [muRegs, Function.update_apply]
          omega)
    rw [tsR_setv src _ _ _ _ _ _ _ _ _ ⟨by decide, by decide⟩ (by decide)] at c4
    have c5 := wclear_spec cap rN1 (b % 2)
      (ts src h O (regsOf (Function.update (Function.update (Function.update (Function.update (muRegs v0 a b) rX 0) rN0 0)
        rXS 0) rY 0) Z4 Z4 Z4 okm) cl)
      (by rw [tsR_val src _ _ _ _ _ _ _ _ _ ⟨by decide, by decide⟩ (by decide)]; simp +decide [muRegs, Function.update_apply])
      (by rw [tsR_val src _ _ _ _ _ _ _ _ _ ⟨by decide, by decide⟩ (by decide)]; simp +decide [muRegs, Function.update_apply]
          have := Nat.mod_lt b (show 2 > 0 by omega); omega)
    rw [tsR_setv src _ _ _ _ _ _ _ _ _ ⟨by decide, by decide⟩ (by decide)] at c5
    have c6 := wclear_spec cap rYS (b / 2 * v0 rSS)
      (ts src h O (regsOf (Function.update (Function.update (Function.update (Function.update (Function.update
        (muRegs v0 a b) rX 0) rN0 0) rXS 0) rY 0) rN1 0) Z4 Z4 Z4 okm) cl)
      (by rw [tsR_val src _ _ _ _ _ _ _ _ _ ⟨by decide, by decide⟩ (by decide)]; simp +decide [muRegs, Function.update_apply])
      (by rw [tsR_val src _ _ _ _ _ _ _ _ _ ⟨by decide, by decide⟩ (by decide)]; simp +decide [muRegs, Function.update_apply]
          have : b / 2 * v0 rSS ≤ b * v0 rSS := Nat.mul_le_mul_right _ (Nat.div_le_self _ _); omega)
    rw [tsR_setv src _ _ _ _ _ _ _ _ _ ⟨by decide, by decide⟩ (by decide)] at c6
    have e6 : Function.update (Function.update (Function.update (Function.update (Function.update (Function.update
        (muRegs v0 a b) rX 0) rN0 0) rXS 0) rY 0) rN1 0) rYS 0 = v0 := by
      funext r
      simp +decide only [muRegs, Function.update_apply]
      split_ifs <;> simp_all
    rw [e6] at c6
    refine WExec.mono (WExec.seq c1 (WExec.seq c2 (WExec.seq c3 (WExec.seq c4 (WExec.seq c5 c6))))) ?_
    have := Nat.div_le_self a 2
    have := Nat.div_le_self b 2
    have := Nat.mod_lt a (show 2 > 0 by omega)
    have := Nat.mod_lt b (show 2 > 0 by omega)
    have : a / 2 * v0 rSS ≤ a * v0 rSS := Nat.mul_le_mul_right _ (Nat.div_le_self _ _)
    have : b / 2 * v0 rSS ≤ b * v0 rSS := Nat.mul_le_mul_right _ (Nat.div_le_self _ _)
    have hAB : 3 * (a + b) * (v0 rSS + 1) = 3 * (a * v0 rSS) + 3 * a + 3 * (b * v0 rSS) + 3 * b := by ring
    rw [hAB]
    omega
  refine WExec.mono (WExec.seq m1 (WExec.seq s1 (WExec.seq m2 (WExec.seq s2 (WExec.seq bl cl6))))) ?_
  rw [u1LIT, show mX 1 = rSS from rfl, u1o _ (by decide) (by decide), show mY 1 = rSS from rfl, u3LIT,
    u3o _ (by decide) (by decide), u2o _ (by decide) (by decide) (by decide) (by decide), u1o _ (by decide) (by decide)]
  have := Nat.div_le_self a 2
  have := Nat.div_le_self b 2
  have hA : v0 rSS * (18 * (a / 2) + 8) ≤ 18 * (a * v0 rSS) + 8 * v0 rSS := by
    have h1 : v0 rSS * (a / 2) ≤ a * v0 rSS := by rw [Nat.mul_comm a]; exact Nat.mul_le_mul_left _ (Nat.div_le_self _ _)
    have h2 : v0 rSS * (18 * (a / 2) + 8) = 18 * (v0 rSS * (a / 2)) + 8 * v0 rSS := by ring
    omega
  have hB' : v0 rSS * (18 * (b / 2) + 8) ≤ 18 * (b * v0 rSS) + 8 * v0 rSS := by
    have h1 : v0 rSS * (b / 2) ≤ b * v0 rSS := by rw [Nat.mul_comm b]; exact Nat.mul_le_mul_left _ (Nat.div_le_self _ _)
    have h2 : v0 rSS * (18 * (b / 2) + 8) = 18 * (v0 rSS * (b / 2)) + 8 * v0 rSS := by ring
    omega
  have hA2 : (a + 1) * (v0 rSS + 1) = a * v0 rSS + a + v0 rSS + 1 := by ring
  have hB2 : (b + 1) * (v0 rSS + 1) = b * v0 rSS + b + v0 rSS + 1 := by ring
  rw [Nat.mul_assoc 100, hA2, Nat.mul_assoc 100, hB2]
  have hk := u1LIT
  have hl := u3LIT
  have hu : (Function.update (Function.update v0 rL0 a) rL1 b) rL0 = a := by simp +decide [Function.update_apply]
  have hw : 3 * (a + b) * (v0 rSS + 1) = 3 * (a * v0 rSS) + 3 * a + 3 * (b * v0 rSS) + 3 * b := by ring
  omega

end NearCubicWires.WireExponent3_5.UnionMachine.FrontTW
