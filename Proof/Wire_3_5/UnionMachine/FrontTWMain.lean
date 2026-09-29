import Proof.Wire_3_5.UnionMachine.FrontTWLoop

/-! # C6 front, U5: the table writer (P3:3685-3691, 3483-3489)

**`twP`**: three passes over the clauses (the validity test at every position, the second-moment test at every
position, the clause test at every clause), then the table's closing `0`. **`twT`**: the written table is the three
passes' entries in order, and `OK` is every call's admissibility.

Paper quantity of the main statement: the call table of `(tr:tests)` (its word) and the calls' admissibility. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unnecessarySimpa false

namespace NearCubicWires.WireExponent3_5.UnionMachine.FrontTW
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.UnionMachine.FrontTWKit NearCubicWires.WireExponent3_5.UnionMachine.FrontTWFrame
open NearCubicWires.RepairRepresentation (natWord)

variable (cap : ℕ) (src : Fin 11 → List Bool)

theorem bodyV_noCL : usesR rCL bodyV = false := by decide
theorem bodyQ_noCL : usesR rCL bodyQ = false := by decide
theorem bodyMu_noCL : usesR rCL bodyMu = false := by decide

/-- **The table writer**: the three passes, then the table's closing `0`. -/
def twP : WM 10 NR := .seq (passP bodyV) (.seq (passP bodyQ) (.seq (passP bodyMu) (emitC sOut rOP false)))

/-- A clause body's contract over a pass (as `clLoopT` reads it). -/
def BodyOK (body : WM 10 NR) (cl : Bool) (v0 : Fin NR → ℕ) (lits : List ℕ) (M : ℕ) (Wc : ℕ → ℕ → List Bool)
    (bc : ℕ → ℕ → Bool) (L cc : ℕ) : Prop :=
  ∀ i < M, ∀ (h : ℕ) (o : List Bool) (ok : ℕ), ok ≤ 1 →
    o.length + (Wc (litA lits i) (litB lits i)).length + L ≤ cap →
    WExec cap body (ts src h o (regsOf (Function.update (Function.update v0 rL0 (litA lits i)) rL1 (litB lits i))
      Z4 Z4 Z4 ok) cl) (ts src h (o ++ Wc (litA lits i) (litB lits i))
        (regsOf v0 Z4 Z4 Z4 (if bc (litA lits i) (litB lits i) then ok else 0)) cl) cc

/-- **The table writer's run**: the table word is the three passes' entries and the closing `0`; `OK` is every call's
admissibility. -/
theorem twT (cl : Bool) (v0 : Fin NR → ℕ) (hv : RdOK v0) (hT : v0 rT = 0) (hBc : v0 rBIG ≤ cap) (lits : List ℕ)
    (M : ℕ) (hPO : POLayout cap src v0 lits M) (WV WQ WM : ℕ → ℕ → List Bool) (bV bQ bM : ℕ → ℕ → Bool)
    (L cV cQ cM Rb : ℕ) (hV : BodyOK cap src bodyV cl v0 lits M WV bV L cV)
    (hQ : BodyOK cap src bodyQ cl v0 lits M WQ bQ L cQ) (hM : BodyOK cap src bodyMu cl v0 lits M WM bM L cM)
    (hrd : ∀ x ∈ lits, rdCost x ≤ Rb ∧ 2 ^ (natBitLength x + 1) ≤ cap) (hMc : M + 1 ≤ cap)
    (hlen : (accW lits WV M).length + (accW lits WQ M).length + (accW lits WM M).length + L + 1 ≤ cap) :
    WExec cap twP (ts src 0 [] (regsOf v0 Z4 Z4 Z4 1) cl)
      (ts src 0 (accW lits WV M ++ accW lits WQ M ++ accW lits WM M ++ [false])
        (regsOf v0 Z4 Z4 Z4 (if (accB lits bV M && accB lits bQ M && accB lits bM M) then 1 else 0)) cl)
      (3 * (60 * v0 rBIG + 250 + 18 * M + M * (2 * Rb + cV + cQ + cM + 8)) + 10) := by
  have p1 := passT cap src bodyV bodyV_noCL cl v0 hv hT hBc lits M hPO WV bV L cV Rb hV hrd hMc [] 1 le_rfl
    (by simp; omega)
  set k1 := if accB lits bV M then 1 else 0 with hk1
  have p2 := passT cap src bodyQ bodyQ_noCL cl v0 hv hT hBc lits M hPO WQ bQ L cQ Rb hQ hrd hMc
    ([] ++ accW lits WV M) k1 (by simp only [k1]; split_ifs <;> omega) (by simp; omega)
  set k2 := if accB lits bQ M then k1 else 0 with hk2
  have p3 := passT cap src bodyMu bodyMu_noCL cl v0 hv hT hBc lits M hPO WM bM L cM Rb hM hrd hMc
    ([] ++ accW lits WV M ++ accW lits WQ M) k2 (by simp only [k2, k1]; split_ifs <;> omega) (by simp; omega)
  set k3 := if accB lits bM M then k2 else 0 with hk3
  have p4 := emitRawT cap src 0 ([] ++ accW lits WV M ++ accW lits WQ M ++ accW lits WM M) (regsOf v0 Z4 Z4 Z4 k3) cl
    false (by simp; omega)
  have ek : k3 = if (accB lits bV M && accB lits bQ M && accB lits bM M) then 1 else 0 := by
    simp only [k3, k2, k1]
    cases accB lits bV M <;> cases accB lits bQ M <;> cases accB lits bM M <;> simp
  simp only [List.nil_append] at p2 p3 p4
  rw [← ek]
  refine WExec.mono (WExec.seq p1 (WExec.seq p2 (WExec.seq p3 p4))) ?_
  nlinarith

/-! ## The three passes' clause bodies -/

/-- The validity test's clause output. -/
def WVof (d : TWData) (v0 : Fin NR → ℕ) (a b : ℕ) : List Bool :=
  outV d (posRegs (Function.update (Function.update v0 rL1 b) rLIT a)) ++ outV d (posRegs (Function.update v0 rLIT b))
def bVof (d : TWData) (v0 : Fin NR → ℕ) (a b : ℕ) : Bool :=
  okV d (posRegs (Function.update (Function.update v0 rL1 b) rLIT a)) && okV d (posRegs (Function.update v0 rLIT b))
/-- The second-moment test's clause output. -/
def WQof (d : TWData) (v0 : Fin NR → ℕ) (a b : ℕ) : List Bool :=
  outQ d (posRegs (Function.update (Function.update v0 rL1 b) rLIT a)) ++ outQ d (posRegs (Function.update v0 rLIT b))
def bQof (d : TWData) (v0 : Fin NR → ℕ) (a b : ℕ) : Bool :=
  okQ d (posRegs (Function.update (Function.update v0 rL1 b) rLIT a)) && okQ d (posRegs (Function.update v0 rLIT b))
/-- The clause test's clause output. -/
def WMof (d : TWData) (v0 : Fin NR → ℕ) (a b : ℕ) : List Bool := outMu d (FrontTW.muRegs v0 a b)
def bMof (d : TWData) (v0 : Fin NR → ℕ) (a b : ℕ) : Bool := okMu d (FrontTW.muRegs v0 a b)

/-- The plain registers' state between clauses. -/
structure ClauseRegs (d : TWData) (B : ℕ) (v0 : Fin NR → ℕ) : Prop where
  g : GInv cap d B v0
  l0 : v0 rL0 = 0
  l1 : v0 rL1 = 0
  lit : v0 rLIT = 0
  x : v0 rX = 0
  n0 : v0 rN0 = 0
  xs : v0 rXS = 0
  sy : v0 rSYSX = 0
  y : v0 rY = 0
  n1 : v0 rN1 = 0
  ys : v0 rYS = 0
  s0 : v0 rSS ≤ d.es.length
  c0 : 0 < d.crs.length ∧ 0 < d.ef.length
  cs : v0 rSS + 1 ≤ cap

/-- A clause's literal variables are valid (their grid entries, parity and carrier exist). -/
def LitsOK (d : TWData) (v0 : Fin NR → ℕ) (lits : List ℕ) (M : ℕ) : Prop :=
  ∀ i < M, XOK cap d (v0 rSS) (litA lits i / 2) ∧ XOK cap d (v0 rSS) (litB lits i / 2) ∧
    litA lits i + litA lits i * v0 rSS + v0 rSS + v0 rSYS + litB lits i + litB lits i * v0 rSS + 1 ≤ cap

theorem bodyV_ok (cl : Bool) (d : TWData) (hd : d.Holds src) (B : ℕ) (hB : d.Bnd B) (v0 : Fin NR → ℕ)
    (hc : ClauseRegs cap d B v0) (lits : List ℕ) (M : ℕ) (hl : LitsOK cap d v0 lits M) (cc : ℕ)
    (hcc : ∀ i < M, 7 * litA lits i + 1 + 1 + (110 * (litA lits i * v0 rSS) + 110 * litA lits i + 110 * v0 rSS +
      30 * v0 rSYS + costV B (posRegs (Function.update (Function.update v0 rL1 (litB lits i)) rLIT (litA lits i))) + 120) +
      1 + (7 * litB lits i + 1 + 1 + (110 * (litB lits i * v0 rSS) + 110 * litB lits i + 110 * v0 rSS + 30 * v0 rSYS +
        costV B (posRegs (Function.update v0 rLIT (litB lits i))) + 120)) ≤ cc) :
    BodyOK cap src bodyV cl v0 lits M (WVof d v0) (bVof d v0) (30 * B + 40) cc := by
  intro i hi h o ok hok hlen
  obtain ⟨ha, hb, hcap⟩ := hl i hi
  have := bodyPT cap src vBlocks h cl d B (outV d) (okV d) (costV B)
    (fun v hg hv => vBlocksP cap src d hd B hB h cl v hg hv) v0 hc.g hc.l0 hc.l1 hc.lit hc.x hc.n0 hc.xs hc.sy
    (by rw [hc.ys]; simpa using hc.s0) (by rw [hc.y]; exact hc.c0) (by rw [hc.ys]; simpa using hc.cs) (litA lits i) (litB lits i)
    ha hb (by omega) (by omega) o ok hok (by simp only [WVof, List.length_append] at hlen; omega)
  exact WExec.mono this (hcc i hi)

theorem bodyQ_ok (cl : Bool) (d : TWData) (hd : d.Holds src) (B : ℕ) (hB : d.Bnd B) (v0 : Fin NR → ℕ)
    (hc : ClauseRegs cap d B v0) (lits : List ℕ) (M : ℕ) (hl : LitsOK cap d v0 lits M) (cc : ℕ)
    (hcc : ∀ i < M, 7 * litA lits i + 1 + 1 + (110 * (litA lits i * v0 rSS) + 110 * litA lits i + 110 * v0 rSS +
      30 * v0 rSYS + mbCost B (posRegs (Function.update (Function.update v0 rL1 (litB lits i)) rLIT (litA lits i))) rMb
        (FrontTableRef.patQ 0) + 120) +
      1 + (7 * litB lits i + 1 + 1 + (110 * (litB lits i * v0 rSS) + 110 * litB lits i + 110 * v0 rSS + 30 * v0 rSYS +
        mbCost B (posRegs (Function.update v0 rLIT (litB lits i))) rMb (FrontTableRef.patQ 0) + 120)) ≤ cc) :
    BodyOK cap src bodyQ cl v0 lits M (WQof d v0) (bQof d v0) (30 * B + 40) cc := by
  intro i hi h o ok hok hlen
  obtain ⟨ha, hb, hcap⟩ := hl i hi
  have := bodyPT cap src qBlocks h cl d B (outQ d) (okQ d) (fun v => mbCost B v rMb (FrontTableRef.patQ 0))
    (fun v hg hv => qBlocksP cap src d hd B hB h cl v hg hv) v0 hc.g hc.l0 hc.l1 hc.lit hc.x hc.n0 hc.xs hc.sy
    (by rw [hc.ys]; simpa using hc.s0) (by rw [hc.y]; exact hc.c0) (by rw [hc.ys]; simpa using hc.cs) (litA lits i) (litB lits i)
    ha hb (by omega) (by omega) o ok hok (by simp only [WQof, List.length_append] at hlen; omega)
  exact WExec.mono this (hcc i hi)

theorem bodyMu_ok (cl : Bool) (d : TWData) (hd : d.Holds src) (B : ℕ) (hB : d.Bnd B) (v0 : Fin NR → ℕ)
    (hc : ClauseRegs cap d B v0) (lits : List ℕ) (M : ℕ) (hl : LitsOK cap d v0 lits M) (cc : ℕ)
    (hcc : ∀ i < M, 100 * (litA lits i + 1) * (v0 rSS + 1) + 100 * (litB lits i + 1) * (v0 rSS + 1) +
      costMu B (FrontTW.muRegs v0 (litA lits i) (litB lits i)) + 100 ≤ cc) :
    BodyOK cap src bodyMu cl v0 lits M (WMof d v0) (bMof d v0) (30 * B + 40) cc := by
  intro i hi h o ok hok hlen
  obtain ⟨ha, hb, hcap⟩ := hl i hi
  have := bodyMuT cap src h cl d hd B hB v0 hc.g hc.l0 hc.l1 hc.lit hc.x hc.n0 hc.xs hc.y hc.n1 hc.ys
    (litA lits i) (litB lits i) ha hb (by omega) o ok hok (by simp only [WMof] at hlen; omega)
  exact WExec.mono this (hcc i hi)

end NearCubicWires.WireExponent3_5.UnionMachine.FrontTW
