import Proof.Wire_3_5.Primitive.Writers.PopSetupNums
import Proof.Wire_3_5.Primitive.Writers.PopSetupWords
import Proof.Wire_3_5.Primitive.Writers.PopSetupIface

/-! # PA POP setup, part 5a: the whole program's run

**`popProg x`** = the numbers (`PopSetupNums`: `pwA`, `prA`, `prB`, `pmC`, `psq`, `ptD1 … ptD3`), then the words
(`PopSetupWords.pwordsW`). **`pop_run`**: from the POP setup's entry bank (`PopSetup.PopIn`) and one capacity fact,
the run within **`popCost cap`** (`O(cap³)`) and every fact `UnitReady.PopReady` reads from the state: C5's builder
registers, the POP cell's registers, every other register below `250` zero, the words, the other streams, the heads
and the cell unchanged.

Paper quantity: none (the run of the POP setup of `list:flatten`'s row at the list seed, P3:1491-1510). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace NearCubicWires.WireExponent3_5.PrimAsm.PopSetupRun
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.SignedSortKey NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimAsm NearCubicWires.WireExponent3_5.PrimAsm.SymLayout

/-! ## The numbers, named -/

/-- list:base's `J = ⌈log₂ B⌉ + 9`. -/
def pJ (B : ℕ) : ℕ := Nat.clog 2 B + 9
/-- The rank `max J ⌈log₂ M⌉`. -/
def pRk (M B : ℕ) : ℕ := max (pJ B) (Nat.clog 2 M)
/-- The walk side bits `⌊3·rank/2⌋`. -/
def pSb (M B : ℕ) : ℕ := (pRk M B + pRk M B + pRk M B) / 2
/-- The padding `2·sb − (3·rank − 1)`. -/
def pPad (M B : ℕ) : ℕ := pSb M B + pSb M B - (pRk M B + pRk M B + pRk M B - 1)
/-- `n = 2⌊err/4⌋`. -/
def pN (err : ℕ) : ℕ := 2 * (err / 4)
/-- The index word's width `160n + 2·sb`. -/
def pWid (M B err : ℕ) : ℕ := 160 * pN err + pSb M B + pSb M B
/-- The window count `⌈√(4096·B)⌉`. -/
def pS (B : ℕ) : ℕ := CanonicalFourfoldRowProgram.natCeilSqrt (4096 * B)
/-- The labels' bound. -/
def pMl (r4 G off L : ℕ) : ℕ := off + L + (r4 + 4) * G

/-! ## The program -/

/-- The numbers, first half: the walk numbers, the rank, the widths, `Mlab` and `4096·B`. -/
def progA {ns : ℕ} : WM ns LNR :=
  .seq PopSetupNums.pwAW (.seq PopSetupNums.prAW (.seq PopSetupNums.prBW PopSetupNums.pmCW))

/-- The numbers, second half: the window count and the targets. -/
def progB {ns : ℕ} : WM ns LNR :=
  .seq PopSetupNums.psqW (.seq PopSetupNums.ptD1W (.seq PopSetupNums.ptD2W PopSetupNums.ptD3W))

/-- **The POP setup's program.** -/
def popProg (x : ℕ) : WM (LNS x) LNR := .seq progA (.seq progB (PopSetupWords.pwordsW x))

/-- The registers the first half writes. -/
def outA : List (Fin LNR) := PopSetupNums.pwAOut ++ PopSetupNums.prAOut ++ PopSetupNums.prBOut ++ PopSetupNums.pmCOut

/-- The registers the second half writes. -/
def outB : List (Fin LNR) := PopSetupNums.psqOut ++ PopSetupNums.ptD1Out ++ PopSetupNums.ptD2Out ++ PopSetupNums.ptD3Out

/-- The program's cost. -/
def popCost (cap : ℕ) : ℕ :=
  400 * UnaryPow.sq cap + 200 * ((cap + 2) * (cap + 2) * (cap + 2)) + 1000 * ((cap + 1) * (cap + 1)) + 100

/-- The registers below `250` the program writes. -/
def lowOut : List (Fin LNR) := [6, 7, 8, 10, 15, 20, 21, 22, 23, 39, 40, 63, 64, 69, 71, 72, 82, 199]

/-- The capacity the run needs. -/
def runNeed (M B err f sg s r4 G off L : ℕ) : ℕ :=
  1000000 * (M + B + err + f + sg + s + r4 + G + off + L + 10) + (r4 + 4) * G + (4096 * B + 2) * (4096 * B + 2)

variable (cap : ℕ)

theorem runA {ns : ℕ} (σ : WState ns LNR) (M B err f sg s r4 G off L : ℕ) (h400 : σ.val 400 = M) (h401 : σ.val 401 = B)
    (h402 : σ.val 402 = err) (h403 : σ.val 403 = f) (h404 : σ.val 404 = sg) (h405 : σ.val 405 = s)
    (h406 : σ.val 406 = r4) (h407 : σ.val 407 = G) (h408 : σ.val 408 = off) (h409 : σ.val 409 = L)
    (hz : ∀ r : Fin LNR, 410 ≤ r.val → σ.val r = 0) (hc1 : 1 ≤ cap) (hN : runNeed M B err f sg s r4 G off L ≤ cap) :
    ∃ τ : WState ns LNR, WExec cap progA σ τ (200 * UnaryPow.sq cap) ∧ τ.st = σ.st ∧ τ.sh = σ.sh ∧ τ.cell = σ.cell ∧
      (∀ r : Fin LNR, r ∉ outA → τ.val r = σ.val r) ∧ τ.val 441 = pN err ∧ τ.val 442 = pN err + 1 ∧
      τ.val 443 = err / 4 + 1 ∧ τ.val 444 = pJ B ∧ τ.val 446 = pRk M B ∧ τ.val 447 = pSb M B ∧
      τ.val 448 = pRk M B - 1 ∧ τ.val 449 = pRk M B + pRk M B + pRk M B - 1 ∧ τ.val 458 = pRk M B + pRk M B - 1 ∧
      τ.val 459 = pSb M B + pSb M B + 1 ∧ τ.val 460 = pPad M B ∧ τ.val 461 = pWid M B err ∧ τ.val 462 = pJ B + 1 ∧
      τ.val 463 = 4096 * B ∧ τ.val 465 = pMl r4 G off L := by
  have hcB : Nat.clog 2 B ≤ B := Nat.clog_le_of_le_pow (Nat.lt_two_pow_self).le
  have hcM : Nat.clog 2 M ≤ M := Nat.clog_le_of_le_pow (Nat.lt_two_pow_self).le
  have hmx : max (Nat.clog 2 B + 9) (Nat.clog 2 M) ≤ B + M + 9 := max_le (by omega) (by omega)
  have hsq := UnaryPow.sq_ge cap
  unfold runNeed at hN
  have X1 := PopSetupNums.pwA_spec cap σ (err)
    (h402 := h402)
    (z410 := hz _ (by decide))
    (z411 := hz _ (by decide))
    (z412 := hz _ (by decide))
    (z413 := hz _ (by decide))
    (z414 := hz _ (by decide))
    (z415 := hz _ (by decide))
    (z416 := hz _ (by decide))
    (z417 := hz _ (by decide))
    (z418 := hz _ (by decide))
    (z419 := hz _ (by decide))
    (z441 := hz _ (by decide))
    (z442 := hz _ (by decide))
    (z443 := hz _ (by decide))
    (hcr := by omega)
    (hc1 := hc1)
  obtain ⟨τ1, e1, st1, sh1, ce1, o1, v1_410, v1_411, v1_412, v1_441, v1_442, v1_443⟩ := X1
  have X2 := PopSetupNums.prA_spec cap τ1 (M) (B)
    (h400 := by rw [o1 _ (by decide)]; exact h400)
    (h401 := by rw [o1 _ (by decide)]; exact h401)
    (z444 := by rw [o1 _ (by decide)]; exact hz _ (by decide))
    (z445 := by rw [o1 _ (by decide)]; exact hz _ (by decide))
    (z446 := by rw [o1 _ (by decide)]; exact hz _ (by decide))
    (z447 := by rw [o1 _ (by decide)]; exact hz _ (by decide))
    (z450 := by rw [o1 _ (by decide)]; exact hz _ (by decide))
    (z451 := by rw [o1 _ (by decide)]; exact hz _ (by decide))
    (z452 := by rw [o1 _ (by decide)]; exact hz _ (by decide))
    (z453 := by rw [o1 _ (by decide)]; exact hz _ (by decide))
    (z454 := by rw [o1 _ (by decide)]; exact hz _ (by decide))
    (z455 := by rw [o1 _ (by decide)]; exact hz _ (by decide))
    (z456 := by rw [o1 _ (by decide)]; exact hz _ (by decide))
    (z457 := by rw [o1 _ (by decide)]; exact hz _ (by decide))
    (hcB := hcB)
    (hcM := hcM)
    (hmx := hmx)
    (hcr := by omega)
    (hc1 := hc1)
  obtain ⟨τ2, e2, st2, sh2, ce2, o2, v2_444, v2_445, v2_446, v2_447⟩ := X2
  have X3 := PopSetupNums.prB_spec cap τ2 ((2 * (err / 4))) ((Nat.clog 2 B + 9)) ((max (Nat.clog 2 B + 9) (Nat.clog 2 M))) ((((max (Nat.clog 2 B + 9) (Nat.clog 2 M)) + (max (Nat.clog 2 B + 9) (Nat.clog 2 M)) + (max (Nat.clog 2 B + 9) (Nat.clog 2 M))) / 2))
    (h441 := by rw [o2 _ (by decide)]; exact v1_441)
    (h444 := v2_444)
    (h446 := v2_446)
    (h447 := v2_447)
    (z448 := by rw [o2 _ (by decide), o1 _ (by decide)]; exact hz _ (by decide))
    (z449 := by rw [o2 _ (by decide), o1 _ (by decide)]; exact hz _ (by decide))
    (z458 := by rw [o2 _ (by decide), o1 _ (by decide)]; exact hz _ (by decide))
    (z459 := by rw [o2 _ (by decide), o1 _ (by decide)]; exact hz _ (by decide))
    (z460 := by rw [o2 _ (by decide), o1 _ (by decide)]; exact hz _ (by decide))
    (z461 := by rw [o2 _ (by decide), o1 _ (by decide)]; exact hz _ (by decide))
    (z462 := by rw [o2 _ (by decide), o1 _ (by decide)]; exact hz _ (by decide))
    (z419 := by rw [o2 _ (by decide), o1 _ (by decide)]; exact hz _ (by decide))
    (z420 := by rw [o2 _ (by decide), o1 _ (by decide)]; exact hz _ (by decide))
    (z421 := by rw [o2 _ (by decide), o1 _ (by decide)]; exact hz _ (by decide))
    (z413 := by rw [o2 _ (by decide), o1 _ (by decide)]; exact hz _ (by decide))
    (z414 := by rw [o2 _ (by decide), o1 _ (by decide)]; exact hz _ (by decide))
    (hcr := by omega)
    (hc1 := hc1)
  obtain ⟨τ3, e3, st3, sh3, ce3, o3, v3_448, v3_449, v3_458, v3_459, v3_460, v3_461, v3_462, v3_421⟩ := X3
  have X4 := PopSetupNums.pmC_spec cap τ3 (B) (r4) (G) (off) (L)
    (h401 := by rw [o3 _ (by decide), o2 _ (by decide), o1 _ (by decide)]; exact h401)
    (h406 := by rw [o3 _ (by decide), o2 _ (by decide), o1 _ (by decide)]; exact h406)
    (h407 := by rw [o3 _ (by decide), o2 _ (by decide), o1 _ (by decide)]; exact h407)
    (h408 := by rw [o3 _ (by decide), o2 _ (by decide), o1 _ (by decide)]; exact h408)
    (h409 := by rw [o3 _ (by decide), o2 _ (by decide), o1 _ (by decide)]; exact h409)
    (z463 := by rw [o3 _ (by decide), o2 _ (by decide), o1 _ (by decide)]; exact hz _ (by decide))
    (z465 := by rw [o3 _ (by decide), o2 _ (by decide), o1 _ (by decide)]; exact hz _ (by decide))
    (z466 := by rw [o3 _ (by decide), o2 _ (by decide), o1 _ (by decide)]; exact hz _ (by decide))
    (z422 := by rw [o3 _ (by decide), o2 _ (by decide), o1 _ (by decide)]; exact hz _ (by decide))
    (z413 := by rw [o3 _ (by decide), o2 _ (by decide), o1 _ (by decide)]; exact hz _ (by decide))
    (z414 := by rw [o3 _ (by decide), o2 _ (by decide), o1 _ (by decide)]; exact hz _ (by decide))
    (z419 := by rw [o3 _ (by decide), o2 _ (by decide), o1 _ (by decide)]; exact hz _ (by decide))
    (hcr := by omega)
    (hc1 := hc1)
  obtain ⟨τ4, e4, st4, sh4, ce4, o4, v4_465, v4_463, v4_466, v4_422⟩ := X4
  have f441 : τ4.val 441 = pN err := by rw [o4 _ (by decide), o3 _ (by decide), o2 _ (by decide)]; exact v1_441
  have f442 : τ4.val 442 = pN err + 1 := by rw [o4 _ (by decide), o3 _ (by decide), o2 _ (by decide)]; exact v1_442
  have f443 : τ4.val 443 = err / 4 + 1 := by rw [o4 _ (by decide), o3 _ (by decide), o2 _ (by decide)]; exact v1_443
  have f444 : τ4.val 444 = pJ B := by rw [o4 _ (by decide), o3 _ (by decide)]; exact v2_444
  have f446 : τ4.val 446 = pRk M B := by rw [o4 _ (by decide), o3 _ (by decide)]; exact v2_446
  have f447 : τ4.val 447 = pSb M B := by rw [o4 _ (by decide), o3 _ (by decide)]; exact v2_447
  have f448 : τ4.val 448 = pRk M B - 1 := by rw [o4 _ (by decide)]; exact v3_448
  have f449 : τ4.val 449 = pRk M B + pRk M B + pRk M B - 1 := by rw [o4 _ (by decide)]; exact v3_449
  have f458 : τ4.val 458 = pRk M B + pRk M B - 1 := by rw [o4 _ (by decide)]; exact v3_458
  have f459 : τ4.val 459 = pSb M B + pSb M B + 1 := by rw [o4 _ (by decide)]; exact v3_459
  have f460 : τ4.val 460 = pPad M B := by rw [o4 _ (by decide)]; exact v3_460
  have f461 : τ4.val 461 = pWid M B err := by rw [o4 _ (by decide)]; exact v3_461
  have f462 : τ4.val 462 = pJ B + 1 := by rw [o4 _ (by decide)]; exact v3_462
  have f463 : τ4.val 463 = 4096 * B := v4_463
  have f465 : τ4.val 465 = pMl r4 G off L := v4_465
  refine ⟨τ4, WExec.mono (WExec.seq e1 (WExec.seq e2 (WExec.seq e3 e4))) (by omega), by rw [st4, st3, st2, st1],
    by rw [sh4, sh3, sh2, sh1], by rw [ce4, ce3, ce2, ce1], ?_, f441, f442, f443, f444, f446, f447, f448, f449, f458,
    f459, f460, f461, f462, f463, f465⟩
  intro r hr
  rw [o4 r (fun h => hr (by simp [outA, h])), o3 r (fun h => hr (by simp [outA, h])),
    o2 r (fun h => hr (by simp [outA, h])), o1 r (fun h => hr (by simp [outA, h]))]

theorem runB {ns : ℕ} (σ : WState ns LNR) (M B err sg s r4 G off L : ℕ) (h400 : σ.val 400 = M)
    (h404 : σ.val 404 = sg) (h405 : σ.val 405 = s) (h406 : σ.val 406 = r4) (h407 : σ.val 407 = G)
    (h408 : σ.val 408 = off) (h409 : σ.val 409 = L) (h442 : σ.val 442 = pN err + 1) (h443 : σ.val 443 = err / 4 + 1)
    (h444 : σ.val 444 = pJ B) (h446 : σ.val 446 = pRk M B) (h447 : σ.val 447 = pSb M B)
    (h448 : σ.val 448 = pRk M B - 1) (h460 : σ.val 460 = pPad M B) (h463 : σ.val 463 = 4096 * B)
    (h465 : σ.val 465 = pMl r4 G off L)
    (z6 : σ.val 6 = 0) (z7 : σ.val 7 = 0) (z8 : σ.val 8 = 0) (z10 : σ.val 10 = 0) (z15 : σ.val 15 = 0)
    (z20 : σ.val 20 = 0) (z21 : σ.val 21 = 0) (z22 : σ.val 22 = 0) (z23 : σ.val 23 = 0) (z39 : σ.val 39 = 0)
    (z40 : σ.val 40 = 0) (z63 : σ.val 63 = 0) (z64 : σ.val 64 = 0) (z69 : σ.val 69 = 0) (z71 : σ.val 71 = 0)
    (z72 : σ.val 72 = 0) (z82 : σ.val 82 = 0) (z199 : σ.val 199 = 0) (z419 : σ.val 419 = 0) (z450 : σ.val 450 = 0)
    (z451 : σ.val 451 = 0) (z452 : σ.val 452 = 0) (z453 : σ.val 453 = 0) (z454 : σ.val 454 = 0) (z455 : σ.val 455 = 0)
    (z456 : σ.val 456 = 0) (z457 : σ.val 457 = 0) (z464 : σ.val 464 = 0) (hc1 : 1 ≤ cap)
    (hN : runNeed M B err 0 sg s r4 G off L ≤ cap) :
    ∃ τ : WState ns LNR, WExec cap progB σ τ (200 * ((cap + 2) * (cap + 2) * (cap + 2)) + 100 * UnaryPow.sq cap) ∧
      τ.st = σ.st ∧ τ.sh = σ.sh ∧ τ.cell = σ.cell ∧ (∀ r : Fin LNR, r ∉ outB → τ.val r = σ.val r) ∧
      τ.val 6 = pSb M B ∧ τ.val 7 = pRk M B ∧ τ.val 8 = pRk M B - 1 ∧ τ.val 10 = L ∧ τ.val 15 = pPad M B ∧
      τ.val 20 = r4 ∧ τ.val 21 = G ∧ τ.val 22 = off ∧ τ.val 23 = L ∧ τ.val 39 = pS B ∧ τ.val 40 = pJ B ∧
      τ.val 63 = M ∧ τ.val 64 = L ∧ τ.val 69 = sg ∧ τ.val 71 = pN err + 1 ∧ τ.val 72 = err / 4 + 1 ∧
      τ.val 82 = s ∧ τ.val 199 = pMl r4 G off L := by
  have hcB : Nat.clog 2 B ≤ B := Nat.clog_le_of_le_pow (Nat.lt_two_pow_self).le
  have hcM : Nat.clog 2 M ≤ M := Nat.clog_le_of_le_pow (Nat.lt_two_pow_self).le
  have hmx : max (Nat.clog 2 B + 9) (Nat.clog 2 M) ≤ B + M + 9 := max_le (by omega) (by omega)
  have hSq : CanonicalFourfoldRowProgram.natCeilSqrt (4096 * B) ≤ 4096 * B + 1 := LevelW.natCeilSqrt_le _
  have hsq := UnaryPow.sq_ge cap
  unfold runNeed at hN
  have X1 := PopSetupNums.psq_spec cap σ ((4096 * B))
    (h463 := h463)
    (z464 := z464)
    (z450 := z450)
    (z451 := z451)
    (z452 := z452)
    (z453 := z453)
    (z454 := z454)
    (z455 := z455)
    (z456 := z456)
    (z457 := z457)
    (hcap := by omega)
  obtain ⟨τ1, e1, st1, sh1, ce1, o1, v1_464⟩ := X1
  have X2 := PopSetupNums.ptD1_spec cap τ1 ((((max (Nat.clog 2 B + 9) (Nat.clog 2 M)) + (max (Nat.clog 2 B + 9) (Nat.clog 2 M)) + (max (Nat.clog 2 B + 9) (Nat.clog 2 M))) / 2)) ((max (Nat.clog 2 B + 9) (Nat.clog 2 M))) (((max (Nat.clog 2 B + 9) (Nat.clog 2 M)) - 1)) (L) (((((max (Nat.clog 2 B + 9) (Nat.clog 2 M)) + (max (Nat.clog 2 B + 9) (Nat.clog 2 M)) + (max (Nat.clog 2 B + 9) (Nat.clog 2 M))) / 2) + (((max (Nat.clog 2 B + 9) (Nat.clog 2 M)) + (max (Nat.clog 2 B + 9) (Nat.clog 2 M)) + (max (Nat.clog 2 B + 9) (Nat.clog 2 M))) / 2) - ((max (Nat.clog 2 B + 9) (Nat.clog 2 M)) + (max (Nat.clog 2 B + 9) (Nat.clog 2 M)) + (max (Nat.clog 2 B + 9) (Nat.clog 2 M)) - 1))) (r4)
    (h447 := by rw [o1 _ (by decide)]; exact h447)
    (h446 := by rw [o1 _ (by decide)]; exact h446)
    (h448 := by rw [o1 _ (by decide)]; exact h448)
    (h409 := by rw [o1 _ (by decide)]; exact h409)
    (h460 := by rw [o1 _ (by decide)]; exact h460)
    (h406 := by rw [o1 _ (by decide)]; exact h406)
    (z6 := by rw [o1 _ (by decide)]; exact z6)
    (z7 := by rw [o1 _ (by decide)]; exact z7)
    (z8 := by rw [o1 _ (by decide)]; exact z8)
    (z10 := by rw [o1 _ (by decide)]; exact z10)
    (z15 := by rw [o1 _ (by decide)]; exact z15)
    (z20 := by rw [o1 _ (by decide)]; exact z20)
    (z419 := by rw [o1 _ (by decide)]; exact z419)
    (hcr := by omega)
    (hc1 := hc1)
  obtain ⟨τ2, e2, st2, sh2, ce2, o2, v2_6, v2_7, v2_8, v2_10, v2_15, v2_20⟩ := X2
  have X3 := PopSetupNums.ptD2_spec cap τ2 (G) (off) (L) ((CanonicalFourfoldRowProgram.natCeilSqrt (4096 * B))) ((Nat.clog 2 B + 9)) (M)
    (h407 := by rw [o2 _ (by decide), o1 _ (by decide)]; exact h407)
    (h408 := by rw [o2 _ (by decide), o1 _ (by decide)]; exact h408)
    (h409 := by rw [o2 _ (by decide), o1 _ (by decide)]; exact h409)
    (h464 := by rw [o2 _ (by decide)]; exact v1_464)
    (h444 := by rw [o2 _ (by decide), o1 _ (by decide)]; exact h444)
    (h400 := by rw [o2 _ (by decide), o1 _ (by decide)]; exact h400)
    (z21 := by rw [o2 _ (by decide), o1 _ (by decide)]; exact z21)
    (z22 := by rw [o2 _ (by decide), o1 _ (by decide)]; exact z22)
    (z23 := by rw [o2 _ (by decide), o1 _ (by decide)]; exact z23)
    (z39 := by rw [o2 _ (by decide), o1 _ (by decide)]; exact z39)
    (z40 := by rw [o2 _ (by decide), o1 _ (by decide)]; exact z40)
    (z63 := by rw [o2 _ (by decide), o1 _ (by decide)]; exact z63)
    (z419 := by rw [o2 _ (by decide), o1 _ (by decide)]; exact z419)
    (hcr := by omega)
    (hc1 := hc1)
  obtain ⟨τ3, e3, st3, sh3, ce3, o3, v3_21, v3_22, v3_23, v3_39, v3_40, v3_63⟩ := X3
  have X4 := PopSetupNums.ptD3_spec cap τ3 (L) (sg) ((2 * (err / 4) + 1)) ((err / 4 + 1)) (s) ((off + L + (r4 + 4) * G))
    (h409 := by rw [o3 _ (by decide), o2 _ (by decide), o1 _ (by decide)]; exact h409)
    (h404 := by rw [o3 _ (by decide), o2 _ (by decide), o1 _ (by decide)]; exact h404)
    (h442 := by rw [o3 _ (by decide), o2 _ (by decide), o1 _ (by decide)]; exact h442)
    (h443 := by rw [o3 _ (by decide), o2 _ (by decide), o1 _ (by decide)]; exact h443)
    (h405 := by rw [o3 _ (by decide), o2 _ (by decide), o1 _ (by decide)]; exact h405)
    (h465 := by rw [o3 _ (by decide), o2 _ (by decide), o1 _ (by decide)]; exact h465)
    (z64 := by rw [o3 _ (by decide), o2 _ (by decide), o1 _ (by decide)]; exact z64)
    (z69 := by rw [o3 _ (by decide), o2 _ (by decide), o1 _ (by decide)]; exact z69)
    (z71 := by rw [o3 _ (by decide), o2 _ (by decide), o1 _ (by decide)]; exact z71)
    (z72 := by rw [o3 _ (by decide), o2 _ (by decide), o1 _ (by decide)]; exact z72)
    (z82 := by rw [o3 _ (by decide), o2 _ (by decide), o1 _ (by decide)]; exact z82)
    (z199 := by rw [o3 _ (by decide), o2 _ (by decide), o1 _ (by decide)]; exact z199)
    (z419 := by rw [o3 _ (by decide), o2 _ (by decide), o1 _ (by decide)]; exact z419)
    (hcr := by omega)
    (hc1 := hc1)
  obtain ⟨τ4, e4, st4, sh4, ce4, o4, v4_64, v4_69, v4_71, v4_72, v4_82, v4_199⟩ := X4
  have f6 : τ4.val 6 = pSb M B := by rw [o4 _ (by decide), o3 _ (by decide)]; exact v2_6
  have f7 : τ4.val 7 = pRk M B := by rw [o4 _ (by decide), o3 _ (by decide)]; exact v2_7
  have f8 : τ4.val 8 = pRk M B - 1 := by rw [o4 _ (by decide), o3 _ (by decide)]; exact v2_8
  have f10 : τ4.val 10 = L := by rw [o4 _ (by decide), o3 _ (by decide)]; exact v2_10
  have f15 : τ4.val 15 = pPad M B := by rw [o4 _ (by decide), o3 _ (by decide)]; exact v2_15
  have f20 : τ4.val 20 = r4 := by rw [o4 _ (by decide), o3 _ (by decide)]; exact v2_20
  have f21 : τ4.val 21 = G := by rw [o4 _ (by decide)]; exact v3_21
  have f22 : τ4.val 22 = off := by rw [o4 _ (by decide)]; exact v3_22
  have f23 : τ4.val 23 = L := by rw [o4 _ (by decide)]; exact v3_23
  have f39 : τ4.val 39 = pS B := by rw [o4 _ (by decide)]; exact v3_39
  have f40 : τ4.val 40 = pJ B := by rw [o4 _ (by decide)]; exact v3_40
  have f63 : τ4.val 63 = M := by rw [o4 _ (by decide)]; exact v3_63
  have f64 : τ4.val 64 = L := v4_64
  have f69 : τ4.val 69 = sg := v4_69
  have f71 : τ4.val 71 = pN err + 1 := v4_71
  have f72 : τ4.val 72 = err / 4 + 1 := v4_72
  have f82 : τ4.val 82 = s := v4_82
  have f199 : τ4.val 199 = pMl r4 G off L := v4_199
  have hX : 4096 * B + 2 ≤ cap + 2 := by omega
  have hX3 : (4096 * B + 2) * (4096 * B + 2) * (4096 * B + 2) ≤ (cap + 2) * (cap + 2) * (cap + 2) :=
    Nat.mul_le_mul (Nat.mul_le_mul hX hX) hX
  have hq := PopSetupNums.sqCost_le (4096 * B)
  refine ⟨τ4, WExec.mono (WExec.seq e1 (WExec.seq e2 (WExec.seq e3 e4))) (by omega), by rw [st4, st3, st2, st1],
    by rw [sh4, sh3, sh2, sh1], by rw [ce4, ce3, ce2, ce1], ?_, f6, f7, f8, f10, f15, f20, f21, f22, f23, f39, f40,
    f63, f64, f69, f71, f72, f82, f199⟩
  intro r hr
  rw [o4 r (fun h => hr (by simp [outB, h])), o3 r (fun h => hr (by simp [outB, h])),
    o2 r (fun h => hr (by simp [outB, h])), o1 r (fun h => hr (by simp [outB, h]))]

end NearCubicWires.WireExponent3_5.PrimAsm.PopSetupRun
