import Proof.Wire_3_5.FinalPass.FreeGen7

/-! # The free numbers, v2, part 3: the program `freeProg2`

`freeW2 κ = freeW (κ.base); fixW κ` leaves the v2 free numbers `freeVal2 κ x` (`Q' = dQ(2kh+β)`, `h = dH(n+1)^{eH}`,
`pr = dP(n+1)^{eP}`; P3:1886-1906, P3:1596-1615) in `FB`, every register off `130 … 136`, `177 … 199`, every stream,
head and the cell as they were: C4.K's `FreeProg.run` at `freeW2 κ`.
* `freeOut_base`, **`freeW2_run`**, **`freeProg2`**.
Paper quantity of the main type: the free numbers `TWd, Cap, Q', h, m, pr, ρ` of a call. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 4000000

namespace NearCubicWires.WireExponent3_5.FinalPass.FreeGen
open NearCubicWires NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimAsm NearCubicWires.WireExponent3_5.PrimAsm.SparseNum
open NearCubicWires.WireExponent3_5.PrimT.C4Set NearCubicWires.WireExponent3_5.PrimAsm.SymLayout

/-- **The v2 program**: FreeGen's at `dQ = dH = dP = 0`, then the second pass. -/
def freeW2 (κ : FreeK2) : WM (LNS 0) LNR := .seq (freeW κ.base) (fixW κ)

theorem freeOut_base (κ : FreeK2) (x : FreeIn) (σ : WState (LNS 0) LNR) :
    (freeOut κ.base x σ).val (Gall 2) = 0 ∧ (freeOut κ.base x σ).val (Gall 3) = 0 ∧
      (freeOut κ.base x σ).val (Gall 5) = 0 := by
  refine ⟨?_, ?_, ?_⟩ <;> simp [freeOut, FreeK2.base, Function.update_apply]

theorem FB_Gall (j : Fin 7) : FB j = Gall ⟨j.val, by omega⟩ := by
  fin_cases j <;> rfl

/-- **The v2 program's run** (C4.K's `FreeProg.run` shape). -/
theorem freeW2_run (κ : FreeK2) (cap : ℕ) (σ : WState (LNS 0) LNR) (x : FreeIn) (hR : FreeRegs σ x)
    (hF : ∀ q : Fin LNR, 130 ≤ q.val → q.val < 137 → σ.val q = 0)
    (hS : ∀ q : Fin LNR, 177 ≤ q.val → q.val < 200 → σ.val q = 0) (hc : need κ.base x + need2 κ x ≤ cap) :
    ∃ τ, WExec cap (freeW2 κ) σ τ ((201 + fixN κ) * UnaryPow.sq cap) ∧ (∀ j, τ.val (FB j) = freeVal2 κ x j) ∧
      (∀ q : Fin LNR, (q.val < 130 ∨ (137 ≤ q.val ∧ q.val < 177) ∨ 200 ≤ q.val) → τ.val q = σ.val q) ∧
      τ.st = σ.st ∧ τ.sh = σ.sh ∧ τ.cell = σ.cell := by
  have hsq := UnaryPow.sq_ge cap
  have hz0 : ∀ k : Fin 35, k.val < 30 → σ.val (Gall k) = 0 := by
    intro k hk
    rcases Gall_range k hk with h | h
    · exact hF _ h.1 h.2
    · exact hS _ h.1 h.2
  have e1 := freeW_exec κ.base cap σ x hR hF hS (by omega)
  have hb := freeOut_base κ x σ
  have hkh : (freeOut κ.base x σ).val (Gall 31) = x.kh := by
    rw [freeOut_val κ.base x σ 31 (by decide)]; exact hR.2.1
  have hn : (freeOut κ.base x σ).val (Gall 30) = x.n := by
    rw [freeOut_val κ.base x σ 30 (by decide)]; exact hR.1
  have hm : (freeOut κ.base x σ).val (Gall 4) = mOf κ.base x := by
    have h := freeOut_fb κ.base x σ 4
    rw [FB_Gall] at h
    exact h
  have hz : ∀ k : Fin 35, k ∈ ({7, 9, 10, 11, 26, 27, 28, 2, 3, 5} : Finset (Fin 35)) →
      (freeOut κ.base x σ).val (Gall k) = 0 := by
    intro k hk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hk
    rcases hk with h | h | h | h | h | h | h | h | h | h <;> subst h
    all_goals first
      | exact hb.1
      | exact hb.2.1
      | exact hb.2.2
      | (rw [freeOut_val κ.base x σ _ (by decide)]; exact hz0 _ (by decide))
  have hz' : ∀ k : Fin 35, k ∈ ({12, 13, 14, 15, 16, 29} : Finset (Fin 35)) →
      (freeOut κ.base x σ).val (Gall k) = 0 := by
    intro k hk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hk
    rcases hk with h | h | h | h | h | h <;> subst h <;>
      (rw [freeOut_val κ.base x σ _ (by decide)]; exact hz0 _ (by decide))
  have h20 : (freeOut κ.base x σ).val (Gall 20) = κ.k.dC * (β x * β x) := by
    simp [freeOut, FreeK2.base, Function.update_apply]
  have h1 : (freeOut κ.base x σ).val (Gall 1) = 2 ^ (κ.k.dC * (β x * β x)) := by
    simp [freeOut, FreeK2.base, Function.update_apply]
  have e2 := fixW_exec κ cap x (freeOut κ.base x σ) hkh (freeOut_beta κ.base x σ) hn hm h20 h1 hz hz' (by omega)
  have hne : ∀ {i j : Fin 35}, i ≠ j → Gall i ≠ Gall j := fun h => Gall.injective.ne h
  refine ⟨fixOut κ x (freeOut κ.base x σ), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · refine WExec.mono (WExec.seq e1 e2) ?_
    rw [Nat.add_mul]
    have : 1 ≤ 1 * UnaryPow.sq cap := by omega
    omega
  · intro j
    have hfb := freeOut_fb κ.base x σ j
    rw [FB_Gall] at hfb ⊢
    have h16 : x.n / 2 / 2 / 2 / 2 = x.n / 16 := by omega
    fin_cases j
    · simp [fixOut, fixCOut, fixAMOut, fixAOut, freeOut, Function.update_apply, freeVal2, FreeK2.base]
    · simp [fixOut, fixCOut, fixAMOut, fixAOut, Function.update_apply, freeVal2, h16]
    · simp [fixOut, fixCOut, fixAMOut, fixAOut, Function.update_apply, freeVal2]
    · simp [fixOut, fixCOut, fixAMOut, fixAOut, Function.update_apply, freeVal2]
    · simp [fixOut, fixCOut, fixAMOut, fixAOut, Function.update_apply, freeVal2, mOf, FreeK2.base]
    · simp [fixOut, fixCOut, fixAMOut, fixAOut, Function.update_apply, freeVal2]
    · simp [fixOut, fixCOut, fixAMOut, fixAOut, freeOut, Function.update_apply, freeVal2, FreeK2.base, Nat.sub_sub]
  · intro q hq
    have hne' : ∀ k : Fin 35, k.val < 30 → q ≠ Gall k := by
      intro k hk h
      have := Gall_range k hk
      rw [← h] at this
      omega
    have hkept : (freeOut κ.base x σ).val q = σ.val q := by
      simp [freeOut, hne' _ (by decide : (8 : Fin 35).val < 30), hne' _ (by decide : (17 : Fin 35).val < 30),
        hne' _ (by decide : (18 : Fin 35).val < 30), hne' _ (by decide : (19 : Fin 35).val < 30),
        hne' _ (by decide : (0 : Fin 35).val < 30), hne' _ (by decide : (2 : Fin 35).val < 30),
        hne' _ (by decide : (3 : Fin 35).val < 30), hne' _ (by decide : (5 : Fin 35).val < 30),
        hne' _ (by decide : (20 : Fin 35).val < 30), hne' _ (by decide : (1 : Fin 35).val < 30),
        hne' _ (by decide : (21 : Fin 35).val < 30), hne' _ (by decide : (22 : Fin 35).val < 30),
        hne' _ (by decide : (23 : Fin 35).val < 30), hne' _ (by decide : (24 : Fin 35).val < 30),
        hne' _ (by decide : (25 : Fin 35).val < 30), hne' _ (by decide : (4 : Fin 35).val < 30),
        hne' _ (by decide : (6 : Fin 35).val < 30)]
    rw [← hkept]
    simp [fixOut, fixCOut, fixAMOut, fixAOut, hne' _ (by decide : (7 : Fin 35).val < 30),
      hne' _ (by decide : (2 : Fin 35).val < 30), hne' _ (by decide : (14 : Fin 35).val < 30),
      hne' _ (by decide : (16 : Fin 35).val < 30), hne' _ (by decide : (27 : Fin 35).val < 30),
      hne' _ (by decide : (28 : Fin 35).val < 30), hne' _ (by decide : (29 : Fin 35).val < 30),
      hne' _ (by decide : (1 : Fin 35).val < 30),
      hne' _ (by decide : (10 : Fin 35).val < 30), hne' _ (by decide : (9 : Fin 35).val < 30),
      hne' _ (by decide : (3 : Fin 35).val < 30), hne' _ (by decide : (11 : Fin 35).val < 30),
      hne' _ (by decide : (5 : Fin 35).val < 30), hne' _ (by decide : (12 : Fin 35).val < 30),
      hne' _ (by decide : (4 : Fin 35).val < 30), hne' _ (by decide : (13 : Fin 35).val < 30)]
  · simp [fixOut, fixCOut, fixAMOut, fixAOut, freeOut]
  · simp [fixOut, fixCOut, fixAMOut, fixAOut, freeOut]
  · simp [fixOut, fixCOut, fixAMOut, fixAOut, freeOut]

/-- **The v2 free numbers' program** (C4.K's `FreeProg`). -/
noncomputable def freeProg2 (κ : FreeK2) : FreeProg where
  prog := freeW2 κ
  val := freeVal2 κ
  cost := fun cap _ => (201 + fixN κ) * UnaryPow.sq cap
  ok := fun cap x => need κ.base x + need2 κ x ≤ cap
  run := fun cap σ x hR hF hS hok => freeW2_run κ cap σ x hR hF hS hok

end NearCubicWires.WireExponent3_5.FinalPass.FreeGen

