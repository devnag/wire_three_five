import Proof.Wire_3_5.UnionMachine.SampRun

/-! # C6 tail, item 2 (part 6): the register tapes of the expansion's word program

The expansion's word program `SampRun.mainW` keeps 16 registers of capacity `18ℓ + 20` (C5's Horner program counts the
seed records' position, `|seedWord| + 2ℓ + 2 ≤ cap`). Its register tapes are `regTape cap 0 = 0^{18ℓ+21}`, written
before it runs by a register-free word program from the ruler `1^ℓ`: per cell of the ruler `18` zeros on each of the
16 target streams, then `21` more (**`regs_spec`**).

Paper quantity: none (the capacity of the word program's registers). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

namespace NearCubicWires.WireExponent3_5.UnionMachine.SampRegs
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimT (Same Same.trans' emit_facts emitW)
open NearCubicWires.WireExponent3_5.UnionMachine.SampKit (rd_rep rd_rep_end)

variable (cap : ℕ)

/-- Append a fixed word to stream `o`. -/
def emitLW (o : Fin 17) : List Bool → WM 16 0
  | [] => .skip
  | b :: w => .seq (emitW o b) (emitLW o w)

theorem emitLW_spec (o : Fin 17) :
    ∀ (w : List Bool) (σ : WState 16 0), σ.sh o = (σ.st o).length →
      ∃ τ, WExec cap (emitLW o w) σ τ (4 * w.length) ∧ τ.st o = σ.st o ++ w ∧ τ.sh o = (τ.st o).length ∧
        (∀ j, j ≠ o → Same σ τ j) ∧ τ.val = σ.val ∧ τ.cell = σ.cell
  | [], σ, ho => ⟨σ, WExec.skip σ, by simp, ho, fun _ _ => ⟨rfl, rfl⟩, rfl, rfl⟩
  | b :: w, σ, ho => by
    obtain ⟨σ1, s1, e1, e1h, o1, v1, c1⟩ := emit_facts cap o b σ ho
    obtain ⟨τ, s2, e2, e2h, o2, v2, c2⟩ := emitLW_spec o w σ1 e1h
    refine ⟨τ, WExec.mono (WExec.seq s1 s2) (by simp; omega), by rw [e2, e1]; simp, e2h,
      fun j hj => (o1 j hj).trans' (o2 j hj), by rw [v2, v1], by rw [c2, c1]⟩

/-- Append a fixed word to each stream of a list. -/
def emitAllW (w : List Bool) : List (Fin 17) → WM 16 0
  | [] => .skip
  | t :: ts => .seq (emitLW t w) (emitAllW w ts)

theorem emitAll_spec (w : List Bool) :
    ∀ (ts : List (Fin 17)), ts.Nodup → ∀ σ : WState 16 0, (∀ t ∈ ts, σ.sh t = (σ.st t).length) →
      ∃ τ, WExec cap (emitAllW w ts) σ τ (ts.length * (4 * w.length + 1)) ∧
        (∀ t ∈ ts, τ.st t = σ.st t ++ w ∧ τ.sh t = (τ.st t).length) ∧ (∀ j, j ∉ ts → Same σ τ j) ∧
        τ.val = σ.val ∧ τ.cell = σ.cell
  | [], _, σ, _ => ⟨σ, WExec.mono (WExec.skip σ) (by simp), by simp, fun _ _ => ⟨rfl, rfl⟩, rfl, rfl⟩
  | t :: ts, hnd, σ, hO => by
    have htn : t ∉ ts := (List.nodup_cons.mp hnd).1
    have hnd' : ts.Nodup := (List.nodup_cons.mp hnd).2
    obtain ⟨σ1, s1, e1, e1h, o1, v1, c1⟩ := emitLW_spec cap t w σ (hO t (by simp))
    obtain ⟨τ, s2, f2, o2, v2, c2⟩ := emitAll_spec w ts hnd' σ1 (fun u hu => by
      have hut : u ≠ t := fun h => htn (h ▸ hu)
      rw [(o1 u hut).1, (o1 u hut).2]; exact hO u (by simp [hu]))
    refine ⟨τ, WExec.mono (WExec.seq s1 s2) (by simp only [List.length_cons]; rw [Nat.add_mul, Nat.one_mul]; omega),
      ?_, ?_, by rw [v2, v1], by rw [c2, c1]⟩
    · intro u hu
      rcases List.mem_cons.mp hu with rfl | hu'
      · rw [(o2 u htn).1, (o2 u htn).2, e1]; exact ⟨rfl, by rw [← e1]; exact e1h⟩
      · have hut : u ≠ t := fun h => htn (h ▸ hu')
        exact ⟨by rw [(f2 u hu').1, (o1 u hut).1], (f2 u hu').2⟩
    · intro j hj
      have hjt : j ≠ t := fun h => hj (h ▸ List.mem_cons_self)
      have hjs : j ∉ ts := fun h => hj (List.mem_cons_of_mem t h)
      exact (o1 j hjt).trans' (o2 j hjs)

/-- The 16 register tapes' streams. -/
def tgts : List (Fin 17) := (List.finRange 16).map Fin.succ

theorem tgts_nodup : tgts.Nodup := (List.nodup_finRange 16).map (Fin.succ_injective _)

theorem zero_notin : (0 : Fin 17) ∉ tgts := by decide

/-- The register tapes' writer: `18` zeros per cell of the ruler on stream `0`, then `21`. -/
def regW : WM 16 0 :=
  .seq (.whs 0 (.seq (emitAllW (List.replicate 18 false) tgts) (.fwd 0))) (emitAllW (List.replicate 21 false) tgts)

theorem regLoop_spec (ℓ : ℕ) : ∀ (m k : ℕ) (σ : WState 16 0), k + m = ℓ → σ.st 0 = List.replicate ℓ true →
    σ.sh 0 = k → (∀ t ∈ tgts, σ.st t = List.replicate (18 * k) false ∧ σ.sh t = 18 * k) →
    ∃ τ, WExec cap (.whs 0 (.seq (emitAllW (List.replicate 18 false) tgts) (.fwd 0))) σ τ (m * (16 * 73 + 4) + 1) ∧
      τ.st 0 = List.replicate ℓ true ∧ (∀ t ∈ tgts, τ.st t = List.replicate (18 * ℓ) false ∧ τ.sh t = 18 * ℓ) ∧
      τ.cell = σ.cell
  | 0, k, σ, hk, h0, hh0, hT => by
    have hz : wbit σ 0 = false := by unfold wbit; rw [h0, hh0, show k = ℓ by omega]; exact rd_rep_end ℓ
    refine ⟨σ, WExec.mono (WExec.whsF hz) (by omega), h0, fun t ht => ?_, rfl⟩
    rw [show ℓ = k by omega]; exact hT t ht
  | m + 1, k, σ, hk, h0, hh0, hT => by
    have hw : wbit σ 0 = true := by unfold wbit; rw [h0, hh0]; exact rd_rep ℓ k (by omega)
    obtain ⟨σ1, s1, f1, o1, -, c1⟩ := emitAll_spec cap (List.replicate 18 false) tgts tgts_nodup σ
      (fun t ht => by rw [(hT t ht).1, (hT t ht).2]; simp)
    have s2 := WExec.fwd (cap := cap) 0 σ1
    obtain ⟨τ, s3, e0, eT, ec⟩ := regLoop_spec ℓ m (k + 1) (σ1.seth 0 (σ1.sh 0 + 1)) (by omega)
      (by simp only [WState.seth_st]; rw [(o1 0 zero_notin).1]; exact h0)
      (by simp only [WState.seth_sh, Function.update_self]; rw [(o1 0 zero_notin).2, hh0])
      (fun t ht => by
        have ht0 : t ≠ 0 := fun h => zero_notin (h ▸ ht)
        simp only [WState.seth_st, WState.seth_sh, Function.update_of_ne ht0]
        rw [(f1 t ht).1, (hT t ht).1, List.replicate_append_replicate]
        refine ⟨by rw [show 18 * k + 18 = 18 * (k + 1) by ring], ?_⟩
        rw [(f1 t ht).2, (f1 t ht).1, (hT t ht).1]
        simp only [List.length_append, List.length_replicate]
        omega)
    refine ⟨τ, WExec.mono (WExec.whsT hw (WExec.seq s1 s2) s3) ?_, e0, eT, by rw [ec]; simp [c1]⟩
    simp only [tgts, List.length_map, List.length_finRange, List.length_replicate]
    rw [Nat.add_mul, Nat.one_mul]; omega

/-- **The register tapes**: from the ruler `1^ℓ` on stream `0` and blank targets, each target holds
`0^{18ℓ + 21}` (`= regTape (18ℓ + 20) 0`). -/
theorem regs_spec (ℓ : ℕ) (σ : WState 16 0) (h0 : σ.st 0 = List.replicate ℓ true) (hh : ∀ i, σ.sh i = 0)
    (hT : ∀ t ∈ tgts, σ.st t = []) :
    ∃ τ, WExec cap regW σ τ (ℓ * (16 * 73 + 4) + 1 + 1 + 16 * (4 * 21 + 1)) ∧ τ.st 0 = List.replicate ℓ true ∧
      (∀ t ∈ tgts, τ.st t = regTape (18 * ℓ + 20) 0) := by
  obtain ⟨τ1, s1, e0, eT, -⟩ := regLoop_spec cap ℓ ℓ 0 σ (by omega) h0 (hh 0)
    (fun t ht => by rw [hT t ht, hh t]; simp)
  obtain ⟨τ, s2, f2, o2, -, -⟩ := emitAll_spec cap (List.replicate 21 false) tgts tgts_nodup τ1
    (fun t ht => by rw [(eT t ht).1, (eT t ht).2]; simp)
  refine ⟨τ, WExec.mono (WExec.seq s1 s2) (by simp [tgts]), by rw [(o2 0 zero_notin).1]; exact e0, fun t ht => ?_⟩
  rw [(f2 t ht).1, (eT t ht).1, List.replicate_append_replicate, regTape_zero]

end NearCubicWires.WireExponent3_5.UnionMachine.SampRegs
