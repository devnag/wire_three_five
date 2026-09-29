import Proof.Wire_3_5.FinalPass.SdNum

/-! # S4 (the seeds phase), part 23: reading a unary list into registers (P3:3170-3178)

S4's small numbers arrive as the raw unary list `unaryList [v₀, v₁, …]` (front word `7`); **`readList i c rs`** reads
it into the registers `rs` in order (C5's `WM.readU` per field, the head moves counted in `c`). **`readList_spec`**:
register `rs[k]` holds `vs[k]`, the head moved past the list, every other register, stream and head kept.

Paper quantity of the main type: S4's small numbers (`s4Small2`: the star parameters' `b, s, r/2`, the geometry, the
mask lengths, the seed width, the filter's `len, cap, errExp`) in registers. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace NearCubicWires.WireExponent3_5.FinalPass.Sd
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimAsm

section RL
variable {ns nr : ℕ} (cap : ℕ) (i : Fin (ns + 1)) (c : Fin nr)

/-- Read the unary list's fields into `rs`, in order. -/
def readList : List (Fin nr) → WM ns nr
  | [] => .skip
  | r :: rs => .seq (WM.readU i c r) (readList rs)

theorem readTapeBit_unary (v : ℕ) (rest : List Bool) (k : ℕ) (hk : k ≤ v) :
    readTapeBit (List.replicate v true ++ false :: rest) k = decide (k < v) := by
  unfold readTapeBit
  by_cases h : k < v
  · rw [List.getD_append _ _ _ _ (by simp; omega)]
    simp [h]
  · have : k = v := by omega
    subst this
    rw [List.getD_append_right _ _ _ _ (by simp)]
    simp

theorem readList_spec : ∀ (rs : List (Fin nr)) (vs : List ℕ) (σ : WState ns nr) (pre post : List Bool),
    rs.length = vs.length → (∀ r ∈ rs, r ≠ c) → rs.Nodup → (∀ r ∈ rs, σ.val r = 0) →
    σ.st i = pre ++ Data.unaryList vs ++ post → σ.sh i = pre.length →
    σ.val c + (Data.unaryList vs).length ≤ cap → (∀ v ∈ vs, v ≤ cap) →
    ∃ σ' : WState ns nr, WExec cap (readList i c rs) σ σ' (11 * (Data.unaryList vs).length) ∧ σ'.st = σ.st ∧
      σ'.sh = Function.update σ.sh i (σ.sh i + (Data.unaryList vs).length) ∧
      σ'.val c = σ.val c + (Data.unaryList vs).length ∧
      (∀ k : Fin rs.length, σ'.val (rs.get k) = vs.getD k 0) ∧ (∀ q, q ≠ c → q ∉ rs → σ'.val q = σ.val q) ∧
      σ'.cell = σ.cell
  | [], vs, σ, pre, post, hl, _, _, _, _, _, _, _ => by
    have hv : vs = [] := List.eq_nil_of_length_eq_zero (by simpa using hl.symm)
    subst hv
    refine ⟨σ, WExec.mono (WExec.skip σ) (by simp), rfl, by simp [Data.unaryList], by simp [Data.unaryList],
      fun k => k.elim0,
      fun _ _ _ => rfl, rfl⟩
  | r :: rs, [], _, _, _, hl, _, _, _, _, _, _, _ => by simp at hl
  | r :: rs, v :: vs, σ, pre, post, hl, hc, hnd, hz, hst, hsh, hcap, hvc => by
    have hcr : c ≠ r := (hc r (List.mem_cons_self)).symm
    have hul : Data.unaryList (v :: vs) = List.replicate v true ++ false :: Data.unaryList vs := by
      simp [Data.unaryList]
    have hst' : σ.st i = pre ++ (List.replicate v true ++ false :: (Data.unaryList vs ++ post)) := by
      rw [hst, hul]; simp
    have hlen : (Data.unaryList (v :: vs)).length = v + 1 + (Data.unaryList vs).length := by
      rw [hul]; simp; omega
    have e1 := wreadU_spec cap i c r hcr v σ
      (fun k hk => by rw [hst', hsh, ParseNat.read_pre, readTapeBit_unary v _ k (by omega)]; simp [hk])
      (by rw [hst', hsh, ParseNat.read_pre, readTapeBit_unary v _ v le_rfl]; simp)
      (by omega) (by rw [hz r (List.mem_cons_self)]; have := hvc v (List.mem_cons_self); omega)
    obtain ⟨σ1, h1⟩ : ∃ y : WState ns nr, y = ((σ.seth i (σ.sh i + v + 1)).setv c (σ.val c + v + 1)).setv r
        (σ.val r + v) := ⟨_, rfl⟩
    rw [← h1] at e1
    have hnd' : r ∉ rs ∧ rs.Nodup := List.nodup_cons.mp hnd
    obtain ⟨σ', e2, s2, h2, c2, v2, o2, l2⟩ := readList_spec rs vs σ1 (pre ++ List.replicate v true ++ [false]) post
      (by simpa using hl) (fun r' hr' => hc r' (List.mem_cons_of_mem _ hr'))
      hnd'.2 (fun r' hr' => by
        have hne : r' ≠ r := fun e => hnd'.1 (e ▸ hr')
        rw [h1]
        simp [Function.update_of_ne hne, Function.update_of_ne (hc r' (List.mem_cons_of_mem _ hr')),
          hz r' (List.mem_cons_of_mem _ hr')])
      (by rw [h1]; simp [hst']) (by rw [h1]; simp [hsh]; omega)
      (by rw [h1]; simp [Function.update_of_ne hcr]; omega) (fun v' hv' => hvc v' (List.mem_cons_of_mem _ hv'))
    refine ⟨σ', WExec.mono (WExec.seq e1 e2) (by rw [hlen]; omega), by rw [s2, h1]; rfl, ?_, ?_, ?_, ?_, ?_⟩
    · rw [h2]
      funext j
      by_cases hj : j = i
      · subst hj
        rw [h1]
        simp [hlen]
        omega
      · rw [Function.update_of_ne hj, Function.update_of_ne hj, h1]
        simp [Function.update_of_ne hj]
    · rw [c2, h1, hlen]
      simp [Function.update_of_ne hcr]
      omega
    · intro k
      rcases k with ⟨k, hk⟩
      cases k with
      | zero =>
        show σ'.val r = v
        rw [o2 r (hc r (List.mem_cons_self)) hnd'.1, h1]
        simp [hz r (List.mem_cons_self)]
      | succ k =>
        show σ'.val (rs.get ⟨k, by simpa using hk⟩) = vs.getD k 0
        exact v2 ⟨k, by simpa using hk⟩
    · intro q hqc hq
      have hqr : q ≠ r := fun e => hq (e ▸ List.mem_cons_self)
      have hqrs : q ∉ rs := fun h => hq (List.mem_cons_of_mem _ h)
      rw [o2 q hqc hqrs, h1]
      simp [Function.update_of_ne hqr, Function.update_of_ne hqc]
    · rw [l2, h1]; rfl

end RL

end NearCubicWires.WireExponent3_5.FinalPass.Sd
