import Proof.Wire_3_5.Primitive.Writers.SBFieldC

/-! # SB, part 10: the field phase's word tail, run

* **`w3_spec`** (see `SBFieldC`): zero words, the trace mask, the erase bound, the erase of `Fs 2 … 22`, the clears. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace NearCubicWires.WireExponent3_5.PrimAsm.SBField
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary.SignedSortKey (binary)
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimAsm.WriteNat NearCubicWires.WireExponent3_5.PrimAsm.SBWords
open NearCubicWires.WireExponent3_5.PrimAsm.SBFieldA

section Tail
variable {ns nr : ℕ} (cap : ℕ) (Fs : Fin 23 ↪ Fin (ns + 1)) (Rb : Fin 16 ↪ Fin nr)

theorem w3_spec (ℓ : ℕ) (hℓ : 1 ≤ ℓ) (σ : WState ns nr) (hc : 4 * ℓ + 6 ≤ cap)
    (hmod : σ.st (Fs 1) = frame (binary ℓ (GF.firstPrimitive ℓ)))
    (hlen : ∀ k : Fin 23, 2 ≤ k.val → k.val ≤ 17 → (σ.st (Fs k)).length ≤ 4 * ℓ + 6)
    (hbl : ∀ k : Fin 23, (k.val = 0 ∨ 18 ≤ k.val) → σ.st (Fs k) = [])
    (hsh : ∀ k, σ.sh (Fs k) = 0) (hL : σ.val (Rb 0) = ℓ) (hz : ∀ j : Fin 16, j ≠ 0 → σ.val (Rb j) = 0) :
    ∃ τ : WState ns nr, WExec cap (w3 Fs Rb) σ τ (w3Cost cap ℓ ((eraseL Fs).map fun i => i.val)) ∧
      τ.st (Fs 0) = frame (binary ℓ (GF2.tau (GF.firstPrimitive ℓ) ℓ)) ∧ τ.st (Fs 1) = σ.st (Fs 1) ∧
      (∀ k : Fin 23, 2 ≤ k.val → τ.st (Fs k) = List.replicate (4 * ℓ + 6) false) ∧ (∀ k, τ.sh (Fs k) = 0) ∧
      (∀ j, τ.val (Rb j) = 0) ∧ (∀ i, (∀ k, Fs k ≠ i) → τ.st i = σ.st i ∧ τ.sh i = σ.sh i) ∧
      (∀ r, (∀ j, Rb j ≠ r) → τ.val r = σ.val r) ∧ τ.cell = σ.cell := by
  have R : ∀ {a b : Fin 16}, a ≠ b → Rb a ≠ Rb b := fun h => rbne Rb h
  -- 1: the six zero words
  obtain ⟨τa, ea, za, oa, sha, va, ca⟩ := zeros_spec cap (Rb 0) (Rb 1) (Rb 3) (Rb 2) (R (by decide)) (R (by decide))
    (R (by decide)) (R (by decide)) ℓ (by omega) (zeroL Fs) σ (zeroL_nodup Fs) hL (hz 1 (by decide)) (hz 3 (by decide))
    (hz 2 (by decide)) (fun O hO => by
      obtain ⟨k, hk, rfl⟩ := (mem_zeroL Fs O).1 hO
      exact ⟨hbl k hk, hsh k⟩)
  have za' : ∀ k : Fin 23, (k.val = 0 ∨ 18 ≤ k.val) → τa.st (Fs k) = frame (binary ℓ 0) :=
    fun k hk => (za (Fs k) ((mem_zeroL Fs _).2 ⟨k, hk, rfl⟩)).1
  have oa' : ∀ k : Fin 23, 1 ≤ k.val → k.val ≤ 17 → τa.st (Fs k) = σ.st (Fs k) := fun k h1 h2 =>
    oa (Fs k) (fun hm => by
      obtain ⟨k', hk', e⟩ := (mem_zeroL Fs _).1 hm
      have := Fs.injective e; subst this; omega)
  -- 2: the degree into the trace program's register `Rg 4 = Rb 11`
  have eb1 := SparseNum.copy1 cap (Rb 0) (rgOf Rb 4) (Rb 3) (R (by decide)) (R (by decide)) (R (by decide)) ℓ τa
    (by rw [va]; exact hL) (by rw [va]; exact hz 11 (by decide)) (by rw [va]; exact hz 3 (by decide)) (by omega)
  set τa' := τa.setv (rgOf Rb 4) ℓ with hτa'
  -- 3: the trace mask
  have sm : ∀ j : Fin 7, smOf Fs j = Fs (smIdx j) := fun _ => rfl
  obtain ⟨τb, eb2, tb1, tbh1, tb0, tbsh, tb4, tbz, tbF, tbW⟩ := SBTau.tauW_spec2 cap (smOf Fs) (rgOf Rb) ℓ
    (GF.firstPrimitive ℓ) (GF.firstPrimitive_cert ℓ hℓ) (by omega) τa'
    (by rw [sm]; simp [hτa', smIdx]; rw [oa' 1 (by decide) (by decide)]; exact hmod)
    (by rw [sm]; simp [hτa', smIdx, sha, hsh])
    (by rw [sm]; simp [hτa', smIdx]; exact za' 0 (by decide)) (by rw [sm]; simp [hτa', smIdx, sha, hsh])
    (by rw [sm]; simp [hτa', smIdx]; exact za' 18 (by decide)) (by rw [sm]; simp [hτa', smIdx, sha, hsh])
    0 0 0 0
    (by rw [sm]; simp [hτa', smIdx]; exact za' 19 (by decide)) (by rw [sm]; simp [hτa', smIdx, sha, hsh])
    (by rw [sm]; simp [hτa', smIdx]; exact za' 20 (by decide)) (by rw [sm]; simp [hτa', smIdx, sha, hsh])
    (by rw [sm]; simp [hτa', smIdx]; exact za' 21 (by decide)) (by rw [sm]; simp [hτa', smIdx, sha, hsh])
    (by rw [sm]; simp [hτa', smIdx]; exact za' 22 (by decide)) (by rw [sm]; simp [hτa', smIdx, sha, hsh])
    (fun j hj => by
      simp only [hτa', WState.setv_val]
      rw [Function.update_of_ne (fun e => hj ((rgOf Rb).injective e)), va, rgOf_eq]
      exact hz _ (by intro e; have := congrArg Fin.val e; simp at this))
    (by simp [hτa'])
  have tbS : ∀ i, (∀ j : Fin 7, smOf Fs j ≠ i) → τb.st i = τa'.st i ∧ τb.sh i = τa'.sh i :=
    fun i hi => tbF.1 i (fun ⟨j, e⟩ => hi j e)
  have tbR : ∀ r, (∀ j : Fin 9, rgOf Rb j ≠ r) → τb.val r = τa'.val r := fun r hr => tbF.2.1 r (fun ⟨j, e⟩ => hr j e)
  have smne : ∀ k : Fin 23, 2 ≤ k.val → k.val ≤ 17 → ∀ j : Fin 7, smOf Fs j ≠ Fs k := by
    intro k h1 h2 j e
    have := Fs.injective e
    have hv := congrArg Fin.val this
    fin_cases j <;> simp [smIdx] at hv <;> omega
  have rgne : ∀ j : Fin 16, j.val < 7 → ∀ i : Fin 9, rgOf Rb i ≠ Rb j := by
    intro j hj i e
    have := congrArg Fin.val (Rb.injective e)
    simp at this; omega
  have vb : ∀ j : Fin 16, j.val < 7 → τb.val (Rb j) = σ.val (Rb j) := by
    intro j hj
    rw [tbR _ (rgne j hj), hτa', WState.setv_val, Function.update_of_ne (Ne.symm (rgne j hj 4)), va]
  -- 4: the erase bound `4ℓ + 6` in `Rb 4`
  have ec := bound_spec cap (Rb 0) (Rb 1) (Rb 3) (Rb 4) (R (by decide)) (R (by decide)) (R (by decide))
    (R (by decide)) (R (by decide)) (R (by decide)) ℓ τb (by rw [vb 0 (by decide)]; exact hL)
    (by rw [vb 1 (by decide)]; exact hz 1 (by decide)) (by rw [vb 3 (by decide)]; exact hz 3 (by decide))
    (by rw [vb 4 (by decide)]; exact hz 4 (by decide)) hc
  set τc := τb.setv (Rb 4) (4 * ℓ + 6) with hτc
  have hlist : ∀ i ∈ eraseL Fs, τc.sh i = 0 ∧ (τc.st i).length ≤ 4 * ℓ + 6 := by
    intro i hi
    obtain ⟨k, hk, rfl⟩ := (mem_eraseL Fs i).1 hi
    by_cases h17 : k.val ≤ 17
    · obtain ⟨a, b⟩ := tbS (Fs k) (smne k hk h17)
      refine ⟨by simp [hτc, b, hτa', sha, hsh], ?_⟩
      simp only [hτc, WState.setv_st, a, hτa']
      rw [oa' k (by omega) h17]
      exact hlen k hk h17
    · have hk23 := k.isLt
      obtain ⟨m, hm⟩ : ∃ m, k.val = 18 + m := ⟨k.val - 18, by omega⟩
      have hm5 : m < 5 := by omega
      have hj : smOf Fs ⟨m + 2, by omega⟩ = Fs k := by
        rw [sm]; congr 1; apply Fin.ext
        interval_cases m <;> simp [smIdx, hm]
      refine ⟨by rw [← hj]; simp [hτc, tbsh], ?_⟩
      obtain ⟨x, hx⟩ := tbW ⟨m + 2, by omega⟩ (by simp)
      simp only [hτc, WState.setv_st]
      rw [← hj, hx]
      simp [RepairOrdinary.frame]
      omega
  -- 5: the erase
  obtain ⟨τd, ed, din, dout, dv, dcl⟩ := eraseList_spec cap (Rb 4) (Rb 5) (Rb 6) (Rb 3) (R (by decide))
    (R (by decide)) (R (by decide)) (R (by decide)) (R (by decide)) (R (by decide)) (4 * ℓ + 6) hc (eraseL Fs) τc
    (by simp [hτc])
    (by simp [hτc, Function.update_of_ne (R (by decide) : Rb 5 ≠ Rb 4)]; rw [vb 5 (by decide)]; exact hz 5 (by decide))
    (by simp [hτc, Function.update_of_ne (R (by decide) : Rb 6 ≠ Rb 4)]; rw [vb 6 (by decide)]; exact hz 6 (by decide))
    (by simp [hτc, Function.update_of_ne (R (by decide) : Rb 3 ≠ Rb 4)]; rw [vb 3 (by decide)]; exact hz 3 (by decide))
    hlist
  -- 6: the clears
  have e1 := wclear_spec cap (Rb 4) (4 * ℓ + 6) τd (by rw [dv]; simp [hτc]) (by rw [dv]; simp [hτc]; omega)
  have e2 := wclear_spec cap (Rb 0) ℓ (τd.setv (Rb 4) 0)
    (by simp [Function.update_of_ne (R (by decide) : Rb 0 ≠ Rb 4), dv, hτc]; rw [vb 0 (by decide)]; exact hL)
    (by simp [Function.update_of_ne (R (by decide) : Rb 0 ≠ Rb 4), dv, hτc]; rw [vb 0 (by decide)]; omega)
  have e3 := wclear_spec cap (rgOf Rb 4) ℓ ((τd.setv (Rb 4) 0).setv (Rb 0) 0)
    (by simp only [WState.setv_val]; rw [rg4, Function.update_of_ne (R (by decide) : Rb 11 ≠ Rb 0),
          Function.update_of_ne (R (by decide) : Rb 11 ≠ Rb 4), dv, hτc, WState.setv_val,
          Function.update_of_ne (R (by decide) : Rb 11 ≠ Rb 4), ← rg4]; exact tb4)
    (by simp only [WState.setv_val]; rw [rg4, Function.update_of_ne (R (by decide) : Rb 11 ≠ Rb 0),
          Function.update_of_ne (R (by decide) : Rb 11 ≠ Rb 4), dv, hτc, WState.setv_val,
          Function.update_of_ne (R (by decide) : Rb 11 ≠ Rb 4), ← rg4, tb4]; omega)
  set τ := ((τd.setv (Rb 4) 0).setv (Rb 0) 0).setv (rgOf Rb 4) 0 with hτ
  have ht : WExec cap (w3 Fs Rb) σ τ (w3Cost cap ℓ ((eraseL Fs).map fun i => i.val)) := by
    have := WExec.seq ea (WExec.seq (WExec.seq eb1 eb2) (WExec.seq ec (WExec.seq ed (WExec.seq e1 (WExec.seq e2 e3)))))
    exact WExec.mono this (by simp [w3Cost, zeroL, zerosCost])
  have smi0 : smOf Fs 1 = Fs 0 := rfl
  have smi1 : smOf Fs 0 = Fs 1 := rfl
  have nE : ∀ k : Fin 23, k.val < 2 → Fs k ∉ eraseL Fs := by
    intro k hk hm
    obtain ⟨k', hk', e⟩ := (mem_eraseL Fs _).1 hm
    have := Fs.injective e; subst this; omega
  have st01 : ∀ k : Fin 23, k.val < 2 → τd.st (Fs k) = τb.st (Fs k) ∧ τd.sh (Fs k) = τb.sh (Fs k) := by
    intro k hk
    obtain ⟨a, b⟩ := dout (Fs k) (nE k hk)
    exact ⟨by rw [a]; simp [hτc], by rw [b]; simp [hτc]⟩
  refine ⟨τ, ht, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [hτ, WState.setv_st]
    rw [(st01 0 (by decide)).1, ← smi0, tb1]
  · simp only [hτ, WState.setv_st]
    rw [(st01 1 (by decide)).1, ← smi1, tb0, smi1, hτa', WState.setv_st, oa' 1 (by decide) (by decide)]
  · intro k hk
    simp only [hτ, WState.setv_st]
    exact (din (Fs k) ((mem_eraseL Fs _).2 ⟨k, hk, rfl⟩)).1
  · intro k
    simp only [hτ, WState.setv_sh]
    by_cases hk : 2 ≤ k.val
    · exact (din (Fs k) ((mem_eraseL Fs _).2 ⟨k, hk, rfl⟩)).2
    · rw [(st01 k (by omega)).2]
      have hk2 : k.val = 0 ∨ k.val = 1 := by omega
      rcases hk2 with h0 | h1
      · rw [show k = 0 from Fin.ext h0, ← smi0]; exact tbsh 1
      · rw [show k = 1 from Fin.ext h1, ← smi1]; exact tbsh 0
  · intro j
    simp only [hτ, WState.setv_val]
    by_cases h11 : j = 11
    · subst h11; rw [rg4]; simp
    · rw [Function.update_of_ne (fun e => h11 (Rb.injective (by rw [e, rg4])))]
      by_cases h0 : j = 0
      · subst h0; simp
      · rw [Function.update_of_ne (fun e => h0 (Rb.injective e))]
        by_cases h4 : j = 4
        · subst h4; simp
        · rw [Function.update_of_ne (fun e => h4 (Rb.injective e)), dv, hτc, WState.setv_val,
            Function.update_of_ne (fun e => h4 (Rb.injective e))]
          by_cases hj7 : j.val < 7
          · rw [vb j hj7]; exact hz j h0
          · have hr : Rb j = rgOf Rb ⟨j.val - 7, by omega⟩ := by
              rw [rgOf_eq]; congr 1; apply Fin.ext; simp; omega
            rw [hr]
            exact tbz _ (by intro e; apply h11; apply Fin.ext; have := congrArg Fin.val e; simp at this; omega)
  · intro i hi
    have hiE : i ∉ eraseL Fs := fun hm => by
      obtain ⟨k, _, e⟩ := (mem_eraseL Fs _).1 hm; exact hi k e
    have hiS : ∀ j : Fin 7, smOf Fs j ≠ i := fun j e => hi _ e
    have hiZ : i ∉ zeroL Fs := fun hm => by
      obtain ⟨k, _, e⟩ := (mem_zeroL Fs _).1 hm; exact hi k e
    obtain ⟨a, b⟩ := dout i hiE
    obtain ⟨c, d⟩ := tbS i hiS
    simp only [hτ, WState.setv_st, WState.setv_sh]
    refine ⟨by rw [a]; simp [hτc]; rw [c]; simp [hτa']; exact oa i hiZ, by rw [b]; simp [hτc]; rw [d]; simp [hτa', sha]⟩
  · intro r hr
    have hrR : ∀ j : Fin 9, rgOf Rb j ≠ r := fun j e => hr _ e
    simp only [hτ, WState.setv_val]
    rw [Function.update_of_ne (fun e => hrR 4 e.symm), Function.update_of_ne (fun e => hr 0 e.symm),
      Function.update_of_ne (fun e => hr 4 e.symm), dv, hτc, WState.setv_val, Function.update_of_ne (fun e => hr 4 e.symm),
      tbR r hrR, hτa', WState.setv_val, Function.update_of_ne (fun e => hrR 4 e.symm), va]
  · simp only [hτ, WState.setv_cell]
    rw [dcl]; simp [hτc]; rw [tbF.2.2]; simp [hτa', ca]

end Tail

end NearCubicWires.WireExponent3_5.PrimAsm.SBField
