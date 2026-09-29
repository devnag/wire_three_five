import Proof.Wire_3_5.FinalPass.S5TSeed2

/-! # S5-THR, part 12: the hash bits' frame on a stream (P3:2150-2157)

**`seedSrc_spec`**: from the input `frame fpIn` (`fpIn = pre ++ frame w`, `|w| = 2·t·ℓ`), the prelude's template
`sent (|fpIn|+1)` and the unary ports `1^t`, `1^ℓ` (W6's `tt`, `ell0`), the program `seedSrc` leaves `frame w` on a
blank stream `SRC`, every head back at `0`, `t` and `ℓ` in registers `1`, `2`, its other registers at `0`, everything
else unchanged. Three phases: `seedA` (the length `m = |fpIn|` by `lenM`, `t`, `ℓ` by `countU`, `2tℓ` by `mulAddW`
and `c = 2·(2tℓ) + 1` by `addTo`), `seedB` (the first `m − c` bits skipped by `walkP`, the last `c` copied raw by
`copyRaw`), `seedC` (the heads returned by `rewIn` and `WM.rewind`, the scratch registers cleared).

Paper quantity of the main type: the fixed hash's bits `frame (ofFn s)` (`filt:soft`, P3:2150-2157). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false

namespace NearCubicWires.WireExponent3_5.FinalPass.S5T
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.FinalPass.HashSeed

variable {ns nr : ℕ} (cap : ℕ)

/-- `K -= B` (truncated), `B := 0`. -/
def subLs (B K : Fin nr) : WM ns nr := .whr B (.seq (.dec B) (.dec K))

theorem subLs_spec (B K : Fin nr) (hBK : B ≠ K) :
    ∀ (n : ℕ) (σ : WState ns nr), σ.val B = n → n ≤ cap → σ.val K ≤ cap →
      WExec cap (subLs B K) σ ((σ.setv B 0).setv K (σ.val K - n)) (5 * n + 1)
  | 0, σ, h0, _, _ => by
    have e : (σ.setv B 0).setv K (σ.val K - 0) = σ := by
      refine WState.eq rfl rfl ?_ rfl
      funext j
      by_cases hjK : j = K
      · subst hjK; simp
      · by_cases hjB : j = B
        · subst hjB; simp [Function.update_apply, hjK]; omega
        · simp [Function.update_apply, hjK, hjB]
    rw [e]
    exact WExec.whrF h0
  | n + 1, σ, hn, hB, hK => by
    have h1 : WExec cap (.dec B) σ (σ.setv B n) 1 :=
      WExec.cast cap (WExec.dec (cap := cap) B σ (by omega)) (by rw [hn, Nat.add_sub_cancel]) le_rfl
    have h2 := WExec.dec (cap := cap) K (σ.setv B n) (by rw [wsetv_val_ne _ _ (Ne.symm hBK)]; exact hK)
    have ih := subLs_spec B K hBK n ((σ.setv B n).setv K ((σ.setv B n).val K - 1))
      (by rw [wsetv_val_ne _ _ hBK, wsetv_val_self]) (by omega)
      (by rw [wsetv_val_self, wsetv_val_ne _ _ (Ne.symm hBK)]; omega)
    refine WExec.cast cap (WExec.whrT (by omega) (WExec.seq h1 h2) ih) ?_ (by omega)
    refine WState.eq rfl rfl ?_ rfl
    funext j
    by_cases hjK : j = K
    · subst hjK; simp [Function.update_apply, Ne.symm hBK]; omega
    · by_cases hjB : j = B
      · subst hjB; simp [Function.update_apply, hjK]
      · simp [Function.update_apply, hjK, hjB]

/-- The product registers inside the seed registers: `(a, b, c, t, w) = (1, 2, 3, 6, 7)`. -/
def mE : Fin 5 ↪ Fin 10 := ⟨![1, 2, 3, 6, 7], by decide⟩

/-- The seed registers after phase A: `E 0 = m`, `E 1 = t`, `E 2 = ℓ`, `E 3 = 2tℓ`, `E 4 = 2·(2tℓ) + 1`. -/
def seedV (m t ℓ : ℕ) (j : Fin 10) : ℕ :=
  if j = 0 then m else if j = 1 then t else if j = 2 then ℓ else if j = 3 then 2 * t * ℓ
  else if j = 4 then 2 * (2 * t * ℓ) + 1 else 0

/-- Phase A: the length, the two counts, the product and the frame length `c`. -/
def seedA (T P13 P15 : Fin (ns + 1)) (E : Fin 10 ↪ Fin nr) : WM ns nr :=
  .seq (lenM T (E 0)) (.seq (countU P13 (E 1) (E 6)) (.seq (countU P15 (E 2) (E 6))
  (.seq (PrimAsm.UnaryArith.mulAddW (mE.trans E)) (.seq (PrimAsm.UnaryArith.mulAddW (mE.trans E))
  (.seq (PrimAsm.ParseNat.addTo (E 3) (E 4) (E 6)) (.seq (PrimAsm.ParseNat.addTo (E 3) (E 4) (E 6))
  (.inc (E 4))))))))

/-- Phase B: skip `m − c` input bits, copy the last `c` raw onto `SRC`. -/
def seedB (I SRC : Fin (ns + 1)) (E : Fin 10 ↪ Fin nr) : WM ns nr :=
  .seq (FinalPass.Hash4.wcopyR (E 0) (E 5) (E 6)) (.seq (FinalPass.Hash4.wcopyR (E 4) (E 8) (E 6))
  (.seq (subLs (E 8) (E 5)) (.seq (walkP I (E 5)) (.seq (FinalPass.Hash4.wcopyR (E 4) (E 8) (E 6))
  (copyRaw I SRC (E 8))))))

/-- Phase C: the heads back to `0`, the scratch registers `E 0`, `E 3`, `E 4` cleared. -/
def seedC (I T SRC : Fin (ns + 1)) (E : Fin 10 ↪ Fin nr) : WM ns nr :=
  .seq (rewIn I T) (.seq (WM.rewind SRC (E 4)) (.seq (WM.clear (E 0)) (WM.clear (E 3))))

/-- **The hash bits' frame**: the program. -/
def seedSrc (I T P13 P15 SRC : Fin (ns + 1)) (E : Fin 10 ↪ Fin nr) : WM ns nr :=
  .seq (seedA T P13 P15 E) (.seq (seedB I SRC E) (seedC I T SRC E))

theorem seedA_spec (T P13 P15 : Fin (ns + 1)) (E : Fin 10 ↪ Fin nr) (m t ℓ : ℕ) (σ : WState ns nr)
    (hT : σ.st T = sent (m + 1)) (hTh : σ.sh T = 0)
    (hP : σ.st P13 = List.replicate t true) (hPh : σ.sh P13 = 0)
    (hQ : σ.st P15 = List.replicate ℓ true) (hQh : σ.sh P15 = 0)
    (hz : ∀ j, σ.val (E j) = 0) (htl : t * ℓ ≤ m) (hcap : 100 * (m + 1) + 10 * (t + ℓ) ≤ cap) :
    ∃ τ, WExec cap (seedA T P13 P15 E) σ τ (200 * (m + t + ℓ + 1) ^ 2) ∧
      τ.st = σ.st ∧ τ.sh = σ.sh ∧ τ.cell = σ.cell ∧ (∀ j, τ.val (E j) = seedV m t ℓ j) ∧
      (∀ r, (∀ j, E j ≠ r) → τ.val r = σ.val r) := by
  have hne : ∀ {i j : Fin 10}, i ≠ j → E i ≠ E j := fun h => E.injective.ne h
  have hE : ∀ i j : Fin 10, E i = E j ↔ i = j := fun i j => E.injective.eq_iff
  have h2tl : 2 * t * ℓ = 2 * (t * ℓ) := by ring
  have s1 := lenM_spec cap T (E 0) m σ hT hTh (hz 0) (by omega)
  have s2 := countU_spec cap P13 (E 1) (E 6) (hne (by decide)) t (σ.setv (E 0) m) (by simpa using hP)
    (by simpa using hPh) (by simp [Function.update_apply, hE, hz]) (by simp [Function.update_apply, hE, hz])
    (by omega)
  have s3 := countU_spec cap P15 (E 2) (E 6) (hne (by decide)) ℓ ((σ.setv (E 0) m).setv (E 1) t)
    (by simpa using hQ) (by simpa using hQh) (by simp [Function.update_apply, hE, hz])
    (by simp [Function.update_apply, hE, hz]) (by omega)
  obtain ⟨σ3, hσ3⟩ : ∃ τ, τ = ((σ.setv (E 0) m).setv (E 1) t).setv (E 2) ℓ := ⟨_, rfl⟩
  rw [← hσ3] at s3
  have v3 : ∀ j : Fin 10, σ3.val (E j) = if j = 0 then m else if j = 1 then t else if j = 2 then ℓ else 0 := by
    clear * - hσ3 hE hz
    intro j; rw [hσ3]; simp only [WState.setv_val, Function.update_apply, hE]
    split_ifs <;> simp_all
  have hmE : ∀ i : Fin 5, (mE.trans E) i = E (mE i) := fun _ => rfl
  have m0 : E (mE 0) = E 1 := rfl
  have m1 : E (mE 1) = E 2 := rfl
  have m2' : E (mE 2) = E 3 := rfl
  have m3 : E (mE 3) = E 6 := rfl
  have m4 : E (mE 4) = E 7 := rfl
  have s4 := PrimAsm.UnaryArith.mulAddW_spec cap (mE.trans E) σ3 (by rw [hmE, m3, v3]; rfl)
    (by rw [hmE, m4, v3]; rfl) (by rw [hmE, m1, v3]; simp; omega)
    (by rw [hmE, hmE, hmE, m2', m0, m1, v3, v3, v3]; simp; omega) (by rw [hmE, m0, v3]; simp; omega)
  simp only [hmE, m0, m1, m2'] at s4
  rw [show σ3.val (E 3) = 0 by rw [v3]; rfl, show σ3.val (E 1) = t by rw [v3]; rfl,
    show σ3.val (E 2) = ℓ by rw [v3]; rfl, Nat.zero_add] at s4
  obtain ⟨σ4, hσ4⟩ : ∃ τ, τ = σ3.setv (E 3) (t * ℓ) := ⟨_, rfl⟩
  rw [← hσ4] at s4
  have v4 : ∀ j : Fin 10, σ4.val (E j) = if j = 0 then m else if j = 1 then t else if j = 2 then ℓ
      else if j = 3 then t * ℓ else 0 := by
    clear * - hσ4 hE v3
    intro j; rw [hσ4]; simp only [WState.setv_val, Function.update_apply, hE, v3]
    split_ifs <;> simp_all
  have s5 := PrimAsm.UnaryArith.mulAddW_spec cap (mE.trans E) σ4 (by rw [hmE, m3, v4]; rfl)
    (by rw [hmE, m4, v4]; rfl) (by rw [hmE, m1, v4]; simp; omega)
    (by rw [hmE, hmE, hmE, m2', m0, m1, v4, v4, v4]; simp; omega) (by rw [hmE, m0, v4]; simp; omega)
  simp only [hmE, m0, m1, m2'] at s5
  rw [show σ4.val (E 3) = t * ℓ by rw [v4]; rfl, show σ4.val (E 1) = t by rw [v4]; rfl,
    show σ4.val (E 2) = ℓ by rw [v4]; rfl] at s5
  obtain ⟨σ5, hσ5⟩ : ∃ τ, τ = σ4.setv (E 3) (t * ℓ + t * ℓ) := ⟨_, rfl⟩
  rw [← hσ5] at s5
  have v5 : ∀ j : Fin 10, σ5.val (E j) = if j = 0 then m else if j = 1 then t else if j = 2 then ℓ
      else if j = 3 then 2 * t * ℓ else 0 := by
    intro j; rw [hσ5]
    by_cases h3 : j = 3
    · subst h3; rw [wsetv_val_self]; simp; ring
    · rw [wsetv_val_ne _ _ (hne h3), v4]; simp [h3]
  have s6 := PrimAsm.ParseNat.addTo_spec cap (E 3) (E 4) (E 6) (hne (by decide)) (hne (by decide))
    (hne (by decide)) σ5 (by rw [v5]; rfl) (by rw [v5]; simp; omega) (by rw [v5, v5]; simp; omega)
  rw [show σ5.val (E 4) = 0 by rw [v5]; rfl, show σ5.val (E 3) = 2 * t * ℓ by rw [v5]; rfl, Nat.zero_add] at s6
  have s7 := PrimAsm.ParseNat.addTo_spec cap (E 3) (E 4) (E 6) (hne (by decide)) (hne (by decide))
    (hne (by decide)) (σ5.setv (E 4) (2 * t * ℓ)) (by simp [Function.update_apply, hE, v5])
    (by simp [Function.update_apply, hE, v5]; omega) (by simp [Function.update_apply, hE, v5]; omega)
  rw [wsetv_val_self, wsetv_val_ne _ _ (hne (by decide)), show σ5.val (E 3) = 2 * t * ℓ by rw [v5]; rfl,
    wsetv_setv] at s7
  have s8 := WExec.inc (cap := cap) (E 4) (σ5.setv (E 4) (2 * t * ℓ + 2 * t * ℓ)) (by simp; omega)
  rw [wsetv_val_self, wsetv_setv] at s8
  obtain ⟨σ8, hσ8⟩ : ∃ τ, τ = σ5.setv (E 4) (2 * t * ℓ + 2 * t * ℓ + 1) := ⟨_, rfl⟩
  rw [← hσ8] at s8
  refine ⟨σ8, WExec.mono (WExec.seq s1 (WExec.seq s2 (WExec.seq s3 (WExec.seq s4 (WExec.seq s5
    (WExec.seq s6 (WExec.seq s7 s8))))))) ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have hmul : ℓ * (18 * t + 8) = 18 * (t * ℓ) + 8 * ℓ := by ring
    have h2 : 2 * t * ℓ = 2 * (t * ℓ) := by ring
    have hsq := Nat.le_self_pow (n := 2) (by norm_num) (m + t + ℓ + 1)
    simp only [hmul, h2]
    clear * - hsq htl
    omega
  · rw [hσ8, hσ5, hσ4, hσ3]; rfl
  · rw [hσ8, hσ5, hσ4, hσ3]; rfl
  · rw [hσ8, hσ5, hσ4, hσ3]; rfl
  · clear * - hσ8 hE v5
    intro j; rw [hσ8]; simp only [WState.setv_val, Function.update_apply, hE, v5, seedV]
    split_ifs <;> simp_all <;> omega
  · intro r hr; rw [hσ8, hσ5, hσ4, hσ3]
    simp only [WState.setv_val, Function.update_apply]
    simp [fun j => Ne.symm (hr j)]

theorem seedB_spec (I SRC : Fin (ns + 1)) (hIS : I ≠ SRC) (E : Fin 10 ↪ Fin nr) (pre w : List Bool)
    (t ℓ : ℕ) (σ : WState ns nr) (hI : σ.st I = frame (pre ++ frame w)) (hIh : σ.sh I = 0)
    (hS : σ.st SRC = []) (hSh : σ.sh SRC = 0) (hv : ∀ j, σ.val (E j) = seedV (pre ++ frame w).length t ℓ j)
    (hw : w.length = 2 * t * ℓ) (hcap : 100 * ((pre ++ frame w).length + 1) ≤ cap) :
    ∃ τ, WExec cap (seedB I SRC E) σ τ (100 * ((pre ++ frame w).length + 1)) ∧
      τ.st SRC = frame w ∧ (∀ i, i ≠ SRC → τ.st i = σ.st i) ∧
      τ.sh I = 2 * (pre ++ frame w).length ∧ τ.sh SRC = (frame w).length ∧
      (∀ i, i ≠ I → i ≠ SRC → τ.sh i = σ.sh i) ∧ τ.val = σ.val ∧ τ.cell = σ.cell := by
  have hne : ∀ {i j : Fin 10}, i ≠ j → E i ≠ E j := fun h => E.injective.ne h
  have hE : ∀ i j : Fin 10, E i = E j ↔ i = j := fun i j => E.injective.eq_iff
  obtain ⟨m, hm⟩ : ∃ x, x = (pre ++ frame w).length := ⟨_, rfl⟩
  rw [← hm] at hv hcap ⊢
  obtain ⟨c, hc⟩ : ∃ x, x = (frame w).length := ⟨_, rfl⟩
  have hc2 : c = 2 * (2 * t * ℓ) + 1 := by rw [hc, frame_length', hw]
  have hmc : c ≤ m := by rw [hm, hc, List.length_append]; omega
  have v8 : ∀ j : Fin 10, σ.val (E j) = if j = 0 then m else if j = 1 then t else if j = 2 then ℓ
      else if j = 3 then 2 * t * ℓ else if j = 4 then c else 0 := by
    intro j; rw [hv, seedV, hc2]
  have s9 := FinalPass.Hash4.wcopyR_spec cap (E 0) (E 5) (E 6) (hne (by decide)) (hne (by decide))
    (hne (by decide)) σ (by rw [v8]; rfl) (by rw [v8]; rfl) (by rw [v8]; simp; omega)
  rw [show σ.val (E 0) = m by rw [v8]; rfl] at s9
  have s10 := FinalPass.Hash4.wcopyR_spec cap (E 4) (E 8) (E 6) (hne (by decide)) (hne (by decide))
    (hne (by decide)) (σ.setv (E 5) m) (by simp [Function.update_apply, hE, v8])
    (by simp [Function.update_apply, hE, v8]) (by simp [Function.update_apply, hE, v8]; omega)
  rw [wsetv_val_ne _ _ (hne (by decide)), show σ.val (E 4) = c by rw [v8]; rfl] at s10
  have s11 := subLs_spec cap (E 8) (E 5) (hne (by decide)) c ((σ.setv (E 5) m).setv (E 8) c) (by simp)
    (by omega) (by simp [Function.update_apply, hE]; omega)
  rw [wsetv_setv, wsetv_val_ne _ _ (hne (by decide)), wsetv_val_self] at s11
  obtain ⟨σ11, hσ11⟩ : ∃ τ, τ = (((σ.setv (E 5) m).setv (E 8) 0).setv (E 5) (m - c)) := ⟨_, rfl⟩
  rw [← hσ11] at s11
  have v11 : ∀ j : Fin 10, σ11.val (E j) = if j = 0 then m else if j = 1 then t else if j = 2 then ℓ
      else if j = 3 then 2 * t * ℓ else if j = 4 then c else if j = 5 then m - c else 0 := by
    clear * - hσ11 hE v8
    intro j; rw [hσ11]; simp only [WState.setv_val, Function.update_apply, hE, v8]
    split_ifs <;> simp_all
  have sh11 : σ11.sh = σ.sh := by rw [hσ11]; rfl
  have st11 : σ11.st = σ.st := by rw [hσ11]; rfl
  have s12 := walkP_spec cap I (E 5) (m - c) σ11 (by rw [v11]; rfl) (by omega)
  obtain ⟨σ12, hσ12⟩ : ∃ τ, τ = (σ11.setv (E 5) 0).seth I (σ11.sh I + 2 * (m - c)) := ⟨_, rfl⟩
  rw [← hσ12] at s12
  have v12 : ∀ j : Fin 10, σ12.val (E j) = if j = 0 then m else if j = 1 then t else if j = 2 then ℓ
      else if j = 3 then 2 * t * ℓ else if j = 4 then c else 0 := by
    clear * - hσ12 hE v11
    intro j; rw [hσ12]; simp only [WState.seth_val, WState.setv_val, Function.update_apply, hE, v11]
    split_ifs <;> simp_all
  have s13 := FinalPass.Hash4.wcopyR_spec cap (E 4) (E 8) (E 6) (hne (by decide)) (hne (by decide))
    (hne (by decide)) σ12 (by rw [v12]; rfl) (by rw [v12]; rfl) (by rw [v12]; simp; omega)
  rw [show σ12.val (E 4) = c by rw [v12]; rfl] at s13
  have s14 := copyRaw_spec cap I SRC hIS (E 8) (pre ++ frame w) c (m - c) (σ12.setv (E 8) c)
    (by rw [hσ12]; simp [st11, hI]) (by rw [hσ12]; simp [sh11, hIh]) (by omega) (by simp) (by omega)
    (by rw [hσ12]; simp [Function.update_apply, Ne.symm hIS, st11, sh11, hS, hSh])
  rw [wsetv_setv] at s14
  have hdrop : ((pre ++ frame w).drop (m - c)).take c = frame w := by
    rw [show m - c = pre.length by rw [hm, hc, List.length_append]; omega, List.drop_left, hc, List.take_length]
  rw [hdrop, show m - c + c = m by omega] at s14
  refine ⟨_, WExec.mono (WExec.seq s9 (WExec.seq s10 (WExec.seq s11 (WExec.seq s12 (WExec.seq s13 s14))))) ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · clear * - hmc
    omega
  · rw [hσ12]; simp [Function.update_apply, Ne.symm hIS, st11, hS]
  · intro i hi; rw [hσ12]; simp [Function.update_apply, hi, st11]
  · simp
  · rw [hσ12]; simp [Function.update_apply, Ne.symm hIS, sh11, st11, hS, hSh, hc]
  · intro i hiI hiS; rw [hσ12]; simp [Function.update_apply, hiI, hiS, sh11]
  · funext r
    rw [hσ12, hσ11]
    by_cases h8 : r = E 8
    · subst h8; simp [Function.update_apply, hE, v8]
    · by_cases h5 : r = E 5
      · subst h5; simp [Function.update_apply, hE, v8]
      · simp [Function.update_apply, h8, h5]
  · rw [hσ12, hσ11]; simp

theorem seedC_spec (I T SRC : Fin (ns + 1)) (hIT : I ≠ T) (hIS : I ≠ SRC) (E : Fin 10 ↪ Fin nr) (m c : ℕ)
    (σ : WState ns nr) (hT : σ.st T = sent (m + 1)) (hTh : σ.sh T = 0) (hIh : σ.sh I ≤ 2 * (m + 1))
    (h4 : σ.val (E 4) = c) (hSh : σ.sh SRC = c) (hc : c ≤ cap) (h0 : σ.val (E 0) ≤ cap)
    (h3 : σ.val (E 3) ≤ cap) :
    ∃ τ, WExec cap (seedC I T SRC E) σ τ (10 * (m + 1) + 5 * c + 3 * σ.val (E 0) + 3 * σ.val (E 3) + 20) ∧
      τ.st = σ.st ∧ τ.sh I = 0 ∧ τ.sh SRC = 0 ∧ (∀ i, i ≠ I → i ≠ SRC → τ.sh i = σ.sh i) ∧
      τ.val (E 0) = 0 ∧ τ.val (E 3) = 0 ∧ τ.val (E 4) = 0 ∧
      (∀ r, r ≠ E 0 → r ≠ E 3 → r ≠ E 4 → τ.val r = σ.val r) ∧ τ.cell = σ.cell := by
  have hE : ∀ i j : Fin 10, E i = E j ↔ i = j := fun i j => E.injective.eq_iff
  have s1 := rewIn_spec cap I T hIT (m + 1) σ hT hTh hIh
  have s2 := wrewind_spec cap SRC (E 4) c (σ.seth I 0) (by simpa using h4) (by simp; omega)
  have hS0 : (σ.seth I 0).sh SRC - c = 0 := by simp [Function.update_apply, Ne.symm hIS, hSh]
  rw [hS0] at s2
  have s3 := wclear_spec cap (E 0) (σ.val (E 0)) (((σ.seth I 0).setv (E 4) 0).seth SRC 0)
    (by simp [Function.update_apply, hE]) (by simp [Function.update_apply, hE]; omega)
  have s4 := wclear_spec cap (E 3) (σ.val (E 3)) ((((σ.seth I 0).setv (E 4) 0).seth SRC 0).setv (E 0) 0)
    (by simp [Function.update_apply, hE]) (by simp [Function.update_apply, hE]; omega)
  refine ⟨_, WExec.mono (WExec.seq s1 (WExec.seq s2 (WExec.seq s3 s4))) (by omega), rfl, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, rfl⟩
  · simp [Function.update_apply, hIS]
  · simp
  · intro i hiI hiS; simp [Function.update_apply, hiI, hiS]
  · simp [Function.update_apply, hE]
  · simp
  · simp [Function.update_apply, hE]
  · intro r h0 h3 h4; simp [Function.update_apply, h0, h3, h4]

theorem seedSrc_spec (I T P13 P15 SRC : Fin (ns + 1)) (hIT : I ≠ T) (_hIP : I ≠ P13) (_hIQ : I ≠ P15)
    (hIS : I ≠ SRC) (_hTP : T ≠ P13) (_hTQ : T ≠ P15) (hTS : T ≠ SRC) (_hPQ : P13 ≠ P15) (_hPS : P13 ≠ SRC)
    (_hQS : P15 ≠ SRC) (E : Fin 10 ↪ Fin nr) (pre w : List Bool) (t ℓ : ℕ) (σ : WState ns nr)
    (hI : σ.st I = frame (pre ++ frame w)) (hIh : σ.sh I = 0)
    (hT : σ.st T = sent ((pre ++ frame w).length + 1)) (hTh : σ.sh T = 0)
    (hP : σ.st P13 = List.replicate t true) (hPh : σ.sh P13 = 0)
    (hQ : σ.st P15 = List.replicate ℓ true) (hQh : σ.sh P15 = 0)
    (hS : σ.st SRC = []) (hSh : σ.sh SRC = 0) (hz : ∀ j, σ.val (E j) = 0) (hw : w.length = 2 * t * ℓ)
    (hcap : 100 * ((pre ++ frame w).length + 1) + 10 * (t + ℓ) ≤ cap) :
    ∃ τ c, WExec cap (seedSrc I T P13 P15 SRC E) σ τ c ∧
      c ≤ 1000 * ((pre ++ frame w).length + t + ℓ + 1) ^ 2 ∧
      τ.st SRC = frame w ∧ (∀ i, i ≠ SRC → τ.st i = σ.st i) ∧ (∀ i, τ.sh i = σ.sh i) ∧
      τ.val (E 1) = t ∧ τ.val (E 2) = ℓ ∧ (∀ j : Fin 10, j ≠ 1 → j ≠ 2 → τ.val (E j) = 0) ∧
      (∀ r, (∀ j, E j ≠ r) → τ.val r = σ.val r) ∧ τ.cell = σ.cell := by
  have hne : ∀ {i j : Fin 10}, i ≠ j → E i ≠ E j := fun h => E.injective.ne h
  have hc2 : (frame w).length = 2 * (2 * t * ℓ) + 1 := by rw [frame_length', hw]
  have hmc : (frame w).length ≤ (pre ++ frame w).length := by rw [List.length_append]; omega
  have htl : t * ℓ ≤ (pre ++ frame w).length := by
    have : 2 * t * ℓ = 2 * (t * ℓ) := by ring
    omega
  obtain ⟨σA, eA, stA, shA, cA, vA, oA⟩ := seedA_spec cap T P13 P15 E (pre ++ frame w).length t ℓ σ hT hTh
    hP hPh hQ hQh hz htl hcap
  obtain ⟨σB, eB, stB1, stB2, shB1, shB2, shB3, vB, cB⟩ := seedB_spec cap I SRC hIS E pre w t ℓ σA
    (by rw [stA]; exact hI) (by rw [shA]; exact hIh) (by rw [stA]; exact hS) (by rw [shA]; exact hSh) vA hw
    (by omega)
  have vB0 : σB.val (E 0) = (pre ++ frame w).length := by rw [vB, vA]; rfl
  have vB3 : σB.val (E 3) = 2 * t * ℓ := by rw [vB, vA]; rfl
  have vB4 : σB.val (E 4) = (frame w).length := by rw [vB, vA, hc2]; rfl
  obtain ⟨σC, eC, stC, shC1, shC2, shC3, vC0, vC3, vC4, vCo, cC⟩ := seedC_spec cap I T SRC hIT hIS E
    (pre ++ frame w).length (frame w).length σB (by rw [stB2 T hTS, stA, hT])
    (by rw [shB3 T (Ne.symm hIT) hTS, shA, hTh]) (by rw [shB1]; omega) vB4 shB2 (by omega) (by omega)
    (by rw [vB3]; have : 2 * t * ℓ = 2 * (t * ℓ) := by ring
        omega)
  rw [vB0, vB3] at eC
  refine ⟨σC, _, WExec.seq eA (WExec.seq eB eC), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have h2 : 2 * t * ℓ = 2 * (t * ℓ) := by ring
    have hsq := Nat.le_self_pow (n := 2) (by norm_num) ((pre ++ frame w).length + t + ℓ + 1)
    rw [h2]
    clear * - hsq htl hmc
    omega
  · rw [stC]; exact stB1
  · intro i hi; rw [stC, stB2 i hi, stA]
  · intro i
    by_cases hiI : i = I
    · subst hiI; rw [shC1, hIh]
    · by_cases hiS : i = SRC
      · subst hiS; rw [shC2, hSh]
      · rw [shC3 i hiI hiS, shB3 i hiI hiS, shA]
  · rw [vCo _ (hne (by decide)) (hne (by decide)) (hne (by decide)), vB, vA]; rfl
  · rw [vCo _ (hne (by decide)) (hne (by decide)) (hne (by decide)), vB, vA]; rfl
  · intro j h1 h2
    by_cases j0 : j = 0
    · subst j0; exact vC0
    · by_cases j3 : j = 3
      · subst j3; exact vC3
      · by_cases j4 : j = 4
        · subst j4; exact vC4
        · rw [vCo _ (hne j0) (hne j3) (hne j4), vB, vA]
          simp [seedV, j0, h1, h2, j3, j4]
  · intro r hr
    rw [vCo r (Ne.symm (hr 0)) (Ne.symm (hr 3)) (Ne.symm (hr 4)), vB, oA r hr]
  · rw [cC, cB, cA]

end NearCubicWires.WireExponent3_5.FinalPass.S5T
