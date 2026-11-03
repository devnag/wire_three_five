import Proof.Wire_3_5.Foundations.OutMachineSwL

/-! # SWl (root #262/#273/#278/#283), part 3: **`swL : ∀ l, SWParts.SWlT l`** (the templates' writer)

The SYM words writer's templates (slots `28 … 31`: `symWords` word `4·3 + j` = `S3.templJ`, the stage-5 template
`levelWord M J W (blank rows of length |G_j|)` of the base list, P3:1449-1477, 1508-1520, 3170-3178) at a SYM request,
from the core's blank entry, on NW's bank `x ≥ DT + 7`:

1. The SYM front `frontM` (`front_run`, `FrontOut`: `M`, `B` in `G 32 = 440`, `G 33 = 441`, `|G_j|` in `330 + j`);
2. **`swlP`**: the low registers `0 … 55` cleared, `numsP` (part 2), `circ` (part 1) per circuit on the blank streams
   `oL j = sT (DT + 3 + j)`, every register cleared (**`swlP_spec`**, `circCap`);
3. **`swl_word`** (slot `12 + j` is `templJ`) and E's `tplWord_eq`: the written words ARE the slots.

* `lowRegs`, `oL`, `lR`, `swlP`, `tplOf`, `circCap`, `swlP_spec`, `swl_word`, `KcL`/`DkL`/`CsL`/`DsL`, `capArith`,
  `costArith`, `lM`, **`lRun`**, **`swL`**, **`swLAll`** (`Pl` of `Close7.finalPassClose7`).

Paper quantity of the main type: the SYM call's stage-5 templates (`symWords`, kind `3`, P3:1449-1477,
3170-3178). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

namespace NearCubicWires.WireExponent3_5.FinalPass.Out.SwL
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimAsm.SymLayout (LNS LNR sT)
open NearCubicWires.WireExponent3_5.FinalPass.SymParts.Tmpl (tplWord)

variable (cap : ℕ)

/-! ## The whole program -/

/-- The low registers `0 … 55`. -/
def lowRegs : List (Fin LNR) :=
  (List.finRange 56).map fun i => ⟨i.val, by have := i.isLt; show i.val < 512; omega⟩

theorem mem_low (q : Fin LNR) (h : q.val < 56) : q ∈ lowRegs :=
  List.mem_map.mpr ⟨⟨q.val, h⟩, List.mem_finRange _, rfl⟩

theorem not_mem_low (q : Fin LNR) (h : 56 ≤ q.val) : q ∉ lowRegs := by
  intro hq
  obtain ⟨i, _, e⟩ := List.mem_map.mp hq
  have h2 : i.val = q.val := congrArg Fin.val e
  have := i.isLt
  omega

theorem lowRegs_length : lowRegs.length = 56 := by simp [lowRegs]

/-- The four output streams `sT (DT + 3 + j)` (blank at the front's exit). -/
def oL (x : ℕ) (hx : UnionMachine.DataDock.DT + 7 ≤ x) : Fin 4 ↪ Fin (LNS x + 1) :=
  ⟨fun k => sT x ⟨UnionMachine.DataDock.DT + 3 + k.val, by have := k.isLt; omega⟩, fun a b h => by
    have h2 : 161 + (UnionMachine.DataDock.DT + 3 + a.val) = 161 + (UnionMachine.DataDock.DT + 3 + b.val) :=
      congrArg Fin.val h
    exact Fin.ext (by omega)⟩

theorem oL_val (x : ℕ) (hx : UnionMachine.DataDock.DT + 7 ≤ x) (k : Fin 4) :
    (oL x hx k).val = 161 + (UnionMachine.DataDock.DT + 3 + k.val) := rfl

theorem oL_ne (x : ℕ) (hx : UnionMachine.DataDock.DT + 7 ≤ x) (k : Fin 4) : oL x hx k ≠ UnionMachine.NumsPh2.sIn x :=
  fun e => by
    have h1 := congrArg Fin.val e
    have h2 : (UnionMachine.NumsPh2.sIn x).val = 150 := rfl
    rw [oL_val] at h1
    omega

theorem hx3 (x : ℕ) (hx : UnionMachine.DataDock.DT + 7 ≤ x) : UnionMachine.DataDock.DT + 3 ≤ x := by omega

/-- Circuit `j`'s count `|G_j|` (the front's register `330 + j`). -/
def lR (j : Fin 4) : Fin LNR := ⟨330 + j.val, by have := j.isLt; show 330 + j.val < 512; omega⟩

/-- **SWl's program after the front**: the low registers cleared, `numsP`, the four templates, every register cleared. -/
noncomputable def swlP (x : ℕ) (hx : UnionMachine.DataDock.DT + 7 ≤ x) : WM (LNS x) LNR :=
  .seq (FinalPass.S5T.clearL lowRegs) (.seq numsP (.seq (circ (oL x hx 0) wL 440 (lR 0) 54)
    (.seq (circ (oL x hx 1) wL 440 (lR 1) 54) (.seq (circ (oL x hx 2) wL 440 (lR 2) 54)
    (.seq (circ (oL x hx 3) wL 440 (lR 3) 54) FinalPass.S5T.clearAll)))))

/-- The template word from `M`, `B`, `L`. -/
noncomputable def tplOf (M B L : ℕ) : List Bool :=
  tplWord M (CanonicalFourfoldRowProgram.natCeilSqrt (64 ^ 2 * B)) (Nat.clog 2 B + 9) L

theorem circCap (M B L V : ℕ) (hM : M ≤ V) (hB : B ≤ V) (hL : L ≤ V) (hc : 2 ^ 25 * (V + 10) ^ 2 ≤ cap) :
    PrimAsm.LevelW.lvCap (CanonicalFourfoldRowProgram.natCeilSqrt (64 ^ 2 * B)) (Nat.clog 2 B + 9)
        (Nat.clog 2 B + 9) ≤ cap ∧
      (tplOf M B L).length ≤ cap ∧ Nat.clog 2 B + 9 + 1 ≤ cap ∧ L ≤ cap ∧ M ≤ cap := by
  obtain ⟨hcl, hp⟩ := clog_le B
  have hs := sqrt_le B
  have e9 : 2 ^ (Nat.clog 2 B + 9) = 2 ^ Nat.clog 2 B * 512 := by rw [pow_add]; norm_num
  have hJ3 : 2 ^ ((Nat.clog 2 B + 9) / 3) ≤ 2 ^ (Nat.clog 2 B + 9) :=
    Nat.pow_le_pow_right (by norm_num) (Nat.div_le_self _ _)
  have hV2 : V + 10 ≤ (V + 10) ^ 2 := Nat.le_self_pow (by norm_num) _
  have hw := tplWord_length_le M (CanonicalFourfoldRowProgram.natCeilSqrt (64 ^ 2 * B)) (Nat.clog 2 B + 9) L
  have hprod : (Nat.clog 2 B + 9 + 1) * (5 * (64 + CanonicalFourfoldRowProgram.natCeilSqrt (64 ^ 2 * B) +
      2 ^ (Nat.clog 2 B + 9)) + 5 + L) ≤ (2 * (V + 10)) * (26000 * (V + 10)) :=
    Nat.mul_le_mul (by omega) (by omega)
  have e : (2 * (V + 10)) * (26000 * (V + 10)) = 52000 * (V + 10) ^ 2 := by ring
  unfold tplOf PrimAsm.LevelW.lvCap
  refine ⟨by omega, by omega, by omega, by omega, by omega⟩

theorem swlP_spec (x : ℕ) (hx : UnionMachine.DataDock.DT + 7 ≤ x) (τ0 : WState (LNS x) LNR) (M B V : ℕ)
    (L : Fin 4 → ℕ) (hM : τ0.val 440 = M) (hB : τ0.val 441 = B) (hL : ∀ j, τ0.val (lR j) = L j)
    (hV : ∀ q, τ0.val q ≤ V) (hBV : B ≤ V) (hMV : M ≤ V) (hLV : ∀ j, L j ≤ V)
    (hO : ∀ j, τ0.st (oL x hx j) = []) (hOh : ∀ j, τ0.sh (oL x hx j) = 0) (hc : 2 ^ 25 * (V + 10) ^ 2 ≤ cap) :
    ∃ (τ : WState (LNS x) LNR) (n : ℕ), n ≤ 140000 * (cap + 2) ^ 3 ∧ WExec cap (swlP x hx) τ0 τ n ∧
      (∀ j, τ.st (oL x hx j) = tplOf M B (L j)) ∧ (∀ i, (∀ j, i ≠ oL x hx j) → τ.st i = τ0.st i) ∧
      τ.sh = τ0.sh ∧ ∀ q, τ.val q = 0 := by
  have hV2 : V + 10 ≤ (V + 10) ^ 2 := Nat.le_self_pow (by norm_num) _
  have hVc : V ≤ cap := by omega
  have hne : ∀ a b : Fin 4, a ≠ b → oL x hx a ≠ oL x hx b := fun a b h => (oL x hx).injective.ne h
  obtain ⟨τ1, e1, st1, sh1, _, z1, u1⟩ := FinalPass.S5T.clearL_spec cap lowRegs τ0 (fun r => (hV r).trans hVc)
  rw [lowRegs_length] at e1
  have hz1 : ∀ q : Fin LNR, q.val < 56 → τ1.val q = 0 := fun q hq => z1 q (mem_low q hq)
  have hu1 : ∀ q : Fin LNR, 56 ≤ q.val → τ1.val q = τ0.val q := fun q hq => u1 q (not_mem_low q hq)
  have hBc : 2 ^ 25 * (B + 10) ^ 2 ≤ cap :=
    le_trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 2)) hc
  obtain ⟨n2, hn2, e2⟩ := numsP_spec cap τ1 B (by rw [hu1 441 (by decide)]; exact hB) hz1 hBc
  set τ2 := (τ1.setv 1 (Nat.clog 2 B + 9)).setv 0 (CanonicalFourfoldRowProgram.natCeilSqrt (64 ^ 2 * B)) with hτ2
  have hv2 : ∀ q : Fin LNR, 2 ≤ q.val → τ2.val q = τ1.val q := fun q hq => by
    have a0 : q ≠ 0 := fun e => by subst e; simp at hq
    have a1 : q ≠ 1 := fun e => by subst e; simp at hq
    simp [hτ2, Function.update_apply, a0, a1]
  have circ_at : ∀ (j : Fin 4) (ρ : WState (LNS x) LNR), ρ.val = τ2.val → ρ.st (oL x hx j) = [] →
      ρ.sh (oL x hx j) = 0 → ∃ n, n ≤ 30000 * (cap + 2) ^ 3 ∧
        WExec cap (circ (oL x hx j) wL 440 (lR j) 54) ρ (ρ.sets (oL x hx j) (tplOf M B (L j))) n := by
    intro j ρ hρ hρO hρh
    obtain ⟨cl, cw, cJ, cL, cM⟩ := circCap cap M B (L j) V hMV hBV (hLV j) hc
    have hj := j.isLt
    exact circ_spec cap (oL x hx j) wL 440 (lR j) 54
      (fun i e => by
        have h1 : i.val = 440 := congrArg Fin.val e
        have := i.isLt
        omega)
      (fun i e => by
        have h1 : i.val = 330 + j.val := congrArg Fin.val e
        have := i.isLt
        omega)
      (fun i e => by
        have h1 : i.val = 54 := congrArg Fin.val e
        have := i.isLt
        omega)
      (by decide)
      (fun e => by
        have h1 : 330 + j.val = 54 := congrArg Fin.val e
        omega)
      ρ M _ _ (L j)
      (by rw [hρ]; simp [hτ2, wL0])
      (by rw [hρ]; simp [hτ2, Function.update_apply, wL1])
      (fun i hi => by
        have := i.isLt
        rw [hρ, hv2 _ (show 2 ≤ i.val from hi)]
        exact hz1 _ (show i.val < 56 by omega))
      (by rw [hρ, hv2 440 (by decide), hu1 440 (by decide)]; exact hM)
      (by
        rw [hρ, hv2 _ (show 2 ≤ 330 + j.val by omega), hu1 _ (show 56 ≤ 330 + j.val by omega)]
        exact hL j)
      (by rw [hρ, hv2 54 (by decide)]; exact hz1 54 (by decide))
      hρO hρh cl cw cJ cL cM
  obtain ⟨n3, hn3, e3⟩ := circ_at 0 τ2 rfl (by simp [hτ2, st1, hO]) (by simp [hτ2, sh1, hOh])
  set τ3 := τ2.sets (oL x hx 0) (tplOf M B (L 0)) with hτ3
  obtain ⟨n4, hn4, e4⟩ := circ_at 1 τ3 (by simp [hτ3])
    (by simp [hτ3, hτ2, Function.update_apply, hne 1 0 (by decide), st1, hO]) (by simp [hτ3, hτ2, sh1, hOh])
  set τ4 := τ3.sets (oL x hx 1) (tplOf M B (L 1)) with hτ4
  obtain ⟨n5, hn5, e5⟩ := circ_at 2 τ4 (by simp [hτ4, hτ3])
    (by simp [hτ4, hτ3, hτ2, Function.update_apply, hne 2 0 (by decide), hne 2 1 (by decide), st1, hO])
    (by simp [hτ4, hτ3, hτ2, sh1, hOh])
  set τ5 := τ4.sets (oL x hx 2) (tplOf M B (L 2)) with hτ5
  obtain ⟨n6, hn6, e6⟩ := circ_at 3 τ5 (by simp [hτ5, hτ4, hτ3])
    (by simp [hτ5, hτ4, hτ3, hτ2, Function.update_apply, hne 3 0 (by decide), hne 3 1 (by decide),
      hne 3 2 (by decide), st1, hO])
    (by simp [hτ5, hτ4, hτ3, hτ2, sh1, hOh])
  set τ6 := τ5.sets (oL x hx 3) (tplOf M B (L 3)) with hτ6
  have hτ6v : τ6.val = τ2.val := by simp [hτ6, hτ5, hτ4, hτ3]
  obtain ⟨hsc, _⟩ := numsCap B cap hBc
  obtain ⟨hcl, _⟩ := clog_le B
  have hs := sqrt_le B
  obtain ⟨τ7, e7, st7, sh7, _, z7⟩ := FinalPass.S5T.clearAll_spec cap τ6 (fun r => by
    rw [hτ6v]
    simp only [hτ2, WState.setv_val, Function.update_apply]
    split_ifs
    · omega
    · omega
    · by_cases hr : r.val < 56
      · rw [hz1 r hr]; exact Nat.zero_le _
      · rw [hu1 r (by omega)]; exact (hV r).trans hVc)
  have hc3 : cap + 2 ≤ (cap + 2) ^ 3 := Nat.le_self_pow (by norm_num) _
  have hn7 : LNR * (3 * cap + 2) ≤ 512 * (3 * cap + 2) := le_rfl
  refine ⟨τ7, _, ?_, WExec.seq e1 (WExec.seq e2 (WExec.seq e3 (WExec.seq e4 (WExec.seq e5 (WExec.seq e6 e7))))),
    ?_, fun i hi => ?_, ?_, z7⟩
  · omega
  · intro j
    rw [st7]
    fin_cases j
    · simp [hτ6, hτ5, hτ4, hτ3, Function.update_apply, hne 0 3 (by decide), hne 0 2 (by decide),
        hne 0 1 (by decide)]
    · simp [hτ6, hτ5, hτ4, Function.update_apply, hne 1 3 (by decide), hne 1 2 (by decide)]
    · simp [hτ6, hτ5, Function.update_apply, hne 2 3 (by decide)]
    · simp [hτ6]
  · rw [st7]
    simp [hτ6, hτ5, hτ4, hτ3, hτ2, Function.update_apply, hi 0, hi 1, hi 2, hi 3, st1]
  · rw [sh7]
    simp [hτ6, hτ5, hτ4, hτ3, hτ2, sh1]

/-! ## The slots, the constants, the run -/

section Gate
open NearCubicWires.WireExponent3_5.Split NearCubicWires.WireExponent3_5.PrimAsm.Plan
open NearCubicWires.WireExponent3_5.FinalPass.PlanFP NearCubicWires.SupplierPipeline
open NearCubicWires.WireExponent3_5.FinalPass.Finish (symSlot sw0_nw)

variable (l : Literals)


theorem capArith (X KF DF CF DFs : ℕ) (hX : 1 ≤ X) :
    KF * X ^ DF + 2 ^ 25 * (CF * X ^ DFs + 10) ^ 2 ≤ (KF + 2 ^ 25 * (CF + 10) ^ 2) * X ^ (DF + 2 * DFs) := by
  have hp : 1 ≤ X ^ DFs := Nat.one_le_pow _ _ (by omega)
  have h1 : CF * X ^ DFs + 10 ≤ (CF + 10) * X ^ DFs := by
    have e : (CF + 10) * X ^ DFs = CF * X ^ DFs + 10 * X ^ DFs := by ring
    omega
  have h2 : (CF * X ^ DFs + 10) ^ 2 ≤ (CF + 10) ^ 2 * X ^ (2 * DFs) := by
    calc (CF * X ^ DFs + 10) ^ 2 ≤ ((CF + 10) * X ^ DFs) ^ 2 := Nat.pow_le_pow_left h1 2
      _ = (CF + 10) ^ 2 * X ^ (2 * DFs) := by rw [mul_pow, ← pow_mul, Nat.mul_comm DFs 2]
  have h3 : X ^ DF ≤ X ^ (DF + 2 * DFs) := Nat.pow_le_pow_right hX (by omega)
  have h4 : X ^ (2 * DFs) ≤ X ^ (DF + 2 * DFs) := Nat.pow_le_pow_right hX (by omega)
  calc KF * X ^ DF + 2 ^ 25 * (CF * X ^ DFs + 10) ^ 2
      ≤ KF * X ^ (DF + 2 * DFs) + 2 ^ 25 * ((CF + 10) ^ 2 * X ^ (DF + 2 * DFs)) :=
        Nat.add_le_add (Nat.mul_le_mul_left _ h3)
          (Nat.mul_le_mul_left _ (h2.trans (Nat.mul_le_mul_left _ h4)))
    _ = (KF + 2 ^ 25 * (CF + 10) ^ 2) * X ^ (DF + 2 * DFs) := by ring

theorem costArith (X CF DFs Kc Dk m nP : ℕ) (hX : 1 ≤ X) (hKc : 1 ≤ Kc) (hm : m ≤ CF * X ^ DFs)
    (hn : nP ≤ 140000 * (Kc * X ^ Dk + 2) ^ 3) :
    m + 1 + nP ≤ (CF + 1 + 3780000 * Kc ^ 3) * X ^ (DFs + 3 * Dk) := by
  have hp : 1 ≤ X ^ Dk := Nat.one_le_pow _ _ (by omega)
  have hc1 : 1 ≤ Kc * X ^ Dk := by
    have := Nat.mul_le_mul hKc hp
    omega
  have h3 : (Kc * X ^ Dk + 2) ^ 3 ≤ 27 * (Kc ^ 3 * X ^ (3 * Dk)) := by
    calc (Kc * X ^ Dk + 2) ^ 3 ≤ (3 * (Kc * X ^ Dk)) ^ 3 := Nat.pow_le_pow_left (by omega) 3
      _ = 27 * (Kc ^ 3 * X ^ (3 * Dk)) := by rw [mul_pow, mul_pow, ← pow_mul, Nat.mul_comm Dk 3]; norm_num
  have h5 : CF * X ^ DFs ≤ CF * X ^ (DFs + 3 * Dk) := Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hX (by omega))
  have h6 : Kc ^ 3 * X ^ (3 * Dk) ≤ Kc ^ 3 * X ^ (DFs + 3 * Dk) :=
    Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hX (by omega))
  have h7 : 1 ≤ X ^ (DFs + 3 * Dk) := Nat.one_le_pow _ _ (by omega)
  have e : (CF + 1 + 3780000 * Kc ^ 3) * X ^ (DFs + 3 * Dk) =
      CF * X ^ (DFs + 3 * Dk) + X ^ (DFs + 3 * Dk) + 3780000 * (Kc ^ 3 * X ^ (DFs + 3 * Dk)) := by ring
  omega

end Gate

end NearCubicWires.WireExponent3_5.FinalPass.Out.SwL
