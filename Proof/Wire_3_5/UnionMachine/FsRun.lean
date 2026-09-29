import Proof.Wire_3_5.UnionMachine.FsRegs
import Proof.Wire_3_5.UnionMachine.FsWords
import Proof.Wire_3_5.Primitive.Writers.FiltSetupIface2

/-! # C6, the FILTER setup, part 5: the whole program's run

**`fsProg x`** = the numbers at every length (`FsNums.gapX` on the block **`fsK`**: `K 0 = fsCap`, `K 1 = fsLen`,
`K 2 = fsErr`, `K i = 405 + i`), the register stages `FsRegs.rA … rD`, the words `FsWords.wordsW`.
**`fs_exec`**: from the FILTER setup's entry bank (`FiltSetup.FsIn2`) and capacity facts, the run and every fact
`UnitReady.FiltReady` and `FiltSetupSpec4` read: the registers below `250` (C5's builder registers, the trace mask's,
the FILTER numbers), the words, the request, counter and flags, the heads.

Paper quantity: none (the run of the setup of `filt:gap`'s regular filter at the seed, P3:2019-2054, 2083-2100). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false

namespace NearCubicWires.WireExponent3_5.UnionMachine.FsRun
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.SignedSortKey NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimAsm NearCubicWires.WireExponent3_5.PrimAsm.SymLayout
open NearCubicWires.WireExponent3_5.PrimAsm.FiltSetup NearCubicWires.WireExponent3_5.UnionMachine

variable (cap : ℕ)

/-- **The register block** for the filter's numbers: `K 0 = fsCap`, `K 1 = fsLen`, `K 2 = fsErr`, `K i = 405 + i`. -/
def fsK : Fin 32 ↪ Fin LNR :=
  ⟨fun i => ⟨if i.val = 0 then 401 else if i.val = 1 then 400 else if i.val = 2 then 402 else 405 + i.val, by
    have := i.isLt
    unfold LNR
    split_ifs <;> omega⟩, by
    intro a b h
    simp only [Fin.mk.injEq] at h
    apply Fin.ext
    split_ifs at h <;> omega⟩

theorem fsK3 : fsK 3 = 408 := rfl
theorem fsK4 : fsK 4 = 409 := rfl
theorem fsK5 : fsK 5 = 410 := rfl
theorem fsK6 : fsK 6 = 411 := rfl
theorem fsK20 : fsK 20 = 425 := rfl
theorem fsK21 : fsK 21 = 426 := rfl

theorem fsK_ne (i : Fin 32) (r : Fin LNR) (hr : r.val = 437 ∨ r.val = 438) : fsK i ≠ r := by
  intro h
  have hv := congrArg Fin.val h
  simp only [fsK, Function.Embedding.coeFn_mk] at hv
  have := i.isLt
  split_ifs at hv <;> omega

theorem fsK_val (i : Fin 32) (hi : 3 ≤ i.val) : (fsK i).val = 405 + i.val := by
  simp only [fsK, Function.Embedding.coeFn_mk]
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]

/-- **The FILTER setup's program.** -/
def fsProg (x : ℕ) : WM (LNS x) LNR :=
  .seq (FsNums.gapX fsK 437 438) (.seq FsRegs.rAW (.seq FsRegs.rBW (.seq FsRegs.rCW (.seq FsRegs.rDW
    (FsWords.wordsW x)))))

/-- The setup's cost. -/
def fsCost (cap : ℕ) : ℕ :=
  120 * UnaryPow.sq cap + 1 + (52 * UnaryPow.sq cap + 1 + (20 * UnaryPow.sq cap + 1 + (22 * UnaryPow.sq cap + 1 +
    (28 * UnaryPow.sq cap + 1 + 2000 * ((cap + 1) * (cap + 1))))))

/-- The registers below `250` the setup writes. -/
def lowOut : List (Fin LNR) := [6, 7, 8, 9, 10, 223, 231, 232, 233, 234, 243, 244, 245, 246, 247]

theorem nmem_low (r : Fin LNR) (hr : r.val < 250) (l : List (Fin LNR))
    (hl : ∀ q ∈ l, 250 ≤ q.val ∨ q ∈ lowOut) (hno : r ∉ lowOut) : r ∉ l := by
  intro hm
  rcases hl r hm with h | h
  · omega
  · exact hno h

theorem fs_exec (x : ℕ) (P : Filters.GapParams) (g L r4 G off : ℕ) (w out u : List Bool) (j : ℕ)
    (σ : WState (LNS x) LNR) (hin : FsIn2 x σ w out j u P.len P.cap P.errExp g r4 G off L) (hU : 1 ≤ P.cap)
    (hc1 : 1 ≤ cap) (hBc : P.cap * 32 + 2 ≤ cap) (hMc : P.len + 8 ≤ cap) (hEc : P.errExp + 4 ≤ cap)
    (hsc : 2 ^ (P.seedBits + 1) ≤ cap) (hlc : P.labelBits + P.fieldBits + P.walkLen + 512 ≤ cap)
    (hcr : 256 * (2 * P.fieldBits + 3 * P.labelBits) + 160 * P.walkLen + 1000 ≤ cap)
    (hc0 : P.fieldBits + P.labelBits + (P.labelBits - 1) + P.prefixBits + L + r4 + G + off + 1000 ≤ cap)
    (hcC : 384 * P.walkLen + 4 * L + 1000 ≤ cap)
    (hcz : P.walkLen * (L * 256 + 258) + 2 * L + (P.walkLen + 1) / 2 + P.walkLen + 1000 ≤ cap)
    (hcL : 256 * L + 1000 ≤ cap)
    (hcw : P.fieldBits + P.labelBits + (P.walkLen - 1) + 128 * (2 * P.fieldBits + 2 * P.labelBits + (P.labelBits - 1)) +
      (2 * (128 * (2 * P.fieldBits + 2 * P.labelBits + (P.labelBits - 1))) + 1) + (P.labelBits + (P.labelBits - 1)) + g +
      2 * (160 * (P.walkLen - 1) + 2 * (128 * (2 * P.fieldBits + 2 * P.labelBits + (P.labelBits - 1)))) +
      2 * P.fieldBits + 2 * P.labelBits + 2 * (P.labelBits + (P.labelBits - 1)) + 1000 ≤ cap) :
    ∃ τ : WState (LNS x) LNR, WExec cap (fsProg x) σ τ (fsCost cap) ∧
      τ.sh = σ.sh ∧ τ.cell = σ.cell ∧ (∀ i, i ∉ FsWords.wordsOut x → τ.st i = σ.st i) ∧
      (∀ r : Fin LNR, r.val < 250 → r ∉ lowOut → τ.val r = 0) ∧
      τ.val 6 = P.fieldBits ∧ τ.val 7 = P.labelBits ∧ τ.val 8 = P.labelBits - 1 ∧ τ.val 9 = P.prefixBits ∧
      τ.val 10 = L ∧ τ.val 223 = P.fieldBits ∧ τ.val 231 = r4 ∧ τ.val 232 = G ∧ τ.val 233 = off ∧ τ.val 234 = L ∧
      τ.val 243 = 4 * L ∧ τ.val 244 = 384 * P.walkLen + 1 ∧ τ.val 245 = (P.walkLen + 1) / 2 ∧
      τ.val 246 = P.walkLen * (L * 256 + 258) + 1 + 2 * L + (P.walkLen + 1) / 2 + 41 ∧
      τ.val 247 = P.walkLen * (L * 256 + 258) + 1 ∧
      τ.st (sk x 91) = List.replicate P.fieldBits true ∧
      τ.st (sk x 25) = List.replicate (128 * (2 * P.fieldBits + 2 * P.labelBits + (P.labelBits - 1))) true ∧
      τ.st (sk x 26) = List.replicate (P.walkLen - 1) true ∧
      τ.st (sk x 27) = List.replicate (2 * (128 * (2 * P.fieldBits + 2 * P.labelBits + (P.labelBits - 1))) + 1) true ∧
      τ.st (sk x 28) = List.replicate (2 * (128 * (2 * P.fieldBits + 2 * P.labelBits + (P.labelBits - 1))) + 1) true ∧
      τ.st (sk x 24) = frame (binary (160 * (P.walkLen - 1) + 2 * (128 * (2 * P.fieldBits + 2 * P.labelBits +
        (P.labelBits - 1)))) g) ∧
      τ.st (sk x 81) = frame (binary P.fieldBits 0) ∧ τ.st (sk x 108) = frame (binary P.fieldBits 0) ∧
      τ.st (sk x 109) = frame (binary P.fieldBits 0) ∧ τ.st (sk x 110) = frame (binary P.fieldBits 0) ∧
      τ.st (sk x 111) = frame (binary P.fieldBits 0) ∧ τ.st (sk x 112) = frame (binary P.fieldBits 0) ∧
      τ.st (sk x 83) = frame (binary P.fieldBits 0) ∧ τ.st (sk x 84) = frame (binary P.fieldBits 0) ∧
      τ.st (sk x 85) = frame (binary P.fieldBits 0) ∧ τ.st (sk x 86) = frame (binary P.fieldBits 0) ∧
      τ.st (sk x 87) = frame (binary P.fieldBits 0) ∧ τ.st (sk x 88) = frame (binary P.labelBits 0) ∧
      τ.st (sk x 89) = frame (binary P.labelBits 0) ∧
      τ.st (sk x 90) = frame (binary (P.labelBits + (P.labelBits - 1)) 0) ∧ τ.st (sk x 151) = [true] := by
  have hz : ∀ i : Fin 32, 3 ≤ i.val → σ.val (fsK i) = 0 := fun i hi =>
    hin.zHigh _ (by rw [fsK_val i hi]; omega)
  have hlb : 1 ≤ P.labelBits := by
    have h1 : 1 ≤ P.prefixBits := Nat.clog_pos (by norm_num) (by omega)
    exact le_trans h1 (le_max_left _ _)
  have hwl : 1 ≤ P.walkLen := by unfold Filters.GapParams.walkLen; omega
  have g1 := FsNums.gapX_spec cap fsK 437 438 (fun i => fsK_ne i _ (Or.inl rfl)) (fun i => fsK_ne i _ (Or.inr rfl))
    (by decide) σ P hin.vCap hin.vLen hin.vErr hz (hin.zHigh _ (by decide)) (hin.zHigh _ (by decide)) hU hc1 hBc hMc hEc
    hsc hlc
  set S1 : WState (LNS x) LNR := ((((((σ.setv (fsK 3) P.prefixBits).setv (fsK 4) P.labelBits).setv
      (fsK 5) P.fieldBits).setv (fsK 6) P.walkLen).setv (fsK 20) P.seedBits).setv (fsK 21) (2 ^ P.seedBits)) with hS1
  have s408 : S1.val 408 = P.prefixBits := by rw [hS1]; simp [Function.update_apply, fsK3, fsK4, fsK5, fsK6, fsK20, fsK21]
  have s409 : S1.val 409 = P.labelBits := by rw [hS1]; simp [Function.update_apply, fsK3, fsK4, fsK5, fsK6, fsK20, fsK21]
  have s410 : S1.val 410 = P.fieldBits := by rw [hS1]; simp [Function.update_apply, fsK3, fsK4, fsK5, fsK6, fsK20, fsK21]
  have s411 : S1.val 411 = P.walkLen := by rw [hS1]; simp [Function.update_apply, fsK3, fsK4, fsK5, fsK6, fsK20, fsK21]
  have sOther : ∀ r : Fin LNR, (r.val < 408 ∨ 427 ≤ r.val) → S1.val r = σ.val r := by
    intro r hr
    have hne : ∀ i : Fin 32, 3 ≤ i.val → i.val ≤ 21 → r ≠ fsK i := fun i hi hi2 h => by
      have := congrArg Fin.val h
      rw [fsK_val i hi] at this
      omega
    rw [hS1]
    simp only [WState.setv_val]
    rw [Function.update_of_ne (hne 21 (by decide) (by decide)), Function.update_of_ne (hne 20 (by decide) (by decide)),
      Function.update_of_ne (hne 6 (by decide) (by decide)), Function.update_of_ne (hne 5 (by decide) (by decide)),
      Function.update_of_ne (hne 4 (by decide) (by decide)), Function.update_of_ne (hne 3 (by decide) (by decide))]
  have sIn : ∀ r : Fin LNR, r.val < 408 → S1.val r = σ.val r := fun r hr => sOther r (Or.inl hr)
  have sZ : ∀ r : Fin LNR, 427 ≤ r.val → S1.val r = 0 := fun r hr => by
    rw [sOther r (Or.inr hr)]
    exact hin.zHigh r (by omega)
  have sLow : ∀ r : Fin LNR, r.val < 250 → S1.val r = 0 := fun r hr => by rw [sIn r (by omega)]; exact hin.zLow r hr
  have st1 : S1.st = σ.st := by rw [hS1]; simp
  have sh1 : S1.sh = σ.sh := by rw [hS1]; simp
  have cl1 : S1.cell = σ.cell := by rw [hS1]; simp
  -- register stage A
  obtain ⟨S2, a2, st2, sh2, cl2, frA, f440, f442, f443, f444, f445, f446, f448⟩ :=
    FsRegs.rA_spec cap S1 P.fieldBits P.labelBits P.walkLen s409 s410 s411
      (sZ _ (by decide)) (sZ _ (by decide)) (sZ _ (by decide)) (sZ _ (by decide)) (sZ _ (by decide))
      (sZ _ (by decide)) (sZ _ (by decide)) (sZ _ (by decide)) (sZ _ (by decide)) (sZ _ (by decide))
      (sZ _ (by decide)) hc1 hlb hwl hcr
  -- register stage B
  obtain ⟨S3, a3, st3, sh3, cl3, frB, f6, f7, f8, f9, f10, f223, f231, f232, f233, f234⟩ :=
    FsRegs.rB_spec cap S2 P.fieldBits P.labelBits (P.labelBits - 1) P.prefixBits L r4 G off
      (by rw [frA _ (by decide), s410]) (by rw [frA _ (by decide), s409]) f445 (by rw [frA _ (by decide), s408])
      (by rw [frA _ (by decide), sIn _ (by decide)]; exact hin.vL)
      (by rw [frA _ (by decide), sIn _ (by decide)]; exact hin.vR4)
      (by rw [frA _ (by decide), sIn _ (by decide)]; exact hin.vG)
      (by rw [frA _ (by decide), sIn _ (by decide)]; exact hin.vOff)
      (by rw [frA _ (by decide), sLow _ (by decide)]) (by rw [frA _ (by decide), sLow _ (by decide)])
      (by rw [frA _ (by decide), sLow _ (by decide)]) (by rw [frA _ (by decide), sLow _ (by decide)])
      (by rw [frA _ (by decide), sLow _ (by decide)]) (by rw [frA _ (by decide), sLow _ (by decide)])
      (by rw [frA _ (by decide), sLow _ (by decide)]) (by rw [frA _ (by decide), sLow _ (by decide)])
      (by rw [frA _ (by decide), sLow _ (by decide)]) (by rw [frA _ (by decide), sLow _ (by decide)])
      (by rw [frA _ (by decide), sZ _ (by decide)]) hc1 hc0
  -- register stage C
  obtain ⟨S4, a4, st4, sh4, cl4, frC, f243, f244, f245, f448', f462⟩ :=
    FsRegs.rC_spec cap S3 L P.walkLen
      (by rw [frB _ (by decide), frA _ (by decide), sIn _ (by decide)]; exact hin.vL)
      (by rw [frB _ (by decide), frA _ (by decide), s411])
      (by rw [frB _ (by decide), frA _ (by decide), sLow _ (by decide)])
      (by rw [frB _ (by decide), frA _ (by decide), sLow _ (by decide)])
      (by rw [frB _ (by decide), frA _ (by decide), sLow _ (by decide)])
      (by rw [frB _ (by decide), f448])
      (by rw [frB _ (by decide), frA _ (by decide), sZ _ (by decide)])
      (by rw [frB _ (by decide), frA _ (by decide), sZ _ (by decide)])
      (by rw [frB _ (by decide), frA _ (by decide), sZ _ (by decide)])
      (by rw [frB _ (by decide), frA _ (by decide), sZ _ (by decide)]) hc1 hcC
  -- register stage D
  obtain ⟨S5, a5, st5, sh5, cl5, frD, f247, f246, f461, f448''⟩ :=
    FsRegs.rD_spec cap S4 L P.walkLen ((P.walkLen + 1) / 2) (L * 256 + 258)
      (by rw [frC _ (by decide), frB _ (by decide), frA _ (by decide), sIn _ (by decide)]; exact hin.vL)
      (by rw [frC _ (by decide), frB _ (by decide), frA _ (by decide), s411]) f245
      (by rw [frC _ (by decide), frB _ (by decide), frA _ (by decide), sLow _ (by decide)])
      (by rw [frC _ (by decide), frB _ (by decide), frA _ (by decide), sLow _ (by decide)])
      f448' (by rw [frC _ (by decide), frB _ (by decide), frA _ (by decide), sZ _ (by decide)])
      (by rw [frC _ (by decide), frB _ (by decide), frA _ (by decide), sZ _ (by decide)])
      (by rw [frC _ (by decide), frB _ (by decide), frA _ (by decide), sZ _ (by decide)])
      (by rw [frC _ (by decide), frB _ (by decide), frA _ (by decide), sZ _ (by decide)])
      rfl hc1 (by omega) hcL
  -- the words
  have st5' : S5.st = σ.st := by rw [st5, st4, st3, st2, st1]
  have sh5' : S5.sh = σ.sh := by rw [sh5, sh4, sh3, sh2, sh1]
  obtain ⟨S6, a6, v6, sh6, cl6, frW, w91, w25, w26, w27, w28, w24, w81, w108, w109, w110, w111, w112, w83, w84, w85, w86, w87, w88, w89, w90, w151⟩ :=
    FsWords.words_spec cap x S5 P.fieldBits P.labelBits (P.walkLen - 1)
      (128 * (2 * P.fieldBits + 2 * P.labelBits + (P.labelBits - 1)))
      (2 * (128 * (2 * P.fieldBits + 2 * P.labelBits + (P.labelBits - 1))) + 1)
      (160 * (P.walkLen - 1) + 2 * (128 * (2 * P.fieldBits + 2 * P.labelBits + (P.labelBits - 1)))) g
      (P.labelBits + (P.labelBits - 1))
      (by rw [frD _ (by decide), frC _ (by decide), frB _ (by decide), frA _ (by decide), s410])
      (by rw [frD _ (by decide), frC _ (by decide), frB _ (by decide), frA _ (by decide), s409])
      (by rw [frD _ (by decide), frC _ (by decide), frB _ (by decide), f440])
      (by rw [frD _ (by decide), frC _ (by decide), frB _ (by decide), f442])
      (by rw [frD _ (by decide), frC _ (by decide), frB _ (by decide), f444])
      (by rw [frD _ (by decide), frC _ (by decide), frB _ (by decide), f443])
      (by rw [frD _ (by decide), frC _ (by decide), frB _ (by decide), frA _ (by decide), sIn _ (by decide)];
          exact hin.vSeed)
      (by rw [frD _ (by decide), frC _ (by decide), frB _ (by decide), f446])
      (by rw [frD _ (by decide), frC _ (by decide), frB _ (by decide), frA _ (by decide), sZ _ (by decide)])
      (by rw [frD _ (by decide), frC _ (by decide), frB _ (by decide), frA _ (by decide), sZ _ (by decide)])
      (by rw [frD _ (by decide), frC _ (by decide), frB _ (by decide), frA _ (by decide), sZ _ (by decide)])
      (by rw [frD _ (by decide), frC _ (by decide), frB _ (by decide), frA _ (by decide), sZ _ (by decide)])
      (by rw [frD _ (by decide), frC _ (by decide), frB _ (by decide), frA _ (by decide), sZ _ (by decide)])
      (by rw [frD _ (by decide), frC _ (by decide), frB _ (by decide), frA _ (by decide), sZ _ (by decide)])
      (by rw [frD _ (by decide), frC _ (by decide), frB _ (by decide), frA _ (by decide), sZ _ (by decide)])
      (by rw [frD _ (by decide), frC _ (by decide), frB _ (by decide), frA _ (by decide), sZ _ (by decide)])
      (by rw [frD _ (by decide), frC _ (by decide), frB _ (by decide), frA _ (by decide), sZ _ (by decide)])
      (by rw [frD _ (by decide), frC _ (by decide), frB _ (by decide), frA _ (by decide), sZ _ (by decide)])
      (fun q h0 h1 h2 h113 => by rw [st5', sh5']; exact hin.blank q h0 h1 h2 h113) hcw
  refine ⟨S6, WExec.seq g1 (WExec.seq a2 (WExec.seq a3 (WExec.seq a4 (WExec.seq a5 a6)))), ?_, ?_, ?_, ?_, ?_⟩
  · rw [sh6, sh5']
  · rw [cl6, cl5, cl4, cl3, cl2, cl1]
  · intro i hi
    rw [frW i hi, st5']
  · intro r hr hno
    rw [v6, frD r (nmem_low r hr _ (by decide) hno), frC r (nmem_low r hr _ (by decide) hno),
      frB r (nmem_low r hr _ (by decide) hno), frA r (nmem_low r hr _ (by decide) hno)]
    exact sLow r hr
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [v6, frD _ (by decide), frC _ (by decide), f6]
  · rw [v6, frD _ (by decide), frC _ (by decide), f7]
  · rw [v6, frD _ (by decide), frC _ (by decide), f8]
  · rw [v6, frD _ (by decide), frC _ (by decide), f9]
  · rw [v6, frD _ (by decide), frC _ (by decide), f10]
  · rw [v6, frD _ (by decide), frC _ (by decide), f223]
  · rw [v6, frD _ (by decide), frC _ (by decide), f231]
  · rw [v6, frD _ (by decide), frC _ (by decide), f232]
  · rw [v6, frD _ (by decide), frC _ (by decide), f233]
  · rw [v6, frD _ (by decide), frC _ (by decide), f234]
  · rw [v6, frD _ (by decide), f243]
  · rw [v6, frD _ (by decide), f244]
  · rw [v6, frD _ (by decide), f245]
  · rw [v6, f246]
  · rw [v6, f247]
  exact ⟨w91, w25, w26, w27, w28, w24, w81, w108, w109, w110, w111, w112, w83, w84, w85, w86, w87, w88, w89, w90, w151⟩

end NearCubicWires.WireExponent3_5.UnionMachine.FsRun
