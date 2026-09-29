import Proof.Wire_3_5.FinalPass.SymF3
import Proof.Wire_3_5.Primitive.Writers.PopSetupReady

/-! # SWf (the SYM words writer's flat tables), part 4: the table-ready state from PA's POP setup program

PA's POP setup program `PopSetupRun.popProg` (the flat list's numbers, then the walk bank's inputs at the list seed and
C5's builder entry words) runs from `PopIn` at the polynomial need `runNeed` (`PopSetupReady.pop_run`); `PopSetupSpec` wraps the same program with the POP row's need `popNeed`, whose measure holds `(8L+2)^{3·lbP+1}` (the
POP row's counting capacity), which a flat table never needs. **`tab_ready`**: after `popProg`, at every capacity above
`runNeed` and the two table capacities, the state is `TabReady` at the list seed `(flatSeedEquiv Pl).symm f` (the
facts derived exactly as in `PopSetupReady.pop_ready`), the request, output and counter kept, the emission's
registers (`off`, the walk length, `J`, `L`) in place and the registers `83 … 198` zero.

Paper quantity of the main type: the table builder's entry at list seed `f` of the flat list `(M, B, errExp)` (the walk
sample's index word, P3:1505-1510). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace NearCubicWires.WireExponent3_5.FinalPass.SymF
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.SignedSortKey NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimAsm NearCubicWires.WireExponent3_5.PrimAsm.SymLayout
open NearCubicWires.WireExponent3_5.PrimAsm.PopSetupRun NearCubicWires.WireExponent3_5.Lists
open NearCubicWires.WireExponent3_5.FinalPass.Flat NearCubicWires.WireExponent3_5.PrimT.WalkBank
open NearCubicWires.WireExponent3_5.PrimAsm.PopSetupReady NearCubicWires.WireExponent3_5.PrimAsm.PopPipe

variable (cap : ℕ) (W : WalkBankProducer)

/-- **The table-ready state from PA's POP setup program.** -/
theorem tab_ready (Pl : FlatListParams) (f : ℕ) (hf : f < Fintype.card Pl.FlatSeed) (L off : ℕ)
    (w out u : List Bool) (j : ℕ) (σ : WState (LNS W.x) LNR)
    (hN : runNeed Pl.M Pl.B Pl.errExp f 0 0 0 0 off L ≤ cap)
    (hcapC : 8 * sideB Pl.base.rank + 8 * Pl.base.rank + 8 ≤ cap)
    (hO : (2 * (Pl.errExp / 4) + 1) * (1 + (Pl.base.J + 1) * (2 * L + 1)) + 7 < cap)
    (hin : PopSetup.PopIn W.x σ w out j u Pl.M Pl.B Pl.errExp f 0 0 0 0 off L) :
    ∃ τ : WState (LNS W.x) LNR, WExec cap (popProg W.x) σ τ (popCost cap) ∧
      τ.st (sk W.x 0) = frame w ∧ τ.st (sk W.x 1) = out ++ [false] ∧ τ.sh (sk W.x 1) = out.length ∧
      τ.st (sk W.x 2) = List.replicate j true ∧ τ.sh (sk W.x 2) = 0 ∧
      TabReady cap W τ Pl ((PrimAsm.Enum.flatSeedEquiv Pl).symm ⟨f, hf⟩) L (PopSetup.popRW Pl) (PopSetup.popRW Pl) ∧
      τ.val eOff = off ∧ τ.val eW = Pl.walkLen ∧ τ.val eJ = Pl.base.J ∧ τ.val eL = L ∧
      (∀ q : Fin LNR, 83 ≤ q.val → q.val < 199 → τ.val q = 0) := by
  have hc1 : 1 ≤ cap := by unfold runNeed at hN; omega
  obtain ⟨τ, hx, hcl, hsh, hfr, w25, w26, w27, w28, w24, w8, w14, w15, w16, w9, w150, v6, v7, v8, v10, v15, v20, v21,
    v22, v23, v39, v40, v63, v64, v69, v71, v72, v82, v199, hlow⟩ :=
      pop_run cap W.x σ w out u j Pl.M Pl.B Pl.errExp f 0 0 0 0 off L hin hc1 hN
  have kept : ∀ k : Fin 161, k.val ∉ [25, 26, 27, 28, 24, 8, 14, 15, 16, 9, 150] →
      τ.st (sk W.x k) = σ.st (sk W.x k) := fun k hk => hfr _ (fun h => hk (by
        have := List.mem_map_of_mem (f := Fin.val) h
        rwa [pwOut_val, sk_val] at this))
  have heads : ∀ i, τ.sh i = σ.sh i := fun i => by rw [hsh]
  have blank : ∀ k : Fin 161, k.val ≠ 0 → k.val ≠ 1 → k.val ≠ 2 → k.val ≠ 113 →
      k.val ∉ [25, 26, 27, 28, 24, 8, 14, 15, 16, 9, 150] → τ.st (sk W.x k) = [] ∧ τ.sh (sk W.x k) = 0 :=
    fun k h0 h1 h2 h3 hw => ⟨by rw [kept k hw]; exact (hin.blank k h0 h1 h2 h3).1,
      by rw [heads]; exact (hin.blank k h0 h1 h2 h3).2⟩
  have zh : ∀ k : Fin 161, k.val ≠ 0 → k.val ≠ 1 → k.val ≠ 2 → k.val ≠ 113 → τ.sh (sk W.x k) = 0 :=
    fun k h0 h1 h2 h3 => by rw [heads]; exact (hin.blank k h0 h1 h2 h3).2
  obtain ⟨hpad, hps, hsd, hlb, hnJ⟩ := PopSetupMath.rank_facts Pl
  have hrk : pRk Pl.M Pl.B = Pl.base.rank := rfl
  have hsb : pSb Pl.M Pl.B = sideB Pl.base.rank := sb_eq _ hlb
  have hpb : pPad Pl.M Pl.B = padB Pl.base.rank := pad_eq _ hlb
  have hpm : 2 * sideB Pl.base.rank - padB Pl.base.rank = Pl.base.rank + Pl.base.rank + Pl.base.rank - 1 :=
    pmw_len _ hlb
  set e := (PrimAsm.Enum.flatSeedEquiv Pl).symm ⟨f, hf⟩ with he
  have hidx : seedIndexWord (sideB Pl.base.rank) (2 * (Pl.errExp / 4)) e =
      binary (160 * (2 * (Pl.errExp / 4)) + 2 * sideB Pl.base.rank) f := by
    unfold seedIndexWord
    have e1 : (SupplierWalkBridge.positiveWalkSampleFinEquiv (2 ^ sideB Pl.base.rank) (2 * (Pl.errExp / 4)) e).val = f := by
      show ((PrimAsm.Enum.flatSeedEquiv Pl) ((PrimAsm.Enum.flatSeedEquiv Pl).symm ⟨f, hf⟩)).val = f
      rw [Equiv.apply_symm_apply]
    rw [e1]
  have hwid : pWid Pl.M Pl.B Pl.errExp = 160 * (2 * (Pl.errExp / 4)) + 2 * sideB Pl.base.rank := by
    unfold pWid pN; rw [hsb]; ring
  have hports : ∀ jj : Fin 14, τ.st (sk W.x (portT jj)) = inPorts (sideB Pl.base.rank) (2 * (Pl.errExp / 4))
      (PopSetup.popRW Pl) (PopSetup.popRW Pl) (seedIndexWord (sideB Pl.base.rank) (2 * (Pl.errExp / 4)) e) jj := by
    intro jj
    fin_cases jj
    all_goals first
      | exact (blank _ (by decide) (by decide) (by decide) (by decide) (by decide)).1
      | skip
    · show τ.st (sk W.x 24) = frame (seedIndexWord (sideB Pl.base.rank) (2 * (Pl.errExp / 4)) e)
      rw [hidx, w24, hwid]
    · show τ.st (sk W.x 25) = List.replicate (sideB Pl.base.rank) true
      rw [w25, hsb]
    · show τ.st (sk W.x 26) = List.replicate (2 * (Pl.errExp / 4)) true
      rw [w26]; rfl
    · show τ.st (sk W.x 27) = List.replicate (PopSetup.popRW Pl) true
      rw [w27, hsb]; unfold PopSetup.popRW; congr 1; omega
    · show τ.st (sk W.x 28) = List.replicate (PopSetup.popRW Pl) true
      rw [w28, hsb]; unfold PopSetup.popRW; congr 1; omega
  have hh : ∀ jj : Fin 14, τ.sh (sk W.x (portT jj)) = 0 := by
    intro jj
    fin_cases jj <;> exact zh _ (by decide) (by decide) (by decide) (by decide)
  have hC5 : ∀ i : Fin 12, i.val ≠ 0 → i.val ≠ 2 →
      τ.st (fsC W.x i) = (PopPipe.yC Pl e L (PopSetup.popRW Pl) (PopSetup.popRW Pl)).st i ∧ τ.sh (fsC W.x i) = 0 := by
    intro i h0 h2
    fin_cases i
    · exact absurd rfl h0
    · refine ⟨?_, zh 6 (by decide) (by decide) (by decide) (by decide)⟩
      show τ.st (sk W.x 6) = (PopPipe.yC Pl e L (PopSetup.popRW Pl) (PopSetup.popRW Pl)).st 1
      rw [yC_st1]
      exact (blank 6 (by decide) (by decide) (by decide) (by decide) (by decide)).1
    · exact absurd rfl h2
    · refine ⟨?_, zh 8 (by decide) (by decide) (by decide) (by decide)⟩
      show τ.st (sk W.x 8) = (PopPipe.yC Pl e L (PopSetup.popRW Pl) (PopSetup.popRW Pl)).st 3
      rw [yC_st3, w8, hrk, hpm, PopSetupReady.binary_zero', ← frame_eq_frameP]
    · refine ⟨?_, zh 9 (by decide) (by decide) (by decide) (by decide)⟩
      show τ.st (sk W.x 9) = (PopPipe.yC Pl e L (PopSetup.popRW Pl) (PopSetup.popRW Pl)).st 4
      rw [yC_st4, w9]; rfl
    · refine ⟨?_, zh 10 (by decide) (by decide) (by decide) (by decide)⟩
      show τ.st (sk W.x 10) = (PopPipe.yC Pl e L (PopSetup.popRW Pl) (PopSetup.popRW Pl)).st 5
      rw [yC_st5]
      exact (blank 10 (by decide) (by decide) (by decide) (by decide) (by decide)).1
    · refine ⟨?_, zh 11 (by decide) (by decide) (by decide) (by decide)⟩
      show τ.st (sk W.x 11) = (PopPipe.yC Pl e L (PopSetup.popRW Pl) (PopSetup.popRW Pl)).st 6
      rw [yC_st6]
      exact (blank 11 (by decide) (by decide) (by decide) (by decide) (by decide)).1
    · refine ⟨?_, zh 12 (by decide) (by decide) (by decide) (by decide)⟩
      show τ.st (sk W.x 12) = (PopPipe.yC Pl e L (PopSetup.popRW Pl) (PopSetup.popRW Pl)).st 7
      rw [yC_st7]
      exact (blank 12 (by decide) (by decide) (by decide) (by decide) (by decide)).1
    · refine ⟨?_, zh 13 (by decide) (by decide) (by decide) (by decide)⟩
      show τ.st (sk W.x 13) = (PopPipe.yC Pl e L (PopSetup.popRW Pl) (PopSetup.popRW Pl)).st 8
      rw [yC_st8]
      exact (blank 13 (by decide) (by decide) (by decide) (by decide) (by decide)).1
    · refine ⟨?_, zh 14 (by decide) (by decide) (by decide) (by decide)⟩
      show τ.st (sk W.x 14) = (PopPipe.yC Pl e L (PopSetup.popRW Pl) (PopSetup.popRW Pl)).st 9
      rw [yC_st9, w14]; rfl
    · refine ⟨?_, zh 15 (by decide) (by decide) (by decide) (by decide)⟩
      show τ.st (sk W.x 15) = (PopPipe.yC Pl e L (PopSetup.popRW Pl) (PopSetup.popRW Pl)).st 10
      rw [yC_st10, w15, hrk, hpm, bw_zero _ hlb, PopSetupReady.binary_zero', ← frame_eq_frameP]
    · refine ⟨?_, zh 16 (by decide) (by decide) (by decide) (by decide)⟩
      show τ.st (sk W.x 16) = (PopPipe.yC Pl e L (PopSetup.popRW Pl) (PopSetup.popRW Pl)).st 11
      rw [yC_st11, w16, hrk, hpm, ep_zero _ hlb, PopSetupReady.binary_zero', ← frame_eq_frameP]
  have hC5r : ∀ r : Fin 19, τ.val (frC r) = (PopPipe.yC Pl e L (PopSetup.popRW Pl) (PopSetup.popRW Pl)).val r := by
    intro r
    rw [yC_val]
    fin_cases r
    all_goals first
      | (rw [hlow _ (by decide) (by decide)]; rfl)
      | skip
    · show τ.val 6 = sideB Pl.base.rank; rw [v6, hsb]
    · show τ.val 7 = Pl.base.rank; rw [v7]; rfl
    · show τ.val 8 = Pl.base.rank - 1; rw [v8]; rfl
    · show τ.val 10 = L; rw [v10]
    · show τ.val 15 = padB Pl.base.rank; rw [v15, hpb]
  refine ⟨τ, hx, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [kept 0 (by decide)]; exact hin.s0
  · rw [kept 1 (by decide)]; exact hin.s1
  · rw [heads]; exact hin.h1
  · rw [kept 2 (by decide)]; exact hin.s2
  · rw [heads]; exact hin.h2
  · exact
      { hRW := le_rfl
        hLW := le_rfl
        hpad := hpad
        hps := hps
        hsd := hsd
        hlb := hlb
        hnJ := hnJ
        hcapC := hcapC
        hO := hO
        hin := hports
        hh := hh
        hsc := fun k => by
          rw [hfr _ (fun h => by
            have := List.mem_map_of_mem (f := Fin.val) h
            rw [pwOut_val, sT_val] at this
            simp only [List.mem_cons, List.not_mem_nil, or_false] at this
            omega)]
          exact (hin.blankT k).1
        hsh := fun k => by rw [heads]; exact (hin.blankT k).2
        hC5 := hC5
        hC5r := hC5r
        hcell := by rw [hcl, hin.cell]; rfl }
  · rw [show eOff = (22 : Fin LNR) from Fin.ext rfl]; exact v22
  · rw [show eW = (71 : Fin LNR) from Fin.ext rfl, v71]; rfl
  · rw [show eJ = (40 : Fin LNR) from Fin.ext rfl, v40]; rfl
  · rw [show eL = (23 : Fin LNR) from Fin.ext rfl]; exact v23
  · intro q h1 h2
    refine hlow _ (by omega) (fun h => ?_)
    have := lowOut_vals _ h
    omega

end NearCubicWires.WireExponent3_5.FinalPass.SymF
