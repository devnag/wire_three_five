import Proof.Wire_3_5.Primitive.SeedFix.CtrEmit

/-! # X3, part 8: one position of the second pass (P3:1206-1216)

"A fixed linear basis of each code gives polynomial-time encoding" (P3:1216): at position `q` of a block, the second
pass emits `encB P zb q ⊕ offset`: at a data position the next data bit (`enc_data`), at a parity position `2^u − 1`
the parity bit `u`, the low bit of the packed `rgPAR` (`enc_par`). Here: `P2H` (the pass's fixed hypotheses: the
data bits on the stream, the offset, the center's bits `Tl[k0 + q] = encB P zb q ⊕ offset`), `P2S` (the state at
position `q`), `p2Data_spec`, `p2Par_spec`, **`p2Mid_spec`**.

Paper quantity of the main types: the center's coordinates `Tl[k0 + q]` of one block. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace NearCubicWires.WireExponent3_5.PrimT.Ctr
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.Shared
open NearCubicWires.WireExponent3_5.PrimT.C4Geo

/-- The second pass's fixed hypotheses. -/
structure P2H (P : StarParams) (zb : ℕ → Bool) (R : Fin 4) (cnt : Fin 26) (σ0 : CS) (b0 k0 : ℕ)
    (Tl offL : List Bool) : Prop where
  rc : (R = zRow ∧ cnt = rgROWC) ∨ (R = zCol ∧ cnt = rgCOLC)
  dat : ∀ m < dB P, readTapeBit (σ0.st R) (b0 + 2 * m + 1) = zb m
  off : σ0.st zOff = frameP offL ++ [false]
  tl : ∀ q < P.b, Tl.getD (k0 + q) false = xor (encB P zb q) (offL.getD (k0 + q) false)
  ko : k0 + P.b ≤ offL.length
  kt : k0 + P.b ≤ Tl.length

/-- The registers the second pass uses (`cnt` the stream's counter). -/
abbrev p2Regs (cnt : Fin 26) : List (Fin 26) :=
  [rgKQ, rgNP, rgE, rgPAR, rgZ, rgBIT, rgHQ, rgT, rgT2, cnt, rgOC, rgOFFC]

/-- **The second pass's state** after `q` positions. -/
structure P2S (P : StarParams) (zb : ℕ → Bool) (R : Fin 4) (cnt : Fin 26) (σ0 : CS) (b0 c0 k0 : ℕ)
    (Tl Y0 : List Bool) (q : ℕ) (τ : CS) : Prop where
  par : τ.val rgPAR = packB ((parL P zb).drop (npar P q))
  z : τ.val rgZ = 0
  bit : τ.val rgBIT = 0
  hq : τ.val rgHQ = 0
  tt : τ.val rgT = 0
  t2 : τ.val rgT2 = 0
  shR : τ.sh R = b0 + 2 * nd P q
  cn : τ.val cnt = c0 + 2 * nd P q
  out : OutAt Tl Y0 (k0 + q) τ
  st : ∀ i, i ≠ zCtr → τ.st i = σ0.st i
  sh : ∀ i, i ≠ zCtr → i ≠ zOff → i ≠ R → τ.sh i = σ0.sh i
  oth : ∀ r, r ∉ p2Regs cnt → τ.val r = σ0.val r
  cell : τ.cell = σ0.cell

theorem rc_ne {R : Fin 4} {cnt : Fin 26} (h : (R = zRow ∧ cnt = rgROWC) ∨ (R = zCol ∧ cnt = rgCOLC)) :
    R ≠ zCtr ∧ R ≠ zOff ∧ (∀ r, r ≠ rgROWC → r ≠ rgCOLC → r ≠ cnt) := by
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact ⟨by decide, by decide, fun r h1 _ e => h1 e⟩
  · exact ⟨by decide, by decide, fun r _ h2 e => h2 e⟩

theorem packB_drop_lt (l : List Bool) (k : ℕ) : packB (l.drop k) < 2 ^ l.length := by
  have h1 := packB_lt (l.drop k)
  have h2 : 2 ^ (l.drop k).length ≤ 2 ^ l.length := Nat.pow_le_pow_right (by norm_num) (by simp)
  omega

theorem parL_length (P : StarParams) (zb : ℕ → Bool) : (parL P zb).length = P.s := by simp [parL]

section Pass2
variable (cap : ℕ)

/-- A data position of the second pass. -/
def p2Data (R : Fin 4) (cnt : Fin 26) : CM := .seq (readB R cnt) (.seq (emitX rgZ) (WM.clear rgZ))

theorem p2Data_spec (P : StarParams) (zb : ℕ → Bool) (R : Fin 4) (cnt : Fin 26) (σ0 : CS) (b0 c0 k0 : ℕ)
    (Tl offL Y0 : List Bool) (hH : P2H P zb R cnt σ0 b0 k0 Tl offL) (q : ℕ) (hq : q < P.b) (τ : CS)
    (hS : P2S P zb R cnt σ0 b0 c0 k0 Tl Y0 q τ) (hd : isPar P q = false)
    (hc1 : c0 + 2 * dB P + 2 ≤ cap) (hc2 : 2 * (k0 + P.b) + 2 ≤ cap) :
    ∃ τ', WExec cap (p2Data R cnt) τ τ' 70 ∧ P2S P zb R cnt σ0 b0 c0 k0 Tl Y0 (q + 1) τ' ∧
      τ'.val rgNP = τ.val rgNP ∧ τ'.val rgE = τ.val rgE ∧ τ'.val rgKQ = τ.val rgKQ := by
  obtain ⟨hRC, hRO, hcn⟩ := rc_ne hH.rc
  have hn : nd P (q + 1) = nd P q + 1 := by rw [nd_succ, if_neg (by simp [hd])]
  have hnp : npar P (q + 1) = npar P q := by rw [npar_succ, if_neg (by simp [hd])]; rfl
  have hlt : nd P q < dB P := by
    have h1 := nd_mono P (show q + 1 ≤ P.b by omega)
    rw [hn, nd_b] at h1
    omega
  obtain ⟨τ1, e1, a1, z1, w1, s1, o1, v1, c1⟩ := readB_spec cap R cnt (hcn rgZ (by decide) (by decide)).symm τ
    hS.z (by rw [hS.cn]; omega) (by omega)
  have hbit : readTapeBit (τ.st R) (τ.sh R + 1) = zb (nd P q) := by
    rw [hS.st R hRC, hS.shR]; exact hH.dat _ hlt
  rw [hbit] at z1
  have hout1 : OutAt Tl Y0 (k0 + q) τ1 := by
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · rw [s1]; exact hS.out.st
    · rw [o1 zCtr (Ne.symm hRC)]; exact hS.out.sh
    · rw [v1 rgOC (by decide) (hcn rgOC (by decide) (by decide))]; exact hS.out.oc
    · rw [o1 zOff (Ne.symm hRO)]; exact hS.out.osh
    · rw [v1 rgOFFC (by decide) (hcn rgOFFC (by decide) (by decide))]; exact hS.out.ofc
  obtain ⟨τ2, e2, out2, so2, st2, v2, c2⟩ := emit_step cap Tl offL Y0 (k0 + q) rgZ (by decide) (by decide) τ1 hout1
    (by rw [s1, hS.st zOff (by decide), hH.off]) (by have := hH.ko; omega) (by have := hH.kt; omega)
    (zb (nd P q)) z1 (by rw [hH.tl q hq, enc_data P zb q hq hd]) (by omega)
  have e3 := wclear_spec cap rgZ (τ2.val rgZ) τ2 rfl
    (by rw [v2 rgZ (by decide) (by decide), z1]; have := Bool.toNat_le (zb (nd P q)); omega)
  have hz2 : τ2.val rgZ ≤ 1 := by rw [v2 rgZ (by decide) (by decide), z1]; exact Bool.toNat_le _
  have g : ∀ r, r ≠ rgZ → r ≠ rgOC → r ≠ rgOFFC → r ≠ cnt → (τ2.setv rgZ 0).val r = τ.val r := by
    intro r r1 r2 r3 r4
    simp only [WState.setv_val, Function.update_apply, if_neg r1]
    rw [v2 r r2 r3, v1 r r1 r4]
  refine ⟨_, WExec.mono (WExec.seq e1 (WExec.seq e2 e3)) (by omega), ?_, ?_, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [g rgPAR (by decide) (by decide) (by decide) (hcn rgPAR (by decide) (by decide)), hnp]; exact hS.par
    · simp
    · rw [g rgBIT (by decide) (by decide) (by decide) (hcn rgBIT (by decide) (by decide))]; exact hS.bit
    · rw [g rgHQ (by decide) (by decide) (by decide) (hcn rgHQ (by decide) (by decide))]; exact hS.hq
    · rw [g rgT (by decide) (by decide) (by decide) (hcn rgT (by decide) (by decide))]; exact hS.tt
    · rw [g rgT2 (by decide) (by decide) (by decide) (hcn rgT2 (by decide) (by decide))]; exact hS.t2
    · simp only [WState.setv_sh]
      rw [(st2 R hRC hRO).2, a1, hS.shR, hn]; ring
    · have hcz : cnt ≠ rgZ := (hcn rgZ (by decide) (by decide)).symm
      have hco : cnt ≠ rgOC := (hcn rgOC (by decide) (by decide)).symm
      have hcf : cnt ≠ rgOFFC := (hcn rgOFFC (by decide) (by decide)).symm
      simp only [WState.setv_val, Function.update_apply, if_neg hcz]
      rw [v2 cnt hco hcf, w1, hS.cn, hn]; ring
    · have e : k0 + (q + 1) = k0 + q + 1 := by ring
      rw [e]
      exact ⟨by simpa using out2.st, by simpa using out2.sh, by simpa using out2.oc, by simpa using out2.osh,
        by simpa using out2.ofc⟩
    · intro i hi
      simp only [WState.setv_st]
      by_cases h0 : i = zOff
      · subst h0; rw [so2, s1]; exact hS.st zOff (by decide)
      · rw [(st2 i hi h0).1, s1]; exact hS.st i hi
    · intro i i1 i2 i3
      simp only [WState.setv_sh]
      rw [(st2 i i1 i2).2, o1 i i3]; exact hS.sh i i1 i2 i3
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      rw [g r hr.2.2.2.2.1 hr.2.2.2.2.2.2.2.2.2.2.1 hr.2.2.2.2.2.2.2.2.2.2.2 hr.2.2.2.2.2.2.2.2.2.1]
      exact hS.oth r (by simp [hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2.1, hr.2.2.2.2.2.1, hr.2.2.2.2.2.2.1,
        hr.2.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2.2.2.2.1,
        hr.2.2.2.2.2.2.2.2.2.2.2])
    · simp only [WState.setv_cell]; rw [c2, c1]; exact hS.cell
  · rw [g rgNP (by decide) (by decide) (by decide) (hcn rgNP (by decide) (by decide))]
  · rw [g rgE (by decide) (by decide) (by decide) (hcn rgE (by decide) (by decide))]
  · rw [g rgKQ (by decide) (by decide) (by decide) (hcn rgKQ (by decide) (by decide))]

end Pass2

end NearCubicWires.WireExponent3_5.PrimT.Ctr
