import Lean
import Proof.Wire_3_5.UnionMachine.NumsC4
import Proof.Wire_3_5.Primitive.Writers.CopyNat
import Statement_Wire_3_5
import Proof.Wire_3_5.FinalPass.PlanFP
import Proof.Wire_3_5.FinalPass.SdR2
import Proof.Wire_3_5.Assembly.Gate0
import Proof.Wire_3_5.Primitive.Writers.CallIndexR
import Proof.Wire_3_5.Primitive.Writers.Plan
import Proof.Wire_3_5.Assembly.Split
import Proof.Wire_3_5.UnionMachine.NumsPh2
import Proof.Wire_3_5.UnionMachine.NumsC5Base


noncomputable section
set_option maxRecDepth 4096


/-! # NW phase (c), part 5: the front's run and `cProg`'s run at a request

At a request `r` of the family, from the writer's entry: `readNatM` reads `n` (the input is `frame (natWord n ++ …)`,
`NumsX.frame_split`), one step and a test read the mode bit (`mode_bit`), and `rest_run` finishes. The result: `n`,
`mOf r`, `eOf r`, `Sd.R.Tf r` in `rN`, `rM`, `rE`, `rT`, every other register as at the entry, the heads at `0`, the
streams and the cell kept.

* `fpIn_split`, `frontCost`, **`cProg_run`**.

Paper quantities of the main type: `n`, the mode, `n − k`, `T_f` at a request (P3:3044-3048). -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.UnionMachine.NumsC
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimAsm
open NearCubicWires.WireExponent3_5.PrimAsm.SymLayout NearCubicWires.WireExponent3_5.UnionMachine.NumsPh2
open NearCubicWires.WireExponent3_5.Split NearCubicWires.WireExponent3_5.PrimAsm.Plan
open NearCubicWires.WireExponent3_5.FinalPass.PlanFP
open NearCubicWires.RepairOrdinary.Streaming (marks)

section Req
variable (l : Literals) (F : GateFree l) (kclk coef A a : ℕ) (ha : a ≤ kclk + 1)

theorem fpIn_split (r : FReq l F kclk coef A a ha) :
    ∃ tl, fpIn l F kclk coef A a ha r = RepairRepresentation.natWord r.1.n ++
      ((match r.1.mode with | .thr => true | .sym => false) :: tl) :=
  ⟨_, by simp only [fpIn, PrimRequest.word, List.append_assoc, List.cons_append]; rfl⟩

/-- **Phase (c)'s program at a request**: from the entry, the four numbers in their registers. -/
theorem cProg_run (x cap : ℕ) (r : FReq l F kclk coef A a ha) (σ : St x) (hE : Entry x l F kclk coef A a ha r σ)
    (hc1 : 4 * r.1.n + 4 ≤ cap)
    (hTf : FinalPass.Sd.R.Tf l F kclk coef A a ha r ≤ cap) (hcS : 4 * (r.1.n + 3) + 2 * F.cr + 20 ≤ cap) :
    ∃ c, WExec cap (cProg x F.cr (FinalPass.Sd.R.KT l F) (FinalPass.Sd.R.ZT l F)) σ
      (((((σ.seth (sIn x) 0).setv rN r.1.n).setv rM (mOf l F kclk coef A a ha r)).setv rE
        (eOf l F kclk coef A a ha r)).setv rT (FinalPass.Sd.R.Tf l F kclk coef A a ha r)) c ∧
      c ≤ frontCost r.1.n + 1 + restCost r.1.n F.cr (((gate0 l F).budget kclk coef A a ha).kOf r.1.n)
        (FinalPass.Sd.R.KT l F) (FinalPass.Sd.R.ZT l F) (FinalPass.Sd.R.Tf l F kclk coef A a ha r) := by
  have hs : (callInputs l F kclk coef A a ha).StarAt r.1.n := r.2.2.2.2.2.2.1
  obtain ⟨P, hPd⟩ : ∃ p, p = (callInputs l F kclk coef A a ha).starParams r.1.n hs := ⟨_, rfl⟩
  have hPn : P.n = r.1.n := by rw [hPd]; rfl
  have hrP : P.r = Ledger.rowBr F.cr P.n := by rw [hPd]; rfl
  have hPk : P.k = ((gate0 l F).budget kclk coef A a ha).kOf r.1.n := by rw [hPd]; rfl
  have hKT : 8 ≤ FinalPass.Sd.R.KT l F := by unfold FinalPass.Sd.R.KT; omega
  have hZT : 4 ≤ FinalPass.Sd.R.ZT l F := by unfold FinalPass.Sd.R.ZT; omega
  have eTf : FinalPass.Sd.R.Tf l F kclk coef A a ha r =
      FinalPass.Sd.R.KT l F * (r.1.n + 2) ^ FinalPass.Sd.R.ZT l F := rfl
  have eE : eOf l F kclk coef A a ha r = r.1.n - P.k := by rw [hPk]; rfl
  obtain ⟨n, hnd⟩ : ∃ v, v = r.1.n := ⟨_, rfl⟩
  rw [← hnd] at hc1 hcS hPn eTf eE ⊢
  rw [← hnd] at hPk
  -- the input and its split
  obtain ⟨tl, htl⟩ := fpIn_split l F kclk coef A a ha r
  rw [← hnd] at htl
  have hin : σ.st (sIn x) = [] ++ ParseNat.enc true (RepairRepresentation.natWord n) ++
      (marks ((match r.1.mode with | .thr => true | .sym => false) :: tl) ++ [false]) := by
    rw [hE.hin, htl]; exact NumsX.frame_split _ _
  have hz : ∀ q, σ.val q = 0 := hE.regs
  have hpow := CopyNat.two_pow_natBitLength_le n
  have hnb : natBitLength n ≤ n + 1 := by
    show Nat.log 2 n + 1 ≤ n + 1
    have := Nat.log_le_self 2 n; omega
  -- 1: `rN := n`
  have h1 := ParseNat.readNatM_spec cap true (sIn x) (g 0) (g 1) rN (g 2) (g 3) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) n [] _ σ hin
    (by rw [hE.heads]; rfl) (hz _) (hz _) (hz _) (hz _) (by rw [hz, pow_succ]; omega)
  rw [hz, Nat.zero_add] at h1
  obtain ⟨σ1, hσ1⟩ : ∃ s, s = (σ.seth (sIn x) (([] : List Bool).length + ParseNat.stp true *
      (RepairRepresentation.natWord n).length)).setv rN n := ⟨_, rfl⟩
  rw [← hσ1] at h1
  have hlen := ParseNat.natWord_length n
  have sh1 : σ1.sh (sIn x) = 2 * (RepairRepresentation.natWord n).length := by rw [hσ1]; simp [ParseNat.stp]
  -- 2: step over the marker
  have h2 := WExec.fwd (cap := cap) (sIn x) σ1
  obtain ⟨σ2, hσ2⟩ : ∃ s, s = σ1.seth (sIn x) (σ1.sh (sIn x) + 1) := ⟨_, rfl⟩
  rw [← hσ2] at h2
  have st2 : σ2.st = σ.st := by rw [hσ2, hσ1]; rfl
  have sh2 : σ2.sh (sIn x) = 2 * (RepairRepresentation.natWord n).length + 1 := by rw [hσ2]; simp [sh1]
  have hb : wbit σ2 (sIn x) = (match r.1.mode with | .thr => true | .sym => false) := by
    unfold wbit; rw [st2, sh2, hin]; exact mode_bit _ _ _
  have v2 : ∀ q, σ2.val q = if q = rN then n else 0 := fun q => by
    rw [hσ2, hσ1]; simp only [WState.seth_val, WState.setv_val, Function.update_apply]; split_ifs <;> simp [hz]
  -- 3: the mode bit
  obtain ⟨σ3, c3, h3, hc3, hσ3⟩ : ∃ (s : St x) (c : ℕ), WExec cap (.ifs (sIn x) (.inc rM) .skip) σ2 s c ∧
      c ≤ 3 + 1 ∧ s = σ2.setv rM (mOf l F kclk coef A a ha r) := by
    cases hm : r.1.mode with
    | thr =>
      rw [hm] at hb
      have hi := WExec.inc (cap := cap) rM σ2 (by rw [v2]; simp only [show rM ≠ rN by decide, if_false]; omega)
      refine ⟨_, _, WExec.ifsT hb hi, le_rfl, ?_⟩
      rw [v2]
      simp only [show rM ≠ rN by decide, if_false, Nat.zero_add]
      simp [mOf, hm]
    | sym =>
      rw [hm] at hb
      refine ⟨_, _, WExec.ifsF hb (WExec.skip σ2), by omega, ?_⟩
      have e : mOf l F kclk coef A a ha r = 0 := by simp [mOf, hm]
      rw [e]
      have h0 := v2 rM
      rw [if_neg (show rM ≠ rN by decide)] at h0
      rw [← h0, wsetv_same]
  -- 4: the rest
  have v3N : σ3.val rN = n := by rw [hσ3]; simp [show rN ≠ rM by decide, v2]
  have v30 : ∀ q, q ≠ rN → q ≠ rM → σ3.val q = 0 := fun q h1 h2 => by rw [hσ3]; simp [h2, v2, h1]
  have sh3 : σ3.sh (sIn x) = 2 * (RepairRepresentation.natWord n).length + 1 := by rw [hσ3]; simp [sh2]
  have hpw : n + 2 ≤ (n + 2) ^ FinalPass.Sd.R.ZT l F := by
    calc n + 2 = (n + 2) ^ 1 := (pow_one _).symm
      _ ≤ _ := Nat.pow_le_pow_right (by omega) (by omega)
  have hhT : 2 * (RepairRepresentation.natWord n).length + 1 ≤
      FinalPass.Sd.R.KT l F * (n + 2) ^ FinalPass.Sd.R.ZT l F := by
    have := Nat.mul_le_mul hKT hpw
    rw [hlen]; omega
  obtain ⟨c4, h4, hc4⟩ := rest_run x cap F.cr (FinalPass.Sd.R.KT l F) (FinalPass.Sd.R.ZT l F) n
    (2 * (RepairRepresentation.natWord n).length + 1) P hPn hrP σ3 v3N v30 sh3 (by omega) (by rw [← eTf]; exact hTf)
    (by omega) hhT hcS
  refine ⟨_, WExec.cast cap (cProg_eq x _ _ _ ▸ WExec.seq h1 (WExec.seq h2 (WExec.seq h3 h4))) ?_ le_rfl, ?_⟩
  · rw [hσ3, hσ2, hσ1, eE, eTf]
    apply WState.eq
    · simp only [WState.setv_sh, WState.seth_sh, Function.update_idem]
    · rfl
    · funext q
      simp only [WState.setv_val, WState.seth_val]
    · rfl
  · rw [← hPk, eTf]
    unfold frontCost
    omega

end Req

end NearCubicWires.WireExponent3_5.UnionMachine.NumsC

end
