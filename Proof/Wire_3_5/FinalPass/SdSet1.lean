import Proof.Wire_3_5.FinalPass.SdFill2

/-! # S4 (the seeds phase), part 28: register batches for the setup (P3:3170-3178)

Over any word machine: **`cpJobs t ps`** (the copies `dst := src` of `ps`, `cpJobs_spec`, `cpApply_in`,
`cpApply_notin`), **`clJobs rs`** (the registers `rs` cleared, `clJobs_spec`, `clApply_val`), **`flagW`** (the two
presence flags `[1 ≤ v]`, `[2 ≤ v]` of a count `v`, `flagW_spec`), **`ldNums i c rs`** (a unary list read into
registers, the word rewound, `ldNums_spec`).

Paper quantity of the main type: the seeds phase's static numbers in their registers (the star parameters, the
decoder's digits, the carriers' presence, the evaluator's numbers). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSectionVars false

namespace NearCubicWires.WireExponent3_5.FinalPass.Sd
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimAsm

section Regs
variable {ns nr : ℕ} (cap : ℕ)

/-! ## Copies -/

/-- The copies `p.2 := p.1`, in order (through the temporary `t`). -/
def cpJobs (t : Fin nr) : List (Fin nr × Fin nr) → WM ns nr
  | [] => .skip
  | p :: ps => .seq (Hash4.wcopyR p.1 p.2 t) (cpJobs t ps)

def cpApply : WState ns nr → List (Fin nr × Fin nr) → WState ns nr
  | σ, [] => σ
  | σ, p :: ps => cpApply (σ.setv p.2 (σ.val p.1)) ps

def cpjCost (σ : WState ns nr) (ps : List (Fin nr × Fin nr)) : ℕ := (ps.map fun p => 18 * σ.val p.1 + 3 + 1).sum

theorem cpApply_sh : ∀ (σ : WState ns nr) (ps : List (Fin nr × Fin nr)), (cpApply σ ps).sh = σ.sh
  | _, [] => rfl
  | σ, p :: ps => by rw [cpApply, cpApply_sh]; rfl

theorem cpApply_st : ∀ (σ : WState ns nr) (ps : List (Fin nr × Fin nr)), (cpApply σ ps).st = σ.st
  | _, [] => rfl
  | σ, p :: ps => by rw [cpApply, cpApply_st]; rfl

theorem cpApply_cell : ∀ (σ : WState ns nr) (ps : List (Fin nr × Fin nr)), (cpApply σ ps).cell = σ.cell
  | _, [] => rfl
  | σ, p :: ps => by rw [cpApply, cpApply_cell]; rfl

theorem cpApply_notin : ∀ (σ : WState ns nr) (ps : List (Fin nr × Fin nr)) (q : Fin nr),
    q ∉ ps.map Prod.snd → (cpApply σ ps).val q = σ.val q
  | _, [], _, _ => rfl
  | σ, p :: ps, q, hq => by
    rw [List.map_cons, List.mem_cons, not_or] at hq
    rw [cpApply, cpApply_notin _ ps q hq.2]
    simp [Function.update_of_ne hq.1]

theorem cpApply_in : ∀ (σ : WState ns nr) (ps : List (Fin nr × Fin nr)), (ps.map Prod.snd).Nodup →
    (∀ p ∈ ps, ∀ p' ∈ ps, p.1 ≠ p'.2) → ∀ p ∈ ps, (cpApply σ ps).val p.2 = σ.val p.1
  | _, [], _, _, p, hp => absurd hp (by simp)
  | σ, p0 :: ps, hnd, hsd, p, hp => by
    rw [List.map_cons, List.nodup_cons] at hnd
    rw [cpApply]
    rcases List.mem_cons.mp hp with rfl | hp'
    · rw [cpApply_notin _ ps _ hnd.1]
      simp
    · rw [cpApply_in _ ps hnd.2 (fun a ha b hb => hsd a (List.mem_cons_of_mem _ ha) b (List.mem_cons_of_mem _ hb))
        p hp']
      have hne : p.1 ≠ p0.2 := hsd p (List.mem_cons_of_mem _ hp') p0 List.mem_cons_self
      simp [Function.update_of_ne hne]

theorem cpJobs_spec (t : Fin nr) : ∀ (ps : List (Fin nr × Fin nr)) (σ : WState ns nr),
    (ps.map Prod.snd).Nodup → (∀ p ∈ ps, ∀ p' ∈ ps, p.1 ≠ p'.2) →
    (∀ p ∈ ps, p.1 ≠ t ∧ p.2 ≠ t ∧ σ.val p.2 = 0 ∧ σ.val p.1 ≤ cap) → σ.val t = 0 →
    WExec cap (cpJobs t ps) σ (cpApply σ ps) (cpjCost σ ps)
  | [], σ, _, _, _, _ => WExec.skip σ
  | p :: ps, σ, hnd, hsd, hp, ht => by
    rw [List.map_cons, List.nodup_cons] at hnd
    obtain ⟨h1, h2, h3, h4⟩ := hp p List.mem_cons_self
    have hself : p.1 ≠ p.2 := hsd p List.mem_cons_self p List.mem_cons_self
    have e1 := Hash4.wcopyR_spec cap p.1 p.2 t hself h1 h2 σ h3 ht h4
    have e2 := cpJobs_spec t ps (σ.setv p.2 (σ.val p.1)) hnd.2
      (fun a ha b hb => hsd a (List.mem_cons_of_mem _ ha) b (List.mem_cons_of_mem _ hb))
      (fun q hq => by
        obtain ⟨g1, g2, g3, g4⟩ := hp q (List.mem_cons_of_mem _ hq)
        have hne2 : q.2 ≠ p.2 := fun h => hnd.1 (h ▸ List.mem_map_of_mem hq)
        have hne1 : q.1 ≠ p.2 := hsd q (List.mem_cons_of_mem _ hq) p List.mem_cons_self
        exact ⟨g1, g2, by simp [Function.update_of_ne hne2, g3], by simp [Function.update_of_ne hne1, g4]⟩)
      (by simp [Function.update_of_ne (Ne.symm h2), ht])
    have hcost : cpjCost (σ.setv p.2 (σ.val p.1)) ps = cpjCost σ ps := by
      unfold cpjCost
      congr 1
      apply List.map_congr_left
      intro q hq
      have hne1 : q.1 ≠ p.2 := hsd q (List.mem_cons_of_mem _ hq) p List.mem_cons_self
      simp [Function.update_of_ne hne1]
    refine WExec.cast cap (WExec.seq e1 e2) rfl ?_
    rw [hcost]
    simp only [cpjCost, List.map_cons, List.sum_cons]
    omega

/-! ## Clears -/

def clJobs : List (Fin nr) → WM ns nr
  | [] => .skip
  | r :: rs => .seq (WM.clear r) (clJobs rs)

def clApply : WState ns nr → List (Fin nr) → WState ns nr
  | σ, [] => σ
  | σ, r :: rs => clApply (σ.setv r 0) rs

theorem clApply_val : ∀ (σ : WState ns nr) (rs : List (Fin nr)),
    (clApply σ rs).val = fun q => if q ∈ rs then 0 else σ.val q
  | σ, [] => by funext q; simp [clApply]
  | σ, r :: rs => by
    rw [clApply, clApply_val]
    funext q
    by_cases h1 : q ∈ rs
    · simp [h1]
    · by_cases h2 : q = r
      · rw [h2]; simp
      · simp [h1, h2, Function.update_of_ne h2]

theorem clApply_sh : ∀ (σ : WState ns nr) (rs : List (Fin nr)), (clApply σ rs).sh = σ.sh
  | _, [] => rfl
  | σ, r :: rs => by rw [clApply, clApply_sh]; rfl

theorem clApply_st : ∀ (σ : WState ns nr) (rs : List (Fin nr)), (clApply σ rs).st = σ.st
  | _, [] => rfl
  | σ, r :: rs => by rw [clApply, clApply_st]; rfl

theorem clApply_cell : ∀ (σ : WState ns nr) (rs : List (Fin nr)), (clApply σ rs).cell = σ.cell
  | _, [] => rfl
  | σ, r :: rs => by rw [clApply, clApply_cell]; rfl

theorem clJobs_spec : ∀ (rs : List (Fin nr)) (σ : WState ns nr), rs.Nodup → (∀ r ∈ rs, σ.val r ≤ cap) →
    WExec cap (clJobs rs) σ (clApply σ rs) (rs.map fun r => 3 * σ.val r + 2).sum
  | [], σ, _, _ => WExec.skip σ
  | r :: rs, σ, hnd, hc => by
    rw [List.nodup_cons] at hnd
    have e1 := wclear_spec cap r (σ.val r) σ rfl (hc r List.mem_cons_self)
    have e2 := clJobs_spec rs (σ.setv r 0) hnd.2 (fun q hq => by
      have hne : q ≠ r := fun h => hnd.1 (h ▸ hq)
      simp [Function.update_of_ne hne]; exact hc q (List.mem_cons_of_mem _ hq))
    have hcost : (rs.map fun q => 3 * (σ.setv r 0).val q + 2).sum = (rs.map fun q => 3 * σ.val q + 2).sum := by
      congr 1
      apply List.map_congr_left
      intro q hq
      have hne : q ≠ r := fun h => hnd.1 (h ▸ hq)
      simp [Function.update_of_ne hne]
    refine WExec.cast cap (WExec.seq e1 e2) rfl ?_
    rw [hcost]
    simp only [List.map_cons, List.sum_cons]
    omega

/-! ## The presence flags -/

/-- `f₀ := [1 ≤ v]`, `f₁ := [2 ≤ v]` for `v = src` (through `X` and `t`). -/
def flagW (src X t f0 f1 : Fin nr) : WM ns nr :=
  .seq (Hash4.wcopyR src X t)
    (.seq (.ifr X (.seq (.inc f0) (.seq (.dec X) (.ifr X (.inc f1) .skip))) .skip) (WM.clear X))

theorem flagW_spec (src X t f0 f1 : Fin nr) (hsX : src ≠ X) (hst : src ≠ t) (hXt : X ≠ t) (h0X : f0 ≠ X)
    (h1X : f1 ≠ X) (h01 : f0 ≠ f1) (h0s : f0 ≠ src) (h1s : f1 ≠ src) (σ : WState ns nr) (hX : σ.val X = 0)
    (ht : σ.val t = 0) (h0 : σ.val f0 = 0) (h1 : σ.val f1 = 0) (hc : σ.val src ≤ cap) (hc2 : 2 ≤ cap) :
    ∃ m, WExec cap (flagW src X t f0 f1) σ
      ((σ.setv f0 (if 1 ≤ σ.val src then 1 else 0)).setv f1 (if 2 ≤ σ.val src then 1 else 0)) m ∧
      m ≤ 21 * σ.val src + 30 := by
  have e1 := Hash4.wcopyR_spec cap src X t hsX hst hXt σ hX ht hc
  obtain ⟨σ1, g1⟩ : ∃ y : WState ns nr, y = σ.setv X (σ.val src) := ⟨_, rfl⟩
  rw [← g1] at e1
  have x1 : σ1.val X = σ.val src := by rw [g1]; simp
  have f01 : σ1.val f0 = 0 := by rw [g1]; simp [Function.update_of_ne h0X, h0]
  have f11 : σ1.val f1 = 0 := by rw [g1]; simp [Function.update_of_ne h1X, h1]
  by_cases hv0 : σ.val src = 0
  · have e2 : WExec cap (.ifr X (.seq (.inc f0) (.seq (.dec X) (.ifr X (.inc f1) .skip))) .skip) σ1 σ1 1 :=
      WExec.ifrF (by rw [x1, hv0]) (WExec.skip σ1)
    have e3 := wclear_spec cap X 0 σ1 (by rw [x1, hv0]) (by rw [x1, hv0]; omega)
    refine ⟨_, WExec.cast cap (WExec.seq e1 (WExec.seq e2 e3)) ?_ le_rfl, by omega⟩
    rw [g1, hv0]
    wgen_eq [h0, h1, hX, h0X, h1X, h01, Ne.symm h0X, Ne.symm h1X, Ne.symm h01]
  · have e21 := WExec.inc (cap := cap) f0 σ1 (by rw [f01]; omega)
    obtain ⟨σ2, g2⟩ : ∃ y : WState ns nr, y = σ1.setv f0 (σ1.val f0 + 1) := ⟨_, rfl⟩
    rw [← g2] at e21
    have x2 : σ2.val X = σ.val src := by rw [g2, WState.setv_val, Function.update_of_ne (Ne.symm h0X), x1]
    have e22 := WExec.dec (cap := cap) X σ2 (by rw [x2]; exact hc)
    obtain ⟨σ3, g3⟩ : ∃ y : WState ns nr, y = σ2.setv X (σ2.val X - 1) := ⟨_, rfl⟩
    rw [← g3] at e22
    have x3 : σ3.val X = σ.val src - 1 := by rw [g3, WState.setv_val, Function.update_self, x2]
    have f13 : σ3.val f1 = 0 := by
      rw [g3, WState.setv_val, Function.update_of_ne h1X, g2, WState.setv_val, Function.update_of_ne (Ne.symm h01),
        f11]
    by_cases hv1 : σ.val src = 1
    · have e23 : WExec cap (.ifr X (.inc f1) .skip) σ3 σ3 1 := WExec.ifrF (by rw [x3, hv1]) (WExec.skip σ3)
      have e3 := wclear_spec cap X 0 σ3 (by rw [x3, hv1]) (by rw [x3, hv1]; omega)
      refine ⟨_, WExec.cast cap (WExec.seq e1 (WExec.seq (WExec.ifrT (by rw [x1]; exact hv0)
        (WExec.seq e21 (WExec.seq e22 e23))) e3)) ?_ le_rfl, by omega⟩
      rw [g3, x2, g2, f01, g1, hv1]
      wgen_eq [h0, h1, hX, h0X, h1X, h01, Ne.symm h0X, Ne.symm h1X, Ne.symm h01]
    · have e24 := WExec.inc (cap := cap) f1 σ3 (by rw [f13]; omega)
      have e23 : WExec cap (.ifr X (.inc f1) .skip) σ3 (σ3.setv f1 (σ3.val f1 + 1)) (3 + 1) :=
        WExec.ifrT (by rw [x3]; omega) e24
      have e3 := wclear_spec cap X (σ.val src - 1) (σ3.setv f1 (σ3.val f1 + 1))
        (by rw [WState.setv_val, Function.update_of_ne (Ne.symm h1X), x3])
        (by rw [WState.setv_val, Function.update_of_ne (Ne.symm h1X), x3]; omega)
      refine ⟨_, WExec.cast cap (WExec.seq e1 (WExec.seq (WExec.ifrT (by rw [x1]; exact hv0)
        (WExec.seq e21 (WExec.seq e22 e23))) e3)) ?_ le_rfl, by omega⟩
      have hv2 : 2 ≤ σ.val src := by omega
      rw [f13, g3, x2, g2, f01, g1, if_pos (by omega : 1 ≤ σ.val src), if_pos hv2]
      wgen_eq [h0, h1, hX, h0X, h1X, h01, Ne.symm h0X, Ne.symm h1X, Ne.symm h01]

/-! ## A unary list into registers -/

/-- Read `unaryList vs` on `i` into the registers `rs` (counter `c`), the word rewound. -/
def ldNums (i : Fin (ns + 1)) (c : Fin nr) (rs : List (Fin nr)) : WM ns nr :=
  .seq (readList i c rs) (WM.rewind i c)

theorem ldNums_spec (i : Fin (ns + 1)) (c : Fin nr) (rs : List (Fin nr)) (vs : List ℕ) (σ : WState ns nr)
    (hl : rs.length = vs.length) (hrc : ∀ r ∈ rs, r ≠ c) (hnd : rs.Nodup) (hz : ∀ r ∈ rs, σ.val r = 0)
    (hst : σ.st i = Data.unaryList vs) (hsh : σ.sh i = 0) (hc0 : σ.val c = 0)
    (hc : (Data.unaryList vs).length ≤ cap) :
    ∃ σ2 : WState ns nr, WExec cap (ldNums i c rs) σ σ2 (11 * (Data.unaryList vs).length + 1 +
        (5 * (Data.unaryList vs).length + 1)) ∧ σ2.st = σ.st ∧ σ2.sh = σ.sh ∧
      (∀ k : Fin rs.length, σ2.val (rs.get k) = vs.getD k 0) ∧ (∀ q, q ∉ rs → σ2.val q = σ.val q) ∧
      σ2.cell = σ.cell := by
  obtain ⟨σ1, e1, s1, h1, c1, v1, o1, l1⟩ := readList_spec cap i c rs vs σ [] [] hl hrc hnd hz
    (by rw [hst]; simp) (by rw [hsh]; rfl) (by rw [hc0]; omega) (fun v hv => le_trans (ppUl_mem vs v hv) hc)
  have e2 := wrewind_spec cap i c (Data.unaryList vs).length σ1 (by rw [c1, hc0]; omega) (by rw [c1, hc0]; omega)
  refine ⟨_, WExec.seq e1 e2, ?_, ?_, ?_, ?_, ?_⟩
  · simp [s1]
  · funext j
    by_cases hj : j = i
    · rw [hj]; simp [h1, hsh]
    · simp [h1, Function.update_of_ne hj]
  · intro k
    have hkc : rs.get k ≠ c := hrc _ (List.get_mem _ _)
    rw [WState.seth_val, WState.setv_val, Function.update_of_ne hkc, v1 k]
  · intro q hq
    by_cases hqc : q = c
    · rw [hqc]; simp [hc0]
    · simp [Function.update_of_ne hqc, o1 q hqc hq]
  · simp [l1]

end Regs

end NearCubicWires.WireExponent3_5.FinalPass.Sd
