import Proof.Wire_3_5.FinalPass.DigsDig2

/-! # `DigsW`'s body, part 6: one circuit at digit `d` (P3:2585-2599)

`cBodyDW` on circuit `i`'s payload: to the selected child (`navW`), `R 20 := S`, the weights (`weightsW`), back to
the payload's start (`rew2W`), the next power `B := B · base mod p` (`bUpdW`), `S` cleared. From the circuit loop's
state (`R 17 = g / Π_{j<i} m_j`, `R 25 = base^i mod p`, `R 37 = Σ_{j<i} |supp_j|`, output `l`) it reaches the next
one. Main declarations: `fm_mem_le`, `fm_len_ge`, `bUpd_spec`, **`cBodyD_spec`**. Paper quantity: circuit `i`'s
block of digit `d`'s population `v_{·,d}` of row `(g, p)`. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false

namespace NearCubicWires.WireExponent3_5.FinalPass.DigsBody
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.FinalPass.ThrCore
open NearCubicWires.WireExponent3_5.FinalPass.ThrRead NearCubicWires.WireExponent3_5.FinalPass.ThrArith
open NearCubicWires.WireExponent3_5.FinalPass.Digs
open NearCubicWires.RepairRepresentation (natWord intWord)

theorem fm_mem_le (zs : List ℤ) (z : ℤ) (h : z ∈ zs) : (intWord z).length ≤ (zs.flatMap intWord).length := by
  rw [List.length_flatMap]
  exact List.le_sum_of_mem (List.mem_map.mpr ⟨z, h, rfl⟩)

theorem fm_len_ge : ∀ zs : List ℤ, 2 * zs.length ≤ (zs.flatMap intWord).length
  | [] => by simp
  | z :: zs => by
    have := fm_len_ge zs
    rw [List.flatMap_cons, List.length_append, intWord_length', List.length_cons]; omega

theorem nbl_le_fm (zs : List ℤ) (z : ℤ) (h : z ∈ zs) : natBitLength z.natAbs ≤ (zs.flatMap intWord).length := by
  have := fm_mem_le zs z h; rw [intWord_length'] at this; omega

/-- Stream heads of two states built from one state, compared. -/
macro "wst_sh" : tactic => `(tactic| (funext i; simp only [at2, outAt, WState.setv_sh, WState.seth_sh,
  WState.sets_sh, Function.update_apply]; try ((try split_ifs) <;> simp_all)))
/-- Stream contents of two states built from one state, compared. -/
macro "wst_st" : tactic => `(tactic| (funext i; simp only [at2, outAt, WState.setv_st, WState.seth_st,
  WState.sets_st, Function.update_apply]; try ((try split_ifs) <;> simp_all)))

variable {ns nr : ℕ} (cap : ℕ) (R : Fin digsK ↪ Fin nr)

@[simp] theorem mlB0 : mlB R 0 = R 26 := rfl
@[simp] theorem mlB1 : mlB R 1 = R 27 := rfl
@[simp] theorem mlB2 : mlB R 2 = R 28 := rfl
@[simp] theorem mlB3 : mlB R 3 = R 25 := rfl
@[simp] theorem mlB4 : mlB R 4 = R 39 := rfl
@[simp] theorem mlB5 : mlB R 5 = R 40 := rfl

/-- `B := B · base mod p` (`B` in `R 25`, the base in `R 23`). -/
def bUpdW : WM ns nr :=
  .seq (Hash4.wcopyR (R 23) (R 28) (R 39)) (.seq (Hash4.wcopyR (R 2) (R 27) (R 39)) (.seq (mulLoopW (mlB R))
    (.seq (WM.clear (R 27)) (.seq (WM.clear (R 25)) (WM.move (R 26) (R 25))))))

/-- `bUpdW`'s step bound. -/
def bUpdCost (p : ℕ) : ℕ := 18 * p + 4 + (18 * p + 4 + (p * mulStep p + 2 + (3 * p + 2 + (3 * p + 2 + (7 * p + 1)))))

theorem bUpd_spec (p bm B : ℕ) (hpc : p ≤ cap) (hbm : bm < p) (hB : B < p) (τ : WState ns nr)
    (hP : τ.val (R 2) = p) (h23 : τ.val (R 23) = bm) (h25 : τ.val (R 25) = B) (h26 : τ.val (R 26) = 0)
    (h27 : τ.val (R 27) = 0) (h28 : τ.val (R 28) = 0) (h39 : τ.val (R 39) = 0) (h40 : τ.val (R 40) = 0) :
    WExec cap (bUpdW R) τ (τ.setv (R 25) (B * bm % p)) (bUpdCost p) := by
  have hpos : 0 < p := by omega
  have d1 := Hash4.wcopyR_spec cap (R 23) (R 28) (R 39) (R.injective.ne (by decide)) (R.injective.ne (by decide))
    (R.injective.ne (by decide)) τ h28 h39 (by omega)
  rw [h23] at d1
  have d2 := Hash4.wcopyR_spec cap (R 2) (R 27) (R 39) (R.injective.ne (by decide)) (R.injective.ne (by decide))
    (R.injective.ne (by decide)) (τ.setv (R 28) bm) (by simp [h27]) (by simp [h39]) (by simp [hP]; omega)
  rw [show (τ.setv (R 28) bm).val (R 2) = p by simp [hP]] at d2
  have d3 := mulLoop_spec cap (mlB R) p B hpc hB bm ((τ.setv (R 28) bm).setv (R 27) p) 0 (by simp) (by omega)
    (by simp [h26]) hpos (by simp) (by simp [h25]) (by simp [h39]) (by simp [h40])
  simp only [mlB0, mlB1, mlB2] at d3
  obtain ⟨a, ha⟩ : ∃ a, a = (0 + B * bm) % p := ⟨_, rfl⟩
  rw [← ha] at d3
  have hap : a < p := by rw [ha]; exact Nat.mod_lt _ hpos
  have e3 : ((((τ.setv (R 28) bm).setv (R 27) p).setv (R 28) 0).setv (R 26) a).setv (R 27) (p - a) =
      (τ.setv (R 26) a).setv (R 27) (p - a) := by clear d1 d2 d3; wst_eq
  rw [e3] at d3
  have d4 := wclear_spec cap (R 27) (p - a) ((τ.setv (R 26) a).setv (R 27) (p - a)) (by simp) (by simp; omega)
  have e4 : ((τ.setv (R 26) a).setv (R 27) (p - a)).setv (R 27) 0 = τ.setv (R 26) a := by
    clear d1 d2 d3 d4; wst_eq
  rw [e4] at d4
  have d5 := wclear_spec cap (R 25) B (τ.setv (R 26) a) (by simp [h25]) (by simp [h25]; omega)
  have d6 := wmove_spec cap (R 26) (R 25) (R.injective.ne (by decide)) a ((τ.setv (R 26) a).setv (R 25) 0) (by simp)
    (by simp; omega) (by simp; omega)
  refine WExec.cast cap (WExec.seq d1 (WExec.seq d2 (WExec.seq d3 (WExec.seq d4 (WExec.seq d5 d6))))) ?_ (by
    unfold bUpdCost
    have : bm * mulStep p ≤ p * mulStep p := Nat.mul_le_mul_right _ hbm.le
    omega)
  rw [show B * bm % p = a by rw [ha, Nat.zero_add]]
  clear d1 d2 d3 d4 d5 d6
  wst_eq

/-- One circuit at digit `d`. -/
def cBodyDW (E Dg : Fin (ns + 1)) : WM ns nr :=
  .seq (navW R E) (.seq (Hash4.wcopyR (R 15) (R 20) (R 39)) (.seq (weightsW R E Dg) (.seq (rew2W E (R 14))
    (.seq (bUpdW R) (WM.clear (R 15))))))

/-- A circuit's zero registers. -/
def cL : List (Fin digsK) :=
  [5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 18, 19, 20, 21, 22, 26, 27, 28, 29, 30, 31, 32, 33, 39, 40]

/-- One circuit's step bound at digit `d`. -/
def cDCost (S m g nz Lm p d off o J : ℕ) : ℕ :=
  navCost S m g nz Lm + 1 + (18 * S + 3 + 1 + ((S * (wCost Lm p d off (o + S) + 4) + 1) + 1 + ((7 * J + 3) + 1 +
    (bUpdCost p + 1 + (3 * S + 1)))))

theorem cBodyD_spec (E Dg : Fin (ns + 1)) (hED : E ≠ Dg) (S m g : ℕ) (zs ws : List ℤ) (c rest : List Bool)
    (p B bm d off o U : ℕ) (l : List Bool) (σ : WState ns nr) (hst : σ.st E = frame c) (hs : σ.sh E = 0)
    (hc : c = natWord S ++ (natWord m ++ (zs.flatMap intWord ++ (ws.flatMap intWord ++ rest))))
    (hzs : zs.length = g % m * (S + 1)) (hws : ws.length = S) (hm : 1 ≤ m) (hp : 1 ≤ p) (hB : B < p)
    (hbm : bm < p) (hlst : σ.st Dg = l) (hlsh : σ.sh Dg = l.length) (hlw : σ.val (R 34) = l.length)
    (hg : σ.val (R 17) = g) (hBv : σ.val (R 25) = B) (hbmv : σ.val (R 23) = bm) (hP : σ.val (R 2) = p)
    (hdv : σ.val (R 36) = d) (hov : σ.val (R 4) = off) (hoc : σ.val (R 37) = o) (hz : Zs R σ cL)
    (hcU : c.length ≤ U) (hmU : m ≤ U) (hgU : g ≤ U) (hpU : p ≤ U) (hdU : d ≤ U)
    (hlU : (l ++ emitList off d B p o ws).length + off + o + S + 2 ≤ U) (hU : 2 * U + 2 ≤ cap) :
    WExec cap (cBodyDW R E Dg) σ
      (outAt (((σ.setv (R 17) (g / m)).setv (R 25) (B * bm % p)).setv (R 37) (o + S)) Dg (R 34)
        (l ++ emitList off d B p o ws))
      (cDCost S m g zs.length c.length p d off o ((natWord S).length + (natWord m).length + (zs.flatMap intWord).length +
        (ws.flatMap intWord).length)) := by
  have hlen : c.length = (natWord S).length + (natWord m).length + (zs.flatMap intWord).length +
      (ws.flatMap intWord).length + rest.length := by rw [hc]; simp only [List.length_append]; ring
  have hzl := fm_len_ge zs
  have hwl := fm_len_ge ws
  have h15 := hz 15 (by decide)
  have h20 := hz 20 (by decide)
  have h39 := hz 39 (by decide)
  obtain ⟨J1, hJ1⟩ : ∃ J, J = (natWord S).length + (natWord m).length + (zs.flatMap intWord).length := ⟨_, rfl⟩
  -- to the selected child
  have d1 := nav_spec cap R E S m g zs c.length (fun z hz' => le_trans (nbl_le_fm zs z hz') (by omega)) c
    (ws.flatMap intWord ++ rest) σ hst hs hc hzs (Zs_sub R _ _ _ (by decide) hz) hg hm (by omega) (by omega)
    (by omega) (by omega) (by omega)
  rw [← hJ1] at d1
  have d2 := Hash4.wcopyR_spec cap (R 15) (R 20) (R 39) (R.injective.ne (by decide)) (R.injective.ne (by decide))
    (R.injective.ne (by decide)) (at2 ((σ.setv (R 15) S).setv (R 17) (g / m)) E (R 14) J1)
    (by simp [at2, h20]) (by simp [at2, h39]) (by simp [at2]; omega)
  have e2 : (at2 ((σ.setv (R 15) S).setv (R 17) (g / m)) E (R 14) J1).setv (R 20)
      ((at2 ((σ.setv (R 15) S).setv (R 17) (g / m)) E (R 14) J1).val (R 15)) =
      dSt R ((σ.setv (R 15) S).setv (R 17) (g / m)) E Dg J1 o l S := by
    unfold dSt; clear d1 d2 hz; wst_eq
  rw [e2, show (at2 ((σ.setv (R 15) S).setv (R 17) (g / m)) E (R 14) J1).val (R 15) = S by simp [at2]] at d2
  -- the weights
  have d3 := weights_spec cap R E Dg hED ws c.length (fun w hw => le_trans (nbl_le_fm ws w hw) (by omega)) c rest J1
    p B d off o l hp (by omega) hB ((σ.setv (R 15) S).setv (R 17) (g / m)) (by simp [hst])
    (by rw [hc, hJ1, ← List.append_assoc, ← List.append_assoc, List.drop_left' (by simp; ring)])
    (by simp [hP]) (by simp [hBv]) (by simp [hdv]) (by simp [hov]) (Zs_setv R _ _ _ _ (by decide)
      (Zs_setv R _ _ _ _ (by decide) (Zs_sub R _ _ _ (by decide) hz))) (by omega) (by omega) (by omega)
    (by rw [hws]; omega)
  rw [hws] at d3
  -- back to the start
  have d4 := rew2_spec cap E (R 14) (J1 + (ws.flatMap intWord).length)
    (dSt R ((σ.setv (R 15) S).setv (R 17) (g / m)) E Dg (J1 + (ws.flatMap intWord).length) (o + S)
      (l ++ emitList off d B p o ws) 0) (by simp [dSt, at2, outAt]) (by omega) (by simp [dSt, at2])
  have e4 : ((dSt R ((σ.setv (R 15) S).setv (R 17) (g / m)) E Dg (J1 + (ws.flatMap intWord).length) (o + S)
      (l ++ emitList off d B p o ws) 0).setv (R 14) 0).seth E 0 =
      outAt (((σ.setv (R 15) S).setv (R 17) (g / m)).setv (R 37) (o + S)) Dg (R 34) (l ++ emitList off d B p o ws) := by
    have h14 := hz 14 (by decide)
    unfold dSt; clear d1 d2 d3 hz e2; wst_eq
  rw [e4] at d4
  -- the next power
  have d5 := bUpd_spec cap R p bm B (by omega) hbm hB
    (outAt (((σ.setv (R 15) S).setv (R 17) (g / m)).setv (R 37) (o + S)) Dg (R 34) (l ++ emitList off d B p o ws))
    (by simp [outAt, hP]) (by simp [outAt, hbmv]) (by simp [outAt, hBv]) (by simp [outAt, hz 26 (by decide)])
    (by simp [outAt, hz 27 (by decide)]) (by simp [outAt, hz 28 (by decide)]) (by simp [outAt, h39])
    (by simp [outAt, hz 40 (by decide)])
  have d6 := wclear_spec cap (R 15) S ((outAt (((σ.setv (R 15) S).setv (R 17) (g / m)).setv (R 37) (o + S)) Dg (R 34)
    (l ++ emitList off d B p o ws)).setv (R 25) (B * bm % p)) (by simp [outAt]) (by simp [outAt]; omega)
  refine WExec.cast cap (WExec.seq d1 (WExec.seq d2 (WExec.seq d3 (WExec.seq d4 (WExec.seq d5 d6))))) ?_ (by
    unfold cDCost; omega)
  clear d1 d2 d3 d4 d5 d6 e2 e4 hz
  refine WState.eq ?_ ?_ ?_ ?_
  · wst_sh
  · wst_st
  · funext x
    by_cases x1 : x = R 15
    · rw [x1]; simp_all [outAt, Function.update_apply]
    by_cases x2 : x = R 17
    · rw [x2]; simp_all [outAt, Function.update_apply]
    by_cases x3 : x = R 37
    · rw [x3]; simp_all [outAt, Function.update_apply]
    by_cases x4 : x = R 34
    · rw [x4]; simp_all [outAt, Function.update_apply]
    by_cases x5 : x = R 25
    · rw [x5]; simp_all [outAt, Function.update_apply]
    simp_all [outAt, Function.update_apply]
  · rfl

end NearCubicWires.WireExponent3_5.FinalPass.DigsBody
