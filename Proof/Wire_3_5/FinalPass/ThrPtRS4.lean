import Proof.Wire_3_5.FinalPass.ThrPtRS3

/-! # S2 (THR per point), part 18: the row's factor into the accumulator (P3:2587-2630)

After the digits: the digit counter moved back into the digits' counter (`dRestore_spec`: `DREM := D`, `D := 0`), the
reports' stream rewound (`rewRep_spec`), stage 8 (`thr8T_spec`: `[thrTermOk …]` in register `92`), and the factor
added to the accumulator (`accAdd_spec`). Paper quantity: `R̂_{g,p}(c, u, v)` added to `Σ_{g,p} R̂_{g,p}`. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearCubicWires.WireExponent3_5.FinalPass.ThrPt
open NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.WireExponent3_5.FinalPass.Tm

variable (cap : ℕ) (σB : WState 16 118)

theorem dRestore_spec (t : TSt) (n : ℕ) (hd : t.d = n) (hr : t.dRem = 0) (hc : n ≤ cap) :
    WExec cap (WM.move 53 111) (t.w σB) ({ t with d := 0, dRem := n }.w σB) (7 * n + 1) := by
  have e := wmove_spec cap (53 : Fin 118) 111 (by decide) n (t.w σB) (by rw [tw_val_d, hd])
    (by rw [tw_val_d, hd]; exact hc) (by rw [tw_val_dRem, tw_val_d, hr, hd]; omega)
  rw [tw_val_d, tw_setv_d, tw_val_dRem, tw_setv_dRem] at e
  refine WExec.cast cap e (tw_eq ?_) le_rfl
  simp only [hr, hd, Nat.zero_add]

theorem rewRep_spec (t : TSt) (h : t.rH = t.hRep) (hc : t.rH ≤ cap) :
    WExec cap (WM.rewind 16 112) (t.w σB) ({ t with rH := 0, hRep := 0 }.w σB) (5 * t.rH + 1) := by
  have e := wrewind_spec cap (16 : Fin 17) (112 : Fin 118) t.rH (t.w σB) (by rw [tw_val_rH]) (by rw [tw_val_rH]; exact hc)
  rw [tw_setv_rH, tw_sh_hRep, tw_seth_hRep] at e
  refine WExec.cast cap e (tw_eq ?_) le_rfl
  simp only [h, Nat.sub_self]

theorem accAdd_spec (t : TSt) (hc : t.w92 ≤ cap) (hc2 : t.acc + t.w92 ≤ cap) :
    WExec cap (WM.move 92 0) (t.w σB) ({ t with w92 := 0, acc := t.acc + t.w92 }.w σB) (7 * t.w92 + 1) := by
  have e := wmove_spec cap (92 : Fin 118) 0 (by decide) t.w92 (t.w σB) (by rw [tw_val_w92])
    (by rw [tw_val_w92]; exact hc) (by rw [tw_val_acc, tw_val_w92]; exact hc2)
  rw [tw_val_w92, tw_setv_w92, tw_val_acc, tw_setv_acc] at e
  exact e

theorem thr8T_spec (a τ M : ℕ) (hB : BaseOK σB a τ M) (X : List Bool) (as ws tp tm : List ℕ) (L p r0 : ℕ)
    (rest0 rest1 rest2 : List Bool) (hl : X.length = 4 * L) (has : as.length = L) (h1l : ws.length = tp.length)
    (h2l : ws.length = tm.length) (hr0 : r0 < p) (t : TSt) (hx : t.x = frameP X ++ false :: rest0)
    (hrw : t.rw = Term.rowWord p r0 as ws ++ rest1) (hrep : t.rep = Term.repWord tp tm ++ rest2)
    (hhRw : t.hRw = 0) (hhRep : t.hRep = 0) (hw : t.w92 = 0) (hcap : Term.capT p r0 L as ws tp tm ≤ cap) :
    WExec cap (thr8I.liftR fsT frT) (t.w σB)
      ({ t with w92 := (Term.thrTermOk p r0 X as ws tp tm).toNat }.w σB) (costTI p r0 L as ws tp tm) := by
  have e := thr8L_spec cap X as ws tp tm L p r0 rest0 rest1 rest2 hl has h1l h2l hr0 (t.w σB) (by rw [tw_st_x, hx])
    (by rw [tw_st_rw, hrw]) (by rw [tw_st_rep, hrep])
    (by rw [tw_sh_other σB t 12 (by decide) (by decide) (by decide), hB.sh]) (by rw [tw_sh_hRw, hhRw])
    (by rw [tw_sh_hRep, hhRep])
    (fun q h1 h2 => by
      by_cases hq : q = 92
      · subst hq; rw [tw_val_w92, hw]
      · have hq' : q.val ≠ 92 := fun e => hq (Fin.ext e)
        rw [tw_val_other σB t q (by omega) (by omega) (by omega) (by omega) (by omega) hq' (by omega) (by omega)
          (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)]
        exact hB.stZ q (by omega) (by omega)) hcap
  rwa [tw_setv_w92] at e

end NearCubicWires.WireExponent3_5.FinalPass.ThrPt
