import Proof.Packets.PacketsMetaChild

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false

namespace NearCubicWires.PacketsMeta
open NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.RecoveryExecution NearCubicWires.ExtDecompositionBatch
open NearCubicWires.PacketsMeta.CutoffMath
noncomputable section

namespace Horner

abbrev rl : Fin 12 := 0
abbrev bb : Fin 12 := 1
abbrev d0 : Fin 12 := 2
abbrev d1 : Fin 12 := 3
abbrev d2 : Fin 12 := 4
abbrev d3 : Fin 12 := 5
abbrev zz : Fin 12 := 6
abbrev pr : Fin 12 := 7
abbrev mt : Fin 12 := 8
abbrev mm : Fin 12 := 9
abbrev fl : Fin 12 := 10
abbrev zo : Fin 12 := 11

def mul := RecoveryFocus.machine ![rl, bb, zz, pr, mt, mm, fl, zo] Mul.machine

def machine :=
  Composition.machine (swAt copyF false true rl zz d3 fl)
  (Composition.machine mul (Composition.machine (swAt copyF false true rl zz pr fl)
  (Composition.machine (swAt addF false true rl zz d2 fl)
  (Composition.machine mul (Composition.machine (swAt copyF false true rl zz pr fl)
  (Composition.machine (swAt addF false true rl zz d1 fl)
  (Composition.machine mul (Composition.machine (swAt copyF false true rl zz pr fl)
  (Composition.machine (swAt addF false true rl zz d0 fl) (swAt zeroF false true rl pr zo fl))))))))))

def hst (b a0 a1 a2 a3 z p t m : ℕ) (c : Bool) : Fin 12 → TS :=
  ![.ruler, .reg b, .reg a0, .reg a1, .reg a2, .reg a3, .reg z, .reg p, .reg t, .reg m, .flag c, .reg 0]

theorem horner4 (b a0 a1 a2 a3 : ℕ) : horner b [a0, a1, a2, a3] = a0 + b * (a1 + b * (a2 + b * a3)) := by
  simp [horner]

/-- **Horner.** -/
theorem run (W b a0 a1 a2 a3 z p t m : ℕ) (c : Bool) (hW : 1 ≤ W) (hb : 1 ≤ b)
    (hH : a0 + b * (a1 + b * (a2 + b * a3)) < 2 ^ W) :
    LRuns W machine (40 * W * W + 200 * W + 200) (hst b a0 a1 a2 a3 z p t m c)
      (hst b a0 a1 a2 a3 (horner b [a0, a1, a2, a3]) 0 0 0 false) := by
  have e1 : a3 ≤ b * a3 := Nat.le_mul_of_pos_left a3 hb
  have e2 : b * a3 + a2 ≤ b * (b * a3 + a2) := Nat.le_mul_of_pos_left _ hb
  have e3 : b * (b * a3 + a2) + a1 ≤ b * (b * (b * a3 + a2) + a1) := Nat.le_mul_of_pos_left _ hb
  have hH' : b * (b * (b * a3 + a2) + a1) + a0 < 2 ^ W := by
    have : b * (b * (b * a3 + a2) + a1) + a0 = a0 + b * (a1 + b * (a2 + b * a3)) := by ring
    omega
  have hall := (cpy_at (W := W) (hst b a0 a1 a2 a3 z p t m c) rl zz d3 fl (by decide) z a3 c rfl rfl rfl rfl
      (by omega)).seq
    ((Mul.at_run (W := W) _ rl bb zz pr mt mm fl zo (by decide) b a3 p t m _ (by rfl) (by rfl) (by rfl) (by rfl)
      (by rfl) (by rfl) (by rfl) (by rfl) (by omega) (by omega) hW).seq
    ((cpy_at (W := W) _ rl zz pr fl (by decide) a3 (b * a3) _ (by rfl) (by rfl) (by rfl) (by rfl) (by omega)).seq
    ((add_at (W := W) _ rl zz d2 fl (by decide) (b * a3) a2 _ (by rfl) (by rfl) (by rfl) (by rfl) (by omega)
      (by omega) (by omega)).seq
    ((Mul.at_run (W := W) _ rl bb zz pr mt mm fl zo (by decide) b (b * a3 + a2) (b * a3) 0 0 _ (by rfl) (by rfl)
      (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by omega) (by omega) hW).seq
    ((cpy_at (W := W) _ rl zz pr fl (by decide) (b * a3 + a2) (b * (b * a3 + a2)) _ (by rfl) (by rfl) (by rfl)
      (by rfl) (by omega)).seq
    ((add_at (W := W) _ rl zz d1 fl (by decide) (b * (b * a3 + a2)) a1 _ (by rfl) (by rfl) (by rfl) (by rfl)
      (by omega) (by omega) (by omega)).seq
    ((Mul.at_run (W := W) _ rl bb zz pr mt mm fl zo (by decide) b (b * (b * a3 + a2) + a1) (b * (b * a3 + a2)) 0 0 _
      (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by omega) (by omega) hW).seq
    ((cpy_at (W := W) _ rl zz pr fl (by decide) (b * (b * a3 + a2) + a1) (b * (b * (b * a3 + a2) + a1)) _
      (by rfl) (by rfl) (by rfl) (by rfl) (by omega)).seq
    ((add_at (W := W) _ rl zz d0 fl (by decide) (b * (b * (b * a3 + a2) + a1)) a0 _ (by rfl) (by rfl) (by rfl)
      (by rfl) (by omega) (by omega) hH').seq
    (zero_at (W := W) _ rl pr zo fl (by decide) (b * (b * (b * a3 + a2) + a1)) 0 _ (by rfl) (by rfl) (by rfl)
      (by rfl)))))))))))
  refine (hall.congr_out ?_).enlarge (by nlinarith)
  rw [horner4, show a0 + b * (a1 + b * (a2 + b * a3)) = b * (b * (b * a3 + a2) + a1) + a0 by ring]
  funext j; fin_cases j <;> rfl

/-- Horner docked at twelve ambient slots. -/
theorem at_run {N W : ℕ} (σ : Fin N → TS) (r b0 e0 e1 e2 e3 z p t m f o : Fin N)
    (hi : Function.Injective ![r, b0, e0, e1, e2, e3, z, p, t, m, f, o]) (b a0 a1 a2 a3 zv pv tv mv : ℕ) (c : Bool)
    (hr : σ r = .ruler) (hb0 : σ b0 = .reg b) (he0 : σ e0 = .reg a0) (he1 : σ e1 = .reg a1) (he2 : σ e2 = .reg a2)
    (he3 : σ e3 = .reg a3) (hz : σ z = .reg zv) (hp : σ p = .reg pv) (ht : σ t = .reg tv) (hm : σ m = .reg mv)
    (hf : σ f = .flag c) (ho : σ o = .reg 0) (hW : 1 ≤ W) (hb : 1 ≤ b)
    (hH : a0 + b * (a1 + b * (a2 + b * a3)) < 2 ^ W) :
    LRuns W (RecoveryFocus.machine ![r, b0, e0, e1, e2, e3, z, p, t, m, f, o] machine) (40 * W * W + 200 * W + 200) σ
      (Function.update (Function.update (Function.update (Function.update (Function.update σ
        z (.reg (horner b [a0, a1, a2, a3]))) p (.reg 0)) t (.reg 0)) m (.reg 0)) f (.flag false)) := by
  have h := (run W b a0 a1 a2 a3 zv pv tv mv c hW hb hH).dockK ![r, b0, e0, e1, e2, e3, z, p, t, m, f, o] hi σ
    (by intro j; fin_cases j
        · exact hr
        · exact hb0
        · exact he0
        · exact he1
        · exact he2
        · exact he3
        · exact hz
        · exact hp
        · exact ht
        · exact hm
        · exact hf
        · exact ho) [10, 9, 8, 7, 6]
    (by intro j hj; fin_cases j <;> simp [hst] at hj ⊢)
  exact h

end Horner

end
end NearCubicWires.PacketsMeta

