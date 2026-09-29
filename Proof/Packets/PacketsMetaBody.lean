import Proof.Packets.PacketsMetaHorner

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

/-! ## `D := |X − Y|` -/

namespace AbsDiff

def machine :=
  Composition.machine (swAt subF false false (0 : Fin 6) 1 2 4)
    (Ite (nop 6) (Composition.machine (swAt copyF false true (0 : Fin 6) 3 2 4) (swAt subF false true (0 : Fin 6) 3 1 4))
      (Composition.machine (swAt copyF false true (0 : Fin 6) 3 1 4) (swAt subF false true (0 : Fin 6) 3 2 4)) 4)

theorem run (W x y d : ℕ) (c : Bool) (hx : x < 2 ^ W) (hy : y < 2 ^ W) :
    LRuns W machine (10 * W + 20) ![.ruler, .reg x, .reg y, .reg d, .flag c, .reg 0]
      ![.ruler, .reg x, .reg y, .reg ((x : ℤ) - y).natAbs, .flag false, .reg 0] := by
  have hall := (lt_at (W := W) (![.ruler, .reg x, .reg y, .reg d, .flag c, .reg 0] : Fin 6 → TS) 0 1 2 4 (by decide)
    x y c rfl rfl rfl rfl hx hy).seq
    (Ite.runs (W := W) (nop 6) _ _ 4 (decide (x < y)) (nop_lruns _) (by rfl)
      (ρ := ![.ruler, .reg x, .reg y, .reg ((x : ℤ) - y).natAbs, .flag false, .reg 0])
      (fun hb => by
        have hxy : x < y := of_decide_eq_true hb
        exact ((cpy_at (W := W) _ 0 3 2 4 (by decide) d y _ (by rfl) (by rfl) (by rfl) (by rfl) hy).seq
          (sub_at (W := W) _ 0 3 1 4 (by decide) y x _ (by rfl) (by rfl) (by rfl) (by rfl) hy hx (by omega))).congr_out
          (by
            funext j; fin_cases j
            · rfl
            · rfl
            · rfl
            · exact congrArg TS.reg (by omega)
            · rfl
            · rfl))
      (fun hb => by
        have hxy : ¬ x < y := of_decide_eq_false hb
        exact ((cpy_at (W := W) _ 0 3 1 4 (by decide) d x _ (by rfl) (by rfl) (by rfl) (by rfl) hx).seq
          (sub_at (W := W) _ 0 3 2 4 (by decide) x y _ (by rfl) (by rfl) (by rfl) (by rfl) hx hy (by omega))).congr_out
          (by
            funext j; fin_cases j
            · rfl
            · rfl
            · rfl
            · exact congrArg TS.reg (by omega)
            · rfl
            · rfl)))
  refine (hall.congr_out ?_).enlarge (by omega)
  funext j; fin_cases j <;> rfl

theorem at_run {N W : ℕ} (σ : Fin N → TS) (r xs ys ds f o : Fin N) (hi : Function.Injective ![r, xs, ys, ds, f, o])
    (x y d : ℕ) (c : Bool) (hr : σ r = .ruler) (hxs : σ xs = .reg x) (hys : σ ys = .reg y) (hds : σ ds = .reg d)
    (hf : σ f = .flag c) (ho : σ o = .reg 0) (hx : x < 2 ^ W) (hy : y < 2 ^ W) :
    LRuns W (RecoveryFocus.machine ![r, xs, ys, ds, f, o] machine) (10 * W + 20) σ
      (Function.update (Function.update σ ds (.reg ((x : ℤ) - y).natAbs)) f (.flag false)) := by
  have h := (run W x y d c hx hy).dockK ![r, xs, ys, ds, f, o] hi σ
    (by intro j; fin_cases j
        · exact hr
        · exact hxs
        · exact hys
        · exact hds
        · exact hf
        · exact ho) [4, 3]
    (by intro j hj; fin_cases j <;> simp at hj ⊢)
  exact h

end AbsDiff

namespace Body

abbrev rl : Fin 24 := 0
abbrev fl : Fin 24 := 1
abbrev zo : Fin 24 := 2
abbrev bb : Fin 24 := 15
abbrev xa : Fin 24 := 16
abbrev xp : Fin 24 := 17
abbrev xq : Fin 24 := 18
abbrev tm : Fin 24 := 19
abbrev mt : Fin 24 := 20
abbrev mm : Fin 24 := 21
abbrev ff : Fin 24 := 22
abbrev cn : Fin 24 := 23
def part1 :=
  (Composition.machine (swAt zeroF false true rl bb zo fl)
  (Composition.machine (swAt addF false true rl bb 3 fl)
  (Composition.machine (swAt addF false true rl bb 7 fl)
  (Composition.machine (swAt addF false true rl bb 11 fl)
  (Composition.machine (swAt addF false true rl bb 4 fl)
  (Composition.machine (swAt addF false true rl bb 8 fl)
  (Composition.machine (swAt addF false true rl bb 12 fl)
  (Composition.machine (swAt addF false true rl bb 5 fl)
  (Composition.machine (swAt addF false true rl bb 9 fl)
  (Composition.machine (swAt addF false true rl bb 13 fl)
  (Composition.machine (swAt addF false true rl bb 6 fl)
  (Composition.machine (swAt addF false true rl bb 10 fl)
  (Composition.machine (swAt addF false true rl bb 14 fl)
  (swAt addF true true rl bb zo fl))))))))))))))

def part2 :=
  (Composition.machine (RecoveryFocus.machine ![rl, bb, 3, 4, 5, 6, xa, tm, mt, mm, fl, zo] Horner.machine)
  (Composition.machine (RecoveryFocus.machine ![rl, bb, 7, 8, 9, 10, xp, tm, mt, mm, fl, zo] Horner.machine)
  (Composition.machine (RecoveryFocus.machine ![rl, bb, 11, 12, 13, 14, xq, tm, mt, mm, fl, zo] Horner.machine)
  (RecoveryFocus.machine ![rl, xp, xq, tm, fl, zo] AbsDiff.machine))))

def part3 :=
  (Composition.machine (swAt addF false true rl ff xa fl)
  (Composition.machine (swAt addF false true rl ff tm fl)
  (Composition.machine (swAt addF true true rl cn zo fl)
  (Composition.machine (swAt zeroF false true rl bb zo fl)
  (Composition.machine (swAt zeroF false true rl xa zo fl)
  (Composition.machine (swAt zeroF false true rl xp zo fl)
  (Composition.machine (swAt zeroF false true rl xq zo fl)
  (swAt zeroF false true rl tm zo fl))))))))

def machine := Composition.machine part1 (Composition.machine part2 part3)

/-- The roles (scratch values `b x y z d` explicit). -/
def bst (a0 a1 a2 a3 p0 p1 p2 p3 q0 q1 q2 q3 b x y z d f n : ℕ) (c : Bool) : Fin 24 → TS :=
  ![.ruler, .flag c, .reg 0, .reg a0, .reg a1, .reg a2, .reg a3, .reg p0, .reg p1, .reg p2, .reg p3, .reg q0, .reg q1, .reg q2, .reg q3, .reg b, .reg x, .reg y, .reg z, .reg d, .reg 0, .reg 0, .reg f, .reg n]

/-- The base of the stacked selection. -/
def base (a0 a1 a2 a3 p0 p1 p2 p3 q0 q1 q2 q3 : ℕ) : ℕ := ((((((((((((0 + a0) + p0) + q0) + a1) + p1) + q1) + a2) + p2) + q2) + a3) + p3) + q3) + 1

theorem selMag_eq (a0 a1 a2 a3 p0 p1 p2 p3 q0 q1 q2 q3 : ℕ) :
    selMag [(a0, p0, q0), (a1, p1, q1), (a2, p2, q2), (a3, p3, q3)] =
      horner (base a0 a1 a2 a3 p0 p1 p2 p3 q0 q1 q2 q3) [a0, a1, a2, a3] +
        ((horner (base a0 a1 a2 a3 p0 p1 p2 p3 q0 q1 q2 q3) [p0, p1, p2, p3] : ℤ) -
          horner (base a0 a1 a2 a3 p0 p1 p2 p3 q0 q1 q2 q3) [q0, q1, q2, q3]).natAbs := by
  have hb : ([(a0, p0, q0), (a1, p1, q1), (a2, p2, q2), (a3, p3, q3)].map recMag).sum + 1 =
      base a0 a1 a2 a3 p0 p1 p2 p3 q0 q1 q2 q3 := by
    simp [recMag, base]; ring
  unfold selMag
  rw [hb]
  rfl

theorem run1 (W a0 a1 a2 a3 p0 p1 p2 p3 q0 q1 q2 q3 f n : ℕ) (c : Bool) (hB : (base a0 a1 a2 a3 p0 p1 p2 p3 q0 q1 q2 q3) < 2 ^ W) :
    LRuns W part1 (30 * W + 60) (bst a0 a1 a2 a3 p0 p1 p2 p3 q0 q1 q2 q3 0 0 0 0 0 f n c) (bst a0 a1 a2 a3 p0 p1 p2 p3 q0 q1 q2 q3 (base a0 a1 a2 a3 p0 p1 p2 p3 q0 q1 q2 q3) 0 0 0 0 f n false) := by
  have hBv : (base a0 a1 a2 a3 p0 p1 p2 p3 q0 q1 q2 q3) = ((((((((((((0 + a0) + p0) + q0) + a1) + p1) + q1) + a2) + p2) + q2) + a3) + p3) + q3) + 1 := rfl
  rw [hBv] at hB ⊢
  have hall := ((zero_at (W := W) (bst a0 a1 a2 a3 p0 p1 p2 p3 q0 q1 q2 q3 0 0 0 0 0 f n c) rl bb zo fl (by decide) 0 0 c rfl rfl rfl rfl)).seq
    (((add_at (W := W) _ rl bb 3 fl (by decide) 0 a0 _ (by rfl) (by rfl) (by rfl) (by rfl) (by omega) (by omega) (by omega))).seq
    (((add_at (W := W) _ rl bb 7 fl (by decide) (0 + a0) p0 _ (by rfl) (by rfl) (by rfl) (by rfl) (by omega) (by omega) (by omega))).seq
    (((add_at (W := W) _ rl bb 11 fl (by decide) ((0 + a0) + p0) q0 _ (by rfl) (by rfl) (by rfl) (by rfl) (by omega) (by omega) (by omega))).seq
    (((add_at (W := W) _ rl bb 4 fl (by decide) (((0 + a0) + p0) + q0) a1 _ (by rfl) (by rfl) (by rfl) (by rfl) (by omega) (by omega) (by omega))).seq
    (((add_at (W := W) _ rl bb 8 fl (by decide) ((((0 + a0) + p0) + q0) + a1) p1 _ (by rfl) (by rfl) (by rfl) (by rfl) (by omega) (by omega) (by omega))).seq
    (((add_at (W := W) _ rl bb 12 fl (by decide) (((((0 + a0) + p0) + q0) + a1) + p1) q1 _ (by rfl) (by rfl) (by rfl) (by rfl) (by omega) (by omega) (by omega))).seq
    (((add_at (W := W) _ rl bb 5 fl (by decide) ((((((0 + a0) + p0) + q0) + a1) + p1) + q1) a2 _ (by rfl) (by rfl) (by rfl) (by rfl) (by omega) (by omega) (by omega))).seq
    (((add_at (W := W) _ rl bb 9 fl (by decide) (((((((0 + a0) + p0) + q0) + a1) + p1) + q1) + a2) p2 _ (by rfl) (by rfl) (by rfl) (by rfl) (by omega) (by omega) (by omega))).seq
    (((add_at (W := W) _ rl bb 13 fl (by decide) ((((((((0 + a0) + p0) + q0) + a1) + p1) + q1) + a2) + p2) q2 _ (by rfl) (by rfl) (by rfl) (by rfl) (by omega) (by omega) (by omega))).seq
    (((add_at (W := W) _ rl bb 6 fl (by decide) (((((((((0 + a0) + p0) + q0) + a1) + p1) + q1) + a2) + p2) + q2) a3 _ (by rfl) (by rfl) (by rfl) (by rfl) (by omega) (by omega) (by omega))).seq
    (((add_at (W := W) _ rl bb 10 fl (by decide) ((((((((((0 + a0) + p0) + q0) + a1) + p1) + q1) + a2) + p2) + q2) + a3) p3 _ (by rfl) (by rfl) (by rfl) (by rfl) (by omega) (by omega) (by omega))).seq
    (((add_at (W := W) _ rl bb 14 fl (by decide) (((((((((((0 + a0) + p0) + q0) + a1) + p1) + q1) + a2) + p2) + q2) + a3) + p3) q3 _ (by rfl) (by rfl) (by rfl) (by rfl) (by omega) (by omega) (by omega))).seq
    ((inc_at (W := W) _ rl bb zo fl (by decide) ((((((((((((0 + a0) + p0) + q0) + a1) + p1) + q1) + a2) + p2) + q2) + a3) + p3) + q3) 0 _ (by rfl) (by rfl) (by rfl) (by rfl) rfl (by omega)))))))))))))))
  refine (hall.congr_out ?_).enlarge (by omega)
  funext j; fin_cases j <;> rfl

theorem run2 (W a0 a1 a2 a3 p0 p1 p2 p3 q0 q1 q2 q3 f n : ℕ) (hW : 1 ≤ W)
    (hA : a0 + (base a0 a1 a2 a3 p0 p1 p2 p3 q0 q1 q2 q3) * (a1 + (base a0 a1 a2 a3 p0 p1 p2 p3 q0 q1 q2 q3) * (a2 + (base a0 a1 a2 a3 p0 p1 p2 p3 q0 q1 q2 q3) * a3)) < 2 ^ W)
    (hP : p0 + (base a0 a1 a2 a3 p0 p1 p2 p3 q0 q1 q2 q3) * (p1 + (base a0 a1 a2 a3 p0 p1 p2 p3 q0 q1 q2 q3) * (p2 + (base a0 a1 a2 a3 p0 p1 p2 p3 q0 q1 q2 q3) * p3)) < 2 ^ W)
    (hQ : q0 + (base a0 a1 a2 a3 p0 p1 p2 p3 q0 q1 q2 q3) * (q1 + (base a0 a1 a2 a3 p0 p1 p2 p3 q0 q1 q2 q3) * (q2 + (base a0 a1 a2 a3 p0 p1 p2 p3 q0 q1 q2 q3) * q3)) < 2 ^ W) :
    LRuns W part2 (130 * W * W + 650 * W + 700) (bst a0 a1 a2 a3 p0 p1 p2 p3 q0 q1 q2 q3 (base a0 a1 a2 a3 p0 p1 p2 p3 q0 q1 q2 q3) 0 0 0 0 f n false)
      (bst a0 a1 a2 a3 p0 p1 p2 p3 q0 q1 q2 q3 (base a0 a1 a2 a3 p0 p1 p2 p3 q0 q1 q2 q3) (horner (base a0 a1 a2 a3 p0 p1 p2 p3 q0 q1 q2 q3) [a0, a1, a2, a3]) (horner (base a0 a1 a2 a3 p0 p1 p2 p3 q0 q1 q2 q3) [p0, p1, p2, p3]) (horner (base a0 a1 a2 a3 p0 p1 p2 p3 q0 q1 q2 q3) [q0, q1, q2, q3]) (((horner (base a0 a1 a2 a3 p0 p1 p2 p3 q0 q1 q2 q3) [p0, p1, p2, p3] : ℤ) - horner (base a0 a1 a2 a3 p0 p1 p2 p3 q0 q1 q2 q3) [q0, q1, q2, q3]).natAbs) f n false) := by
  have hb1 : 1 ≤ (base a0 a1 a2 a3 p0 p1 p2 p3 q0 q1 q2 q3) := by unfold base; omega
  have hPl : horner (base a0 a1 a2 a3 p0 p1 p2 p3 q0 q1 q2 q3) [p0, p1, p2, p3] < 2 ^ W := by rw [Horner.horner4]; exact hP
  have hQl : horner (base a0 a1 a2 a3 p0 p1 p2 p3 q0 q1 q2 q3) [q0, q1, q2, q3] < 2 ^ W := by rw [Horner.horner4]; exact hQ
  have hall := ((Horner.at_run (W := W) (bst a0 a1 a2 a3 p0 p1 p2 p3 q0 q1 q2 q3 (base a0 a1 a2 a3 p0 p1 p2 p3 q0 q1 q2 q3) 0 0 0 0 f n false) rl bb 3 4 5 6 xa tm mt mm fl zo (by decide) (base a0 a1 a2 a3 p0 p1 p2 p3 q0 q1 q2 q3) a0 a1 a2 a3 0 0 0 0 false rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl hW hb1 hA)).seq
    (((Horner.at_run (W := W) _ rl bb 7 8 9 10 xp tm mt mm fl zo (by decide) (base a0 a1 a2 a3 p0 p1 p2 p3 q0 q1 q2 q3) p0 p1 p2 p3 0 0 0 0 _ (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) hW hb1 hP)).seq
    (((Horner.at_run (W := W) _ rl bb 11 12 13 14 xq tm mt mm fl zo (by decide) (base a0 a1 a2 a3 p0 p1 p2 p3 q0 q1 q2 q3) q0 q1 q2 q3 0 0 0 0 _ (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) hW hb1 hQ)).seq
    ((AbsDiff.at_run (W := W) _ rl xp xq tm fl zo (by decide) (horner (base a0 a1 a2 a3 p0 p1 p2 p3 q0 q1 q2 q3) [p0, p1, p2, p3]) (horner (base a0 a1 a2 a3 p0 p1 p2 p3 q0 q1 q2 q3) [q0, q1, q2, q3]) 0 _ (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) hPl hQl))))
  refine (hall.congr_out ?_).enlarge (by nlinarith)
  funext j; fin_cases j <;> rfl

theorem run3 (W a0 a1 a2 a3 p0 p1 p2 p3 q0 q1 q2 q3 bv x y z d f n : ℕ) (h : f + x + d < 2 ^ W) (hn : n + 1 < 2 ^ W) :
    LRuns W part3 (20 * W + 40) (bst a0 a1 a2 a3 p0 p1 p2 p3 q0 q1 q2 q3 bv x y z d f n false) (bst a0 a1 a2 a3 p0 p1 p2 p3 q0 q1 q2 q3 0 0 0 0 0 (f + x + d) (n + 1) false) := by
  have hall := ((add_at (W := W) (bst a0 a1 a2 a3 p0 p1 p2 p3 q0 q1 q2 q3 bv x y z d f n false) rl ff xa fl (by decide) f x false rfl rfl rfl rfl (by omega) (by omega) (by omega))).seq
    (((add_at (W := W) _ rl ff tm fl (by decide) (f + x) d _ (by rfl) (by rfl) (by rfl) (by rfl) (by omega) (by omega) h)).seq
    (((inc_at (W := W) _ rl cn zo fl (by decide) n 0 _ (by rfl) (by rfl) (by rfl) (by rfl) rfl hn)).seq
    (((zero_at (W := W) _ rl bb zo fl (by decide) bv 0 _ (by rfl) (by rfl) (by rfl) (by rfl))).seq
    (((zero_at (W := W) _ rl xa zo fl (by decide) x 0 _ (by rfl) (by rfl) (by rfl) (by rfl))).seq
    (((zero_at (W := W) _ rl xp zo fl (by decide) y 0 _ (by rfl) (by rfl) (by rfl) (by rfl))).seq
    (((zero_at (W := W) _ rl xq zo fl (by decide) z 0 _ (by rfl) (by rfl) (by rfl) (by rfl))).seq
    ((zero_at (W := W) _ rl tm zo fl (by decide) d 0 _ (by rfl) (by rfl) (by rfl) (by rfl)))))))))
  refine (hall.congr_out ?_).enlarge (by omega)
  funext j; fin_cases j <;> rfl

theorem run (W a0 a1 a2 a3 p0 p1 p2 p3 q0 q1 q2 q3 f n : ℕ) (c : Bool) (hW : 1 ≤ W)
    (hB : (base a0 a1 a2 a3 p0 p1 p2 p3 q0 q1 q2 q3) < 2 ^ W)
    (hA : a0 + (base a0 a1 a2 a3 p0 p1 p2 p3 q0 q1 q2 q3) * (a1 + (base a0 a1 a2 a3 p0 p1 p2 p3 q0 q1 q2 q3) * (a2 + (base a0 a1 a2 a3 p0 p1 p2 p3 q0 q1 q2 q3) * a3)) < 2 ^ W)
    (hP : p0 + (base a0 a1 a2 a3 p0 p1 p2 p3 q0 q1 q2 q3) * (p1 + (base a0 a1 a2 a3 p0 p1 p2 p3 q0 q1 q2 q3) * (p2 + (base a0 a1 a2 a3 p0 p1 p2 p3 q0 q1 q2 q3) * p3)) < 2 ^ W)
    (hQ : q0 + (base a0 a1 a2 a3 p0 p1 p2 p3 q0 q1 q2 q3) * (q1 + (base a0 a1 a2 a3 p0 p1 p2 p3 q0 q1 q2 q3) * (q2 + (base a0 a1 a2 a3 p0 p1 p2 p3 q0 q1 q2 q3) * q3)) < 2 ^ W)
    (hF : f + selMag [(a0, p0, q0), (a1, p1, q1), (a2, p2, q2), (a3, p3, q3)] < 2 ^ W) (hn : n + 1 < 2 ^ W) :
    LRuns W machine (130 * W * W + 700 * W + 900) (bst a0 a1 a2 a3 p0 p1 p2 p3 q0 q1 q2 q3 0 0 0 0 0 f n c)
      (bst a0 a1 a2 a3 p0 p1 p2 p3 q0 q1 q2 q3 0 0 0 0 0 (f + selMag [(a0, p0, q0), (a1, p1, q1), (a2, p2, q2), (a3, p3, q3)]) (n + 1) false) := by
  have hsel := selMag_eq a0 a1 a2 a3 p0 p1 p2 p3 q0 q1 q2 q3
  have h3 := run3 W a0 a1 a2 a3 p0 p1 p2 p3 q0 q1 q2 q3 (base a0 a1 a2 a3 p0 p1 p2 p3 q0 q1 q2 q3) (horner (base a0 a1 a2 a3 p0 p1 p2 p3 q0 q1 q2 q3) [a0, a1, a2, a3]) (horner (base a0 a1 a2 a3 p0 p1 p2 p3 q0 q1 q2 q3) [p0, p1, p2, p3]) (horner (base a0 a1 a2 a3 p0 p1 p2 p3 q0 q1 q2 q3) [q0, q1, q2, q3]) (((horner (base a0 a1 a2 a3 p0 p1 p2 p3 q0 q1 q2 q3) [p0, p1, p2, p3] : ℤ) - horner (base a0 a1 a2 a3 p0 p1 p2 p3 q0 q1 q2 q3) [q0, q1, q2, q3]).natAbs) f n (by rw [hsel] at hF; omega) hn
  rw [Nat.add_assoc, ← hsel] at h3
  exact ((run1 W a0 a1 a2 a3 p0 p1 p2 p3 q0 q1 q2 q3 f n c hB).seq ((run2 W a0 a1 a2 a3 p0 p1 p2 p3 q0 q1 q2 q3 f n hW hA hP hQ).seq h3)).enlarge (by nlinarith)

theorem at_run {N W : ℕ} (σ : Fin N → TS) (s : Fin 24 → Fin N) (hi : Function.Injective s)
    (a0 a1 a2 a3 p0 p1 p2 p3 q0 q1 q2 q3 f n : ℕ) (c : Bool)
    (hσ : ∀ j, σ (s j) = bst a0 a1 a2 a3 p0 p1 p2 p3 q0 q1 q2 q3 0 0 0 0 0 f n c j) (hW : 1 ≤ W)
    (hB : (base a0 a1 a2 a3 p0 p1 p2 p3 q0 q1 q2 q3) < 2 ^ W)
    (hA : a0 + (base a0 a1 a2 a3 p0 p1 p2 p3 q0 q1 q2 q3) * (a1 + (base a0 a1 a2 a3 p0 p1 p2 p3 q0 q1 q2 q3) * (a2 + (base a0 a1 a2 a3 p0 p1 p2 p3 q0 q1 q2 q3) * a3)) < 2 ^ W)
    (hP : p0 + (base a0 a1 a2 a3 p0 p1 p2 p3 q0 q1 q2 q3) * (p1 + (base a0 a1 a2 a3 p0 p1 p2 p3 q0 q1 q2 q3) * (p2 + (base a0 a1 a2 a3 p0 p1 p2 p3 q0 q1 q2 q3) * p3)) < 2 ^ W)
    (hQ : q0 + (base a0 a1 a2 a3 p0 p1 p2 p3 q0 q1 q2 q3) * (q1 + (base a0 a1 a2 a3 p0 p1 p2 p3 q0 q1 q2 q3) * (q2 + (base a0 a1 a2 a3 p0 p1 p2 p3 q0 q1 q2 q3) * q3)) < 2 ^ W)
    (hF : f + selMag [(a0, p0, q0), (a1, p1, q1), (a2, p2, q2), (a3, p3, q3)] < 2 ^ W) (hn : n + 1 < 2 ^ W) :
    LRuns W (RecoveryFocus.machine s machine) (130 * W * W + 700 * W + 900) σ
      (Function.update (Function.update (Function.update σ (s 1) (.flag false)) (s 22)
        (.reg (f + selMag [(a0, p0, q0), (a1, p1, q1), (a2, p2, q2), (a3, p3, q3)]))) (s 23) (.reg (n + 1))) := by
  have h := (run W a0 a1 a2 a3 p0 p1 p2 p3 q0 q1 q2 q3 f n c hW hB hA hP hQ hF hn).dockK s hi σ hσ [23, 22, 1]
    (by intro j hj; fin_cases j <;> simp [bst] at hj ⊢)
  exact h

end Body

end
end NearCubicWires.PacketsMeta

