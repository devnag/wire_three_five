import Proof.Wire_3_5.Foundations.OutMachineSlot0G
import Proof.Wire_3_5.Foundations.OutMachineSlot1P

/-! # SA's slot 0, part 2: the request word trimmed out of the final pass's input

The geo writer reads `frame r.word`; the final pass's input is `frame (r.word ++ seed)`. The trim, on the slot-0
bank (`WState S0ns 17`: the input `I0`, a scratch `U0`, then the geo writer's tapes `gs j`, its request port
`T0 = gs (gInP flD)`): count `|fpIn|` ten times; copy the input frame to the scratch; skip the request word there
(`ReqSkip.reqSkip_spec`) and close it with a `false`; copy that frame, `frame r.word`, to the geo writer's request
port; rewind everything:

* the layout (`S0ns`, `I0`, `U0`, `gs`, `T0`, `Out0`, registers `f0 … R0`, `kk i`), `Vt` (the registers' values);
* **`trimP`**, **`trim_spec`**: `T0 = frame r.word`, the input kept, the scratch at most `2|fpIn|+1`, every other
  stream blank, every head and register `0`, within `3000·(|fpIn|+1)^2` steps at `28·(|fpIn|+1)`.

Paper quantity of the main type: the request word inside the final pass's input (P3:3165-3175). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

namespace NearCubicWires.WireExponent3_5.FinalPass.Out.Slot0
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.WireExponent3_5
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimAsm.GeoFront (GLt gInP gOutP)
open NearCubicWires.WireExponent3_5.PrimT.FlipsPack (flD)
open NearCubicWires.WireExponent3_5.FinalPass.Out.ReqSkip
open NearCubicWires.RepairOrdinary.Streaming (marks marks_append marks_length)

/-! ## The layout -/

/-- The slot-0 bank's stream count: the input, a scratch, the geo writer's tapes. -/
noncomputable def S0ns : ℕ := GLt flD + 2

theorem S0ns_eq : S0ns + 1 = GLt flD + 1 + 2 := by unfold S0ns; omega

def I0 : Fin (S0ns + 1) := ⟨0, by rw [S0ns_eq]; omega⟩
def U0 : Fin (S0ns + 1) := ⟨1, by rw [S0ns_eq]; omega⟩

/-- The geo writer's tape `j` on the slot-0 bank. -/
def gs (j : Fin (GLt flD + 1)) : Fin (S0ns + 1) := ⟨2 + j.val, by rw [S0ns_eq]; omega⟩

/-- The geo writer's request port and output port on the slot-0 bank. -/
noncomputable def T0 : Fin (S0ns + 1) := gs (gInP flD)
noncomputable def Out0 : Fin (S0ns + 1) := gs (gOutP flD)

theorem gs_inj : Function.Injective gs := fun a b h => by
  have h2 : 2 + a.val = 2 + b.val := congrArg Fin.val h
  exact Fin.ext (by omega)

theorem gs_ne_I (j : Fin (GLt flD + 1)) : gs j ≠ I0 := fun h => by
  have h2 : 2 + j.val = 0 := congrArg Fin.val h
  omega

theorem gs_ne_U (j : Fin (GLt flD + 1)) : gs j ≠ U0 := fun h => by
  have h2 : 2 + j.val = 1 := congrArg Fin.val h
  omega

theorem I_ne_U : I0 ≠ U0 := fun h => by
  have h2 : (0 : ℕ) = 1 := congrArg Fin.val h
  omega

def f0 : Fin 17 := 0
def c0 : Fin 17 := 1
def v0 : Fin 17 := 2
def p0 : Fin 17 := 3
def t0 : Fin 17 := 4
def M0 : Fin 17 := 5
def R0 : Fin 17 := 16

/-- The `i`-th copy of `|fpIn|`. -/
def kk (i : ℕ) (h : i < 10) : Fin 17 := ⟨6 + i, by omega⟩

/-- The registers' values: the mode flag `m`, copies `lo ≤ i < hi` of `L`, everything else `0`. -/
def Vt (L m lo hi : ℕ) : Fin 17 → ℕ := fun q =>
  if q.val = 5 then m else if 6 ≤ q.val ∧ q.val < 16 ∧ lo + 6 ≤ q.val ∧ q.val < hi + 6 then L else 0

theorem Vt_fill (L m lo hi : ℕ) (h : hi < 10) (hlo : lo ≤ hi) :
    Function.update (Vt L m lo hi) (kk hi h) L = Vt L m lo (hi + 1) := by
  funext q
  simp only [Function.update_apply, Vt, kk]
  by_cases hq : q = ⟨6 + hi, by omega⟩
  · subst hq; simp only [if_true]; split_ifs <;> omega
  · rw [if_neg hq]
    have hv : q.val ≠ 6 + hi := fun e => hq (Fin.ext e)
    split_ifs <;> omega

theorem Vt_use (L m lo hi : ℕ) (h : lo < 10) :
    Function.update (Vt L m lo hi) (kk lo h) 0 = Vt L m (lo + 1) hi := by
  funext q
  simp only [Function.update_apply, Vt, kk]
  by_cases hq : q = ⟨6 + lo, by omega⟩
  · subst hq; simp only [if_true]; split_ifs <;> omega
  · rw [if_neg hq]
    have hv : q.val ≠ 6 + lo := fun e => hq (Fin.ext e)
    split_ifs <;> omega

theorem Vt_M (L m lo hi x : ℕ) : Function.update (Vt L m lo hi) M0 x = Vt L x lo hi := by
  funext q
  simp only [Function.update_apply, Vt, M0]
  by_cases hq : q = 5
  · subst hq; simp
  · rw [if_neg hq]
    have hv : q.val ≠ 5 := fun e => hq (Fin.ext e)
    simp [hv]

theorem Vt_k (L m lo hi i : ℕ) (h : i < 10) (h1 : lo ≤ i) (h2 : i < hi) : Vt L m lo hi (kk i h) = L := by
  simp only [Vt, kk]; split_ifs <;> omega

theorem Vt_low (L m lo hi : ℕ) (q : Fin 17) (hq : q.val < 5) : Vt L m lo hi q = 0 := by
  simp only [Vt]; split_ifs <;> omega

theorem Vt_zero (L : ℕ) : Vt L 0 10 10 = fun _ => 0 := by
  funext q; simp only [Vt]; split_ifs <;> omega

theorem Vt_start (L : ℕ) : Vt L 0 0 0 = fun _ => 0 := by
  funext q; simp only [Vt]; split_ifs <;> omega

theorem Vt_R (L m lo hi : ℕ) : Vt L m lo hi R0 = 0 := by simp [Vt, R0]

theorem Vt_Mv (L m lo hi : ℕ) : Vt L m lo hi M0 = m := by simp [Vt, M0]

/-! ## The program -/

/-- Ten copies of `|fpIn|`. -/
noncomputable def cnt10 : WM S0ns 17 :=
  .seq (P1.cntW I0 R0 (kk 0 (by omega))) (.seq (P1.cntW I0 R0 (kk 1 (by omega))) (.seq (P1.cntW I0 R0 (kk 2 (by omega)))
    (.seq (P1.cntW I0 R0 (kk 3 (by omega))) (.seq (P1.cntW I0 R0 (kk 4 (by omega))) (.seq (P1.cntW I0 R0 (kk 5 (by omega)))
      (.seq (P1.cntW I0 R0 (kk 6 (by omega))) (.seq (P1.cntW I0 R0 (kk 7 (by omega)))
        (.seq (P1.cntW I0 R0 (kk 8 (by omega))) (P1.cntW I0 R0 (kk 9 (by omega)))))))))))

/-- **The trim.** -/
noncomputable def trimP : WM S0ns 17 :=
  .seq cnt10 (.seq (PrimT.CarWM.copyFrameW I0 U0) (.seq (WM.rewind I0 (kk 0 (by omega))) (.seq (WM.rewind I0 (kk 1 (by omega)))
    (.seq (WM.rewind U0 (kk 2 (by omega))) (.seq (WM.rewind U0 (kk 3 (by omega))) (.seq (.bwd U0)
      (.seq (reqSkipW U0 f0 c0 v0 p0 t0 M0) (.seq (.wr U0 false) (.seq (WM.rewind U0 (kk 4 (by omega)))
        (.seq (WM.rewind U0 (kk 5 (by omega))) (.seq (PrimT.CarWM.copyFrameW U0 T0)
          (.seq (WM.rewind U0 (kk 6 (by omega))) (.seq (WM.rewind U0 (kk 7 (by omega)))
            (.seq (WM.rewind T0 (kk 8 (by omega))) (.seq (WM.rewind T0 (kk 9 (by omega))) (.seq (.bwd T0)
              (.ifr M0 (.dec M0) .skip)))))))))))))))))

end NearCubicWires.WireExponent3_5.FinalPass.Out.Slot0
