import Codec.Frame
import CheckedPCPP.LitDecode

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

namespace NearCubicGates.Close.Recovery.HTParts

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimAsm.WriteNat
open NearCubicWires.RepairOrdinary.Streaming (marks)
open NearCubicGates.Close.CheckedPCPP.LitDecode (rtb_off rtb_off0)

variable {ns nr : ℕ} (cap : ℕ)

section Adv
variable (src dst : Fin (ns + 1)) (OP SC : Fin nr)

/-- `u` appended to `dst`, the head of `src` and the counter `SC` advanced by `k`. -/
def adv (σ : WState ns nr) (u : List Bool) (k : ℕ) : WState ns nr :=
  ((appendO σ dst OP u).seth src (σ.sh src + k)).setv SC (σ.val SC + k)

variable {src dst OP SC}

theorem adv_zero (σ : WState ns nr) : adv src dst OP SC σ [] 0 = σ := by
  unfold adv; rw [appendO_nil]; simp only [Nat.add_zero]; rw [wseth_same, wsetv_same]

theorem adv_adv (hsd : src ≠ dst) (hOS : OP ≠ SC) (σ : WState ns nr) (u u' : List Bool) (k k' : ℕ) :
    adv src dst OP SC (adv src dst OP SC σ u k) u' k' = adv src dst OP SC σ (u ++ u') (k + k') := by
  apply WState.eq
  · funext j; by_cases hj : j = src
    · subst hj; simp [adv, appendO, Function.update_apply, Ne.symm hsd]; ring
    · by_cases hd : j = dst
      · subst hd; simp [adv, appendO, Function.update_apply, hj]; ring
      · simp [adv, appendO, Function.update_apply, hj, hd]
  · funext j; by_cases hd : j = dst
    · subst hd; simp [adv, appendO, Function.update_apply, Ne.symm hsd]
    · simp [adv, appendO, Function.update_apply, hd]
  · funext r; by_cases hr : r = SC
    · subst hr; simp [adv, appendO, Function.update_apply, Ne.symm hOS]; ring
    · by_cases ho : r = OP
      · subst ho; simp [adv, appendO, Function.update_apply, hr]; ring
      · simp [adv, appendO, Function.update_apply, hr, ho]
  · simp [adv, appendO]

@[simp] theorem adv_st_dst (σ : WState ns nr) (u : List Bool) (k : ℕ) :
    (adv src dst OP SC σ u k).st dst = σ.st dst ++ u := by simp [adv, appendO]
@[simp] theorem adv_sh_dst (hsd : src ≠ dst) (σ : WState ns nr) (u : List Bool) (k : ℕ) :
    (adv src dst OP SC σ u k).sh dst = σ.sh dst + u.length := by
  simp [adv, appendO, Function.update_apply, Ne.symm hsd]
@[simp] theorem adv_st_src (hsd : src ≠ dst) (σ : WState ns nr) (u : List Bool) (k : ℕ) :
    (adv src dst OP SC σ u k).st src = σ.st src := by simp [adv, appendO, Function.update_apply, hsd]
@[simp] theorem adv_sh_src (σ : WState ns nr) (u : List Bool) (k : ℕ) :
    (adv src dst OP SC σ u k).sh src = σ.sh src + k := by simp [adv]
@[simp] theorem adv_val_OP (hOS : OP ≠ SC) (σ : WState ns nr) (u : List Bool) (k : ℕ) :
    (adv src dst OP SC σ u k).val OP = σ.val OP + u.length := by
  simp [adv, appendO, Function.update_apply, hOS]
@[simp] theorem adv_val_SC (σ : WState ns nr) (u : List Bool) (k : ℕ) :
    (adv src dst OP SC σ u k).val SC = σ.val SC + k := by simp [adv]

end Adv

/-! ## One cell -/

section Cell
variable (src dst : Fin (ns + 1)) (OP SC : Fin nr)

/-- Emit `E b` for the scanned bit `b` of `src`, then step `src` (counted in `SC`). -/
def cellE (E : Bool → WM ns nr) : WM ns nr := .seq (.ifs src (E true) (E false)) (WM.fwdC src SC)

/-- An emitter: `E b` appends `e b` to `dst` in `c` steps. -/
def Emits (e : Bool → List Bool) (E : Bool → WM ns nr) (c : ℕ) : Prop :=
  ∀ (b : Bool) (τ : WState ns nr), τ.sh dst = (τ.st dst).length → τ.val OP + (e b).length ≤ cap →
    WExec cap (E b) τ (appendO τ dst OP (e b)) c

variable {src dst OP SC}

theorem emits_pair : Emits cap dst OP (fun b => [true, b]) (fun b => emitPair dst OP b) 15 := fun b τ ho hc =>
  emitPair_spec cap dst OP b τ ho (by simpa using hc)

theorem emits_none : Emits cap dst OP (fun _ => []) (fun _ => WM.skip) 0 := fun _ τ _ _ => by
  rw [appendO_nil]; exact WExec.skip τ

theorem cellE_spec (hsd : src ≠ dst) (hOS : OP ≠ SC) {e : Bool → List Bool} {E : Bool → WM ns nr} {c : ℕ}
    (hE : Emits cap dst OP e E c) (σ : WState ns nr) (hd : σ.sh dst = (σ.st dst).length)
    (hc : σ.val OP + (e (readTapeBit (σ.st src) (σ.sh src))).length ≤ cap) (hsc : σ.val SC < cap) :
    WExec cap (cellE src SC E) σ (adv src dst OP SC σ (e (readTapeBit (σ.st src) (σ.sh src))) 1) (c + 7) := by
  set b := readTapeBit (σ.st src) (σ.sh src) with hb
  have h1 : WExec cap (.ifs src (E true) (E false)) σ (appendO σ dst OP (e b)) (c + 1) := by
    cases hbv : b
    · rw [hbv] at hc
      exact WExec.ifsF (by unfold wbit; rw [← hb, hbv]) (hE false σ hd hc)
    · rw [hbv] at hc
      exact WExec.ifsT (by unfold wbit; rw [← hb, hbv]) (hE true σ hd hc)
  have h2 := wfwdC_spec cap src SC (appendO σ dst OP (e b)) (by simp [appendO, Function.update_apply, Ne.symm hOS]; omega)
  refine WExec.mono (WExec.cast cap (WExec.seq h1 h2) ?_ le_rfl) (by omega)
  simp [adv, appendO, Function.update_apply, hsd, Ne.symm hsd, Ne.symm hOS]

end Cell

/-! ## Counted runs of cells -/

section Loops

end Loops

end NearCubicGates.Close.Recovery.HTParts
