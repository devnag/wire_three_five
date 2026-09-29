import Proof.Wire_3_5.Foundations.OutMachineCarDock

/-! # The output machine carrier phase, part 2: the call's `1^n` and `1^L`

PA's carrier blocks (`Data.setup_spec`) need `1^n` on `sNT` and `1^L` on `sLT`, `L = (n+1)^{26} + 1` (every carrier
atom's description is below `L`: `Call`'s `WithinEnvelope 26`, P3:3071-3086). This stage reads `n` off the framed
request (PA's `readNatM`), computes `L` in unary registers (`powConstW`), and writes both counts:

* `emitR S r c` / **`emitR_spec`**: a register's value `m` as `1^m` on a blank stream, the register consumed, the
  head back at `0`;
* the registers `rn … rcnt` (`8 … 15`, off PA's `0 … 7`), `powR`;
* **`m1P`**, **`m1_spec`**: from the request (heads, registers `0`): `sNT = 1^n`, `sLT = 1^L`, every register `0`,
  every head `0` but the request's, every other stream kept.

Paper quantity of the main type: the call's `n` and the carriers' description bound `L = (n+1)^{26} + 1`. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

namespace NearCubicWires.WireExponent3_5.FinalPass.Out.CarM1
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimAsm.Data
open NearCubicWires.WireExponent3_5.PrimAsm.ParseNat NearCubicWires.WireExponent3_5.PrimAsm.UnaryPow

/-! ## A register as a unary word -/

section Emit
variable {ns nr : ℕ} (cap : ℕ)

def emitBody (S : Fin (ns + 1)) (r c : Fin nr) : WM ns nr := .seq (.dec r) (.seq (.wr S true) (.seq (.fwd S) (.inc c)))

/-- **`S := 1^m`** from `r = m` (consumed), the head back by the counter `c`. -/
def emitR (S : Fin (ns + 1)) (r c : Fin nr) : WM ns nr := .seq (.whr r (emitBody S r c)) (WM.rewind S c)

theorem emitLoop_spec (S : Fin (ns + 1)) (r c : Fin nr) (hrc : r ≠ c) :
    ∀ (m k : ℕ) (σ : WState ns nr), σ.val r = m → σ.st S = List.replicate k true → σ.sh S = k → σ.val c = k →
      k + m ≤ cap →
      WExec cap (.whr r (emitBody S r c)) σ
        ((((σ.sets S (List.replicate (k + m) true)).seth S (k + m)).setv r 0).setv c (k + m)) (m * 11 + 1)
  | 0, k, σ, hr, hS, hh, hc, _ => by
    refine WExec.cast cap (WExec.whrF hr) ?_ (by omega)
    refine WState.eq ?_ ?_ ?_ rfl
    · funext i; simp only [WState.setv_sh, WState.seth_sh, WState.sets_sh, Function.update_apply]
      split_ifs with h
      · subst h; simp [hh]
      · rfl
    · funext i; simp only [WState.setv_st, WState.seth_st, WState.sets_st, Function.update_apply]
      split_ifs with h
      · subst h; simp [hS]
      · rfl
    · funext j; simp only [WState.setv_val, WState.seth_val, WState.sets_val, Function.update_apply]
      split_ifs with h1 h2
      · subst h1; simp [hc]
      · subst h2; exact hr
      · rfl
  | m + 1, k, σ, hr, hS, hh, hc, hk => by
    have d := WExec.dec (cap := cap) r σ (by omega)
    rw [hr, Nat.add_sub_cancel] at d
    have w := WExec.wr (cap := cap) S true (σ.setv r m)
    simp only [WState.setv_st, WState.setv_sh, hS, hh] at w
    have e : writeTapeBit (List.replicate k true) k true = List.replicate k true ++ [true] := by
      have := PrimAsm.Data.wtb_end (List.replicate k true) true
      rwa [List.length_replicate] at this
    rw [e] at w
    have f := WExec.fwd (cap := cap) S ((σ.setv r m).sets S (List.replicate k true ++ [true]))
    simp only [WState.sets_sh, WState.setv_sh, hh] at f
    have i := WExec.inc (cap := cap) c (((σ.setv r m).sets S (List.replicate k true ++ [true])).seth S (k + 1))
      (by simp [Function.update_of_ne (Ne.symm hrc), hc]; omega)
    have ih := emitLoop_spec S r c hrc m (k + 1)
      ((((σ.setv r m).sets S (List.replicate k true ++ [true])).seth S (k + 1)).setv c
        ((((σ.setv r m).sets S (List.replicate k true ++ [true])).seth S (k + 1)).val c + 1))
      (by simp [Function.update_of_ne hrc])
      (by simp only [WState.setv_st, WState.seth_st, WState.sets_st, Function.update_self]
          exact (List.replicate_succ' ..).symm) (by simp)
      (by simp [Function.update_of_ne (Ne.symm hrc), hc]) (by omega)
    refine WExec.cast cap (WExec.whrT (by omega) (WExec.seq d (WExec.seq w (WExec.seq f i))) ih) ?_ (by ring_nf; omega)
    refine WState.eq ?_ ?_ ?_ rfl
    · funext j; simp only [WState.setv_sh, WState.seth_sh, WState.sets_sh, Function.update_apply]
      split_ifs <;> first | rfl | omega
    · funext j; simp only [WState.setv_st, WState.seth_st, WState.sets_st, Function.update_apply]
      split_ifs <;> first | rfl | (congr 1; omega)
    · funext j; simp only [WState.setv_val, WState.seth_val, WState.sets_val, Function.update_apply]
      split_ifs <;> first | rfl | omega

/-- **`S := 1^m`** on a blank stream. -/
theorem emitR_spec (S : Fin (ns + 1)) (r c : Fin nr) (hrc : r ≠ c) (m : ℕ) (σ : WState ns nr)
    (hr : σ.val r = m) (hS : σ.st S = []) (hh : σ.sh S = 0) (hc : σ.val c = 0) (hm : m ≤ cap) :
    WExec cap (emitR S r c) σ ((σ.sets S (List.replicate m true)).setv r 0) (16 * m + 3) := by
  have l := emitLoop_spec cap S r c hrc m 0 σ hr (by simp [hS]) hh hc (by omega)
  simp only [Nat.zero_add] at l
  have rw' := wrewind_spec cap S c m ((((σ.sets S (List.replicate m true)).seth S m).setv r 0).setv c m)
    (by simp) (by simp; omega)
  refine WExec.cast cap (WExec.seq l rw') ?_ (by omega)
  refine WState.eq ?_ ?_ ?_ rfl
  · funext j; simp only [WState.setv_sh, WState.seth_sh, WState.sets_sh, Function.update_apply]
    split_ifs with h
    · subst h; simp [hh]
    · rfl
  · funext j; simp only [WState.setv_st, WState.seth_st, WState.sets_st, Function.update_apply]
  · funext j; simp only [WState.setv_val, WState.seth_val, WState.sets_val, Function.update_apply]
    split_ifs with h1 h2 <;> (try subst_vars) <;> simp_all

end Emit

/-! ## The stage -/

/-- The stage's registers (off PA's `0 … 7`). -/
def rn : Fin DR := 8
def rb : Fin DR := 9
def rp1 : Fin DR := 10
def rw2 : Fin DR := 11
def rw3 : Fin DR := 12
def rw4 : Fin DR := 13
def rtmp : Fin DR := 14
def rcnt : Fin DR := 15

/-- `powConstW`'s registers: base, power, scratch. -/
def powR : Fin 5 ↪ Fin DR := ⟨![rb, rp1, rw2, rw3, rw4], by decide⟩

/-- The carriers' description bound. -/
def Lof (n : ℕ) : ℕ := (n + 1) ^ 26 + 1

/-- **The stage**: read `n`; `L := (n+1)^{26} + 1`; `sLT := 1^L`; `sNT := 1^n`. -/
def m1P : WM DS DR :=
  .seq (readNatM true sIN rf rc rn rp rt) (.seq (UnionMachine.BinW.dupR rn rb rtmp) (.seq (.inc rb)
    (.seq (powConstW powR 26) (.seq (.inc rp1) (.seq (WM.clear rb) (.seq (emitR sLT rp1 rcnt) (emitR sNT rn rcnt)))))))

/-- The stage's cost. -/
def m1Cost (cap n : ℕ) : ℕ :=
  (natBitLength n + 2) * (40 * 2 ^ natBitLength n + 40) + 1 + (18 * n + 3 + 1 + (3 + 1 + ((26 + 1) * (4 * PrimAsm.UnaryPow.sq cap) + 1 +
    (3 + 1 + (3 * (n + 1) + 1 + 1 + (16 * Lof n + 3 + 1 + (16 * n + 3)))))))

/-- **The stage's run**: the request's head moves, `sLT := 1^L`, `sNT := 1^n`, every register back at `0`. -/
theorem m1_spec (cap n : ℕ) (mb : Bool) (codes cc : List ℕ) (tl : List Bool) (σ : WState DS DR)
    (hIN : σ.st sIN = RepairOrdinary.frame (reqW n mb codes cc tl)) (hsh : ∀ i, σ.sh i = 0) (hv : ∀ r, σ.val r = 0)
    (hNT : σ.st sNT = []) (hLT : σ.st sLT = []) (hcap : Lof n ≤ cap) (hcapN : 2 ^ (natBitLength n + 1) ≤ cap) :
    WExec cap m1P σ (((σ.seth sIN (stp true * (RepairRepresentation.natWord n).length)).sets sLT
      (List.replicate (Lof n) true)).sets sNT (List.replicate n true)) (m1Cost cap n) := by
  have hn1 : n + 1 ≤ (n + 1) ^ 26 := Nat.le_self_pow (by decide) _
  have hL : (n + 1) ^ 26 + 1 ≤ cap := hcap
  have hIN' := hIN
  rw [enc_reqW] at hIN'
  have s1 := readNatM_spec cap true sIN rf rc rn rp rt (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) n []
    (enc true [mb] ++ (enc true (RepairRepresentation.natWord codes.length) ++
      (enc true (codes.flatMap RepairRepresentation.natWord) ++
        (enc true (RepairRepresentation.natWord cc.length) ++
          (enc true (cc.flatMap RepairRepresentation.natWord) ++ (enc true tl ++ [false]))))))
    σ (by rw [hIN']; rfl) (by simp [hsh]) (hv _) (hv _) (hv _) (hv _) (by rw [hv]; omega)
  simp only [List.length_nil, Nat.zero_add, hv] at s1
  set σ1 := (σ.seth sIN (stp true * (RepairRepresentation.natWord n).length)).setv rn n with hσ1
  have s2 := UnionMachine.BinW.dupR_spec cap rn rb rtmp (by decide) (by decide) (by decide) σ1 n (by simp [hσ1])
    (by simp [hσ1, Function.update_apply, hv, rb, rn]) (by simp [hσ1, Function.update_apply, hv, rtmp, rn]) (by omega)
  have s3 := WExec.inc (cap := cap) rb (σ1.setv rb n) (by simp; omega)
  simp only [wsetv_val_self, wsetv_setv] at s3
  have hR : ∀ j : Fin 5, 1 ≤ j.val → ((σ1.setv rb (n + 1)).val (powR j)) = 0 := by
    intro j hj
    fin_cases j
    · simp at hj
    all_goals simp [powR, hσ1, Function.update_apply, hv, rb, rp1, rw2, rw3, rw4, rn]
  have s4 := powConstW_spec cap powR 26 (σ1.setv rb (n + 1)) (hR 1 (by decide)) (hR 2 (by decide))
    (hR 3 (by decide)) (hR 4 (by decide)) (by omega) (by simp [powR]; omega)
    (by
      simp only [show powR 0 = rb from rfl, wsetv_val_self]
      exact pow_le_of (by omega) (by omega))
  simp only [show powR 0 = rb from rfl, show powR 1 = rp1 from rfl, wsetv_val_self] at s4
  have s5 := WExec.inc (cap := cap) rp1 ((σ1.setv rb (n + 1)).setv rp1 ((n + 1) ^ 26)) (by simp; omega)
  simp only [wsetv_val_self, wsetv_setv] at s5
  have s6 := wclear_spec cap rb (n + 1) ((σ1.setv rb (n + 1)).setv rp1 ((n + 1) ^ 26 + 1))
    (by simp [Function.update_apply, rb, rp1]) (by simp [Function.update_apply, rb, rp1]; omega)
  set σ6 := ((σ1.setv rb (n + 1)).setv rp1 ((n + 1) ^ 26 + 1)).setv rb 0 with hσ6
  have s7 := emitR_spec cap sLT rp1 rcnt (by decide) (Lof n) σ6
    (by simp [hσ6, Function.update_apply, rb, rp1, Lof]) (by simp [hσ6, hσ1, hLT])
    (by simp [hσ6, hσ1, hsh, Function.update_of_ne (show sLT ≠ sIN by decide)])
    (by simp [hσ6, hσ1, Function.update_apply, hv, rb, rp1, rn, rcnt]) hcap
  set σ7 := (σ6.sets sLT (List.replicate (Lof n) true)).setv rp1 0 with hσ7
  have s8 := emitR_spec cap sNT rn rcnt (by decide) n σ7
    (by simp [hσ7, hσ6, hσ1, Function.update_apply, rb, rp1, rn])
    (by simp [hσ7, hσ6, hσ1, hNT, Function.update_of_ne (show sNT ≠ sLT by decide)])
    (by simp [hσ7, hσ6, hσ1, hsh, Function.update_of_ne (show sNT ≠ sIN by decide)]) (by simp [hσ7, hσ6, hσ1, Function.update_apply, hv, rb, rp1, rn, rcnt])
    (by omega)
  refine WExec.cast cap (WExec.seq s1 (WExec.seq s2 (WExec.seq s3 (WExec.seq s4 (WExec.seq s5 (WExec.seq s6
    (WExec.seq s7 s8))))))) ?_ (by unfold m1Cost; omega)
  refine WState.eq rfl rfl ?_ rfl
  funext j
  simp only [hσ7, hσ6, hσ1, WState.setv_val, WState.sets_val, WState.seth_val, Function.update_apply]
  split_ifs <;> simp [hv]

end NearCubicWires.WireExponent3_5.FinalPass.Out.CarM1
