import Proof.Wire_3_5.Foundations.OutMachineCarKit

/-! # The output machine carrier phase, part 5: the outer programs

On the outer layout (`CarL`: PA's streams and the log), around the two masked stages:

* **`mkT Dt`** / **`mkT_spec`**: `rb := |fpIn| + 2`, `rp1 := T = (|fpIn| + 2)^{Dt}` (P1's count, `powConstW`);
* **`s1P Dt`** / **`s1_spec`**: `mkT`, the log `:= 0^T` (the masked resets' workspace), the registers back at `0`;
* `keepL` (the request, the two tables, the two counts, stream `6`), **`eraseL`** (every other PA stream), `cntC`;
* **`s3P Dt`** / **`s3_spec`**: `1^c` on stream `6` (`c` read off the slots' first cells), `mkT`, every stream of
  `eraseL` `:= 0^T`, the registers back at `0`.

Paper quantity of the main type: the carrier phase's count `1^{|carriers|}` and its junk-free exit (P3:3071-3086). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

namespace NearCubicWires.WireExponent3_5.FinalPass.Out.CarS
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimAsm.Data
open NearCubicWires.WireExponent3_5.PrimAsm.DockW NearCubicWires.WireExponent3_5.PrimAsm.UnaryPow
open NearCubicWires.WireExponent3_5.FinalPass.Out.CarL NearCubicWires.WireExponent3_5.FinalPass.Out.CarM1
open NearCubicWires.WireExponent3_5.FinalPass.Out.CarKit
open NearCubicWires.WireExponent3_5.PrimAsm.SBErase (eraseW erase_spec)

/-! ## The bound `T` -/

/-- **`T := (|fpIn| + 2)^{Dt}`** into `rp1` (and `rb := |fpIn| + 2`). -/
def mkT (Dt : ℕ) : WM NS NR :=
  .seq (P1.cntW (oS sIN) rcnt rb) (.seq (.inc rb) (.seq (.inc rb) (powConstW powR Dt)))

def mkTCost (cap Dt N : ℕ) : ℕ := 27 * N + 3 + 1 + (3 + 1 + (3 + 1 + (Dt + 1) * (4 * PrimAsm.UnaryPow.sq cap)))

theorem mkT_spec (cap Dt : ℕ) (w : List Bool) (σ : OSt) (hA : σ.st (oS sIN) = frame w) (hh : σ.sh (oS sIN) = 0)
    (hb : σ.val rb = 0) (hp : σ.val rp1 = 0) (h2 : σ.val rw2 = 0) (h3 : σ.val rw3 = 0) (h4 : σ.val rw4 = 0)
    (hc : σ.val rcnt = 0) (hcap : (w.length + 2) ^ Dt ≤ cap) (hcap2 : 2 * w.length + 2 ≤ cap) :
    WExec cap (mkT Dt) σ ((σ.setv rb (w.length + 2)).setv rp1 ((w.length + 2) ^ Dt)) (mkTCost cap Dt w.length) := by
  have s1 := cntF_spec cap (oS sIN) rcnt rb (by decide) w σ hA hh hc hb (by omega)
  have s2 := WExec.inc (cap := cap) rb (σ.setv rb w.length) (by simp; omega)
  simp only [wsetv_val_self, wsetv_setv] at s2
  have s3 := WExec.inc (cap := cap) rb (σ.setv rb (w.length + 1)) (by simp; omega)
  simp only [wsetv_val_self, wsetv_setv] at s3
  have hR : ∀ j : Fin 5, 1 ≤ j.val → (σ.setv rb (w.length + 1 + 1)).val (powR j) = 0 := by
    intro j hj
    fin_cases j
    · simp at hj
    · simpa [powR, Function.update_apply, rb, rp1] using hp
    · simpa [powR, Function.update_apply, rb, rw2] using h2
    · simpa [powR, Function.update_apply, rb, rw3] using h3
    · simpa [powR, Function.update_apply, rb, rw4] using h4
  have s4 := powConstW_spec cap powR Dt (σ.setv rb (w.length + 1 + 1)) (hR 1 (by decide)) (hR 2 (by decide))
    (hR 3 (by decide)) (hR 4 (by decide)) (by omega) (by simp [powR]; omega)
    (by
      simp only [show powR 0 = rb from rfl, wsetv_val_self]
      exact pow_le_of (by omega) (by simpa using hcap))
  simp only [show powR 0 = rb from rfl, show powR 1 = rp1 from rfl, wsetv_val_self] at s4
  exact WExec.cast cap (WExec.seq s1 (WExec.seq s2 (WExec.seq s3 s4))) rfl (by unfold mkTCost; omega)

/-- **The outer prologue**: `T`, the log `:= 0^T`, the registers back at `0`. -/
def s1P (Dt : ℕ) : WM NS NR := .seq (mkT Dt) (.seq (eraseW oLog rp1 rcnt) (WM.clear rb))

def s1Cost (cap Dt N : ℕ) : ℕ := mkTCost cap Dt N + 1 + (16 * (N + 2) ^ Dt + 3 + 1 + (3 * (N + 2) + 1))

theorem s1_spec (cap Dt : ℕ) (w : List Bool) (σ : OSt) (hA : σ.st (oS sIN) = frame w) (hsh : ∀ i, σ.sh i = 0)
    (hv : ∀ r, σ.val r = 0) (hlog : σ.st oLog = []) (hcap : (w.length + 2) ^ Dt ≤ cap)
    (hcap2 : 2 * w.length + 2 ≤ cap) :
    WExec cap (s1P Dt) σ (σ.sets oLog (List.replicate ((w.length + 2) ^ Dt) false)) (s1Cost cap Dt w.length) := by
  have s1 := mkT_spec cap Dt w σ hA (hsh _) (hv _) (hv _) (hv _) (hv _) (hv _) (hv _) hcap hcap2
  set T := (w.length + 2) ^ Dt with hT
  have s2 := erase_spec cap oLog rp1 rcnt (by decide) T ((σ.setv rb (w.length + 2)).setv rp1 T) (by simp)
    (by simp [Function.update_apply, rp1, rb, rcnt, hv]) (by simp [hsh]) (by simp [hlog]) hcap
  have s3 := wclear_spec cap rb (w.length + 2)
    ((((σ.setv rb (w.length + 2)).setv rp1 T).sets oLog (List.replicate T false)).setv rp1 0)
    (by simp [Function.update_apply, rp1, rb]) (by simp [Function.update_apply, rp1, rb]; omega)
  refine WExec.cast cap (WExec.seq s1 (WExec.seq s2 s3)) ?_ (by unfold s1Cost; omega)
  refine WState.eq rfl rfl ?_ rfl
  funext j
  simp only [WState.setv_val, WState.sets_val, Function.update_apply]
  split_ifs <;> simp [hv]

/-! ## The epilogue -/

/-- The streams the phase keeps: the request, the two tables, the two counts, stream `6`. -/
def keepL : List (Fin (DS + 1)) := [sIN, sCar 0 3, sCar 1 3, sCar 0 5, sCar 1 5, CarM2.s6]

/-- SB's variant keeps the counts only (the tables erased too). -/
def keepLS : List (Fin (DS + 1)) := [sIN, sCar 0 5, sCar 1 5, CarM2.s6]

/-- **Every other PA stream** (erased to `0^T`). -/
def eraseOf (kp : List (Fin (DS + 1))) : List (Fin (NS + 1)) :=
  ((List.finRange (DS + 1)).filter (fun i => decide (i ∉ kp))).map oS

theorem eraseOf_nodup (kp : List (Fin (DS + 1))) : (eraseOf kp).Nodup :=
  List.Nodup.map oS_inj (List.Nodup.filter _ (List.nodup_finRange _))

theorem mem_eraseOf (kp : List (Fin (DS + 1))) (i : Fin (NS + 1)) : i ∈ eraseOf kp ↔ ∃ j, j ∉ kp ∧ oS j = i := by
  unfold eraseOf
  simp [List.mem_map, List.mem_filter]

theorem eraseOf_length (kp : List (Fin (DS + 1))) : (eraseOf kp).length ≤ 9884 := by
  unfold eraseOf
  rw [List.length_map]
  exact (List.length_filter_le _ _).trans (by simp)

theorem eraseOf_ne6 (kp : List (Fin (DS + 1))) (h6 : CarM2.s6 ∈ kp) : ∀ i ∈ eraseOf kp, i ≠ oS CarM2.s6 := by
  intro i hi e
  obtain ⟨j, hj, hji⟩ := (mem_eraseOf kp i).1 hi
  rw [e] at hji
  have := oS_inj hji
  subst this
  exact hj h6


/-- The carriers' count from the slots' first cells. -/
def cntC : WM NS NR := .seq (.ifs (oS (sCar 0 0)) (.inc rn) .skip) (.ifs (oS (sCar 1 0)) (.inc rn) .skip)

theorem cntC_spec (cap : ℕ) (b0 b1 : Bool) (σ : OSt) (hb0 : wbit σ (oS (sCar 0 0)) = b0)
    (hb1 : wbit σ (oS (sCar 1 0)) = b1) (hn : σ.val rn = 0) (hc : 2 ≤ cap) :
    WExec cap cntC σ (σ.setv rn (b0.toNat + b1.toNat)) 9 := by
  have first : WExec cap (.ifs (oS (sCar 0 0)) (.inc rn) .skip) σ (σ.setv rn b0.toNat) 4 := by
    cases b0
    · have e : σ.setv rn (false.toNat) = σ := by rw [Bool.toNat_false, ← hn, wsetv_same]
      rw [e]; exact WExec.mono (WExec.ifsF hb0 (WExec.skip σ)) (by omega)
    · have i := WExec.inc (cap := cap) rn σ (by omega)
      rw [hn] at i
      exact WExec.ifsT hb0 i
  have second : WExec cap (.ifs (oS (sCar 1 0)) (.inc rn) .skip) (σ.setv rn b0.toNat)
      (σ.setv rn (b0.toNat + b1.toNat)) 4 := by
    have hb1' : wbit (σ.setv rn b0.toNat) (oS (sCar 1 0)) = b1 := by rw [wsbit_setv]; exact hb1
    cases b1
    · have e : (σ.setv rn b0.toNat) = σ.setv rn (b0.toNat + false.toNat) := by simp
      rw [← e]; exact WExec.mono (WExec.ifsF hb1' (WExec.skip _)) (by omega)
    · have i := WExec.inc (cap := cap) rn (σ.setv rn b0.toNat) (by simp; cases b0 <;> simp <;> omega)
      simp only [wsetv_val_self, wsetv_setv] at i
      exact WExec.ifsT hb1' i
  exact WExec.cast cap (WExec.seq first second) rfl (by omega)

/-- **The outer epilogue**: the count, `T`, every stream of `el` to `0^T`, the registers back at `0`. -/
def s3P (Dt : ℕ) (el : List (Fin (NS + 1))) : WM NS NR :=
  .seq cntC (.seq (emitR (oS CarM2.s6) rn rcnt) (.seq (mkT Dt) (.seq (eraseList rp1 rtmp rcnt rw2 el)
    (.seq (WM.clear rp1) (WM.clear rb)))))

def s3Cost (cap Dt N c : ℕ) : ℕ :=
  9 + 1 + (16 * c + 3 + 1 + (mkTCost cap Dt N + 1 + (9884 * (34 * (N + 2) ^ Dt + 8) + 1 +
    (3 * (N + 2) ^ Dt + 1 + 1 + (3 * (N + 2) + 1)))))

theorem s3_spec (cap Dt : ℕ) (kp : List (Fin (DS + 1))) (hk6 : CarM2.s6 ∈ kp) (w : List Bool) (b0 b1 : Bool)
    (σ : OSt) (hA : σ.st (oS sIN) = frame w)
    (hsh : ∀ i, σ.sh i = 0) (hv : ∀ r, σ.val r = 0) (hb0 : wbit σ (oS (sCar 0 0)) = b0)
    (hb1 : wbit σ (oS (sCar 1 0)) = b1) (h6 : σ.st (oS CarM2.s6) = [])
    (hL : ∀ i ∈ eraseOf kp, (σ.st i).length ≤ (w.length + 2) ^ Dt) (hcap : (w.length + 2) ^ Dt ≤ cap)
    (hcap2 : 2 * w.length + 2 ≤ cap) :
    WExec cap (s3P Dt (eraseOf kp)) σ (setsAll (σ.sets (oS CarM2.s6) (List.replicate (b0.toNat + b1.toNat) true))
      (eraseOf kp) (List.replicate ((w.length + 2) ^ Dt) false)) (s3Cost cap Dt w.length (b0.toNat + b1.toNat)) := by
  set T := (w.length + 2) ^ Dt with hT
  set c := b0.toNat + b1.toNat with hcdef
  have hc2 : c ≤ 2 := by rw [hcdef]; cases b0 <;> cases b1 <;> simp
  have x1 := cntC_spec cap b0 b1 σ hb0 hb1 (hv _) (by omega)
  have x2 := emitR_spec cap (oS CarM2.s6) rn rcnt (by decide) c (σ.setv rn c) (by simp) (by simp [h6])
    (by simp [hsh]) (by simp [Function.update_apply, rn, rcnt, hv]) (by omega)
  have e2 : ((σ.setv rn c).sets (oS CarM2.s6) (List.replicate c true)).setv rn 0 =
      σ.sets (oS CarM2.s6) (List.replicate c true) := by
    refine WState.eq rfl rfl ?_ rfl
    funext j; simp only [WState.setv_val, WState.sets_val, Function.update_apply]
    split_ifs with h
    · subst h; exact (hv _).symm
    · rfl
  rw [e2] at x2
  set σb := σ.sets (oS CarM2.s6) (List.replicate c true) with hσb
  have x3 := mkT_spec cap Dt w σb (by simp [hσb, Function.update_of_ne (show oS sIN ≠ oS CarM2.s6 by decide), hA])
    (by simp [hσb, hsh]) (hv _) (hv _) (hv _) (hv _) (hv _) (hv _) hcap hcap2
  have hne6 := eraseOf_ne6 kp hk6
  have x4 := eraseList_spec cap rp1 rtmp rcnt rw2 (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) T hcap (eraseOf kp) ((σb.setv rb (w.length + 2)).setv rp1 T) (eraseOf_nodup kp)
    (fun s hs => ⟨by simp [hσb, hsh], by
      simp only [WState.setv_st, hσb, WState.sets_st, Function.update_of_ne (hne6 s hs)]; exact hL s hs⟩)
    (by simp) (by simp [Function.update_apply, rtmp, rb, rp1, hσb, hv])
    (by simp [Function.update_apply, rcnt, rb, rp1, hσb, hv]) (by simp [Function.update_apply, rw2, rb, rp1, hσb, hv])
  have hlen := Nat.mul_le_mul_right (34 * T + 8) (eraseOf_length kp)
  have x4' := WExec.mono x4 hlen
  set σd := setsAll ((σb.setv rb (w.length + 2)).setv rp1 T) (eraseOf kp) (List.replicate T false) with hσd
  have hd1 : σd.val rp1 = T := by show ((σb.setv rb (w.length + 2)).setv rp1 T).val rp1 = T; simp
  have hd2 : σd.val rb = w.length + 2 := by
    show ((σb.setv rb (w.length + 2)).setv rp1 T).val rb = w.length + 2
    simp [Function.update_apply, rb, rp1]
  have x5 := wclear_spec cap rp1 T σd hd1 (by rw [hd1]; omega)
  have x6 := wclear_spec cap rb (w.length + 2) (σd.setv rp1 0)
    (by rw [WState.setv_val, Function.update_of_ne (show rb ≠ rp1 by decide)]; exact hd2)
    (by rw [WState.setv_val, Function.update_of_ne (show rb ≠ rp1 by decide), hd2]; omega)
  refine WExec.cast cap (WExec.seq x1 (WExec.seq x2 (WExec.seq x3 (WExec.seq x4' (WExec.seq x5 x6))))) ?_ ?_
  · refine WState.eq rfl rfl ?_ rfl
    funext j
    simp only [hσd, setsAll, WState.setv_val, WState.sets_val, Function.update_apply]
    split_ifs <;> simp [hσb, hv]
  · unfold s3Cost
    omega


end NearCubicWires.WireExponent3_5.FinalPass.Out.CarS
