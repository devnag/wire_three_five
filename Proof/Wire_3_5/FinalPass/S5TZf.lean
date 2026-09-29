import Proof.Wire_3_5.FinalPass.S5TUtil

/-! # S5-THR, part 17: framed zeros and the THR numbers' slot (P3:2150-2157, 2596-2599)

* `emitK_wSt'`, `wSt_rew` (a written word, the head rewound: the stream set to the word);
* `zfr` / **`zfr_spec`**: `frame (binary ℓ 0)` on a blank stream from `ℓ` in a register (PA's `Emit.repRegW`), head
  back at `0`, every register restored (the table builder's scratch words `ACC`, `NEW`, `ST`, `X`);
* `slot15W` / **`slot15W_spec`**: `unaryList [a, x, y, z]` from a register (`a`) and three unary ports (THR slot
  `15`, S2's numbers `a, |𝒢|, τ₀, |occs|`).

Paper quantities of the main types: the builder's zero words; S2's numbers (the THR per-point evaluator's reads). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false

namespace NearCubicWires.WireExponent3_5.FinalPass.S5T
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.SignedSortKey
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.FinalPass.HashSeed

variable {ns nr : ℕ} (cap : ℕ)

theorem emitK_wSt' (O : Fin (ns + 1)) (KW : Fin nr) (σ : WState ns nr) (hO : σ.sh O = (σ.st O).length)
    (u : List Bool) (b : Bool) (hc : σ.val KW + u.length < cap) :
    WExec cap (emitK O KW b) (wSt O KW σ u) (wSt O KW σ (u ++ [b])) 7 := by
  have hO' : (wSt O KW σ u).sh O = ((wSt O KW σ u).st O).length := by simp [wSt, hO]
  have e1 := emit1_spec cap O b (wSt O KW σ u) hO'
  have e2 := WExec.inc (cap := cap) KW (appW (wSt O KW σ u) O [b]) (by simp [wSt]; omega)
  refine WExec.cast cap (WExec.seq e1 e2) ?_ (by omega)
  apply WState.eq
  · funext i; by_cases hi : i = O
    · subst hi; simp [wSt, hO]; omega
    · simp [wSt, Function.update_apply, hi]
  · funext i; by_cases hi : i = O
    · subst hi; simp [wSt]
    · simp [wSt, Function.update_apply, hi]
  · funext r; by_cases hr : r = KW
    · subst hr; simp [wSt]; omega
    · simp [wSt, Function.update_apply, hr]
  · rfl

theorem wSt_rew (O : Fin (ns + 1)) (KW : Fin nr) (σ : WState ns nr) (w : List Bool) (hO : σ.st O = [])
    (hOh : σ.sh O = 0) (hKW : σ.val KW = 0) (hc : w.length ≤ cap) :
    WExec cap (WM.rewind O KW) (wSt O KW σ w) (σ.sets O w) (5 * w.length + 1) := by
  have e := wrewind_spec cap O KW w.length (wSt O KW σ w) (by simp [wSt, hKW]) (by simp [wSt, hKW]; omega)
  refine WExec.cast cap e ?_ le_rfl
  apply WState.eq
  · funext i; by_cases hi : i = O
    · subst hi; simp [wSt, hO, hOh]
    · simp [wSt, Function.update_apply, hi]
  · funext i; by_cases hi : i = O
    · subst hi; simp [wSt, hO]
    · simp [wSt, Function.update_apply, hi]
  · funext r; by_cases hr : r = KW
    · subst hr; simp [wSt, hKW]
    · simp [wSt, Function.update_apply, hr]
  · rfl

theorem binary_zero_rep : ∀ ℓ : ℕ, binary ℓ 0 = List.replicate ℓ false
  | 0 => rfl
  | ℓ + 1 => by rw [binary, binary_zero_rep ℓ]; rfl

theorem frame_zero_reps (ℓ : ℕ) : frame (binary ℓ 0) = PrimAsm.FiltRec.reps ℓ [true, false] ++ [false] := by
  rw [frame_pairs, binary_zero_rep, PrimAsm.FiltRec.flatMap_replicate]

/-- **Framed zeros** `frame (binary ℓ 0)` on `O`, `ℓ` read from `A`, the head rewound by `OP`. -/
def zfr (O : Fin (ns + 1)) (OP A K T : Fin nr) : WM ns nr :=
  .seq (PrimAsm.Emit.repRegW O OP A K T [true, false]) (.seq (emitK O OP false) (WM.rewind O OP))

/-- The framed zeros' cost. -/
def zfrCost (ℓ : ℕ) : ℕ := 18 * ℓ + 3 + 1 + (ℓ * 20 + 1) + 1 + (7 + 1 + (5 * (2 * ℓ + 1) + 1))

theorem zfr_spec (O : Fin (ns + 1)) (OP A K T : Fin nr) (hAK : A ≠ K) (hAT : A ≠ T) (hKT : K ≠ T) (hKO : K ≠ OP)
    (σ : WState ns nr) (ℓ : ℕ) (hO : σ.st O = []) (hOh : σ.sh O = 0) (hA : σ.val A = ℓ) (hK : σ.val K = 0)
    (hT : σ.val T = 0) (hOP : σ.val OP = 0) (hc : 2 * ℓ + 2 ≤ cap) :
    WExec cap (zfr O OP A K T) σ (σ.sets O (frame (binary ℓ 0))) (zfrCost ℓ) := by
  have e1 := PrimAsm.Emit.repRegW_spec cap O OP A K T hAK hAT hKT hKO [true, false] σ hK hT (by rw [hO, hOh]; rfl)
    (by omega) (by rw [hOP, hA]; simp; omega)
  rw [appendO_wSt σ O OP _ (by rw [hO, hOh]; rfl), hA] at e1
  have hl : (PrimAsm.FiltRec.reps ℓ [true, false]).length = 2 * ℓ := by
    have := frame_zero_reps ℓ
    have h2 := congrArg List.length this
    rw [frame_length', binary_length, List.length_append] at h2
    simp at h2; omega
  have e2 := emitK_wSt' cap O OP σ (by rw [hO, hOh]; rfl) (PrimAsm.FiltRec.reps ℓ [true, false]) false
    (by rw [hOP, hl]; omega)
  have e3 := wSt_rew cap O OP σ (PrimAsm.FiltRec.reps ℓ [true, false] ++ [false]) hO hOh hOP (by simp [hl]; omega)
  refine WExec.cast cap (WExec.seq e1 (WExec.seq e2 e3)) (by rw [frame_zero_reps]) ?_
  have h20 : ℓ * (8 * [true, false].length + 4) = ℓ * 20 := by simp
  rw [h20, List.length_append, hl]
  unfold zfrCost; simp only [List.length_cons, List.length_nil]; omega

theorem reps_true : ∀ a : ℕ, PrimAsm.FiltRec.reps a [true] = List.replicate a true
  | 0 => rfl
  | a + 1 => by rw [PrimAsm.FiltRec.reps_succ, reps_true a, List.replicate_succ']

/-- **THR slot `15`**: `a` from a register, then three unary ports, each field closed by `0`. -/
def slot15W (O P3 P8 P9 : Fin (ns + 1)) (A KW K T K' : Fin nr) : WM ns nr :=
  .seq (PrimAsm.Emit.repRegW O KW A K T [true]) (.seq (emitK O KW false) (.seq (fieldR P3 O K' KW)
    (.seq (fieldR P8 O K' KW) (fieldR P9 O K' KW))))

theorem slot15W_spec (O P3 P8 P9 : Fin (ns + 1)) (h3 : P3 ≠ O) (h8 : P8 ≠ O) (h9 : P9 ≠ O) (A KW K T K' : Fin nr)
    (hAK : A ≠ K) (hAT : A ≠ T) (hKT : K ≠ T) (hKO : K ≠ KW) (hK' : K' ≠ KW) (σ : WState ns nr) (a x y z : ℕ)
    (hO : σ.st O = []) (hOh : σ.sh O = 0) (hA : σ.val A = a) (hK : σ.val K = 0) (hT : σ.val T = 0)
    (hKW : σ.val KW = 0) (hK0 : σ.val K' = 0)
    (hP3 : σ.st P3 = List.replicate x true) (hP3h : σ.sh P3 = 0) (hP8 : σ.st P8 = List.replicate y true)
    (hP8h : σ.sh P8 = 0) (hP9 : σ.st P9 = List.replicate z true) (hP9h : σ.sh P9 = 0)
    (hc : a + x + y + z + 4 ≤ cap) :
    WExec cap (slot15W O P3 P8 P9 A KW K T K') σ (wSt O KW σ (PrimAsm.Data.unaryList [a, x, y, z]))
      (40 * (a + x + y + z) + 120) := by
  have e1 := PrimAsm.Emit.repRegW_spec cap O KW A K T hAK hAT hKT hKO [true] σ hK hT (by rw [hO, hOh]; rfl)
    (by omega) (by rw [hKW, hA]; simp; omega)
  rw [appendO_wSt σ O KW _ (by rw [hO, hOh]; rfl), hA] at e1
  rw [reps_true] at e1
  have e2 := emitK_wSt' cap O KW σ (by rw [hO, hOh]; rfl) (List.replicate a true) false (by rw [hKW]; simp; omega)
  obtain ⟨o3, n3⟩ := reads_ones (σ.st P3) x hP3
  obtain ⟨o8, n8⟩ := reads_ones (σ.st P8) y hP8
  obtain ⟨o9, n9⟩ := reads_ones (σ.st P9) z hP9
  have e3 := fieldR_spec cap P3 O h3 K' KW hK' σ hK0 x (List.replicate a true ++ [false])
    (by rw [hP3h]; exact o3) (by rw [hP3h]; exact n3) (by rw [hKW]; simp; omega)
  have e4 := fieldR_spec cap P8 O h8 K' KW hK' σ hK0 y
    (List.replicate a true ++ [false] ++ (List.replicate x true ++ [false]))
    (by rw [hP8h]; exact o8) (by rw [hP8h]; exact n8) (by rw [hKW]; simp; omega)
  have e5 := fieldR_spec cap P9 O h9 K' KW hK' σ hK0 z
    (List.replicate a true ++ [false] ++ (List.replicate x true ++ [false]) ++ (List.replicate y true ++ [false]))
    (by rw [hP9h]; exact o9) (by rw [hP9h]; exact n9) (by rw [hKW]; simp; omega)
  have h12 : a * (8 * [true].length + 4) = 12 * a := by simp; ring
  refine WExec.cast cap (WExec.seq e1 (WExec.seq e2 (WExec.seq e3 (WExec.seq e4 e5)))) ?_ (by rw [h12]; omega)
  simp [PrimAsm.Data.unaryList, List.append_assoc]

end NearCubicWires.WireExponent3_5.FinalPass.S5T
