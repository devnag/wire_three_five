import Proof.Wire_3_5.FinalPass.SdPrep1
import Proof.Wire_3_5.FinalPass.TabDec2

/-! # S4 (the seeds phase), part 24: the tables writer's request (P3:3170-3178)

The tables writer (`TabW.tab_writer`) starts from `frame w` on its input port, `w = reqT n len cap err L₀ L₁ nE` (the
empty THR tuple's request word with the unit numbers as its tail). **`reqWM o Rw`** writes it from registers: PA's
`WriteNat.writeNatM` (`natWord n`), the seven fixed bits (`rqBits`), the six unary fields (`rqFields`: per field a
copy of the value, PA's `onesLoop`, the field's `0`), the frame's end, the port rewound. **`reqWM_spec`**: from an
empty port, the port holds `frame (reqT n len cap err L₀ L₁ nE)`, everything else as it was.

Paper quantity of the main type: the tables writer's request word, `frame (reqT …)`. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSectionVars false

namespace NearCubicWires.WireExponent3_5.FinalPass.Sd
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimAsm
open NearCubicWires.WireExponent3_5.PrimAsm.WriteNat

theorem rqMarks_frameP (w : List Bool) : RepairOrdinary.Streaming.marks w = frameP w := rfl

theorem rqMarksLen (w : List Bool) : (RepairOrdinary.Streaming.marks w).length = 2 * w.length := by
  rw [rqMarks_frameP]; exact frameP_length w

section Gen
variable {ns nr : ℕ} (cap : ℕ) (o : Fin (ns + 1))

theorem rqAp_sh (σ : WState ns nr) (OP : Fin nr) (u : List Bool) (h : σ.sh o = (σ.st o).length) :
    (WriteNat.appendO σ o OP u).sh o = ((WriteNat.appendO σ o OP u).st o).length := by simp [h]

theorem rqAp_op (σ : WState ns nr) (OP : Fin nr) (u : List Bool) :
    (WriteNat.appendO σ o OP u).val OP = σ.val OP + u.length := by simp

theorem rqAp_ne (σ : WState ns nr) (OP q : Fin nr) (u : List Bool) (h : q ≠ OP) :
    (WriteNat.appendO σ o OP u).val q = σ.val q := by simp [Function.update_of_ne h]

/-- Fixed bits, each as the pair `[true, b]`. -/
def rqBits (OP : Fin nr) : List Bool → WM ns nr
  | [] => .skip
  | b :: bs => .seq (WriteNat.emitPair o OP b) (rqBits OP bs)

theorem rqBits_spec (OP : Fin nr) : ∀ (bs : List Bool) (σ : WState ns nr), σ.sh o = (σ.st o).length →
    σ.val OP + 2 * bs.length ≤ cap →
    WExec cap (rqBits o OP bs) σ (WriteNat.appendO σ o OP (RepairOrdinary.Streaming.marks bs)) (16 * bs.length)
  | [], σ, _, _ => by
    rw [show RepairOrdinary.Streaming.marks ([] : List Bool) = [] from rfl, WriteNat.appendO_nil]
    exact WExec.skip σ
  | b :: bs, σ, ho, hc => by
    simp only [List.length_cons] at hc
    have e1 := WriteNat.emitPair_spec cap o OP b σ ho (by omega)
    have e2 := rqBits_spec OP bs (WriteNat.appendO σ o OP [true, b]) (rqAp_sh o σ OP _ ho)
      (by rw [rqAp_op]; simp only [List.length_cons, List.length_nil]; omega)
    rw [WriteNat.appendO_append] at e2
    refine WExec.cast cap (WExec.seq e1 e2) ?_ (by simp only [List.length_cons]; omega)
    rw [show RepairOrdinary.Streaming.marks (b :: bs) = [true, b] ++ RepairOrdinary.Streaming.marks bs by
      simp [RepairOrdinary.Streaming.marks]]

/-- One unary field: the value copied into `K`, `K` ones, the field's `0`. -/
def rqField (OP K t v : Fin nr) : WM ns nr :=
  .seq (Hash4.wcopyR v K t) (.seq (WriteNat.onesLoop o OP K) (WriteNat.emitPair o OP false))

theorem rqField_spec (OP K t v : Fin nr) (hKO : K ≠ OP) (hKt : K ≠ t) (hvK : v ≠ K) (hvt : v ≠ t)
    (σ : WState ns nr) (hK : σ.val K = 0) (ht : σ.val t = 0) (ho : σ.sh o = (σ.st o).length)
    (hc : σ.val OP + 2 * σ.val v + 2 ≤ cap) :
    WExec cap (rqField o OP K t v) σ
      (WriteNat.appendO σ o OP (RepairOrdinary.Streaming.marks (List.replicate (σ.val v) true ++ [false])))
      (37 * σ.val v + 21) := by
  have e1 := Hash4.wcopyR_spec cap v K t hvK hvt hKt σ hK ht (by omega)
  have e2 := WriteNat.onesLoop_spec cap o OP K hKO (σ.val v) (σ.setv K (σ.val v)) (by simp) (by simpa using ho)
    (by simp [Function.update_apply, Ne.symm hKO]; omega) (by omega)
  have hval : (WriteNat.appendO σ o OP
      (RepairOrdinary.Streaming.marks (List.replicate (σ.val v) true))).val K = 0 := by
    rw [rqAp_ne o σ OP K _ hKO, hK]
  have hw : (WriteNat.appendO (σ.setv K (σ.val v)) o OP
      (RepairOrdinary.Streaming.marks (List.replicate (σ.val v) true))).setv K 0 =
      WriteNat.appendO σ o OP (RepairOrdinary.Streaming.marks (List.replicate (σ.val v) true)) := by
    rw [WriteNat.appendO_setv _ _ _ _ hKO, wsetv_setv]
    have := wsetv_same (WriteNat.appendO σ o OP
      (RepairOrdinary.Streaming.marks (List.replicate (σ.val v) true))) K
    rw [hval] at this
    exact this
  rw [hw] at e2
  have e3 := WriteNat.emitPair_spec cap o OP false
    (WriteNat.appendO σ o OP (RepairOrdinary.Streaming.marks (List.replicate (σ.val v) true)))
    (rqAp_sh o σ OP _ ho) (by rw [rqAp_op, rqMarksLen, List.length_replicate]; omega)
  refine WExec.cast cap (WExec.seq e1 (WExec.seq e2 e3)) ?_ (by omega)
  rw [WriteNat.appendO_append, WriteNat.marks_append]
  rfl

/-- The unary fields of the registers `vs`, in order. -/
def rqFields (OP K t : Fin nr) : List (Fin nr) → WM ns nr
  | [] => .skip
  | v :: vs => .seq (rqField o OP K t v) (rqFields OP K t vs)

theorem rqFields_spec (OP K t : Fin nr) (hKO : K ≠ OP) (hKt : K ≠ t) (htO : t ≠ OP) :
    ∀ (vs : List (Fin nr)) (σ : WState ns nr), (∀ v ∈ vs, v ≠ K ∧ v ≠ t ∧ v ≠ OP) → σ.val K = 0 →
      σ.val t = 0 → σ.sh o = (σ.st o).length → σ.val OP + 2 * (Data.unaryList (vs.map σ.val)).length ≤ cap →
      ∃ m, WExec cap (rqFields o OP K t vs) σ
        (WriteNat.appendO σ o OP (RepairOrdinary.Streaming.marks (Data.unaryList (vs.map σ.val)))) m ∧
        m ≤ 40 * (Data.unaryList (vs.map σ.val)).length
  | [], σ, _, _, _, _, _ => by
    refine ⟨0, ?_, Nat.zero_le _⟩
    rw [show RepairOrdinary.Streaming.marks (Data.unaryList (([] : List (Fin nr)).map σ.val)) = [] from rfl,
      WriteNat.appendO_nil]
    exact WExec.skip σ
  | v :: vs, σ, hv, hK, ht, ho, hc => by
    have hvs := hv v List.mem_cons_self
    have hul : Data.unaryList (σ.val v :: vs.map σ.val) =
        List.replicate (σ.val v) true ++ [false] ++ Data.unaryList (vs.map σ.val) := by
      simp [Data.unaryList]
    have hlen : (Data.unaryList (σ.val v :: vs.map σ.val)).length =
        σ.val v + 1 + (Data.unaryList (vs.map σ.val)).length := by
      rw [hul, List.length_append, List.length_append, List.length_replicate, List.length_singleton]
    rw [List.map_cons] at hc ⊢
    rw [hlen] at hc
    have e1 := rqField_spec cap o OP K t v hKO hKt hvs.1 hvs.2.1 σ hK ht ho (by omega)
    obtain ⟨τ, hτ⟩ : ∃ y : WState ns nr, y = WriteNat.appendO σ o OP
        (RepairOrdinary.Streaming.marks (List.replicate (σ.val v) true ++ [false])) := ⟨_, rfl⟩
    rw [← hτ] at e1
    have hτv : ∀ q, q ≠ OP → τ.val q = σ.val q := fun q hq => by rw [hτ, rqAp_ne o σ OP q _ hq]
    have hmap : vs.map τ.val = vs.map σ.val :=
      List.map_congr_left (fun q hq => hτv q (hv q (List.mem_cons_of_mem _ hq)).2.2)
    have hτop : τ.val OP = σ.val OP + 2 * (σ.val v + 1) := by
      rw [hτ, rqAp_op, rqMarksLen, List.length_append, List.length_replicate, List.length_singleton]
    obtain ⟨m, e2, hm⟩ := rqFields_spec OP K t hKO hKt htO vs τ
      (fun q hq => hv q (List.mem_cons_of_mem _ hq))
      (by rw [hτv K hKO, hK]) (by rw [hτv t htO, ht]) (by rw [hτ]; exact rqAp_sh o σ OP _ ho)
      (by rw [hmap, hτop]; omega)
    rw [hmap] at e2 hm
    have hfin : WriteNat.appendO τ o OP (RepairOrdinary.Streaming.marks (Data.unaryList (vs.map σ.val))) =
        WriteNat.appendO σ o OP (RepairOrdinary.Streaming.marks (Data.unaryList (σ.val v :: vs.map σ.val))) := by
      rw [hτ, WriteNat.appendO_append, ← WriteNat.marks_append, hul]
    rw [hfin] at e2
    exact ⟨_, WExec.seq e1 e2, by rw [hlen]; omega⟩

end Gen

section Req
variable {ns nr : ℕ} (cap : ℕ) (o : Fin (ns + 1)) (Rw : Fin 16 ↪ Fin nr)

/-- The writer's registers inside `Rw`: `0` the value, `1 … 6` scratch, `7` the position. -/
def rqR8 : Fin 8 ↪ Fin nr :=
  ⟨fun k => Rw (Fin.castLE (by omega) k), fun _ _ h => Fin.castLE_injective _ (Rw.injective h)⟩

/-- The seven fixed bits between `natWord n` and the tail (`reqW`'s flag and its two empty lists). -/
def rqFix : List Bool := [true, true, false, false, true, false, false]

/-- **The tables writer's request**: `natWord n`, the fixed bits, the six fields, the frame's end, the port
rewound. Registers: `Rw 0 = n`, `Rw 1 … 6` scratch, `Rw 7` the position, `Rw 8, 9` the field scratch,
`Rw 10 … 15 = len, cap, err, L₀, L₁, nE`. -/
def reqWM : WM ns nr :=
  .seq (WriteNat.writeNatM o (rqR8 Rw)) (.seq (rqBits o (Rw 7) rqFix)
    (.seq (rqFields o (Rw 7) (Rw 8) (Rw 9) [Rw 10, Rw 11, Rw 12, Rw 13, Rw 14, Rw 15])
    (.seq (emitC o (Rw 7) false) (WM.rewind o (Rw 7)))))

/-- The request writer's step bound. -/
def reqCost (n L : ℕ) : ℕ := (natBitLength n + 10) * (100 * n + 200) + 50 * L + 200

theorem reqWM_spec (n len cp err L0 L1 nE : ℕ) (σ : WState ns nr) (hst : σ.st o = []) (hsh : σ.sh o = 0)
    (hz : ∀ k : Fin 16, 1 ≤ k.val → k.val ≤ 9 → σ.val (Rw k) = 0) (h0 : σ.val (Rw 0) = n)
    (h10 : σ.val (Rw 10) = len) (h11 : σ.val (Rw 11) = cp) (h12 : σ.val (Rw 12) = err)
    (h13 : σ.val (Rw 13) = L0) (h14 : σ.val (Rw 14) = L1) (h15 : σ.val (Rw 15) = nE)
    (hc : n + 4 * (TabW.reqT n len cp err L0 L1 nE).length + 10 ≤ cap) :
    ∃ m, WExec cap (reqWM o Rw) σ (σ.sets o (frame (TabW.reqT n len cp err L0 L1 nE))) m ∧
      m ≤ reqCost n (TabW.reqT n len cp err L0 L1 nE).length := by
  have d : ∀ a b : Fin 16, a ≠ b → Rw a ≠ Rw b := fun a b h => Rw.injective.ne h
  have h7 : σ.val (Rw 7) = 0 := hz 7 (by decide) (by decide)
  have ho : σ.sh o = (σ.st o).length := by rw [hst, hsh]; rfl
  have hnw := ParseNat.natWord_length n
  have hwl : (TabW.reqT n len cp err L0 L1 nE).length = (RepairRepresentation.natWord n).length +
      (7 + (Data.unaryList [len, cp, err, L0, L1, nE]).length) := by
    rw [TabW.reqT_eq, List.length_append, List.length_append]; rfl
  have hfixl : rqFix.length = 7 := rfl
  -- natWord n
  have e1 : WExec cap (WriteNat.writeNatM o (rqR8 Rw)) σ
      (WriteNat.appendO σ o (Rw 7) (RepairOrdinary.Streaming.marks (RepairRepresentation.natWord n)))
      ((natBitLength n + 10) * (100 * n + 200)) := by
    have := WriteNat.writeNatM_spec cap o (rqR8 Rw) σ (hz 1 (by decide) (by decide)) (hz 2 (by decide) (by decide))
      (hz 3 (by decide) (by decide)) (hz 4 (by decide) (by decide)) (hz 5 (by decide) (by decide))
      (hz 6 (by decide) (by decide)) ho
      (by show σ.val (Rw 0) + σ.val (Rw 7) + 6 * natBitLength (σ.val (Rw 0)) + 6 ≤ cap
          rw [h0, h7]; omega)
    rw [show (rqR8 Rw) 0 = Rw 0 from rfl, show (rqR8 Rw) 7 = Rw 7 from rfl, h0] at this
    exact this
  -- the fixed bits
  have e2 := rqBits_spec cap o (Rw 7) rqFix
    (WriteNat.appendO σ o (Rw 7) (RepairOrdinary.Streaming.marks (RepairRepresentation.natWord n)))
    (rqAp_sh o σ _ _ ho) (by rw [rqAp_op, rqMarksLen, h7, hfixl]; omega)
  rw [WriteNat.appendO_append] at e2
  obtain ⟨τ2, hτ2⟩ : ∃ y : WState ns nr, y = WriteNat.appendO σ o (Rw 7)
      (RepairOrdinary.Streaming.marks (RepairRepresentation.natWord n) ++
        RepairOrdinary.Streaming.marks rqFix) := ⟨_, rfl⟩
  rw [← hτ2] at e2
  -- the six fields
  have hv8 : τ2.val (Rw 8) = 0 := by
    rw [hτ2, rqAp_ne o σ _ _ _ (d 8 7 (by decide)), hz 8 (by decide) (by decide)]
  have hv9 : τ2.val (Rw 9) = 0 := by
    rw [hτ2, rqAp_ne o σ _ _ _ (d 9 7 (by decide)), hz 9 (by decide) (by decide)]
  have hmap : [Rw 10, Rw 11, Rw 12, Rw 13, Rw 14, Rw 15].map τ2.val = [len, cp, err, L0, L1, nE] := by
    rw [hτ2]
    simp only [List.map_cons, List.map_nil]
    rw [rqAp_ne o σ _ _ _ (d 10 7 (by decide)), rqAp_ne o σ _ _ _ (d 11 7 (by decide)),
      rqAp_ne o σ _ _ _ (d 12 7 (by decide)), rqAp_ne o σ _ _ _ (d 13 7 (by decide)),
      rqAp_ne o σ _ _ _ (d 14 7 (by decide)), rqAp_ne o σ _ _ _ (d 15 7 (by decide)), h10, h11, h12, h13, h14,
      h15]
  have hmem : ∀ v ∈ [Rw 10, Rw 11, Rw 12, Rw 13, Rw 14, Rw 15], v ≠ Rw 8 ∧ v ≠ Rw 9 ∧ v ≠ Rw 7 := by
    intro v hv
    simp at hv
    rcases hv with rfl | rfl | rfl | rfl | rfl | rfl <;>
      exact ⟨d _ _ (by decide), d _ _ (by decide), d _ _ (by decide)⟩
  obtain ⟨m3, e3, hm3⟩ := rqFields_spec cap o (Rw 7) (Rw 8) (Rw 9) (d 8 7 (by decide)) (d 8 9 (by decide))
    (d 9 7 (by decide)) [Rw 10, Rw 11, Rw 12, Rw 13, Rw 14, Rw 15] τ2 hmem hv8 hv9
    (by rw [hτ2]; exact rqAp_sh o σ _ _ ho)
    (by rw [hmap, hτ2, rqAp_op, List.length_append, rqMarksLen, rqMarksLen, h7, hfixl]; omega)
  rw [hmap] at e3 hm3
  obtain ⟨τ3, hτ3⟩ : ∃ y : WState ns nr, y = WriteNat.appendO τ2 o (Rw 7)
      (RepairOrdinary.Streaming.marks (Data.unaryList [len, cp, err, L0, L1, nE])) := ⟨_, rfl⟩
  rw [← hτ3] at e3
  -- the frame's end
  have hfr : RepairOrdinary.Streaming.marks (RepairRepresentation.natWord n) ++
      RepairOrdinary.Streaming.marks rqFix ++
      RepairOrdinary.Streaming.marks (Data.unaryList [len, cp, err, L0, L1, nE]) ++ [false] =
      frame (TabW.reqT n len cp err L0 L1 nE) := by
    rw [frame_eq_frameP, ← rqMarks_frameP, TabW.reqT_eq, WriteNat.marks_append, WriteNat.marks_append,
      show rqFix = [true, true, false, false, true, false, false] from rfl]
    simp only [List.append_assoc]
  have e4 : WExec cap (emitC o (Rw 7) false) τ3 (WriteNat.appendO τ3 o (Rw 7) [false]) 7 := by
    have := emitC_spec cap o (Rw 7) false τ3 (by rw [hτ3, hτ2]; exact rqAp_sh o _ _ _ (rqAp_sh o σ _ _ ho))
      (by rw [hτ3, rqAp_op, hτ2, rqAp_op, List.length_append, rqMarksLen, rqMarksLen, rqMarksLen, h7, hfixl]
          omega)
    exact this
  have hend : WriteNat.appendO τ3 o (Rw 7) [false] =
      WriteNat.appendO σ o (Rw 7) (frame (TabW.reqT n len cp err L0 L1 nE)) := by
    rw [hτ3, hτ2, WriteNat.appendO_append, WriteNat.appendO_append]
    simp only [List.append_assoc] at hfr ⊢
    rw [hfr]
  rw [hend] at e4
  -- the port rewound
  obtain ⟨τ4, hτ4⟩ : ∃ y : WState ns nr,
      y = WriteNat.appendO σ o (Rw 7) (frame (TabW.reqT n len cp err L0 L1 nE)) := ⟨_, rfl⟩
  rw [← hτ4] at e4
  have hτ4v : τ4.val (Rw 7) = 2 * (TabW.reqT n len cp err L0 L1 nE).length + 1 := by
    rw [hτ4, rqAp_op, h7, frame_eq_frameP]; simp
  have e5 := wrewind_spec cap o (Rw 7) (τ4.val (Rw 7)) τ4 rfl (by rw [hτ4v]; omega)
  have hfin : (τ4.setv (Rw 7) 0).seth o (τ4.sh o - τ4.val (Rw 7)) =
      σ.sets o (frame (TabW.reqT n len cp err L0 L1 nE)) := by
    rw [hτ4]
    apply WState.eq
    · funext j
      by_cases hj : j = o
      · rw [hj]; simp [hsh, h7]
      · simp [Function.update_of_ne hj]
    · funext j
      by_cases hj : j = o
      · rw [hj]; simp [hst]
      · simp [Function.update_of_ne hj]
    · funext q
      by_cases hq : q = Rw 7
      · rw [hq]; simp [h7]
      · simp [Function.update_of_ne hq]
    · simp
  rw [hfin] at e5
  refine ⟨_, WExec.seq e1 (WExec.seq e2 (WExec.seq e3 (WExec.seq e4 e5))), ?_⟩
  unfold reqCost
  rw [hτ4v]
  omega

end Req

end NearCubicWires.WireExponent3_5.FinalPass.Sd
