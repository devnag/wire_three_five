import Proof.Wire_3_5.Primitive.SeedFix.C4Rec
import Proof.Wire_3_5.Compiler.MachineReqContract3

/-! # SEEDFIX C4.L, the printer dock part 1: framing the compiler's request word (P3:1728-1737, 1886-1890)

The compiler (`alg:compiler`, C3 v3′) leaves the printer's request `MatrixScoreBatch.word r` RAW on its output tape;
the printer (`alg:separable-printer`, base's `CompetitorCountTable.machine`) reads it FRAMED, `physicalInput r =
frame (word r)`. A machine cannot find the end of a raw word on a reused (blank-padded) tape, so the framer PARSES it:
the header's four self-delimiting naturals `d, p, G, w` (PA's `readNatM`), re-emitted framed (PA's `writeNatM`), then
the remaining `d·(2w+1) + G·(2w+2)(2p+3)` bits (the columns of `φ`, the `G` cuts of `2w+2` framed `(p+1)`-bit fields),
copied bit by bit with their markers, then the final `false`.

Paper quantity of the main type: the printer's request word `word r` (**`frameW_spec`**: stream 1 ends as
`frame (word r)`). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSectionVars false

namespace NearCubicWires.WireExponent3_5.PrimT.C4Frame
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.RepairRepresentation
open NearCubicWires.RepairOrdinary.MatrixScoreBatch (Request Cut word cutWord fields signMagnitude header)
open NearCubicWires.RepairOrdinary.SignedSortKey (binary binary_length)

/-! ## The request word's shape -/

/-- The request word after its four header naturals: the columns of `φ`, then the cuts. -/
def rest (r : Request) : List Bool := MatrixScorePhi.columnsWord r.width r.cols ++ r.cuts.flatMap (cutWord r.p)

theorem word_eq (r : Request) :
    word r = natWord r.d ++ (natWord r.p ++ (natWord r.Gates ++ (natWord r.width ++ rest r))) := by
  simp [word, header, rest, List.append_assoc]

/-- The length of the rest: `d·(2w+1) + G·((2w+2)(2p+3))`. -/
def restLen (d p G w : ℕ) : ℕ := d * (2 * w + 1) + G * ((2 * w + 2) * (2 * p + 3))

theorem signMagnitude_length (p : ℕ) (z : ℤ) : (signMagnitude p z).length = p + 1 := by
  simp [signMagnitude, binary_length]

theorem cutWord_length (r : Request) (c : Cut) (hc : c ∈ r.cuts) :
    (cutWord r.p c).length = (2 * r.width + 2) * (2 * r.p + 3) := by
  have hl := r.lengths c hc
  have hf : (fields c).length = 2 * r.width + 2 := by simp [fields, hl.1, hl.2]; ring
  unfold cutWord
  rw [List.length_flatMap]
  have : (fields c).map (fun z => (frame (signMagnitude r.p z)).length) =
      (fields c).map (fun _ => 2 * r.p + 3) := by
    apply List.map_congr_left; intro z _; rw [frame_length, signMagnitude_length]; ring
  rw [this, List.map_const', List.sum_replicate, hf, smul_eq_mul]

theorem rest_length (r : Request) : (rest r).length = restLen r.d r.p r.Gates r.width := by
  unfold rest restLen MatrixScorePhi.columnsWord
  rw [List.length_append, List.length_flatMap, List.length_flatMap]
  have h1 : r.cols.map (fun x => (frame (binary r.width x)).length) = r.cols.map (fun _ => 2 * r.width + 1) := by
    apply List.map_congr_left; intro x _; rw [frame_length, binary_length]
  have h2 : r.cuts.map (fun c => (cutWord r.p c).length) =
      r.cuts.map (fun _ => (2 * r.width + 2) * (2 * r.p + 3)) := by
    apply List.map_congr_left; intro c hc; exact cutWord_length r c hc
  rw [h1, h2, List.map_const', List.map_const', List.sum_replicate, List.sum_replicate, smul_eq_mul, smul_eq_mul]
  have hc : r.cols.length = r.d := by simp [Request.cols]
  rw [hc]
  rfl

/-! ## The framer's word program -/

/-- The framer's state: stream `0` the raw word, stream `1` the framed copy; 18 registers (`0…3` the header naturals
`d, p, G, w`, `4` the rest's length, `5, 6, 13` products, `7…12, 14…16` scratch, `17` the output's length). -/
abbrev FS := WState 1 18
abbrev FW := WM 1 18

/-- Read one header natural into register `x`. -/
def rdW (x : Fin 18) : FW := PrimAsm.ParseNat.readNatM false 0 7 8 x 9 10

def wR0 : Fin 8 ↪ Fin 18 := ⟨![0, 11, 12, 13, 14, 15, 16, 17], by decide⟩
def wR1 : Fin 8 ↪ Fin 18 := ⟨![1, 11, 12, 13, 14, 15, 16, 17], by decide⟩
def wR2 : Fin 8 ↪ Fin 18 := ⟨![2, 11, 12, 13, 14, 15, 16, 17], by decide⟩
def wR3 : Fin 8 ↪ Fin 18 := ⟨![3, 11, 12, 13, 14, 15, 16, 17], by decide⟩

def mA : Fin 5 ↪ Fin 18 := ⟨![0, 5, 4, 11, 12], by decide⟩
def mB : Fin 5 ↪ Fin 18 := ⟨![5, 6, 13, 11, 12], by decide⟩
def mC : Fin 5 ↪ Fin 18 := ⟨![2, 13, 4, 11, 12], by decide⟩

/-- The rest's length into register `4`: `d·(2w+1)`, then `G·((2w+2)(2p+3))`. -/
def lenW : FW :=
  .seq (FinalPass.Hash4.wcopyR 3 5 11) (.seq (PrimAsm.ParseNat.addTo 3 5 11) (.seq (.inc 5)
    (.seq (PrimAsm.UnaryArith.mulAddW mA) (.seq (FinalPass.Hash4.wcopyR 1 6 11) (.seq (PrimAsm.ParseNat.addTo 1 6 11)
      (.seq (.inc 6) (.seq (.inc 6) (.seq (.inc 6) (.seq (.inc 5) (.seq (PrimAsm.UnaryArith.mulAddW mB)
        (PrimAsm.UnaryArith.mulAddW mC)))))))))))

/-- Copy one bit with its marker. -/
def cpBit : FW := .seq (.ifs 0 (PrimAsm.WriteNat.emitPair 1 17 true) (PrimAsm.WriteNat.emitPair 1 17 false)) (.fwd 0)

/-- Copy register `4` bits. -/
def cpLoop : FW := .whr 4 (.seq (.dec 4) cpBit)

/-- One header field: read the natural into register `x`, write it framed. -/
def fieldW (x : Fin 18) (R : Fin 8 ↪ Fin 18) : FW := .seq (rdW x) (PrimAsm.WriteNat.writeNatM 1 R)

/-- The header: the four naturals, each read and written framed. -/
def hdrW : FW := .seq (fieldW 0 wR0) (.seq (fieldW 1 wR1) (.seq (fieldW 2 wR2) (fieldW 3 wR3)))

/-- **The framer.** -/
def frameW : FW := .seq hdrW (.seq lenW (.seq cpLoop (emitC 1 17 false)))

/-! ## The header phase -/

theorem bitLen_le (x : ℕ) : natBitLength x ≤ x + 1 := by
  unfold natBitLength
  have h1 := Nat.log_lt_self 2 (show x + 1 ≠ 0 by omega)
  have h2 := Nat.log_mono_right (show x ≤ x + 1 by omega) (b := 2)
  omega

theorem pow_bitLen_le (x : ℕ) : 2 ^ natBitLength x ≤ 2 * x + 2 := by
  unfold natBitLength
  rw [pow_succ]
  rcases Nat.eq_zero_or_pos x with h | h
  · subst h; simp
  · have := Nat.pow_log_le_self 2 (show x ≠ 0 by omega)
    omega

theorem nw_length (x : ℕ) : (natWord x).length = 2 * natBitLength x + 1 :=
  RepairOrdinary.MatrixScoreRawGateBounds.natWord_length x

theorem marks_length (u : List Bool) : (Streaming.marks u).length = 2 * u.length := by
  simp [Streaming.marks]; ring

/-- `readNatM`'s cost at `x`. -/
def rdC (x : ℕ) : ℕ := (natBitLength x + 2) * (40 * 2 ^ natBitLength x + 40)

/-- `writeNatM`'s cost at `v`. -/
def wtC (v : ℕ) : ℕ := (natBitLength v + 10) * (100 * v + 200)

variable (cap : ℕ)

theorem rd_step (x : Fin 18) (h7 : x ≠ 7) (h8 : x ≠ 8) (h9 : x ≠ 9) (h10 : x ≠ 10) (v : ℕ) (pre rest : List Bool)
    (σ : FS) (hst : σ.st 0 = pre ++ natWord v ++ rest) (hsh : σ.sh 0 = pre.length)
    (hz7 : σ.val 7 = 0) (hz8 : σ.val 8 = 0) (hz9 : σ.val 9 = 0) (hz10 : σ.val 10 = 0)
    (hcap : σ.val x + 2 ^ (natBitLength v + 1) ≤ cap) :
    WExec cap (rdW x) σ ((σ.seth 0 (pre.length + (natWord v).length)).setv x (σ.val x + v)) (rdC v) := by
  have h := PrimAsm.ParseNat.readNatM_spec cap false 0 7 8 x 9 10 (by decide) (Ne.symm h7) (by decide) (by decide)
    (Ne.symm h8) (by decide) (by decide) (Ne.symm h9) (by decide) h10 v pre rest σ
    (by simpa [PrimAsm.ParseNat.enc] using hst) hsh hz7 hz8 hz9 hz10 hcap
  show WExec cap (PrimAsm.ParseNat.readNatM false 0 7 8 x 9 10) σ _ _
  simpa only [PrimAsm.ParseNat.stp, Bool.false_eq_true, if_false, Nat.one_mul, rdC] using h

theorem wt_step (R : Fin 8 ↪ Fin 18) (σ : FS) (hw : σ.val (R 1) = 0) (hq : σ.val (R 2) = 0)
    (hrb : σ.val (R 3) = 0) (hL : σ.val (R 4) = 0) (hK : σ.val (R 5) = 0) (ht : σ.val (R 6) = 0)
    (ho : σ.sh 1 = (σ.st 1).length) (hcap : σ.val (R 0) + σ.val (R 7) + 6 * natBitLength (σ.val (R 0)) + 6 ≤ cap) :
    WExec cap (PrimAsm.WriteNat.writeNatM 1 R) σ
      (PrimAsm.WriteNat.appendO σ 1 (R 7) (Streaming.marks (natWord (σ.val (R 0))))) (wtC (σ.val (R 0))) := by
  have h := PrimAsm.WriteNat.writeNatM_spec cap 1 R σ hw hq hrb hL hK ht ho hcap
  simpa [wtC] using h

/-- **One header field**: the natural `v` at the raw stream's head is read into register `x` and appended framed. -/
theorem field_step (x : Fin 18) (hxlt : x.val < 7) (R : Fin 8 ↪ Fin 18) (hR0 : R 0 = x) (hR1 : R 1 = 11) (hR2 : R 2 = 12) (hR3 : R 3 = 13) (hR4 : R 4 = 14)
    (hR5 : R 5 = 15) (hR6 : R 6 = 16) (hR7 : R 7 = 17)
    (v : ℕ) (pre rest : List Bool) (σ : FS) (hst : σ.st 0 = pre ++ natWord v ++ rest) (hsh : σ.sh 0 = pre.length)
    (hx0 : σ.val x = 0) (hz : ∀ i : Fin 18, 7 ≤ i.val → i.val ≤ 16 → σ.val i = 0)
    (ho : σ.sh 1 = (σ.st 1).length) (hop : σ.val 17 = (σ.st 1).length)
    (hcap : 7 * v + (σ.st 1).length + 12 ≤ cap) :
    WExec cap (fieldW x R) σ
      (PrimAsm.WriteNat.appendO ((σ.seth 0 (pre.length + (natWord v).length)).setv x v) 1 17
        (Streaming.marks (natWord v))) (rdC v + 1 + wtC v) := by
  have bv := pow_bitLen_le v
  have lv := bitLen_le v
  have hx7 : x ≠ 7 := fun h => by rw [h] at hxlt; exact absurd hxlt (by decide)
  have hx8 : x ≠ 8 := fun h => by rw [h] at hxlt; exact absurd hxlt (by decide)
  have hx9 : x ≠ 9 := fun h => by rw [h] at hxlt; exact absurd hxlt (by decide)
  have hx10 : x ≠ 10 := fun h => by rw [h] at hxlt; exact absurd hxlt (by decide)
  have hx17 : x ≠ 17 := fun h => by rw [h] at hxlt; exact absurd hxlt (by decide)
  have s1 := rd_step cap x hx7 hx8 hx9 hx10 v pre rest σ hst hsh (hz 7 (by decide) (by decide))
    (hz 8 (by decide) (by decide)) (hz 9 (by decide) (by decide)) (hz 10 (by decide) (by decide))
    (by rw [hx0, pow_succ]; omega)
  rw [hx0, Nat.zero_add] at s1
  set σ1 := (σ.seth 0 (pre.length + (natWord v).length)).setv x v with hσ1
  have hne : ∀ j : Fin 18, 11 ≤ j.val → j.val ≤ 16 → σ1.val j = 0 := by
    intro j h1 h2
    have : j ≠ x := fun he => by rw [he] at h1; omega
    simp [σ1, Function.update_apply, this, hz j (by omega) h2]
  have s2 := wt_step cap R σ1 (by rw [hR1]; exact hne 11 (by decide) (by decide))
    (by rw [hR2]; exact hne 12 (by decide) (by decide)) (by rw [hR3]; exact hne 13 (by decide) (by decide))
    (by rw [hR4]; exact hne 14 (by decide) (by decide)) (by rw [hR5]; exact hne 15 (by decide) (by decide))
    (by rw [hR6]; exact hne 16 (by decide) (by decide)) (by simp [σ1, ho])
    (by
      rw [hR0, hR7]
      have e1 : σ1.val x = v := by simp [σ1]
      have e2 : σ1.val 17 = (σ.st 1).length := by simp [σ1, Function.update_apply, Ne.symm hx17, hop]
      rw [e1, e2]; omega)
  have e0 : σ1.val (R 0) = v := by rw [hR0]; simp [σ1]
  rw [e0, hR7] at s2
  exact WExec.seq s1 s2

/-- The header's framed words. -/
def hdrMarks (r : Request) : List Bool :=
  Streaming.marks (natWord r.d) ++ Streaming.marks (natWord r.p) ++ Streaming.marks (natWord r.Gates) ++
    Streaming.marks (natWord r.width)

/-- The header's four naturals' length. -/
def hdrLen (r : Request) : ℕ :=
  (natWord r.d).length + (natWord r.p).length + (natWord r.Gates).length + (natWord r.width).length

def hdrCost (r : Request) : ℕ :=
  rdC r.d + 1 + wtC r.d + 1 + (rdC r.p + 1 + wtC r.p + 1 + (rdC r.Gates + 1 + wtC r.Gates + 1 +
    (rdC r.width + 1 + wtC r.width)))

/-- The capacity the framer needs. -/
def frameCap (r : Request) : ℕ :=
  8 * (r.d + r.p + r.Gates + r.width) + 4 * (word r).length + (2 * r.width + 2) * (2 * r.p + 3) + 64

theorem hdr_spec (r : Request) (tl : List Bool) (σ : FS) (h0 : σ.st 0 = word r ++ tl) (hs0 : σ.sh 0 = 0)
    (h1 : σ.st 1 = []) (hs1 : σ.sh 1 = 0) (hv : ∀ i, σ.val i = 0) (hcap : frameCap r ≤ cap) :
    ∃ τ : FS, WExec cap hdrW σ τ (hdrCost r) ∧ τ.st 0 = σ.st 0 ∧ τ.sh 0 = hdrLen r ∧ τ.st 1 = hdrMarks r ∧
      τ.sh 1 = (hdrMarks r).length ∧ τ.val 17 = (hdrMarks r).length ∧ τ.val 0 = r.d ∧ τ.val 1 = r.p ∧
      τ.val 2 = r.Gates ∧ τ.val 3 = r.width ∧ (∀ i : Fin 18, 4 ≤ i.val → i.val < 17 → τ.val i = 0) := by
  have hw := word_eq r
  have hlen : (word r).length = hdrLen r + (rest r).length := by
    rw [hw]; simp only [List.length_append, hdrLen]; ring
  unfold frameCap at hcap
  unfold hdrLen at hlen
  have md := marks_length (natWord r.d)
  have mp := marks_length (natWord r.p)
  have mG := marks_length (natWord r.Gates)
  have nd := nw_length r.d
  have np := nw_length r.p
  have nG := nw_length r.Gates
  have nwl := nw_length r.width
  -- field d
  have s1 := field_step cap 0 (by decide) wR0 rfl rfl rfl rfl rfl rfl rfl rfl r.d []
    (natWord r.p ++ (natWord r.Gates ++ (natWord r.width ++ rest r)) ++ tl) σ
    (by rw [h0, hw]; simp) (by simp [hs0]) (hv 0) (fun i _ _ => hv i) (by rw [hs1, h1]; rfl) (by rw [hv, h1]; rfl)
    (by rw [h1]; simp; omega)
  set σ1 := PrimAsm.WriteNat.appendO ((σ.seth 0 ([].length + (natWord r.d).length)).setv 0 r.d) 1 17
    (Streaming.marks (natWord r.d)) with hσ1
  have z1 : ∀ i : Fin 18, 1 ≤ i.val → i.val ≤ 16 → σ1.val i = 0 := by
    intro i hi1 hi2
    have h17 : i ≠ 17 := by intro h; rw [h] at hi2; exact absurd hi2 (by decide)
    have h0' : i ≠ 0 := by intro h; rw [h] at hi1; exact absurd hi1 (by decide)
    simp [σ1, Function.update_apply, h17, h0', hv]
  -- field p
  have s2 := field_step cap 1 (by decide) wR1 rfl rfl rfl rfl rfl rfl rfl rfl r.p (natWord r.d)
    (natWord r.Gates ++ (natWord r.width ++ rest r) ++ tl) σ1
    (by simp [σ1, h0, hw]) (by simp [σ1]) (z1 1 (by decide) (by decide)) (fun i h h' => z1 i (by omega) h')
    (by simp [σ1, hs1, h1]) (by simp [σ1, hv, h1])
    (by simp [σ1, h1]; omega)
  set σ2 := PrimAsm.WriteNat.appendO ((σ1.seth 0 ((natWord r.d).length + (natWord r.p).length)).setv 1 r.p) 1 17
    (Streaming.marks (natWord r.p)) with hσ2
  have z2 : ∀ i : Fin 18, 2 ≤ i.val → i.val ≤ 16 → σ2.val i = 0 := by
    intro i hi1 hi2
    have h17 : i ≠ 17 := by intro h; rw [h] at hi2; exact absurd hi2 (by decide)
    have h1' : i ≠ 1 := by intro h; rw [h] at hi1; exact absurd hi1 (by decide)
    simp only [σ2, PrimAsm.WriteNat.appendO_val, WState.setv_val, WState.seth_val, Function.update_apply,
      if_neg h17, if_neg h1']
    exact z1 i (by omega) hi2
  -- field G
  have s3 := field_step cap 2 (by decide) wR2 rfl rfl rfl rfl rfl rfl rfl rfl r.Gates (natWord r.d ++ natWord r.p)
    (natWord r.width ++ rest r ++ tl) σ2
    (by simp [σ2, σ1, h0, hw]) (by simp [σ2, σ1]) (z2 2 (by decide) (by decide)) (fun i h h' => z2 i (by omega) h')
    (by simp [σ2, σ1, hs1, h1] <;> ring) (by simp [σ2, σ1, hv, h1] <;> ring)
    (by simp [σ2, σ1, h1]; omega)
  set σ3 := PrimAsm.WriteNat.appendO ((σ2.seth 0 ((natWord r.d ++ natWord r.p).length + (natWord r.Gates).length)).setv
    2 r.Gates) 1 17 (Streaming.marks (natWord r.Gates)) with hσ3
  have z3 : ∀ i : Fin 18, 3 ≤ i.val → i.val ≤ 16 → σ3.val i = 0 := by
    intro i hi1 hi2
    have h17 : i ≠ 17 := by intro h; rw [h] at hi2; exact absurd hi2 (by decide)
    have h2' : i ≠ 2 := by intro h; rw [h] at hi1; exact absurd hi1 (by decide)
    simp only [σ3, PrimAsm.WriteNat.appendO_val, WState.setv_val, WState.seth_val, Function.update_apply,
      if_neg h17, if_neg h2']
    exact z2 i (by omega) hi2
  -- field w
  have s4 := field_step cap 3 (by decide) wR3 rfl rfl rfl rfl rfl rfl rfl rfl r.width
    (natWord r.d ++ natWord r.p ++ natWord r.Gates) (rest r ++ tl) σ3
    (by simp [σ3, σ2, σ1, h0, hw]) (by simp [σ3, σ2, σ1] <;> ring) (z3 3 (by decide) (by decide))
    (fun i h h' => z3 i (by omega) h')
    (by simp [σ3, σ2, σ1, hs1, h1] <;> ring) (by simp [σ3, σ2, σ1, hv, h1] <;> ring)
    (by simp [σ3, σ2, σ1, h1]; omega)
  set σ4 := PrimAsm.WriteNat.appendO ((σ3.seth 0 ((natWord r.d ++ natWord r.p ++ natWord r.Gates).length +
    (natWord r.width).length)).setv 3 r.width) 1 17 (Streaming.marks (natWord r.width)) with hσ4
  refine ⟨σ4, WExec.seq s1 (WExec.seq s2 (WExec.seq s3 s4)), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [σ4, σ3, σ2, σ1]
  · simp [σ4, σ3, σ2, σ1, hdrLen] <;> ring
  · simp [σ4, σ3, σ2, σ1, h1, hdrMarks]
  · simp [σ4, σ3, σ2, σ1, hs1, hdrMarks, marks_length] <;> ring
  · simp [σ4, σ3, σ2, σ1, hv, hdrMarks, marks_length] <;> ring
  · simp [σ4, σ3, σ2, σ1, Function.update_apply]
  · simp [σ4, σ3, σ2, σ1, Function.update_apply]
  · simp [σ4, σ3, σ2, σ1, Function.update_apply]
  · simp [σ4, σ3, σ2, σ1, Function.update_apply]
  · intro i hi1 hi2
    have h17 : i ≠ 17 := by intro h; rw [h] at hi2; exact absurd hi2 (by decide)
    have h3' : i ≠ 3 := by intro h; rw [h] at hi1; exact absurd hi1 (by decide)
    simp only [σ4, PrimAsm.WriteNat.appendO_val, WState.setv_val, WState.seth_val, Function.update_apply,
      if_neg h17, if_neg h3']
    exact z3 i (by omega) (by omega)

/-! ## The rest's length -/

def lenC (d p G w : ℕ) : ℕ :=
  (18 * w + 3) + (18 * w + 3) + 3 + ((2 * w + 1) * (18 * d + 8) + 18 * (2 * w + 1) + 10) + (18 * p + 3) +
    (18 * p + 3) + 3 + 3 + 3 + 3 + ((2 * p + 3) * (18 * (2 * w + 2) + 8) + 18 * (2 * p + 3) + 10) +
    ((2 * w + 2) * (2 * p + 3) * (18 * G + 8) + 18 * ((2 * w + 2) * (2 * p + 3)) + 10) + 11

theorem lenW_spec (d p G w : ℕ) (σ : FS) (h0 : σ.val 0 = d) (h1 : σ.val 1 = p) (h2 : σ.val 2 = G) (h3 : σ.val 3 = w)
    (hz : ∀ i : Fin 18, 4 ≤ i.val → i.val < 17 → σ.val i = 0)
    (hcap : restLen d p G w + (2 * w + 2) * (2 * p + 3) + 2 * (d + p + G + w) + 8 ≤ cap) :
    ∃ τ : FS, WExec cap lenW σ τ (lenC d p G w) ∧ τ.st = σ.st ∧ τ.sh = σ.sh ∧ τ.val 4 = restLen d p G w ∧
      τ.val 17 = σ.val 17 := by
  have z := fun (k : ℕ) (hk : 4 ≤ k ∧ k < 17) => hz ⟨k, by omega⟩ hk.1 hk.2
  have z4 : σ.val 4 = 0 := z 4 (by omega)
  have z5 : σ.val 5 = 0 := z 5 (by omega)
  have z6 : σ.val 6 = 0 := z 6 (by omega)
  have z11 : σ.val 11 = 0 := z 11 (by omega)
  have z12 : σ.val 12 = 0 := z 12 (by omega)
  have z13 : σ.val 13 = 0 := z 13 (by omega)
  have hmul1 : d * (2 * w + 1) ≤ restLen d p G w := by unfold restLen; omega
  have hmul2 : G * ((2 * w + 2) * (2 * p + 3)) ≤ restLen d p G w := by unfold restLen; omega
  have s1 := FinalPass.Hash4.wcopyR_spec cap 3 5 11 (by decide) (by decide) (by decide) σ z5 z11 (by rw [h3]; omega)
  rw [h3] at s1
  set σ1 := σ.setv 5 w with hσ1
  have s2 := PrimAsm.ParseNat.addTo_spec cap 3 5 11 (by decide) (by decide) (by decide) σ1 (by simp [σ1, z11])
    (by simp [σ1, h3]; omega) (by simp [σ1, h3]; omega)
  have e2a : σ1.val 3 = w := by simp [σ1, h3]
  have e2b : σ1.val 5 = w := by simp [σ1]
  rw [e2a, e2b] at s2
  set σ2 := σ1.setv 5 (w + w) with hσ2
  have s3 := WExec.inc (cap := cap) 5 σ2 (by simp [σ2]; omega)
  have e3 : σ2.val 5 + 1 = 2 * w + 1 := by simp [σ2]; omega
  rw [e3] at s3
  set σ3 := σ2.setv 5 (2 * w + 1) with hσ3
  have s4 := PrimAsm.UnaryArith.mulAddW_spec cap mA σ3 (by simp [σ3, σ2, σ1, mA, z11]) (by simp [σ3, σ2, σ1, mA, z12])
    (by simp [σ3, σ2, σ1, mA]; omega) (by simp [σ3, σ2, σ1, mA, z4, h0]; omega) (by simp [σ3, σ2, σ1, mA, h0]; omega)
  have e4a : σ3.val (mA 0) = d := by simp [σ3, σ2, σ1, mA, h0]
  have e4b : σ3.val (mA 1) = 2 * w + 1 := by simp [σ3, σ2, σ1, mA]
  have e4c : σ3.val (mA 2) = 0 := by simp [σ3, σ2, σ1, mA, z4]
  rw [e4a, e4b, e4c, Nat.zero_add] at s4
  set σ4 := σ3.setv (mA 2) (d * (2 * w + 1)) with hσ4
  have s5 := FinalPass.Hash4.wcopyR_spec cap 1 6 11 (by decide) (by decide) (by decide) σ4
    (by simp [σ4, σ3, σ2, σ1, mA, z6]) (by simp [σ4, σ3, σ2, σ1, mA, z11]) (by simp [σ4, σ3, σ2, σ1, mA, h1]; omega)
  have e5 : σ4.val 1 = p := by simp [σ4, σ3, σ2, σ1, mA, h1]
  rw [e5] at s5
  set σ5 := σ4.setv 6 p with hσ5
  have s6 := PrimAsm.ParseNat.addTo_spec cap 1 6 11 (by decide) (by decide) (by decide) σ5
    (by simp [σ5, σ4, σ3, σ2, σ1, mA, z11]) (by simp [σ5, σ4, σ3, σ2, σ1, mA, h1]; omega)
    (by simp [σ5, σ4, σ3, σ2, σ1, mA, h1]; omega)
  have e6a : σ5.val 1 = p := by simp [σ5, σ4, σ3, σ2, σ1, mA, h1]
  have e6b : σ5.val 6 = p := by simp [σ5]
  rw [e6a, e6b] at s6
  set σ6 := σ5.setv 6 (p + p) with hσ6
  have s7 := WExec.inc (cap := cap) 6 σ6 (by simp [σ6]; omega)
  have e7 : σ6.val 6 + 1 = 2 * p + 1 := by simp [σ6]; omega
  rw [e7] at s7
  set σ7 := σ6.setv 6 (2 * p + 1) with hσ7
  have s8 := WExec.inc (cap := cap) 6 σ7 (by simp [σ7]; omega)
  have e8 : σ7.val 6 + 1 = 2 * p + 2 := by simp [σ7]
  rw [e8] at s8
  set σ8 := σ7.setv 6 (2 * p + 2) with hσ8
  have s9 := WExec.inc (cap := cap) 6 σ8 (by simp [σ8]; omega)
  have e9 : σ8.val 6 + 1 = 2 * p + 3 := by simp [σ8]
  rw [e9] at s9
  set σ9 := σ8.setv 6 (2 * p + 3) with hσ9
  have s10 := WExec.inc (cap := cap) 5 σ9 (by simp [σ9, σ8, σ7, σ6, σ5, σ4, σ3, mA]; omega)
  have e10 : σ9.val 5 + 1 = 2 * w + 2 := by simp [σ9, σ8, σ7, σ6, σ5, σ4, σ3, mA]
  rw [e10] at s10
  set σ10 := σ9.setv 5 (2 * w + 2) with hσ10
  have v10 : ∀ k : Fin 18, σ10.val k = σ3.val k ∨ k = 4 ∨ k = 5 ∨ k = 6 := by
    intro k
    by_cases h4' : k = 4
    · exact Or.inr (Or.inl h4')
    by_cases h5' : k = 5
    · exact Or.inr (Or.inr (Or.inl h5'))
    by_cases h6' : k = 6
    · exact Or.inr (Or.inr (Or.inr h6'))
    left
    simp [σ10, σ9, σ8, σ7, σ6, σ5, σ4, mA, Function.update_apply, h4', h5', h6']
  have s11 := PrimAsm.UnaryArith.mulAddW_spec cap mB σ10
    (by simp [σ10, σ9, σ8, σ7, σ6, σ5, σ4, σ3, σ2, σ1, mA, mB, z11])
    (by simp [σ10, σ9, σ8, σ7, σ6, σ5, σ4, σ3, σ2, σ1, mA, mB, z12])
    (by simp [σ10, σ9, mB]; omega) (by simp [σ10, σ9, σ8, σ7, σ6, σ5, σ4, σ3, σ2, σ1, mA, mB, z13]; omega)
    (by simp [σ10, mB]; omega)
  have e11a : σ10.val (mB 0) = 2 * w + 2 := by simp [σ10, mB]
  have e11b : σ10.val (mB 1) = 2 * p + 3 := by simp [σ10, σ9, mB]
  have e11c : σ10.val (mB 2) = 0 := by simp [σ10, σ9, σ8, σ7, σ6, σ5, σ4, σ3, σ2, σ1, mA, mB, z13]
  rw [e11a, e11b, e11c, Nat.zero_add] at s11
  set σ11 := σ10.setv (mB 2) ((2 * w + 2) * (2 * p + 3)) with hσ11
  have s12 := PrimAsm.UnaryArith.mulAddW_spec cap mC σ11
    (by simp [σ11, σ10, σ9, σ8, σ7, σ6, σ5, σ4, σ3, σ2, σ1, mA, mB, mC, z11])
    (by simp [σ11, σ10, σ9, σ8, σ7, σ6, σ5, σ4, σ3, σ2, σ1, mA, mB, mC, z12])
    (by simp [σ11, mB, mC]; omega)
    (by simp [σ11, σ10, σ9, σ8, σ7, σ6, σ5, σ4, σ3, σ2, σ1, mA, mB, mC, h2]; unfold restLen at *; omega)
    (by simp [σ11, σ10, σ9, σ8, σ7, σ6, σ5, σ4, σ3, σ2, σ1, mA, mB, mC, h2]; omega)
  have e12a : σ11.val (mC 0) = G := by simp [σ11, σ10, σ9, σ8, σ7, σ6, σ5, σ4, σ3, σ2, σ1, mA, mB, mC, h2]
  have e12b : σ11.val (mC 1) = (2 * w + 2) * (2 * p + 3) := by simp [σ11, mB, mC]
  have e12c : σ11.val (mC 2) = d * (2 * w + 1) := by simp [σ11, σ10, σ9, σ8, σ7, σ6, σ5, σ4, mA, mB, mC]
  rw [e12a, e12b, e12c] at s12
  refine ⟨_, WExec.cast cap (WExec.seq s1 (WExec.seq s2 (WExec.seq s3 (WExec.seq s4 (WExec.seq s5 (WExec.seq s6
    (WExec.seq s7 (WExec.seq s8 (WExec.seq s9 (WExec.seq s10 (WExec.seq s11 s12))))))))))) rfl
    (le_of_eq (by unfold lenC; ring)), ?_, ?_, ?_, ?_⟩
  · simp [σ11, σ10, σ9, σ8, σ7, σ6, σ5, σ4, σ3, σ2, σ1]
  · simp [σ11, σ10, σ9, σ8, σ7, σ6, σ5, σ4, σ3, σ2, σ1]
  · simp [σ11, mC, restLen] <;> ring
  · simp [σ11, σ10, σ9, σ8, σ7, σ6, σ5, σ4, σ3, σ2, σ1, mA, mB, mC]

/-! ## Copying the rest, and the framer -/

/-- The `k` bits of `W` from position `h`. -/
def cps (W : List Bool) (h k : ℕ) : List Bool := (List.range k).map fun j => readTapeBit W (h + j)

theorem cps_succ (W : List Bool) (h k : ℕ) : cps W h (k + 1) = cps W h k ++ [readTapeBit W (h + k)] := by
  simp [cps, List.range_succ]

theorem cps_eq (pre u t : List Bool) : cps (pre ++ u ++ t) pre.length u.length = u := by
  apply List.ext_getElem
  · simp [cps]
  · intro i h1 h2
    simp only [cps, List.getElem_map, List.getElem_range, readTapeBit]
    rw [List.append_assoc, List.getD_append_right _ _ _ _ (by omega), Nat.add_sub_cancel_left,
      List.getD_append _ _ _ _ h2, List.getD_eq_getElem _ _ h2]

theorem frame_marks : ∀ u : List Bool, frame u = Streaming.marks u ++ [false]
  | [] => rfl
  | b :: u => by
    show true :: b :: frame u = _
    rw [frame_marks u]
    simp [Streaming.marks]

theorem cpLoop_spec (L h : ℕ) (W X : List Bool) (σ : FS) (h0 : σ.st 0 = W) (hs0 : σ.sh 0 = h) (h1 : σ.st 1 = X)
    (hs1 : σ.sh 1 = X.length) (h17 : σ.val 17 = X.length) (h4 : σ.val 4 = L) (hcap : X.length + 2 * L + 2 ≤ cap)
    (hL : L ≤ cap) :
    WExec cap cpLoop σ (((PrimAsm.WriteNat.appendO σ 1 17 (Streaming.marks (cps W h L))).seth 0 (h + L)).setv 4 0)
      (L * (18 + 4) + 1) := by
  let S : ℕ → FS := fun k =>
    ((PrimAsm.WriteNat.appendO σ 1 17 (Streaming.marks (cps W h k))).seth 0 (h + k)).setv 4 (L - k)
  have hS0 : S 0 = σ := by
    apply WState.eq
    · funext i; simp only [S, WState.setv_sh, WState.seth_sh, PrimAsm.WriteNat.appendO_sh, Function.update_apply]
      split_ifs <;> subst_vars <;> simp_all [cps, Streaming.marks]
    · funext i; simp only [S, WState.setv_st, WState.seth_st, PrimAsm.WriteNat.appendO_st, Function.update_apply]
      split_ifs <;> subst_vars <;> simp_all [cps, Streaming.marks]
    · funext i; simp only [S, WState.setv_val, WState.seth_val, PrimAsm.WriteNat.appendO_val, Function.update_apply]
      split_ifs <;> subst_vars <;> simp_all [cps, Streaming.marks]
    · simp [S]
  have hloop := UnionMachine.Round.wloop cap 4 cpBit 18 L S (fun k _ => by simp [S]) hL
    (fun k hk => by
      set τ := (S k).setv 4 (L - k - 1) with hτ
      have hml : (Streaming.marks (cps W h k)).length = 2 * k := by rw [marks_length]; simp [cps]
      have ht0 : τ.st 0 = W := by simp [τ, S, h0]
      have hts0 : τ.sh 0 = h + k := by simp [τ, S]
      have ho : τ.sh 1 = (τ.st 1).length := by simp [τ, S, hs1, h1, hml]
      have hc : τ.val 17 + 2 ≤ cap := by simp [τ, S, h17, hml]; omega
      have hwb : wbit τ 0 = readTapeBit W (h + k) := by simp only [wbit, ht0, hts0]
      have hfw := WExec.fwd (cap := cap) 0 (PrimAsm.WriteNat.appendO τ 1 17 [true, readTapeBit W (h + k)])
      have hifs : WExec cap (.ifs 0 (PrimAsm.WriteNat.emitPair 1 17 true) (PrimAsm.WriteNat.emitPair 1 17 false)) τ
          (PrimAsm.WriteNat.appendO τ 1 17 [true, readTapeBit W (h + k)]) 16 := by
        cases hb : readTapeBit W (h + k)
        · exact WExec.ifsF (by rw [hwb, hb]) (PrimAsm.WriteNat.emitPair_spec cap 1 17 false τ ho hc)
        · exact WExec.ifsT (by rw [hwb, hb]) (PrimAsm.WriteNat.emitPair_spec cap 1 17 true τ ho hc)
      refine WExec.cast cap (WExec.seq hifs hfw) ?_ (le_refl _)
      apply WState.eq
      · funext i; simp only [τ, S, WState.setv_sh, WState.seth_sh, PrimAsm.WriteNat.appendO_sh, Function.update_apply]
        split_ifs <;> subst_vars <;> simp_all [cps_succ, Streaming.marks] <;> omega
      · funext i; simp only [τ, S, WState.setv_st, WState.seth_st, PrimAsm.WriteNat.appendO_st, Function.update_apply]
        split_ifs <;> subst_vars <;> simp_all [cps_succ, Streaming.marks]
      · funext i; simp only [τ, S, WState.setv_val, WState.seth_val, PrimAsm.WriteNat.appendO_val,
          Function.update_apply]
        split_ifs <;> subst_vars <;> simp_all [cps_succ, Streaming.marks] <;> omega
      · simp [τ, S])
  rw [hS0] at hloop
  refine WExec.cast cap hloop ?_ le_rfl
  simp [S]

/-- The framer's cost. -/
def frameCost (r : Request) : ℕ :=
  hdrCost r + 1 + (lenC r.d r.p r.Gates r.width + 1 + (restLen r.d r.p r.Gates r.width * (18 + 4) + 1 + 1 + 7))

/-- **The framer**: from the raw request word `word r` (any tail) on stream `0`, stream `1` ends as its framed copy
`frame (word r)` (the printer's `physicalInput r`), stream `0` unchanged. -/
theorem frameW_spec (r : Request) (tl : List Bool) (σ : FS) (h0 : σ.st 0 = word r ++ tl) (hs0 : σ.sh 0 = 0)
    (h1 : σ.st 1 = []) (hs1 : σ.sh 1 = 0) (hv : ∀ i, σ.val i = 0) (hcap : frameCap r ≤ cap) :
    ∃ τ : FS, WExec cap frameW σ τ (frameCost r) ∧ τ.st 0 = word r ++ tl ∧ τ.st 1 = frame (word r) := by
  obtain ⟨τ1, s1, a0, a1, a2, a3, a4, v0, v1, v2, v3, vz⟩ := hdr_spec cap r tl σ h0 hs0 h1 hs1 hv hcap
  have hw := word_eq r
  have hlen : (word r).length = hdrLen r + restLen r.d r.p r.Gates r.width := by
    rw [← rest_length, hw]; simp only [List.length_append, hdrLen]; ring
  have hml : (hdrMarks r).length = 2 * hdrLen r := by
    simp only [hdrMarks, hdrLen, List.length_append, marks_length]; ring
  unfold frameCap at hcap
  obtain ⟨τ2, s2, b0, b1, b2, b3⟩ := lenW_spec cap r.d r.p r.Gates r.width τ1 v0 v1 v2 v3 vz (by omega)
  have s3 := cpLoop_spec cap (restLen r.d r.p r.Gates r.width) (hdrLen r) (word r ++ tl) (hdrMarks r) τ2
    (by rw [b0, a0, h0]) (by rw [b1, a1]) (by rw [b0, a2]) (by rw [b1, a3]) (by rw [b3, a4]) b2 (by omega) (by omega)
  have hc : cps (word r ++ tl) (hdrLen r) (restLen r.d r.p r.Gates r.width) = rest r := by
    have e := cps_eq (natWord r.d ++ natWord r.p ++ natWord r.Gates ++ natWord r.width) (rest r) tl
    rw [rest_length] at e
    have e2 : (natWord r.d ++ natWord r.p ++ natWord r.Gates ++ natWord r.width).length = hdrLen r := by
      simp only [List.length_append, hdrLen]
    rw [e2] at e
    rw [← e, hw]
    simp [List.append_assoc]
  rw [hc] at s3
  set τ3 := ((PrimAsm.WriteNat.appendO τ2 1 17 (Streaming.marks (rest r))).seth 0
    (hdrLen r + restLen r.d r.p r.Gates r.width)).setv 4 0 with hτ3
  have hmr : (Streaming.marks (rest r)).length = 2 * restLen r.d r.p r.Gates r.width := by
    rw [marks_length, rest_length]
  have s4 := emitC_spec cap 1 17 false τ3 (by simp [τ3, b1, a3, b0, a2]) (by simp [τ3, b3, a4, hmr]; omega)
  refine ⟨_, WExec.seq s1 (WExec.seq s2 (WExec.seq s3 s4)), ?_, ?_⟩
  · simp [τ3, b0, a0, h0]
  · have e3 : τ3.st 1 = hdrMarks r ++ Streaming.marks (rest r) := by simp [τ3, b0, a2]
    simp only [WState.setv_st, WState.seth_st, WState.sets_st, Function.update_self]
    rw [e3, frame_marks, hw]
    simp [hdrMarks, PrimAsm.WriteNat.marks_append, List.append_assoc]

end NearCubicWires.WireExponent3_5.PrimT.C4Frame
