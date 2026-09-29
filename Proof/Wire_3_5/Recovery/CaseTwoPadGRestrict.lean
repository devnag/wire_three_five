import Proof.Wire_3_5.Primitive.Writers.CopyNat
import Proof.Wire_3_5.Recovery.CaseTwoPadG

/-! # Restricting a guessed oracle's description to the native inputs (P3:3637-3644, 3669-3671)

Realizes, on the description of the union machine's guessed oracle of the padded width `q`, the step behind "pad the
outer verifier to the exact width `q(N)` [...] All probabilities and the projection property are preserved"
(P3:3637-3644): the padded address bits above the native width `R` are constant `false`, so the substituted circuit
reads the oracle only through `restrictHigh R O` (`CaseTwoPadG.substituted_restrict`). This module computes that
restriction on the oracle's native description: a register program in C5's writable-stream language (`WM`, sound for
the compiled machine by `WExec.exec`) that reads `frame (R.bits)` and the raw description `PCPPNative.descriptor O`
(`natWord q`, `natWord len`, the nodes' three fields each, `natWord output`) and writes
`frame (PCPPNative.descriptor (restrictHigh R O))`: the arity field becomes `R`, and every input node `[1, i, 0]` with
`i ≥ R` becomes the constant node `[0, 0, 0]`.

Donors checked: PA's field kit (`readNatM`, `writeNatM`, `copyNatM`, `skipNatM`, `emitWordM`;
used), C5's `wcopyR`, `WM.clear`, `emitC` (used), PA's `bitBody` (used for the framed binary `R`); base
`PacketsMetaReadNat` reads a raw machine field (not a register program); no donor rewrites a native description.

Paper quantity of the main type (`restrictM_spec`): the description of the oracle restricted to the native width. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearCubicWires.WireExponent3_5.Transfer.CaseTwoPadG
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimAsm.ParseNat NearCubicWires.WireExponent3_5.PrimAsm.WriteNat
open NearCubicWires.WireExponent3_5.PrimAsm.CopyNat
open NearCubicWires.RepairOrdinary.Streaming (marks)

/-! ## Streams and registers -/

/-- The framed binary width `frame (R.bits)`. -/
abbrev sR : Fin 3 := 0
/-- The raw description. -/
abbrev sD : Fin 3 := 1
/-- The framed output. -/
abbrev sO : Fin 3 := 2

/-- `R`, the node count, the tag, the index. -/
abbrev rR : Fin 18 := 0
abbrev rN : Fin 18 := 1
abbrev rT : Fin 18 := 2
abbrev rI : Fin 18 := 3
/-- Scratch of the field readers: flag, count, power, temporary. -/
abbrev rF : Fin 18 := 4
abbrev rC : Fin 18 := 5
abbrev rP : Fin 18 := 6
abbrev rU : Fin 18 := 7
/-- The output position counter of the emitters. -/
abbrev rO : Fin 18 := 8
/-- The comparison's copies of `R` and of the index, and the copy temporary. -/
abbrev rA : Fin 18 := 15
abbrev rB : Fin 18 := 16
abbrev rX : Fin 18 := 17

/-- The writer's registers for the value in `v` (scratch `9 … 14`, position `rO`). -/
def wR : Fin 8 ↪ Fin 18 := ⟨![0, 9, 10, 11, 12, 13, 14, 8], by decide⟩
def wN : Fin 8 ↪ Fin 18 := ⟨![1, 9, 10, 11, 12, 13, 14, 8], by decide⟩
def wT : Fin 8 ↪ Fin 18 := ⟨![2, 9, 10, 11, 12, 13, 14, 8], by decide⟩
def wI : Fin 8 ↪ Fin 18 := ⟨![3, 9, 10, 11, 12, 13, 14, 8], by decide⟩

/-! ## The program -/

/-- Read `frame (R.bits)` (least significant first) into `rR`. -/
def readBinM : WM 2 18 := .seq (.inc rP) (.seq (.whs sR (bitBody true sR rR rP rU)) (WM.clear rP))

/-- A node that is not an input: write its tag (from `rT`) and copy its two fields. -/
def generalM : WM 2 18 :=
  .seq (writeNatM sO wT) (.seq (copyNatM false sD sO rF rC rO) (.seq (copyNatM false sD sO rF rC rO) (WM.clear rT)))

/-- An input node below `R`: tag `1`, the index (from `rI`), the third field copied. -/
def keepM : WM 2 18 :=
  .seq (emitWordM sO rO (RepairRepresentation.natWord 1)) (.seq (writeNatM sO wI) (copyNatM false sD sO rF rC rO))

/-- An input node at or above `R`: the constant node `[0, 0, 0]`; the third field skipped. -/
def dropM : WM 2 18 :=
  .seq (emitWordM sO rO (RepairRepresentation.natWord 0 ++ RepairRepresentation.natWord 0 ++
    RepairRepresentation.natWord 0)) (skipNatM false sD rF rC)

/-- The comparison: read the index into `rI`, copy `R` to `rA` and the index to `rB`, then `rA := R − i`. -/
def cmpM : WM 2 18 :=
  .seq (readNatM false sD rF rC rI rP rU) (.seq (FinalPass.Hash4.wcopyR rR rA rX)
    (.seq (FinalPass.Hash4.wcopyR rI rB rX) (.whr rB (.seq (.dec rB) (.dec rA)))))

/-- An input node: compare the index with `R`, keep or drop, clear. -/
def inputM : WM 2 18 := .seq cmpM (.seq (.ifr rA keepM dropM) (.seq (WM.clear rA) (WM.clear rI)))

/-- One node: read the tag; tag `0` or `≥ 2` is copied, tag `1` is an input. -/
def nodeM : WM 2 18 :=
  .seq (readNatM false sD rF rC rT rP rU)
    (.ifr rT (.seq (.dec rT) (.ifr rT (.seq (.inc rT) generalM) inputM)) generalM)

/-- The node loop's body. -/
def bodyM : WM 2 18 := .seq (.dec rN) (.seq nodeM (WM.clear rO))

/-- **The restriction program.** -/
def restrictM : WM 2 18 :=
  .seq readBinM (.seq (skipNatM false sD rF rC) (.seq (writeNatM sO wR)
    (.seq (readNatM false sD rF rC rN rP rU) (.seq (writeNatM sO wN) (.seq (WM.clear rO)
      (.seq (.whr rN bodyM) (.seq (copyNatM false sD sO rF rC rO) (.seq (emitC sO rO false)
        (.seq (WM.clear rO) (WM.clear rR))))))))))

/-! ## Reading the framed binary width -/

section Bin
variable (cap : ℕ)

theorem wseth_same {ns nr : ℕ} (σ : WState ns nr) (i : Fin (ns + 1)) : σ.seth i (σ.sh i) = σ :=
  WState.eq (by funext j; by_cases hj : j = i <;> simp [hj]) rfl rfl rfl

/-- The binary loop: from the marker of the `k`-th bit, with `rR` the value of the bits before it and `rP = 2^k`. -/
theorem binLoop_spec (bits : List Bool) (hcap : 2 ^ (bits.length + 1) ≤ cap) :
    ∀ (m k : ℕ) (σ : WState 2 18), k + m = bits.length → σ.st sR = marks bits ++ [false] → σ.sh sR = 2 * k →
      σ.val rR = CanonicalBinary.bitsValue (bits.take k) → σ.val rP = 2 ^ k → σ.val rU = 0 →
      WExec cap (.whs sR (bitBody true sR rR rP rU)) σ
        (((σ.seth sR (2 * bits.length)).setv rR (CanonicalBinary.bitsValue bits)).setv rP (2 ^ bits.length))
        (m * (40 * 2 ^ bits.length + 20) + 1) := by
  have hpowL : 2 ^ (bits.length + 1) = 2 * 2 ^ bits.length := by rw [pow_succ]; ring
  intro m
  induction m with
  | zero =>
    intro k σ hkm hst hsh hv hp _
    have hkL : k = bits.length := by omega
    rw [hkL] at hsh hv hp
    have hend : wbit σ sR = false := by
      simp only [wbit, hst, hsh]
      have := read_pre (marks bits) [false] 0
      rw [show (marks bits).length = 2 * bits.length by simp [marks]; ring] at this
      simp only [Nat.add_zero] at this
      rw [this]; rfl
    rw [List.take_of_length_le le_rfl] at hv
    have e : ((σ.seth sR (2 * bits.length)).setv rR (CanonicalBinary.bitsValue bits)).setv rP
        (2 ^ bits.length) = σ := by
      rw [← hsh, ← hv, ← hp, wseth_same, wsetv_same, wsetv_same]
    rw [e]
    exact WExec.mono (WExec.whsF hend) (by omega)
  | succ m ih =>
    intro k σ hkm hst hsh hv hp hu
    have hk : k < bits.length := by omega
    have hkL : 2 ^ k ≤ 2 ^ bits.length := Nat.pow_le_pow_right (by norm_num) hk.le
    have hk1L : 2 ^ (k + 1) ≤ 2 ^ bits.length := Nat.pow_le_pow_right (by norm_num) hk
    have hvk : CanonicalBinary.bitsValue (bits.take k) < 2 ^ k := by
      have := bitsValue_lt (bits.take k)
      rwa [List.length_take_of_le hk.le] at this
    have hmark : wbit σ sR = true := by
      simp only [wbit, hst, hsh]
      exact read_marks_mark [false] bits k hk
    have h1 := preE_spec cap true sR σ
    set σ1 := σ.seth sR (σ.sh sR + off true) with hσ1
    set b := bits.getD k false with hb
    have hbit : wbit σ1 sR = b := by
      simp only [wbit, σ1, WState.seth_st, WState.seth_sh, Function.update_self, hst, hsh, off]
      exact read_marks_bit [false] bits k hk
    have hσ1v : σ1.val = σ.val := rfl
    set σ2 := σ1.setv rR (σ1.val rR + b.toNat * σ1.val rP) with hσ2
    have h2 : WExec cap (.ifs sR (addTo rP rR rU) .skip) σ1 σ2 (18 * 2 ^ bits.length + 4) := by
      cases hbv : b with
      | true =>
        have ha := addTo_spec cap rP rR rU (by decide) (by decide) (by decide) σ1 (by rw [hσ1v]; exact hu)
          (by rw [hσ1v, hp]; omega) (by rw [hσ1v, hv, hp]; omega)
        have e : σ2 = σ1.setv rR (σ1.val rR + σ1.val rP) := by simp [σ2, hbv]
        rw [e]
        exact WExec.mono (WExec.ifsT (by rw [hbit, hbv]) ha) (by rw [hσ1v, hp]; omega)
      | false =>
        have e : σ2 = σ1 := by simp [σ2, hbv, wsetv_same]
        rw [e]
        exact WExec.mono (WExec.ifsF (by rw [hbit, hbv]) (WExec.skip σ1)) (by omega)
    have hσ2p : σ2.val rP = 2 ^ k := by
      simp [σ2, Function.update_apply, show rP ≠ rR by decide, hσ1v, hp]
    have hσ2u : σ2.val rU = 0 := by
      simp [σ2, Function.update_apply, show rU ≠ rR by decide, hσ1v, hu]
    have h3 := dbl_spec cap rP rU (by decide) σ2 hσ2u (by rw [hσ2p]; omega)
    set σ3 := σ2.setv rP (2 * σ2.val rP) with hσ3
    have h4 := WExec.fwd (cap := cap) sR σ3
    set σ4 := σ3.seth sR (σ3.sh sR + 1) with hσ4
    have hbv' := bitsValue_take_succ bits k hk
    have ih' := ih (k + 1) σ4 (by omega) (by simp [σ4, σ3, σ2, σ1, hst])
      (by simp [σ4, σ3, σ2, σ1, hsh, off]; ring)
      (by simp [σ4, σ3, σ2, σ1, Function.update_apply, show rR ≠ rP by decide, hv, hp, hbv', hb])
      (by simp [σ4, σ3, σ2, σ1, Function.update_apply, hp, show rP ≠ rR by decide]; ring)
      (by simp [σ4, σ3, σ2, σ1, Function.update_apply, show rU ≠ rP by decide, show rU ≠ rR by decide, hu])
    refine WExec.cast cap (WExec.whsT hmark (WExec.seq h1 (WExec.seq h2 (WExec.seq h3 h4))) ih') ?_ ?_
    · apply WState.eq
      · funext j; by_cases hj : j = sR <;> simp [σ4, σ3, σ2, σ1, hj]
      · simp [σ4, σ3, σ2, σ1]
      · funext j
        by_cases hjp : j = rP
        · subst hjp; simp
        · by_cases hjr : j = rR
          · subst hjr; simp [hjp]
          · simp [σ4, σ3, σ2, σ1, Function.update_apply, hjp, hjr]
      · simp [σ4, σ3, σ2, σ1]
    · have e : (m + 1) * (40 * 2 ^ bits.length + 20) = m * (40 * 2 ^ bits.length + 20) +
          (40 * 2 ^ bits.length + 20) := by ring
      have : off true = 1 := rfl
      omega

/-- **Reading `frame (R.bits)` into `rR`.** -/
theorem readBinM_spec (R : ℕ) (σ : WState 2 18) (hst : σ.st sR = marks R.bits ++ [false]) (hsh : σ.sh sR = 0)
    (hr : σ.val rR = 0) (hp : σ.val rP = 0) (hu : σ.val rU = 0) (hcap : 2 ^ (R.bits.length + 1) ≤ cap) :
    WExec cap readBinM σ ((σ.seth sR (2 * R.bits.length)).setv rR R)
      (R.bits.length * (40 * 2 ^ R.bits.length + 20) + 3 * 2 ^ R.bits.length + 8) := by
  have hL1 : 1 ≤ 2 ^ R.bits.length := Nat.one_le_two_pow
  have hpowL : 2 ^ (R.bits.length + 1) = 2 * 2 ^ R.bits.length := by rw [pow_succ]; ring
  have h1 := WExec.inc (cap := cap) rP σ (by rw [hp]; omega)
  set σ1 := σ.setv rP (σ.val rP + 1) with hσ1
  have h2 := binLoop_spec cap R.bits (by omega) R.bits.length 0 σ1 (by omega) (by simp [σ1, hst])
    (by simp [σ1, hsh]) (by simp [σ1, Function.update_apply, show rR ≠ rP by decide, hr, CanonicalBinary.bitsValue])
    (by simp [σ1, hp]) (by simp [σ1, Function.update_apply, show rU ≠ rP by decide, hu])
  set σ2 := ((σ1.seth sR (2 * R.bits.length)).setv rR (CanonicalBinary.bitsValue R.bits)).setv rP
    (2 ^ R.bits.length) with hσ2
  have h3 := wclear_spec cap rP (2 ^ R.bits.length) σ2 (by simp [σ2]) (by simp [σ2]; omega)
  refine WExec.cast cap (WExec.seq h1 (WExec.seq h2 h3)) ?_ ?_
  · rw [CanonicalBinary.bitsValue_natBits] at hσ2
    apply WState.eq
    · simp [σ2, σ1]
    · simp [σ2, σ1]
    · funext j
      by_cases hjp : j = rP
      · subst hjp; simp [σ2, σ1, Function.update_apply, show rP ≠ rR by decide, hp]
      · by_cases hjr : j = rR
        · subst hjr; simp [σ2, σ1, Function.update_apply, hjp, CanonicalBinary.bitsValue_natBits]
        · simp [σ2, σ1, Function.update_apply, hjp, hjr]
    · simp [σ2, σ1]
  · omega

end Bin

/-! ## One node -/

section Node
variable (cap : ℕ)

/-- The scratch registers (`4 … 17` except the position counter `8`) are `0`. -/
def Scr (σ : WState 2 18) : Prop := ∀ r : Fin 18, 4 ≤ r.val → r.val ≠ 8 → σ.val r = 0

theorem natWord_len (x : ℕ) : (RepairRepresentation.natWord x).length ≤ 2 * x + 3 := by
  rw [natWord_length]; have := natBitLength_le_self_succ x; omega

/-- **A node that is not an input** (tag `t` already read into `rT`): its tag written, its two fields copied. -/
theorem general_spec (t f1 f2 : ℕ) (pre rest : List Bool) (σ : WState 2 18)
    (hst : σ.st sD = pre ++ (RepairRepresentation.natWord f1 ++ RepairRepresentation.natWord f2) ++ rest)
    (hsh : σ.sh sD = pre.length) (ho : σ.sh sO = (σ.st sO).length) (hT : σ.val rT = t) (hS : Scr σ)
    (hcap : σ.val rO + 8 * (t + f1 + f2) + 64 ≤ cap) :
    WExec cap generalM σ
      (((appendO σ sO rO (marks (RepairRepresentation.natWord t ++ RepairRepresentation.natWord f1 ++
        RepairRepresentation.natWord f2))).seth sD
          (pre.length + (RepairRepresentation.natWord f1 ++ RepairRepresentation.natWord f2).length)).setv rT 0)
      ((natBitLength t + 10) * (100 * t + 200) + 300 * (t + f1 + f2) + 1000) := by
  have hLt := natBitLength_le_self_succ t
  have hLf1 := natBitLength_le_self_succ f1
  have hLf2 := natBitLength_le_self_succ f2
  have hn1 := natWord_len f1
  have hn2 := natWord_len f2
  have hnt := natWord_length t
  have s1 : WExec cap (writeNatM sO wT) σ (appendO σ sO rO (marks (RepairRepresentation.natWord t)))
      ((natBitLength t + 10) * (100 * t + 200)) := by
    have h := writeNatM_spec cap sO wT σ (hS 9 (by decide) (by decide)) (hS 10 (by decide) (by decide))
      (hS 11 (by decide) (by decide)) (hS 12 (by decide) (by decide)) (hS 13 (by decide) (by decide))
      (hS 14 (by decide) (by decide)) ho (by show σ.val rT + σ.val rO + 6 * natBitLength (σ.val rT) + 6 ≤ cap; rw [hT]; omega)
    rw [show σ.val (wT 0) = t from hT] at h
    exact h
  set τ1 := appendO σ sO rO (marks (RepairRepresentation.natWord t)) with hτ1
  have s2 := copyNatM_spec cap false sD sO (by decide) rF rC rO (by decide) (by decide) (by decide) f1 pre
    (RepairRepresentation.natWord f2 ++ rest) τ1 (by simp (config := {decide := true}) [τ1, hst, PrimAsm.ParseNat.enc, List.append_assoc])
    (by simp (config := {decide := true}) [τ1, hsh]) (by simp (config := {decide := true}) [τ1, ho]) (by simp (config := {decide := true}) [τ1, hS 4 (by decide) (by decide)])
    (by simp (config := {decide := true}) [τ1, hS 5 (by decide) (by decide)]) (by simp (config := {decide := true}) [τ1]; omega)
  set τ2 := (appendO τ1 sO rO (marks (RepairRepresentation.natWord f1))).seth sD
    (pre.length + stp false * (RepairRepresentation.natWord f1).length) with hτ2
  have s3 := copyNatM_spec cap false sD sO (by decide) rF rC rO (by decide) (by decide) (by decide) f2
    (pre ++ RepairRepresentation.natWord f1) rest τ2 (by simp (config := {decide := true}) [τ2, τ1, hst, PrimAsm.ParseNat.enc, List.append_assoc])
    (by simp (config := {decide := true}) [τ2, stp]) (by simp (config := {decide := true}) [τ2, τ1, ho]; ring) (by simp (config := {decide := true}) [τ2, τ1, hS 4 (by decide) (by decide)])
    (by simp (config := {decide := true}) [τ2, τ1, hS 5 (by decide) (by decide)]) (by simp (config := {decide := true}) [τ2, τ1]; omega)
  set τ3 := (appendO τ2 sO rO (marks (RepairRepresentation.natWord f2))).seth sD
    ((pre ++ RepairRepresentation.natWord f1).length + stp false * (RepairRepresentation.natWord f2).length) with hτ3
  have s4 := wclear_spec cap rT t τ3 (by simp (config := {decide := true}) [τ3, τ2, τ1, hT]) (by simp (config := {decide := true}) [τ3, τ2, τ1, hT]; omega)
  refine WExec.cast cap (WExec.seq s1 (WExec.seq s2 (WExec.seq s3 s4))) ?_ ?_
  · apply WState.eq
    · funext j
      by_cases hjD : j = sD
      · subst hjD; simp (config := {decide := true}) [τ3, τ2, stp]; ring
      · by_cases hjO : j = sO
        · subst hjO; simp (config := {decide := true}) [τ3, τ2, τ1]; ring
        · simp (config := {decide := true}) [τ3, τ2, τ1, Function.update_apply, hjD, hjO]
    · funext j
      by_cases hjO : j = sO
      · subst hjO; simp (config := {decide := true}) [τ3, τ2, τ1, marks_append]
      · simp (config := {decide := true}) [τ3, τ2, τ1, Function.update_apply, hjO]
    · funext j
      by_cases hjT : j = rT
      · subst hjT; simp
      · by_cases hjO : j = rO
        · subst hjO; simp (config := {decide := true}) [τ3, τ2, τ1]; ring
        · simp (config := {decide := true}) [τ3, τ2, τ1, Function.update_apply, hjT, hjO]
    · simp (config := {decide := true}) [τ3, τ2, τ1]
  · omega

/-- The comparison loop: `rB` times, decrement `rB` and `rA` (`rA := rA − rB`). -/
theorem decLoop_spec : ∀ (m : ℕ) (σ : WState 2 18), σ.val rB = m → m ≤ cap → σ.val rA ≤ cap →
    WExec cap (.whr rB (.seq (.dec rB) (.dec rA))) σ ((σ.setv rB 0).setv rA (σ.val rA - m)) (5 * m + 1)
  | 0, σ, h0, _, _ => by
    have e : (σ.setv rB 0).setv rA (σ.val rA - 0) = σ := by
      rw [Nat.sub_zero, ← h0, wsetv_same, wsetv_same]
    rw [e]
    exact WExec.whrF h0
  | m + 1, σ, h0, hm, ha => by
    have d1 := WExec.dec (cap := cap) rB σ (by omega)
    have d2 := WExec.dec (cap := cap) rA (σ.setv rB (σ.val rB - 1))
      (by simp (config := {decide := true}); omega)
    have ih := decLoop_spec m ((σ.setv rB (σ.val rB - 1)).setv rA ((σ.setv rB (σ.val rB - 1)).val rA - 1))
      (by simp (config := {decide := true}) [h0]) (by omega) (by simp (config := {decide := true}); omega)
    refine WExec.cast cap (WExec.whrT (by omega) (WExec.seq d1 d2) ih) ?_ (by omega)
    refine WState.eq rfl rfl ?_ rfl
    funext j
    by_cases hjA : j = rA
    · subst hjA; simp (config := {decide := true}); omega
    · by_cases hjB : j = rB
      · subst hjB; simp (config := {decide := true})
      · simp [Function.update_apply, hjA, hjB]

/-- **The comparison**: the index read into `rI`, `rA := R − i`, `rB` back to `0`. -/
theorem cmp_spec (R i : ℕ) (pre rest : List Bool) (σ : WState 2 18)
    (hst : σ.st sD = pre ++ RepairRepresentation.natWord i ++ rest) (hsh : σ.sh sD = pre.length)
    (hR : σ.val rR = R) (hI : σ.val rI = 0) (hA : σ.val rA = 0) (hB : σ.val rB = 0) (hF : σ.val rF = 0)
    (hC : σ.val rC = 0) (hP : σ.val rP = 0) (hU : σ.val rU = 0) (hX : σ.val rX = 0)
    (hcap : 8 * (i + R) + 64 ≤ cap) :
    WExec cap cmpM σ ((((σ.seth sD (pre.length + (RepairRepresentation.natWord i).length)).setv rI i).setv rA
      (R - i)).setv rB 0) (100 * (i + R + 4) ^ 2 + 200) := by
  have hLi := natBitLength_le_self_succ i
  have hPi := two_pow_natBitLength_le i
  have s1 := readNatM_spec cap false sD rF rC rI rP rU (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) i pre rest σ
    (by simp [hst, PrimAsm.ParseNat.enc]) hsh hF hC hP hU (by rw [hI, pow_succ]; omega)
  set τ1 := (σ.seth sD (pre.length + stp false * (RepairRepresentation.natWord i).length)).setv rI (σ.val rI + i)
    with hτ1
  have h1A : τ1.val rA = 0 := by simp (config := {decide := true}) [τ1, hA]
  have h1X : τ1.val rX = 0 := by simp (config := {decide := true}) [τ1, hX]
  have h1R : τ1.val rR = R := by simp (config := {decide := true}) [τ1, hR]
  have s2 := FinalPass.Hash4.wcopyR_spec cap rR rA rX (by decide) (by decide) (by decide) τ1 h1A h1X
    (by rw [h1R]; omega)
  set τ2 := τ1.setv rA (τ1.val rR) with hτ2
  have h2B : τ2.val rB = 0 := by simp (config := {decide := true}) [τ2, τ1, hB]
  have h2X : τ2.val rX = 0 := by simp (config := {decide := true}) [τ2, h1X]
  have h2I : τ2.val rI = i := by simp (config := {decide := true}) [τ2, τ1, hI]
  have s3 := FinalPass.Hash4.wcopyR_spec cap rI rB rX (by decide) (by decide) (by decide) τ2 h2B h2X
    (by rw [h2I]; omega)
  set τ3 := τ2.setv rB (τ2.val rI) with hτ3
  have h3B : τ3.val rB = i := by simp [τ3, h2I]
  have h3A : τ3.val rA = R := by simp (config := {decide := true}) [τ3, τ2, h1R]
  have s4 := decLoop_spec cap i τ3 h3B (by omega) (by rw [h3A]; omega)
  refine WExec.cast cap (WExec.seq s1 (WExec.seq s2 (WExec.seq s3 s4))) ?_ ?_
  · refine WState.eq ?_ ?_ ?_ ?_
    · simp [τ3, τ2, τ1, stp]
    · simp [τ3, τ2, τ1]
    · funext j
      by_cases hjB : j = rB
      · subst hjB; simp (config := {decide := true})
      · by_cases hjA : j = rA
        · subst hjA; simp (config := {decide := true}) [h3A]
        · by_cases hjI : j = rI
          · subst hjI; simp (config := {decide := true}) [τ3, τ2, τ1, hI]
          · simp [τ3, τ2, τ1, Function.update_apply, hjB, hjA, hjI]
    · simp [τ3, τ2, τ1]
  · rw [h1R, h2I]
    have hm := Nat.mul_le_mul (show natBitLength i + 2 ≤ i + 3 by omega)
      (show 40 * 2 ^ natBitLength i + 40 ≤ 80 * i + 120 by omega)
    nlinarith

/-- **Keep**: the input node `[1, i, 0]` (index from `rI`), the third field copied. -/
theorem keep_spec (i : ℕ) (pre rest : List Bool) (κ : WState 2 18)
    (hst : κ.st sD = pre ++ RepairRepresentation.natWord 0 ++ rest) (hsh : κ.sh sD = pre.length)
    (ho : κ.sh sO = (κ.st sO).length) (hI : κ.val rI = i) (hF : κ.val rF = 0) (hC : κ.val rC = 0)
    (hW : ∀ r : Fin 18, 9 ≤ r.val → r.val ≤ 14 → κ.val r = 0) (hcap : κ.val rO + 8 * i + 64 ≤ cap) :
    WExec cap keepM κ ((appendO κ sO rO (marks (RepairRepresentation.natWord 1 ++ RepairRepresentation.natWord i ++
      RepairRepresentation.natWord 0))).seth sD (pre.length + (RepairRepresentation.natWord 0).length))
      (100 * (i + 12) ^ 2 + 1000) := by
  have hLi := natBitLength_le_self_succ i
  have hni := natWord_len i
  have hn0 : (RepairRepresentation.natWord 0).length = 3 := by rw [natWord_length]; simp [natBitLength]
  have hn1 : (RepairRepresentation.natWord 1).length = 3 := by rw [natWord_length]; simp [natBitLength]
  have k1 := emitWordM_spec cap sO rO (RepairRepresentation.natWord 1) κ ho (by rw [hn1]; omega)
  set κ1 := appendO κ sO rO (marks (RepairRepresentation.natWord 1)) with hκ1
  have h1O : κ1.val rO = κ.val rO + 6 := by simp [κ1, hn1]
  have h1o : κ1.sh sO = (κ1.st sO).length := by simp [κ1, ho]
  have k2 : WExec cap (writeNatM sO wI) κ1 (appendO κ1 sO rO (marks (RepairRepresentation.natWord i)))
      ((natBitLength i + 10) * (100 * i + 200)) := by
    have hW1 : ∀ r : Fin 18, 9 ≤ r.val → r.val ≤ 14 → κ1.val r = 0 := by
      intro r h9 h14
      have hr : r ≠ rO := fun e => by rw [e] at h9; simp at h9
      simp [κ1, Function.update_apply, hr, hW r h9 h14]
    have h := writeNatM_spec cap sO wI κ1 (hW1 9 (by decide) (by decide)) (hW1 10 (by decide) (by decide))
      (hW1 11 (by decide) (by decide)) (hW1 12 (by decide) (by decide)) (hW1 13 (by decide) (by decide))
      (hW1 14 (by decide) (by decide)) h1o
      (by show κ1.val rI + κ1.val rO + 6 * natBitLength (κ1.val rI) + 6 ≤ cap
          rw [show κ1.val rI = i by simp (config := {decide := true}) [κ1, hI], h1O]; omega)
    rw [show κ1.val (wI 0) = i by show κ1.val rI = i; simp (config := {decide := true}) [κ1, hI]] at h
    exact h
  set κ2 := appendO κ1 sO rO (marks (RepairRepresentation.natWord i)) with hκ2
  have h2O : κ2.val rO = κ.val rO + 6 + 2 * (RepairRepresentation.natWord i).length := by simp [κ2, h1O]
  have k3 := copyNatM_spec cap false sD sO (by decide) rF rC rO (by decide) (by decide) (by decide) 0 pre rest κ2
    (by simp (config := {decide := true}) [κ2, κ1, hst, PrimAsm.ParseNat.enc])
    (by simp (config := {decide := true}) [κ2, κ1, hsh])
    (by simp [κ2, h1o])
    (by simp (config := {decide := true}) [κ2, κ1, hF])
    (by simp (config := {decide := true}) [κ2, κ1, hC])
    (by rw [h2O, hn0]; omega)
  refine WExec.cast cap (WExec.seq k1 (WExec.seq k2 k3)) ?_ ?_
  · refine WState.eq ?_ ?_ ?_ ?_
    · funext j
      by_cases hjD : j = sD
      · subst hjD; simp (config := {decide := true}) [κ2, κ1, stp]
      · by_cases hjO : j = sO
        · subst hjO; simp (config := {decide := true}) [κ2, κ1]; ring
        · simp [κ2, κ1, Function.update_apply, hjD, hjO]
    · funext j
      by_cases hjO : j = sO
      · subst hjO; simp [κ2, κ1, marks_append]
      · simp [κ2, κ1, Function.update_apply, hjO]
    · funext j
      by_cases hjO : j = rO
      · subst hjO; simp [κ2, κ1]; ring
      · simp [κ2, κ1, Function.update_apply, hjO]
    · simp [κ2, κ1]
  · rw [hn0]; nlinarith

/-- **Drop**: the constant node `[0, 0, 0]`, the third field skipped. -/
theorem drop_spec (pre rest : List Bool) (κ : WState 2 18)
    (hst : κ.st sD = pre ++ RepairRepresentation.natWord 0 ++ rest) (hsh : κ.sh sD = pre.length)
    (ho : κ.sh sO = (κ.st sO).length) (hF : κ.val rF = 0) (hC : κ.val rC = 0) (hcap : κ.val rO + 64 ≤ cap) :
    WExec cap dropM κ ((appendO κ sO rO (marks (RepairRepresentation.natWord 0 ++ RepairRepresentation.natWord 0 ++
      RepairRepresentation.natWord 0))).seth sD (pre.length + (RepairRepresentation.natWord 0).length)) 400 := by
  have hn0 : (RepairRepresentation.natWord 0).length = 3 := by rw [natWord_length]; simp [natBitLength]
  have d1 := emitWordM_spec cap sO rO (RepairRepresentation.natWord 0 ++ RepairRepresentation.natWord 0 ++
    RepairRepresentation.natWord 0) κ ho (by simp [hn0]; omega)
  set δ1 := appendO κ sO rO (marks (RepairRepresentation.natWord 0 ++ RepairRepresentation.natWord 0 ++
    RepairRepresentation.natWord 0)) with hδ1
  have d2 := skipNatM_spec cap false sD rF rC (by decide) 0 pre rest δ1
    (by simp (config := {decide := true}) [δ1, hst, PrimAsm.ParseNat.enc])
    (by simp (config := {decide := true}) [δ1, hsh])
    (by simp (config := {decide := true}) [δ1, hF]) (by simp (config := {decide := true}) [δ1, hC])
    (by simp [natBitLength]; omega)
  refine WExec.cast cap (WExec.seq d1 d2) ?_ ?_
  · refine WState.eq ?_ ?_ ?_ ?_
    · funext j
      by_cases hjD : j = sD
      · subst hjD; simp (config := {decide := true}) [δ1, stp]
      · simp [δ1, Function.update_apply, hjD]
    · simp [δ1]
    · simp [δ1]
    · simp [δ1]
  · simp [hn0, natBitLength]

/-- The restricted input node's word: `[1, i, 0]` below `R`, else `[0, 0, 0]`. -/
def outI (R i : ℕ) : List Bool :=
  if i < R then RepairRepresentation.natWord 1 ++ RepairRepresentation.natWord i ++ RepairRepresentation.natWord 0
  else RepairRepresentation.natWord 0 ++ RepairRepresentation.natWord 0 ++ RepairRepresentation.natWord 0

/-- The zero registers at a node boundary: everything but `R`, the count and the position counter. -/
def Zero (σ : WState 2 18) : Prop := ∀ r : Fin 18, 2 ≤ r.val → r.val ≠ 8 → σ.val r = 0

/-- **An input node** (tag `1` read, `rT = 0`): kept below `R`, else the constant node. -/
theorem inputM_spec (R i : ℕ) (pre rest : List Bool) (σ : WState 2 18)
    (hst : σ.st sD = pre ++ RepairRepresentation.natWord i ++ RepairRepresentation.natWord 0 ++ rest)
    (hsh : σ.sh sD = pre.length) (ho : σ.sh sO = (σ.st sO).length) (hR : σ.val rR = R) (hZ : Zero σ)
    (hcap : σ.val rO + 8 * (i + R) + 64 ≤ cap) :
    WExec cap inputM σ ((appendO σ sO rO (marks (outI R i))).seth sD
      (pre.length + (RepairRepresentation.natWord i).length + (RepairRepresentation.natWord 0).length))
      (300 * (i + R + 12) ^ 2 + 2000) := by
  have z : ∀ r : Fin 18, 2 ≤ r.val → r.val ≠ 8 → σ.val r = 0 := hZ
  have c := cmp_spec cap R i pre (RepairRepresentation.natWord 0 ++ rest) σ (by rw [hst]; simp)
    hsh hR (z rI (by decide) (by decide)) (z rA (by decide) (by decide)) (z rB (by decide) (by decide))
    (z rF (by decide) (by decide)) (z rC (by decide) (by decide)) (z rP (by decide) (by decide))
    (z rU (by decide) (by decide)) (z rX (by decide) (by decide)) (by omega)
  set τ4 := (((σ.seth sD (pre.length + (RepairRepresentation.natWord i).length)).setv rI i).setv rA
    (R - i)).setv rB 0 with hτ4
  have h4st : τ4.st sD = (pre ++ RepairRepresentation.natWord i) ++ RepairRepresentation.natWord 0 ++ rest := by
    simp [τ4, hst]
  have h4sh : τ4.sh sD = (pre ++ RepairRepresentation.natWord i).length := by simp [τ4]
  have h4o : τ4.sh sO = (τ4.st sO).length := by simp (config := {decide := true}) [τ4, ho]
  have h4O : τ4.val rO = σ.val rO := by simp (config := {decide := true}) [τ4]
  have h4A : τ4.val rA = R - i := by simp (config := {decide := true}) [τ4]
  have h4I : τ4.val rI = i := by simp (config := {decide := true}) [τ4]
  have h4F : τ4.val rF = 0 := by simp (config := {decide := true}) [τ4, z rF (by decide) (by decide)]
  have h4C : τ4.val rC = 0 := by simp (config := {decide := true}) [τ4, z rC (by decide) (by decide)]
  have h4W : ∀ r : Fin 18, 9 ≤ r.val → r.val ≤ 14 → τ4.val r = 0 := by
    intro r h9 h14
    have e1 : r ≠ rB := fun e => by rw [e] at h14; simp at h14
    have e2 : r ≠ rA := fun e => by rw [e] at h14; simp at h14
    have e3 : r ≠ rI := fun e => by rw [e] at h9; simp at h9
    simp [τ4, Function.update_apply, e1, e2, e3]
    exact z r (by omega) (fun e => by omega)
  set τ5 := (appendO τ4 sO rO (marks (outI R i))).seth sD
    ((pre ++ RepairRepresentation.natWord i).length + (RepairRepresentation.natWord 0).length) with hτ5
  have s5 : WExec cap (.ifr rA keepM dropM) τ4 τ5 (100 * (i + 12) ^ 2 + 1401) := by
    by_cases hiR : i < R
    · have k := keep_spec cap i (pre ++ RepairRepresentation.natWord i) rest τ4 h4st h4sh h4o h4I h4F h4C h4W
        (by rw [h4O]; omega)
      have e : outI R i = RepairRepresentation.natWord 1 ++ RepairRepresentation.natWord i ++
          RepairRepresentation.natWord 0 := by simp [outI, hiR]
      rw [hτ5, e]
      exact WExec.mono (WExec.ifrT (by rw [h4A]; omega) k) (by omega)
    · have d := drop_spec cap (pre ++ RepairRepresentation.natWord i) rest τ4 h4st h4sh h4o h4F h4C
        (by rw [h4O]; omega)
      have e : outI R i = RepairRepresentation.natWord 0 ++ RepairRepresentation.natWord 0 ++
          RepairRepresentation.natWord 0 := by simp [outI, hiR]
      rw [hτ5, e]
      exact WExec.mono (WExec.ifrF (by rw [h4A]; omega) d) (by nlinarith)
  have s6 := wclear_spec cap rA (R - i) τ5 (by simp (config := {decide := true}) [τ5, h4A])
    (by simp (config := {decide := true}) [τ5, h4A]; omega)
  have s7 := wclear_spec cap rI i (τ5.setv rA 0) (by simp (config := {decide := true}) [τ5, h4I])
    (by simp (config := {decide := true}) [τ5, h4I]; omega)
  refine WExec.cast cap (WExec.seq c (WExec.seq s5 (WExec.seq s6 s7))) ?_ ?_
  · refine WState.eq ?_ ?_ ?_ ?_
    · funext j
      by_cases hjD : j = sD
      · subst hjD; simp [τ5]
      · by_cases hjO : j = sO
        · subst hjO; simp (config := {decide := true}) [τ5, τ4]
        · simp [τ5, τ4, Function.update_apply, hjD, hjO]
    · funext j
      by_cases hjO : j = sO
      · subst hjO; simp (config := {decide := true}) [τ5, τ4]
      · simp [τ5, τ4, Function.update_apply, hjO]
    · funext j
      by_cases hjI : j = rI
      · subst hjI; simp (config := {decide := true}) [z rI (by decide) (by decide)]
      · by_cases hjA : j = rA
        · subst hjA; simp (config := {decide := true}) [z rA (by decide) (by decide)]
        · by_cases hjO : j = rO
          · subst hjO; simp (config := {decide := true}) [τ5, τ4]
          · by_cases hjB : j = rB
            · subst hjB; simp (config := {decide := true}) [τ5, τ4, z rB (by decide) (by decide)]
            · simp [τ5, τ4, Function.update_apply, hjI, hjA, hjO, hjB]
    · simp [τ5, τ4]
  · have := Nat.sub_le R i
    nlinarith

/-- The tag branch at tag `0`. -/
theorem tag0_spec (τ X : WState 2 18) (n : ℕ) (h0 : τ.val rT = 0) (hg : WExec cap generalM τ X n) :
    WExec cap (.ifr rT (.seq (.dec rT) (.ifr rT (.seq (.inc rT) generalM) inputM)) generalM) τ X (n + 1) :=
  WExec.ifrF h0 hg

/-- The tag branch at tag `1`. -/
theorem tag1_spec (τ X : WState 2 18) (n : ℕ) (h1 : τ.val rT = 1) (hc : 1 ≤ cap)
    (hi : WExec cap inputM (τ.setv rT 0) X n) :
    WExec cap (.ifr rT (.seq (.dec rT) (.ifr rT (.seq (.inc rT) generalM) inputM)) generalM) τ X (n + 4) := by
  have d := WExec.dec (cap := cap) rT τ (by omega)
  rw [h1] at d
  have hz : (τ.setv rT (1 - 1)).val rT = 0 := by simp
  exact WExec.mono (WExec.ifrT (by omega) (WExec.seq d (WExec.ifrF hz (by simpa using hi)))) (by omega)

/-- The tag branch at a tag `t ≥ 2`. -/
theorem tagHi_spec (τ X : WState 2 18) (n t : ℕ) (ht : τ.val rT = t) (h2 : 2 ≤ t) (hc : t ≤ cap)
    (hg : WExec cap generalM τ X n) :
    WExec cap (.ifr rT (.seq (.dec rT) (.ifr rT (.seq (.inc rT) generalM) inputM)) generalM) τ X (n + 8) := by
  have d := WExec.dec (cap := cap) rT τ (by omega)
  have i1 := WExec.inc (cap := cap) rT (τ.setv rT (τ.val rT - 1)) (by simp; omega)
  have e : (τ.setv rT (τ.val rT - 1)).setv rT ((τ.setv rT (τ.val rT - 1)).val rT + 1) = τ := by
    rw [wsetv_setv]; simp only [wsetv_val_self]
    rw [show τ.val rT - 1 + 1 = τ.val rT by omega, wsetv_same]
  rw [e] at i1
  exact WExec.mono (WExec.ifrT (by omega) (WExec.seq d (WExec.ifrT (by simp; omega) (WExec.seq i1 hg))))
    (by omega)

/-- The node words: the three fields. -/
theorem native_eq {w : ℕ} (nd : BooleanNode w) : PCPPRequestNodeSchema.native nd =
    RepairRepresentation.natWord (PCPPRequestNodeSchema.fields nd 0) ++
      RepairRepresentation.natWord (PCPPRequestNodeSchema.fields nd 1) ++
        RepairRepresentation.natWord (PCPPRequestNodeSchema.fields nd 2) := rfl

/-- **One node**: the node's three fields read from the description, the restricted node's written. -/
theorem nodeM_spec {w : ℕ} (R : ℕ) (nd : BooleanNode w) (pre rest : List Bool) (σ : WState 2 18)
    (hst : σ.st sD = pre ++ PCPPRequestNodeSchema.native nd ++ rest) (hsh : σ.sh sD = pre.length)
    (ho : σ.sh sO = (σ.st sO).length) (hR : σ.val rR = R) (hZ : Zero σ)
    (hcap : σ.val rO + 8 * (PCPPRequestNodeSchema.fields nd 0 + PCPPRequestNodeSchema.fields nd 1 +
      PCPPRequestNodeSchema.fields nd 2 + R) + 100 ≤ cap) :
    WExec cap nodeM σ ((appendO σ sO rO (marks (PCPPRequestNodeSchema.native (restrictNode R nd)))).seth sD
      (pre.length + (PCPPRequestNodeSchema.native nd).length))
      (1000 * (PCPPRequestNodeSchema.fields nd 0 + PCPPRequestNodeSchema.fields nd 1 +
        PCPPRequestNodeSchema.fields nd 2 + R + 12) ^ 2 + 5000) := by
  have z : ∀ r : Fin 18, 2 ≤ r.val → r.val ≠ 8 → σ.val r = 0 := hZ
  rw [native_eq nd] at hst ⊢
  generalize ht : PCPPRequestNodeSchema.fields nd 0 = t at hst hcap ⊢
  generalize hf1 : PCPPRequestNodeSchema.fields nd 1 = f1 at hst hcap ⊢
  generalize hf2 : PCPPRequestNodeSchema.fields nd 2 = f2 at hst hcap ⊢
  have hLt := natBitLength_le_self_succ t
  have hPt := two_pow_natBitLength_le t
  have s1 := readNatM_spec cap false sD rF rC rT rP rU (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) t pre
    (RepairRepresentation.natWord f1 ++ RepairRepresentation.natWord f2 ++ rest) σ
    (by rw [hst]; simp [PrimAsm.ParseNat.enc]) hsh (z rF (by decide) (by decide))
    (z rC (by decide) (by decide)) (z rP (by decide) (by decide)) (z rU (by decide) (by decide))
    (by rw [z rT (by decide) (by decide), pow_succ]; omega)
  set τ1 := (σ.seth sD (pre.length + stp false * (RepairRepresentation.natWord t).length)).setv rT (σ.val rT + t)
    with hτ1
  have h1T : τ1.val rT = t := by simp [τ1, z rT (by decide) (by decide)]
  have h1st : τ1.st sD = (pre ++ RepairRepresentation.natWord t) ++
      (RepairRepresentation.natWord f1 ++ RepairRepresentation.natWord f2) ++ rest := by
    simp [τ1, hst]
  have h1sh : τ1.sh sD = (pre ++ RepairRepresentation.natWord t).length := by simp [τ1, stp]
  have h1o : τ1.sh sO = (τ1.st sO).length := by simp (config := {decide := true}) [τ1, ho]
  have h1O : τ1.val rO = σ.val rO := by simp (config := {decide := true}) [τ1]
  have h1S : Scr τ1 := by
    intro r h4 h8
    have e : r ≠ rT := fun e => by rw [e] at h4; simp at h4
    simp [τ1, Function.update_apply, e]
    exact z r (by omega) h8
  -- the general target: tag `t` rewritten, the two fields copied
  have hgen : ((appendO τ1 sO rO (marks (RepairRepresentation.natWord t ++ RepairRepresentation.natWord f1 ++
      RepairRepresentation.natWord f2))).seth sD ((pre ++ RepairRepresentation.natWord t).length +
        (RepairRepresentation.natWord f1 ++ RepairRepresentation.natWord f2).length)).setv rT 0 =
      (appendO σ sO rO (marks (RepairRepresentation.natWord t ++ RepairRepresentation.natWord f1 ++
        RepairRepresentation.natWord f2))).seth sD
        (pre.length + (RepairRepresentation.natWord t ++ RepairRepresentation.natWord f1 ++
          RepairRepresentation.natWord f2).length) := by
    refine WState.eq ?_ ?_ ?_ ?_
    · funext j
      by_cases hjD : j = sD
      · subst hjD; simp; ring
      · by_cases hjO : j = sO
        · subst hjO; simp (config := {decide := true}) [τ1]
        · simp [τ1, Function.update_apply, hjD, hjO]
    · funext j
      by_cases hjO : j = sO
      · subst hjO; simp (config := {decide := true}) [τ1]
      · simp [τ1, Function.update_apply, hjO]
    · funext j
      by_cases hjT : j = rT
      · subst hjT; simp (config := {decide := true}) [z rT (by decide) (by decide)]
      · by_cases hjO : j = rO
        · subst hjO; simp (config := {decide := true}) [τ1]
        · simp [τ1, Function.update_apply, hjT, hjO]
    · simp [τ1]
  have htag : t ≤ 4 := by rw [← ht]; cases nd <;> simp [PCPPRequestNodeSchema.fields]
  have hL3 : natBitLength t ≤ 3 := by
    unfold natBitLength
    have := Nat.log_mono_right (b := 2) htag
    have h4 : Nat.log 2 4 = 2 := by decide
    omega
  have hP8 : 2 ^ natBitLength t ≤ 8 := (Nat.pow_le_pow_right (by norm_num) hL3).trans (by norm_num)
  have c1 : (natBitLength t + 2) * (40 * 2 ^ natBitLength t + 40) ≤ 1800 :=
    (Nat.mul_le_mul (show natBitLength t + 2 ≤ 5 by omega) (show 40 * 2 ^ natBitLength t + 40 ≤ 360 by omega))
  have c2 : (natBitLength t + 10) * (100 * t + 200) ≤ 7800 :=
    (Nat.mul_le_mul (show natBitLength t + 10 ≤ 13 by omega) (show 100 * t + 200 ≤ 600 by omega))
  have sq : t + f1 + f2 + R + 12 ≤ (t + f1 + f2 + R + 12) ^ 2 := Nat.le_self_pow two_ne_zero _
  cases nd with
  | const b =>
    have ht0 : t = 0 := by rw [← ht]; rfl
    have g := general_spec cap t f1 f2 (pre ++ RepairRepresentation.natWord t) rest τ1 h1st h1sh h1o h1T h1S
      (by rw [h1O]; omega)
    rw [hgen] at g
    have e : PCPPRequestNodeSchema.native (restrictNode R (BooleanNode.const b : BooleanNode w)) =
        RepairRepresentation.natWord t ++ RepairRepresentation.natWord f1 ++ RepairRepresentation.natWord f2 := by
      rw [← ht, ← hf1, ← hf2]; rfl
    rw [e]
    refine WExec.mono (WExec.seq s1 (tag0_spec cap τ1 _ _ (by rw [h1T, ht0]) g)) ?_
    omega
  | input i =>
    have ht1 : t = 1 := by rw [← ht]; rfl
    have hf1i : f1 = i.val := by rw [← hf1]; rfl
    have hf20 : f2 = 0 := by rw [← hf2]; rfl
    subst ht1 hf1i hf20
    have hZ1 : Zero (τ1.setv rT 0) := by
      intro r h2 h8
      by_cases e : r = rT
      · subst e; simp
      · simp [τ1, Function.update_apply, e]; exact z r h2 h8
    have hi := inputM_spec cap R i (pre ++ RepairRepresentation.natWord 1) rest (τ1.setv rT 0)
      (by simp [τ1, hst]) (by simp [τ1, stp]) (by simp (config := {decide := true}) [τ1, ho])
      (by simp (config := {decide := true}) [τ1, hR]) hZ1 (by simp (config := {decide := true}) [τ1]; omega)
    have hn : PCPPRequestNodeSchema.native (restrictNode R (BooleanNode.input i : BooleanNode w)) = outI R i := by
      show PCPPRequestNodeSchema.native (if hi : i.val < R then (BooleanNode.input ⟨i.val, hi⟩ : BooleanNode R)
        else BooleanNode.const false) = _
      unfold outI
      by_cases hiR : i.val < R
      · rw [dif_pos hiR, if_pos hiR]; rfl
      · rw [dif_neg hiR, if_neg hiR]; rfl
    have e : (appendO (τ1.setv rT 0) sO rO (marks (outI R i))).seth sD
        ((pre ++ RepairRepresentation.natWord 1).length + (RepairRepresentation.natWord i).length +
          (RepairRepresentation.natWord 0).length) =
        (appendO σ sO rO (marks (outI R i))).seth sD
          (pre.length + (RepairRepresentation.natWord 1 ++ RepairRepresentation.natWord i ++
            RepairRepresentation.natWord 0).length) := by
      refine WState.eq ?_ ?_ ?_ ?_
      · funext j
        by_cases hjD : j = sD
        · subst hjD; simp; ring
        · by_cases hjO : j = sO
          · subst hjO; simp (config := {decide := true}) [τ1]
          · simp [τ1, Function.update_apply, hjD, hjO]
      · funext j
        by_cases hjO : j = sO
        · subst hjO; simp (config := {decide := true}) [τ1]
        · simp [τ1, Function.update_apply, hjO]
      · funext j
        by_cases hjT : j = rT
        · subst hjT; simp (config := {decide := true}) [z rT (by decide) (by decide)]
        · by_cases hjO : j = rO
          · subst hjO; simp (config := {decide := true}) [τ1]
          · simp [τ1, Function.update_apply, hjT, hjO]
      · simp [τ1]
    rw [e] at hi
    rw [hn]
    refine WExec.mono (WExec.seq s1 (tag1_spec cap τ1 _ _ h1T (by omega) hi)) ?_
    have hm := Nat.pow_le_pow_left (show i.val + R + 12 ≤ 1 + i.val + 0 + R + 12 by omega) 2
    omega
  | not c =>
    have g := general_spec cap t f1 f2 (pre ++ RepairRepresentation.natWord t) rest τ1 h1st h1sh h1o h1T h1S
      (by rw [h1O]; omega)
    rw [hgen] at g
    have e : PCPPRequestNodeSchema.native (restrictNode R (BooleanNode.not c : BooleanNode w)) =
        RepairRepresentation.natWord t ++ RepairRepresentation.natWord f1 ++ RepairRepresentation.natWord f2 := by
      rw [← ht, ← hf1, ← hf2]; rfl
    have ht2 : t = 2 := by rw [← ht]; rfl
    rw [e]
    refine WExec.mono (WExec.seq s1 (tagHi_spec cap τ1 _ _ t h1T (by omega) (by omega) g)) ?_
    omega
  | and a c =>
    have g := general_spec cap t f1 f2 (pre ++ RepairRepresentation.natWord t) rest τ1 h1st h1sh h1o h1T h1S
      (by rw [h1O]; omega)
    rw [hgen] at g
    have e : PCPPRequestNodeSchema.native (restrictNode R (BooleanNode.and a c : BooleanNode w)) =
        RepairRepresentation.natWord t ++ RepairRepresentation.natWord f1 ++ RepairRepresentation.natWord f2 := by
      rw [← ht, ← hf1, ← hf2]; rfl
    have ht3 : t = 3 := by rw [← ht]; rfl
    rw [e]
    refine WExec.mono (WExec.seq s1 (tagHi_spec cap τ1 _ _ t h1T (by omega) (by omega) g)) ?_
    omega
  | or a c =>
    have g := general_spec cap t f1 f2 (pre ++ RepairRepresentation.natWord t) rest τ1 h1st h1sh h1o h1T h1S
      (by rw [h1O]; omega)
    rw [hgen] at g
    have e : PCPPRequestNodeSchema.native (restrictNode R (BooleanNode.or a c : BooleanNode w)) =
        RepairRepresentation.natWord t ++ RepairRepresentation.natWord f1 ++ RepairRepresentation.natWord f2 := by
      rw [← ht, ← hf1, ← hf2]; rfl
    have ht4 : t = 4 := by rw [← ht]; rfl
    rw [e]
    refine WExec.mono (WExec.seq s1 (tagHi_spec cap τ1 _ _ t h1T (by omega) (by omega) g)) ?_
    omega

/-- The fields' sum of a node. -/
def fsum {w : ℕ} (nd : BooleanNode w) : ℕ :=
  PCPPRequestNodeSchema.fields nd 0 + PCPPRequestNodeSchema.fields nd 1 + PCPPRequestNodeSchema.fields nd 2

theorem native_len_le {w : ℕ} (nd : BooleanNode w) :
    (PCPPRequestNodeSchema.native nd).length ≤ 2 * fsum nd + 9 := by
  rw [native_eq]
  have := natWord_len (PCPPRequestNodeSchema.fields nd 0)
  have := natWord_len (PCPPRequestNodeSchema.fields nd 1)
  have := natWord_len (PCPPRequestNodeSchema.fields nd 2)
  simp only [List.length_append, fsum]; omega

theorem native_restrict_len {w : ℕ} (R : ℕ) (nd : BooleanNode w) :
    (PCPPRequestNodeSchema.native (restrictNode R nd)).length ≤ 2 * fsum nd + 9 := by
  cases nd with
  | input i =>
    show (PCPPRequestNodeSchema.native (if hi : i.val < R then (BooleanNode.input ⟨i.val, hi⟩ : BooleanNode R)
      else BooleanNode.const false)).length ≤ _
    have h0 : (RepairRepresentation.natWord 0).length = 3 := by rw [natWord_length]; simp [natBitLength]
    have h1 : (RepairRepresentation.natWord 1).length = 3 := by rw [natWord_length]; simp [natBitLength]
    have hi := natWord_len i.val
    by_cases hiR : i.val < R
    · rw [dif_pos hiR, native_eq]; simp only [List.length_append, fsum, PCPPRequestNodeSchema.fields]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
        Matrix.tail_cons, h0, h1]
      omega
    · rw [dif_neg hiR, native_eq]; simp only [List.length_append, fsum, PCPPRequestNodeSchema.fields]
      simp [h0]
  | _ => exact native_len_le _

/-- **The loop body**: one node, the count decremented, the position counter cleared. -/
theorem body_spec {w : ℕ} (R m : ℕ) (nd : BooleanNode w) (pre rest : List Bool) (σ : WState 2 18)
    (hst : σ.st sD = pre ++ PCPPRequestNodeSchema.native nd ++ rest) (hsh : σ.sh sD = pre.length)
    (ho : σ.sh sO = (σ.st sO).length) (hR : σ.val rR = R) (hN : σ.val rN = m + 1) (hO : σ.val rO = 0)
    (hZ : Zero σ) (hcap : 8 * (fsum nd + R) + 100 ≤ cap) (hm : m + 1 ≤ cap) :
    WExec cap bodyM σ ((((appendO σ sO rO (marks (PCPPRequestNodeSchema.native (restrictNode R nd)))).seth sD
      (pre.length + (PCPPRequestNodeSchema.native nd).length)).setv rO 0).setv rN m)
      (1000 * (fsum nd + R + 12) ^ 2 + 20 * fsum nd + 5100) := by
  have d := WExec.dec (cap := cap) rN σ (by omega)
  set σ1 := σ.setv rN (σ.val rN - 1) with hσ1
  have n := nodeM_spec cap R nd pre rest σ1 (by simp [σ1, hst]) (by simp [σ1, hsh]) (by simp [σ1, ho])
    (by simp (config := {decide := true}) [σ1, hR])
    (by intro r h2 h8; have e : r ≠ rN := fun e => by rw [e] at h2; simp at h2
        simp [σ1, Function.update_apply, e]; exact hZ r h2 h8)
    (by simp (config := {decide := true}) [σ1, hO]; unfold fsum at hcap; omega)
  set τ := (appendO σ1 sO rO (marks (PCPPRequestNodeSchema.native (restrictNode R nd)))).seth sD
    (pre.length + (PCPPRequestNodeSchema.native nd).length) with hτ
  have hl := native_restrict_len R nd
  have c := wclear_spec cap rO (τ.val rO) τ rfl (by simp (config := {decide := true}) [τ, σ1, hO]; omega)
  refine WExec.cast cap (WExec.seq d (WExec.seq n c)) ?_ ?_
  · refine WState.eq ?_ ?_ ?_ ?_
    · simp [τ, σ1]
    · simp [τ, σ1]
    · funext j
      by_cases hjO : j = rO
      · subst hjO; simp (config := {decide := true})
      · by_cases hjN : j = rN
        · subst hjN; simp (config := {decide := true}) [τ, σ1, hN]
        · simp [τ, σ1, Function.update_apply, hjO, hjN]
    · simp [τ, σ1]
  · have : τ.val rO ≤ 4 * fsum nd + 18 := by simp (config := {decide := true}) [τ, σ1, hO]; omega
    unfold fsum at *
    omega

/-- **The node loop.** -/
theorem loop_spec {w : ℕ} (R : ℕ) :
    ∀ (nds : List (BooleanNode w)) (pre rest : List Bool) (σ : WState 2 18),
      σ.st sD = pre ++ nds.flatMap PCPPRequestNodeSchema.native ++ rest → σ.sh sD = pre.length →
      σ.sh sO = (σ.st sO).length → σ.val rR = R → σ.val rN = nds.length → σ.val rO = 0 → Zero σ →
      (∀ nd ∈ nds, 8 * (fsum nd + R) + 100 ≤ cap) → nds.length ≤ cap →
      WExec cap (.whr rN bodyM) σ ((((appendO σ sO rO (marks ((nds.map (restrictNode R)).flatMap
        PCPPRequestNodeSchema.native))).seth sD (pre.length + (nds.flatMap PCPPRequestNodeSchema.native).length)).setv
          rO 0).setv rN 0) (nds.length * (1100 * (cap + 12) ^ 2 + 5100) + 1)
  | [], pre, rest, σ, _, hsh, _, _, hN, hO, _, _, _ => by
    have e : (((appendO σ sO rO (marks ((([] : List (BooleanNode w)).map (restrictNode R)).flatMap
        PCPPRequestNodeSchema.native))).seth sD (pre.length + (([] : List (BooleanNode w)).flatMap
          PCPPRequestNodeSchema.native).length)).setv rO 0).setv rN 0 = σ := by
      simp only [List.map_nil, List.flatMap_nil, List.length_nil, Nat.add_zero]
      rw [show marks ([] : List Bool) = [] from rfl, appendO_nil, ← hsh, wseth_same]
      simp only [List.length_nil] at hN
      refine WState.eq rfl rfl ?_ rfl
      funext j
      by_cases hjO : j = rO
      · subst hjO; simp (config := {decide := true}) [hO]
      · by_cases hjN : j = rN
        · subst hjN; simp (config := {decide := true}) [hN]
        · simp [Function.update_apply, hjO, hjN]
    rw [e]
    exact WExec.mono (WExec.whrF (by simpa using hN)) (by omega)
  | nd :: nds, pre, rest, σ, hst, hsh, ho, hR, hN, hO, hZ, hb, hlen => by
    have hnd := hb nd (List.mem_cons_self)
    have b := body_spec cap R nds.length nd pre (nds.flatMap PCPPRequestNodeSchema.native ++ rest) σ
      (by rw [hst]; simp) hsh ho hR (by simp [hN]) hO hZ hnd (by simpa using hlen)
    set τ := (((appendO σ sO rO (marks (PCPPRequestNodeSchema.native (restrictNode R nd)))).seth sD
      (pre.length + (PCPPRequestNodeSchema.native nd).length)).setv rO 0).setv rN nds.length with hτ
    have ih := loop_spec R nds (pre ++ PCPPRequestNodeSchema.native nd) rest τ
      (by simp (config := {decide := true}) [τ, hst]) (by simp [τ]) (by simp (config := {decide := true}) [τ, ho])
      (by simp (config := {decide := true}) [τ, hR]) (by simp [τ]) (by simp (config := {decide := true}) [τ])
      (by intro r h2 h8
          have e1 : r ≠ rN := fun e => by rw [e] at h2; simp at h2
          have e2 : r ≠ rO := fun e => by rw [e] at h8; simp at h8
          simp [τ, Function.update_apply, e1, e2]; exact hZ r h2 h8)
      (fun x hx => hb x (List.mem_cons_of_mem _ hx)) (by simp at hlen; omega)
    refine WExec.cast cap (WExec.whrT (by rw [hN]; simp) b ih) ?_ ?_
    · refine WState.eq ?_ ?_ ?_ ?_
      · funext j
        by_cases hjD : j = sD
        · subst hjD; simp; ring
        · by_cases hjO : j = sO
          · subst hjO; simp (config := {decide := true}) [τ]; ring
          · simp [τ, Function.update_apply, hjD, hjO]
      · funext j
        by_cases hjO : j = sO
        · subst hjO; simp (config := {decide := true}) [τ, marks_append]
        · simp [τ, Function.update_apply, hjO]
      · funext j
        by_cases hjO : j = rO
        · subst hjO; simp (config := {decide := true})
        · by_cases hjN : j = rN
          · subst hjN; simp (config := {decide := true})
          · simp [τ, Function.update_apply, hjO, hjN]
      · simp [τ]
    · have hf : fsum nd + R + 12 ≤ cap + 12 := by omega
      have hsq := Nat.pow_le_pow_left hf 2
      have : fsum nd ≤ cap := by omega
      simp only [List.length_cons]
      nlinarith

end Node

/-! ## The whole restriction -/

section Whole
variable (cap : ℕ)

theorem bits_pow_le (R : ℕ) : 2 ^ (R.bits.length + 1) ≤ 4 * R + 2 := by
  rw [Nat.size_eq_bits_len]
  rcases Nat.eq_zero_or_pos R with h | h
  · subst h; simp
  · have hs : 0 < R.size := Nat.size_pos.mpr h
    have := Nat.lt_size.mp (show R.size - 1 < R.size by omega)
    rw [show R.size + 1 = (R.size - 1) + 2 by omega, pow_add]; omega

theorem frame_marks (w : List Bool) : frame w = marks w ++ [false] := by
  induction w with
  | nil => rfl
  | cons b w ih => simp [frame, marks, ih]

/-- A node of a well-formed circuit has fields below `4 + q + 2·(node count)`. -/
theorem fsum_le {q : ℕ} (O : BooleanCircuit q) (nd : BooleanNode q) (h : nd ∈ O.nodes) :
    fsum nd ≤ 4 + q + 2 * O.nodes.length := by
  obtain ⟨k, hk, e⟩ := List.mem_iff_getElem.mp h
  have wf := O.wellFormed ⟨k, hk⟩
  simp only [List.get_eq_getElem, e] at wf
  cases nd with
  | const b =>
    cases b with
    | false => simp [fsum, PCPPRequestNodeSchema.fields]
    | true => simp [fsum, PCPPRequestNodeSchema.fields]; omega
  | input i => have := i.isLt; simp [fsum, PCPPRequestNodeSchema.fields]; omega
  | not c => simp [BooleanNode.WellFormedAt] at wf; simp [fsum, PCPPRequestNodeSchema.fields]; omega
  | and a c => simp [BooleanNode.WellFormedAt] at wf; simp [fsum, PCPPRequestNodeSchema.fields]; omega
  | or a c => simp [BooleanNode.WellFormedAt] at wf; simp [fsum, PCPPRequestNodeSchema.fields]; omega

theorem restrict_descriptor {q : ℕ} (R : ℕ) (O : BooleanCircuit q) :
    PCPPNative.descriptor (restrictHigh R O) = RepairRepresentation.natWord R ++
      RepairRepresentation.natWord O.nodes.length ++
      (O.nodes.map (restrictNode R)).flatMap PCPPRequestNodeSchema.native ++
      RepairRepresentation.natWord O.output.val := by
  rw [PCPPNative.descriptor_eq]
  simp [restrictHigh]

/-- The writer at a value register `E 0`, scratch `9 … 14`, position `rO`. -/
theorem writeAt_spec (E : Fin 8 ↪ Fin 18) (h1 : E 1 = 9) (h2 : E 2 = 10) (h3 : E 3 = 11) (h4 : E 4 = 12)
    (h5 : E 5 = 13) (h6 : E 6 = 14) (h7 : E 7 = rO) (v : ℕ) (σ : WState 2 18) (hv : σ.val (E 0) = v)
    (hz : ∀ r : Fin 18, 9 ≤ r.val → r.val ≤ 14 → σ.val r = 0) (ho : σ.sh sO = (σ.st sO).length)
    (hcap : v + σ.val rO + 6 * natBitLength v + 6 ≤ cap) :
    WExec cap (writeNatM sO E) σ (appendO σ sO rO (marks (RepairRepresentation.natWord v)))
      ((natBitLength v + 10) * (100 * v + 200)) := by
  have h := writeNatM_spec cap sO E σ (by rw [h1]; exact hz 9 (by decide) (by decide))
    (by rw [h2]; exact hz 10 (by decide) (by decide)) (by rw [h3]; exact hz 11 (by decide) (by decide))
    (by rw [h4]; exact hz 12 (by decide) (by decide)) (by rw [h5]; exact hz 13 (by decide) (by decide))
    (by rw [h6]; exact hz 14 (by decide) (by decide)) ho (by rw [hv, h7]; exact hcap)
  rw [hv, h7] at h
  exact h

/-- **The restriction program**: from `frame (R.bits)`, the raw description of `O` and an empty output, with every
register `0`, it writes `frame (PCPPNative.descriptor (restrictHigh R O))`; the other streams are unchanged and every
register is `0` again. -/
theorem restrictM_spec (R q : ℕ) (hRq : R ≤ q) (O : BooleanCircuit q) (σ : WState 2 18)
    (hR0 : σ.st sR = frame R.bits) (hD0 : σ.st sD = PCPPNative.descriptor O) (hO0 : σ.st sO = [])
    (hsh : ∀ i, σ.sh i = 0) (hv : ∀ r, σ.val r = 0) (hcap : 64 * (O.size + q + 4) ≤ cap) :
    ∃ τ n, WExec cap restrictM σ τ n ∧ n ≤ 3000 * (cap + 12) ^ 3 ∧ τ.st sR = σ.st sR ∧ τ.st sD = σ.st sD ∧
      τ.st sO = frame (PCPPNative.descriptor (restrictHigh R O)) ∧ (∀ r, τ.val r = 0) ∧ τ.cell = σ.cell := by
  have hsz : O.size = O.nodes.length := rfl
  set len := O.nodes.length with hlen
  set out := O.output.val with hout
  have hout_lt : out < len := O.output.isLt
  set body := O.nodes.flatMap PCPPRequestNodeSchema.native with hbody
  have hD : σ.st sD = RepairRepresentation.natWord q ++ RepairRepresentation.natWord len ++ body ++
      RepairRepresentation.natWord out := by rw [hD0, PCPPNative.descriptor_eq]
  have hbp := bits_pow_le R
  have hLq := natBitLength_le_self_succ q
  have hLR := natBitLength_le_self_succ R
  have hLn := natBitLength_le_self_succ len
  have hLo := natBitLength_le_self_succ out
  have hPn := two_pow_natBitLength_le len
  have hnR := natWord_len R
  have hnn := natWord_len len
  have hno := natWord_len out
  -- 1. the width `R`
  have e1 := readBinM_spec cap R σ (by rw [hR0, frame_marks]) (hsh sR) (hv rR) (hv rP) (hv rU) (by omega)
  set σ1 := (σ.seth sR (2 * R.bits.length)).setv rR R with hσ1
  -- 2. skip the arity field
  have e2 := skipNatM_spec cap false sD rF rC (by decide) q [] (RepairRepresentation.natWord len ++ body ++
    RepairRepresentation.natWord out) σ1 (by simp (config := {decide := true}) [σ1, hD, PrimAsm.ParseNat.enc])
    (by simp (config := {decide := true}) [σ1, hsh]) (by simp (config := {decide := true}) [σ1, hv])
    (by simp (config := {decide := true}) [σ1, hv]) (by omega)
  set σ2 := σ1.seth sD (([] : List Bool).length + stp false * (RepairRepresentation.natWord q).length) with hσ2
  -- 3. write `natWord R`
  have e3 := writeAt_spec cap wR rfl rfl rfl rfl rfl rfl rfl R σ2 (by simp [σ2, σ1]; rfl)
    (by intro r h9 h14
        have e : r ≠ rR := fun e => by rw [e] at h9; simp at h9
        simp [σ2, σ1, Function.update_apply, e, hv])
    (by simp (config := {decide := true}) [σ2, σ1, hsh, hO0])
    (by simp (config := {decide := true}) [σ2, σ1, hv]; omega)
  set σ3 := appendO σ2 sO rO (marks (RepairRepresentation.natWord R)) with hσ3
  -- 4. read the node count
  have e4 := readNatM_spec cap false sD rF rC rN rP rU (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) len (RepairRepresentation.natWord q)
    (body ++ RepairRepresentation.natWord out) σ3
    (by simp (config := {decide := true}) [σ3, σ2, σ1, hD, PrimAsm.ParseNat.enc])
    (by simp (config := {decide := true}) [σ3, σ2, stp])
    (by simp (config := {decide := true}) [σ3, σ2, σ1, hv]) (by simp (config := {decide := true}) [σ3, σ2, σ1, hv])
    (by simp (config := {decide := true}) [σ3, σ2, σ1, hv]) (by simp (config := {decide := true}) [σ3, σ2, σ1, hv])
    (by simp (config := {decide := true}) [σ3, σ2, σ1, hv, pow_succ]; omega)
  set σ4 := (σ3.seth sD ((RepairRepresentation.natWord q).length + stp false *
    (RepairRepresentation.natWord len).length)).setv rN (σ3.val rN + len) with hσ4
  have h4N : σ4.val rN = len := by simp (config := {decide := true}) [σ4, σ3, σ2, σ1, hv]
  have h4O : σ4.val rO = 2 * (RepairRepresentation.natWord R).length := by
    simp (config := {decide := true}) [σ4, σ3, σ2, σ1, hv]
  -- 5. write `natWord len`
  have e5 := writeAt_spec cap wN rfl rfl rfl rfl rfl rfl rfl len σ4 h4N
    (by intro r h9 h14
        have e1 : r ≠ rR := fun e => by rw [e] at h9; simp at h9
        have e2 : r ≠ rN := fun e => by rw [e] at h9; simp at h9
        have e3 : r ≠ rO := fun e => by rw [e] at h9; simp at h9
        simp [σ4, σ3, σ2, σ1, Function.update_apply, e1, e2, e3, hv])
    (by simp (config := {decide := true}) [σ4, σ3, σ2, σ1, hsh, hO0])
    (by rw [h4O]; omega)
  set σ5 := appendO σ4 sO rO (marks (RepairRepresentation.natWord len)) with hσ5
  -- 6. clear the position counter
  have e6 := wclear_spec cap rO (σ5.val rO) σ5 rfl (by simp (config := {decide := true}) [σ5, h4O]; omega)
  set σ6 := σ5.setv rO 0 with hσ6
  -- 7. the node loop
  have e7 := loop_spec cap R O.nodes (RepairRepresentation.natWord q ++ RepairRepresentation.natWord len)
    (RepairRepresentation.natWord out) σ6
    (by simp (config := {decide := true}) [σ6, σ5, σ4, σ3, σ2, σ1, hD, hbody])
    (by simp (config := {decide := true}) [σ6, σ5, σ4, σ3, σ2, stp, hlen])
    (by simp (config := {decide := true}) [σ6, σ5, σ4, σ3, σ2, σ1, hsh, hO0])
    (by simp (config := {decide := true}) [σ6, σ5, σ4, σ3, σ2, σ1])
    (by simp (config := {decide := true}) [σ6, σ5, h4N, hlen]) (by simp [σ6])
    (by intro r h2 h8
        have e1 : r ≠ rN := fun e => by rw [e] at h2; simp at h2
        have e2 : r ≠ rR := fun e => by rw [e] at h2; simp at h2
        have e3 : r ≠ rO := fun e => by rw [e] at h8; simp at h8
        simp [σ6, σ5, σ4, σ3, σ2, σ1, Function.update_apply, e1, e2, e3, hv])
    (fun nd hnd => by have := fsum_le O nd hnd; omega) (by omega)
  set σ7 := (((appendO σ6 sO rO (marks ((O.nodes.map (restrictNode R)).flatMap
    PCPPRequestNodeSchema.native))).seth sD ((RepairRepresentation.natWord q ++
      RepairRepresentation.natWord len).length + body.length)).setv rO 0).setv rN 0 with hσ7
  -- 8. copy the output field
  have e8 := copyNatM_spec cap false sD sO (by decide) rF rC rO (by decide) (by decide) (by decide) out
    (RepairRepresentation.natWord q ++ RepairRepresentation.natWord len ++ body) [] σ7
    (by simp (config := {decide := true}) [σ7, σ6, σ5, σ4, σ3, σ2, σ1, hD, PrimAsm.ParseNat.enc])
    (by simp (config := {decide := true}) [σ7]; ring)
    (by simp (config := {decide := true}) [σ7, σ6, σ5, σ4, σ3, σ2, σ1, hsh, hO0]; ring)
    (by simp (config := {decide := true}) [σ7, σ6, σ5, σ4, σ3, σ2, σ1, hv])
    (by simp (config := {decide := true}) [σ7, σ6, σ5, σ4, σ3, σ2, σ1, hv])
    (by simp (config := {decide := true}) [σ7]; omega)
  set σ8 := (appendO σ7 sO rO (marks (RepairRepresentation.natWord out))).seth sD
    ((RepairRepresentation.natWord q ++ RepairRepresentation.natWord len ++ body).length + stp false *
      (RepairRepresentation.natWord out).length) with hσ8
  have h8O : σ8.val rO = 2 * (RepairRepresentation.natWord out).length := by
    simp (config := {decide := true}) [σ8, σ7]
  -- 9. the frame's end
  have e9 := emitC_spec cap sO rO false σ8
    (by simp (config := {decide := true}) [σ8, σ7, σ6, σ5, σ4, σ3, σ2, σ1, hsh, hO0]; ring)
    (by rw [h8O]; omega)
  set σ9 := ((σ8.sets sO ((σ8.st sO) ++ [false])).seth sO (σ8.sh sO + 1)).setv rO (σ8.val rO + 1) with hσ9
  have e10 := wclear_spec cap rO (σ9.val rO) σ9 rfl (by simp [σ9, h8O]; omega)
  have h9R : (σ9.setv rO 0).val rR = R := by
    simp (config := {decide := true}) [σ9, σ8, σ7, σ6, σ5, σ4, σ3, σ2, σ1]
  have e11 := wclear_spec cap rR R (σ9.setv rO 0) h9R (by rw [h9R]; omega)
  refine ⟨(σ9.setv rO 0).setv rR 0, _, WExec.seq e1 (WExec.seq e2 (WExec.seq e3 (WExec.seq e4 (WExec.seq e5
    (WExec.seq e6 (WExec.seq e7 (WExec.seq e8 (WExec.seq e9 (WExec.seq e10 e11))))))))), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- the cost
    have hbits : R.bits.length ≤ R + 1 := by
      rw [Nat.size_eq_bits_len]
      exact Nat.size_le.mpr (by have := Nat.lt_two_pow_self (n := R); rw [pow_succ]; omega)
    have hPb : 2 ^ R.bits.length ≤ 2 * R + 1 := by
      have := bits_pow_le R; rw [pow_succ] at this; omega
    have h5O : σ5.val rO = 2 * (RepairRepresentation.natWord R).length +
        2 * (RepairRepresentation.natWord len).length := by simp [σ5, h4O]
    have h9O : σ9.val rO = 2 * (RepairRepresentation.natWord out).length + 1 := by simp [σ9, h8O]
    have hX : 12 * (cap + 12) ^ 2 ≤ (cap + 12) ^ 3 :=
      calc 12 * (cap + 12) ^ 2 ≤ (cap + 12) * (cap + 12) ^ 2 := Nat.mul_le_mul_right _ (by omega)
        _ = (cap + 12) ^ 3 := by ring
    have hXl : cap + 12 ≤ (cap + 12) ^ 2 := Nat.le_self_pow two_ne_zero _
    have sq : ∀ a b : ℕ, a ≤ cap + 12 → b ≤ 100 * (cap + 12) → a * b ≤ 100 * (cap + 12) ^ 2 := by
      intro a b ha hb
      calc a * b ≤ (cap + 12) * (100 * (cap + 12)) := Nat.mul_le_mul ha hb
        _ = 100 * (cap + 12) ^ 2 := by ring
    have m1 := sq _ _ (show R.bits.length ≤ cap + 12 by omega)
      (show 40 * 2 ^ R.bits.length + 20 ≤ 100 * (cap + 12) by omega)
    have m2 := sq _ _ (show natBitLength R + 10 ≤ cap + 12 by omega) (show 100 * R + 200 ≤ 100 * (cap + 12) by omega)
    have m3 := sq _ _ (show natBitLength len + 2 ≤ cap + 12 by omega)
      (show 40 * 2 ^ natBitLength len + 40 ≤ 100 * (cap + 12) by omega)
    have m4 := sq _ _ (show natBitLength len + 10 ≤ cap + 12 by omega)
      (show 100 * len + 200 ≤ 100 * (cap + 12) by omega)
    have m5 : len * (1100 * (cap + 12) ^ 2 + 5100) ≤ 1200 * (cap + 12) ^ 3 :=
      calc len * (1100 * (cap + 12) ^ 2 + 5100) ≤ (cap + 12) * (1200 * (cap + 12) ^ 2) :=
            Nat.mul_le_mul (by omega) (by omega)
        _ = 1200 * (cap + 12) ^ 3 := by ring
    have m5' : O.nodes.length * (1100 * (cap + 12) ^ 2 + 5100) ≤ 1200 * (cap + 12) ^ 3 := m5
    rw [h5O, h9O]
    omega
  · simp (config := {decide := true}) [σ9, σ8, σ7, σ6, σ5, σ4, σ3, σ2, σ1]
  · simp (config := {decide := true}) [σ9, σ8, σ7, σ6, σ5, σ4, σ3, σ2, σ1]
  · simp (config := {decide := true}) [σ9, σ8, σ7, σ6, σ5, σ4, σ3, σ2, σ1, hO0, restrict_descriptor, frame_marks,
      marks_append, hlen, hout]
  · intro r
    simp only [σ9, σ8, σ7, σ6, σ5, σ4, σ3, σ2, σ1, WState.setv_val, WState.seth_val, WState.sets_val, appendO_val,
      Function.update_apply]
    split_ifs <;> simp_all
  · simp [σ9, σ8, σ7, σ6, σ5, σ4, σ3, σ2, σ1]

end Whole

end NearCubicWires.WireExponent3_5.Transfer.CaseTwoPadG
