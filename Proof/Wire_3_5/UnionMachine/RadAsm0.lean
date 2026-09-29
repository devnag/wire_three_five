import Proof.Wire_3_5.UnionMachine.RadPipeB
import Proof.Wire_3_5.UnionMachine.RadBnd

/-! # RADIX assembly (0): the setup's register layout and the frame predicate

The RADIX setup runs on the cell `LNS x` from `RadSetupB3.RsIn4` (inputs in `410 … 432`; registers `< 250`,
`400 … 409` and `≥ 433` zero; `250 … 399` the decode's). Its register blocks, all inside the zero regions:

* `rQ` (`0 … 47`): the numbers program `RadNums.numsP`;
* `rF` (`48 … 95`): the fields program `RadFieldsP.fieldsP`;
* `rY` (`96 … 127`): single registers (the record's position `rY 0`, the scan's counters, the frames', the window's,
  the digit counter, a temporary);
* `rT` (`128 … 137`): the seed program `RadSeed.hashSeedP`;
* `rB` (`138 … 153`): the table builder (`RadTab.buildL_spec`; its registers end as the builder leaves them);
* `rZ` (`160 … 170`): the digit step (`RadDig`);
* `rG` (`448 … 511`): the block writer (`RadSpec3.RadBlockW3`); `RadDigs.dR`'s scratch (`445 … 487`) is back to
  `0` before.

`Keep σ τ S R`: every stream outside `S` and every register outside `R` as in `σ`. Its lemmas compose the phases.

Paper quantity of the main type: none (layout); the phases realize the RADIX row's record (row:radix, P3:2585-2623). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearCubicWires.WireExponent3_5.UnionMachine.RadAsm
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimAsm.SymLayout NearCubicWires.WireExponent3_5.PrimAsm.WriteNat

/-- A register block at offset `b`. -/
def blk (b k : ℕ) (h : b + k ≤ LNR) : Fin k ↪ Fin LNR :=
  ⟨fun i => ⟨b + i.val, by have := i.isLt; omega⟩, fun i j e => Fin.ext (by simpa using congrArg Fin.val e)⟩

theorem blk_val (b k : ℕ) (h : b + k ≤ LNR) (i : Fin k) : (blk b k h i).val = b + i.val := rfl

def rQ : Fin 48 ↪ Fin LNR := blk 0 48 (by decide)
def rF : Fin 48 ↪ Fin LNR := blk 48 48 (by decide)
def rY : Fin 32 ↪ Fin LNR := blk 96 32 (by decide)
def rT : Fin 10 ↪ Fin LNR := blk 128 10 (by decide)
def rB : Fin 16 ↪ Fin LNR := blk 138 16 (by decide)
def rZ : Fin 11 ↪ Fin LNR := blk 160 11 (by decide)
def rG : Fin RadSpec.radBlkK ↪ Fin LNR := blk 448 64 (by decide)

theorem rQ_val (i : Fin 48) : (rQ i).val = i.val := by simp [rQ, blk_val]
theorem rF_val (i : Fin 48) : (rF i).val = 48 + i.val := rfl
theorem rY_val (i : Fin 32) : (rY i).val = 96 + i.val := rfl
theorem rT_val (i : Fin 10) : (rT i).val = 128 + i.val := rfl
theorem rB_val (i : Fin 16) : (rB i).val = 138 + i.val := rfl
theorem rZ_val (i : Fin 11) : (rZ i).val = 160 + i.val := rfl
theorem rG_val (i : Fin RadSpec.radBlkK) : (rG i).val = 448 + i.val := rfl

theorem ne_of_val {a b : Fin LNR} (h : a.val ≠ b.val) : a ≠ b := fun e => h (congrArg Fin.val e)

/-! ## The blocks are disjoint, and below the inputs -/

theorem QF (i j : Fin 48) : rQ i ≠ rF j := ne_of_val (by rw [rQ_val, rF_val]; omega)
theorem QY (i : Fin 48) (j : Fin 32) : rQ i ≠ rY j := ne_of_val (by rw [rQ_val, rY_val]; omega)
theorem QZ (i : Fin 48) (j : Fin 11) : rQ i ≠ rZ j := ne_of_val (by rw [rQ_val, rZ_val]; omega)
theorem QG (i : Fin 48) (j : Fin RadSpec.radBlkK) : rQ i ≠ rG j := ne_of_val (by rw [rQ_val, rG_val]; omega)
theorem FY (i : Fin 48) (j : Fin 32) : rF i ≠ rY j := ne_of_val (by rw [rF_val, rY_val]; omega)
theorem YT (i : Fin 32) (j : Fin 10) : rY i ≠ rT j := ne_of_val (by rw [rY_val, rT_val]; omega)
theorem YZ (i : Fin 32) (j : Fin 11) : rY i ≠ rZ j := ne_of_val (by rw [rY_val, rZ_val]; omega)
theorem YG (i : Fin 32) (j : Fin RadSpec.radBlkK) : rY i ≠ rG j := ne_of_val (by rw [rY_val, rG_val]; omega)
theorem ZG (i : Fin 11) (j : Fin RadSpec.radBlkK) : rZ i ≠ rG j := ne_of_val (by rw [rZ_val, rG_val]; omega)

/-- The inputs `410 … 432` (the twenty values, `|carriers|`, the THR filter cap, `a'`). -/
def rIn (k : ℕ) (h : k < 23 := by decide) : Fin LNR := ⟨410 + k, by unfold LNR; omega⟩

theorem rIn_val (k : ℕ) (h : k < 23) : (rIn k h).val = 410 + k := rfl

theorem Qin (i : Fin 48) (k : ℕ) (h : k < 23) : rQ i ≠ rIn k h := ne_of_val (by rw [rQ_val, rIn_val]; omega)
theorem Fin' (i : Fin 48) (k : ℕ) (h : k < 23) : rF i ≠ rIn k h := ne_of_val (by rw [rF_val, rIn_val]; omega)
theorem Yin (i : Fin 32) (k : ℕ) (h : k < 23) : rY i ≠ rIn k h := ne_of_val (by rw [rY_val, rIn_val]; omega)
theorem Tin (i : Fin 10) (k : ℕ) (h : k < 23) : rT i ≠ rIn k h := ne_of_val (by rw [rT_val, rIn_val]; omega)
theorem Zin (i : Fin 11) (k : ℕ) (h : k < 23) : rZ i ≠ rIn k h := ne_of_val (by rw [rZ_val, rIn_val]; omega)
theorem Gin (i : Fin RadSpec.radBlkK) (k : ℕ) (h : k < 23) : rG i ≠ rIn k h := ne_of_val (by rw [rG_val, rIn_val]; omega)

/-! ## The frame predicate -/

section Keep
variable {ns nr : ℕ}

/-- Every stream outside `S` and every register outside `R` as in `σ`. -/
def Keep (σ τ : WState ns nr) (S : Fin (ns + 1) → Prop) (R : Fin nr → Prop) : Prop :=
  (∀ i, ¬ S i → τ.st i = σ.st i ∧ τ.sh i = σ.sh i) ∧ (∀ r, ¬ R r → τ.val r = σ.val r)

theorem Keep.trans {σ τ ρ : WState ns nr} {S S' : Fin (ns + 1) → Prop} {R R' : Fin nr → Prop} (h : Keep σ τ S R)
    (h' : Keep τ ρ S' R') : Keep σ ρ (fun i => S i ∨ S' i) (fun r => R r ∨ R' r) := by
  refine ⟨fun i hi => ?_, fun r hr => ?_⟩
  · have a := h.1 i (fun e => hi (Or.inl e))
    have b := h'.1 i (fun e => hi (Or.inr e))
    exact ⟨b.1.trans a.1, b.2.trans a.2⟩
  · exact (h'.2 r (fun e => hr (Or.inr e))).trans (h.2 r (fun e => hr (Or.inl e)))

theorem Keep.mono {σ τ : WState ns nr} {S S' : Fin (ns + 1) → Prop} {R R' : Fin nr → Prop} (h : Keep σ τ S R)
    (hS : ∀ i, S i → S' i) (hR : ∀ r, R r → R' r) : Keep σ τ S' R' :=
  ⟨fun i hi => h.1 i (fun e => hi (hS i e)), fun r hr => h.2 r (fun e => hr (hR r e))⟩

theorem Keep.st {σ τ : WState ns nr} {S : Fin (ns + 1) → Prop} {R : Fin nr → Prop} (h : Keep σ τ S R) {i : Fin (ns + 1)}
    (hi : ¬ S i) : τ.st i = σ.st i := (h.1 i hi).1

theorem Keep.sh {σ τ : WState ns nr} {S : Fin (ns + 1) → Prop} {R : Fin nr → Prop} (h : Keep σ τ S R) {i : Fin (ns + 1)}
    (hi : ¬ S i) : τ.sh i = σ.sh i := (h.1 i hi).2

theorem Keep.val {σ τ : WState ns nr} {S : Fin (ns + 1) → Prop} {R : Fin nr → Prop} (h : Keep σ τ S R) {r : Fin nr}
    (hr : ¬ R r) : τ.val r = σ.val r := h.2 r hr

theorem keep_setv (σ : WState ns nr) (r : Fin nr) (x : ℕ) : Keep σ (σ.setv r x) (fun _ => False) (fun q => q = r) :=
  ⟨fun _ _ => ⟨rfl, rfl⟩, fun q hq => by simp [Function.update_apply, hq]⟩

end Keep

end NearCubicWires.WireExponent3_5.UnionMachine.RadAsm
