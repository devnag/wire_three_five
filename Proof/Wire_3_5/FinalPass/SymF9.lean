import Proof.Wire_3_5.FinalPass.SdPrep2
import Proof.Wire_3_5.FinalPass.SymF8
import Proof.Wire_3_5.Primitive.Writers.SymDecTools

/-! # SWf (the SYM words writer's flat tables), part 9: the four writers docked (the part's tail)

After the SYM numbers front (the flat list's `n, M, B, errExp, |FlatSeed|` and the population lengths `L_0 … L_3` in
registers), the flat tables part writes the four requests `reqT n M B errExp L_c 0 |FlatSeed|` (S4's `Sd.reqWM`, one
register embedding `RwC c` per circuit, the registers restored) onto the input tapes of four disjoint writer blocks
(`tmC c`, extra streams past the front's `xF`), runs the flat tables writer docked on each block (`DockW.dockS`, from
its `WriterRun`), and clears every register (PA's `SymDec.clrsW`).

* `xP`, `tmC`, `tmC_inj`, `tmC_ne`; `rwv`, `RwC`, `scrL`; `preT`, `dockC`, **`tailM`**;
* **`tail_run`**: the outputs `v_c` on the blocks' output tapes, the requests kept on their input tapes, every other
  block tape the writer's residue (length `≤ Bud`), every block head `0`, every stream off the blocks untouched,
  every register `0`.

Paper quantity of the main type: the four circuits' flat tables words (`tablesJ k j`, list:flatten P3:1508-1520)
on the part's output streams. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace NearCubicWires.WireExponent3_5.FinalPass.SymF
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimAsm
open NearCubicWires.WireExponent3_5.PrimAsm.SymLayout
open NearCubicWires.RepairOrdinary.RecoveryRootRound (install install_slot install_other)

section Tail
variable (xF tw : ℕ)

/-- The part's extra streams: the front's `xF`, then four writer blocks of `tw` tapes. -/
abbrev xP : ℕ := xF + 4 * tw

/-- Writer block `c`'s tape `j`. -/
def tmC (c : Fin 4) (j : Fin tw) : Fin (LNS (xP xF tw) + 1) :=
  sT (xP xF tw) ⟨xF + (c.val * tw + j.val), by
    have h1 := c.isLt
    have h2 := j.isLt
    have : c.val * tw + j.val < 4 * tw := by nlinarith
    show xF + (c.val * tw + j.val) < xF + 4 * tw
    omega⟩

theorem tmC_val (c : Fin 4) (j : Fin tw) : (tmC xF tw c j).val = 161 + (xF + (c.val * tw + j.val)) := rfl

theorem tmC_inj' (c c' : Fin 4) (j j' : Fin tw) (h : tmC xF tw c j = tmC xF tw c' j') : c = c' ∧ j = j' := by
  have hv := congrArg Fin.val h
  rw [tmC_val, tmC_val] at hv
  have hj := j.isLt
  have hj' := j'.isLt
  have e : c.val * tw + j.val = c'.val * tw + j'.val := by omega
  have hc : c.val = c'.val := by
    rcases Nat.lt_trichotomy c.val c'.val with h1 | h1 | h1
    · exfalso
      have : (c.val + 1) * tw ≤ c'.val * tw := Nat.mul_le_mul_right _ h1
      nlinarith
    · exact h1
    · exfalso
      have : (c'.val + 1) * tw ≤ c.val * tw := Nat.mul_le_mul_right _ h1
      nlinarith
  refine ⟨Fin.ext hc, Fin.ext ?_⟩
  rw [hc] at e
  omega

theorem tmC_inj (c : Fin 4) : Function.Injective (tmC xF tw c) := fun j j' h => (tmC_inj' xF tw c c j j' h).2

theorem tmC_ne (c c' : Fin 4) (hc : c ≠ c') (j j' : Fin tw) : tmC xF tw c j ≠ tmC xF tw c' j' :=
  fun h => hc (tmC_inj' xF tw c c' j j' h).1

/-- The request writer's registers for circuit `c`: `n` in `320`, scratch `500 … 508`, `M, B, errExp` in
`G 32 … G 34` (`440 … 442`), `L_c` in `dM c` (`330 + c`), a zero `509`, `|FlatSeed|` in `G 41` (`449`). -/
def rwv (c : Fin 4) : Fin 16 → ℕ :=
  ![320, 500, 501, 502, 503, 504, 505, 506, 507, 508, 440, 441, 442, 330 + c.val, 509, 449]

theorem rwv_lt : ∀ (c : Fin 4) (k : Fin 16), rwv c k < 512 := by decide

theorem rwv_inj : ∀ (c : Fin 4) (a b : Fin 16), rwv c a = rwv c b → a = b := by decide

def RwC (c : Fin 4) : Fin 16 ↪ Fin LNR := ⟨fun k => ⟨rwv c k, rwv_lt c k⟩, fun a b h => rwv_inj c a b (congrArg Fin.val h)⟩

/-- The scratch registers `500 … 509`. -/
def scrL : List (Fin LNR) := (List.range 10).map fun i => ⟨500 + i % 10, by show 500 + i % 10 < 512; omega⟩

theorem mem_scrL (q : Fin LNR) : q ∈ scrL ↔ 500 ≤ q.val ∧ q.val ≤ 509 := by
  constructor
  · intro h
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp h
    simp only [List.mem_range] at hi
    show 500 ≤ 500 + i % 10 ∧ 500 + i % 10 ≤ 509
    omega
  · intro ⟨h1, h2⟩
    refine List.mem_map.mpr ⟨q.val - 500, by simp only [List.mem_range]; omega, Fin.ext ?_⟩
    show 500 + (q.val - 500) % 10 = q.val
    omega

variable {sw : ℕ} (Mw : Machine tw sw) (win : Fin tw)

/-- The scratch cleared, then the four requests. -/
def preT : WM (LNS (xP xF tw)) LNR :=
  .seq (SymDec.clrsW scrL) (.seq (Sd.reqWM (tmC xF tw 0 win) (RwC 0)) (.seq (Sd.reqWM (tmC xF tw 1 win) (RwC 1))
    (.seq (Sd.reqWM (tmC xF tw 2 win) (RwC 2)) (Sd.reqWM (tmC xF tw 3 win) (RwC 3)))))

/-- The writer docked on block `c`. -/
noncomputable def dockC (c : Fin 4) := RecoveryFocus.machine (fun j => sTape (nr := LNR) (tmC xF tw c j)) Mw

/-- **The part's tail**: the requests, the four docked writers, every register cleared. -/
noncomputable def tailM := Composition.machine (Composition.machine (Composition.machine (Composition.machine
  (Composition.machine (preT xF tw win).toProg.compile (dockC xF tw Mw 0)) (dockC xF tw Mw 1)) (dockC xF tw Mw 2))
  (dockC xF tw Mw 3)) (SymDec.clrsW (List.finRange LNR)).toProg.compile

/-- The tail's step bound. -/
def tailCost (cap : ℕ) (Bud : Fin 4 → ℕ) (n lw : ℕ) : ℕ :=
  (10 * (3 * cap + 2) + 1 + (Sd.reqCost n lw + 1 + (Sd.reqCost n lw + 1 + (Sd.reqCost n lw + 1 +
    Sd.reqCost n lw)))) + 1 + Bud 0 + 1 + Bud 1 + 1 + Bud 2 + 1 + Bud 3 + 1 + 512 * (3 * cap + 2)

/-- One docked writer: from its block holding the request on the input tape, the other tapes blank, heads `0`. -/
theorem dock_one (cap : ℕ) (wout : Fin tw) (c : Fin 4) (Bud : ℕ) (w v : List Bool)
    (hwr : WriterIfaceJ.WriterRun Mw Bud win wout w v) (ρ : WState (LNS (xP xF tw)) LNR)
    (hin : ρ.st (tmC xF tw c win) = frame w) (hbl : ∀ j, j ≠ win → ρ.st (tmC xF tw c j) = [])
    (hh : ∀ j, ρ.sh (tmC xF tw c j) = 0) :
    ∃ J : Fin tw → List Bool, (∀ j, (J j).length ≤ Bud) ∧
      Step (dockC xF tw Mw c) Bud (wenc cap ρ).H (wenc cap ρ).A
        (wenc cap (DockW.updS (tmC xF tw c) ρ (fun _ => 0) (WriterIfaceJ.outBankJ win wout w v J))).H
        (wenc cap (DockW.updS (tmC xF tw c) ρ (fun _ => 0) (WriterIfaceJ.outBankJ win wout w v J))).A := by
  obtain ⟨J, hJ, hready⟩ := hwr
  have hwh : (fun j => ρ.sh (tmC xF tw c j)) = fun _ => 0 := funext hh
  have hwa : (fun j => ρ.st (tmC xF tw c j)) = WriterIface.inBank win w := by
    funext j
    unfold WriterIface.inBank
    by_cases hj : j = win
    · rw [if_pos hj, hj, hin]
    · rw [if_neg hj, hbl j hj]
  have hstep : Step Mw Bud (fun j => ρ.sh (tmC xF tw c j)) (fun j => ρ.st (tmC xF tw c j)) (fun _ => 0)
      (WriterIfaceJ.outBankJ win wout w v J) := by
    rw [hwh, hwa]
    obtain ⟨r, hr, ht, hhd, hs⟩ := hready
    exact ⟨r, hr, funext hhd, ht, hs⟩
  exact ⟨J, hJ, DockW.dockS (cap := cap) (tmC xF tw c) (tmC_inj xF tw c) ρ hstep⟩

end Tail

end NearCubicWires.WireExponent3_5.FinalPass.SymF
