import Proof.Wire_3_5.Primitive.Writers.C3WPhase2
import Proof.Wire_3_5.Primitive.Writers.C3WAppend

/-! # C3 request writer, part 6: the machine's layout and its front

The writer's bank: the register program's `WT = CN + 2 + CR` tapes, the shared record tape of its masked phases, then
the front's tapes (the raw request, `Unframe`'s log, `CapReader`'s scratch, `UnaryCalc`'s tapes, the append record),
the writers' regions (gate twice, halves, width, flips twice, columns twice) and C3a's region.

Paper quantity: none (the machine layout of alg:compiler's request writer, P3:1886-1906). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

namespace NearCubicWires.WireExponent3_5.PrimAsm.C3Mach
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary.RecoveryRootRound NearCubicWires.BlockPlatform NearCubicWires.WireExponent3_5
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.ListMachine NearCubicWires.WireExponent3_5.ListMachine.Row
open NearCubicWires.WireExponent3_5.PrimAsm NearCubicWires.WireExponent3_5.PrimAsm.GeoFront
open NearCubicWires.WireExponent3_5.PrimAsm.DockW
open NearCubicWires.WireExponent3_5.PrimAsm.C3Phase NearCubicWires.WireExponent3_5.PrimAsm.C3Dock

/-- The register program's tapes. -/
abbrev WT : ℕ := CN + 2 + CR

/-- The docked machines' tape counts (the gate, halves, width, flips and columns writers, C3a) and the front's fill
polynomial `Cv(n+1)^Dv`. -/
structure Lay where
  tG : ℕ
  tS : ℕ
  tW : ℕ
  tF : ℕ
  tC : ℕ
  Ua : ℕ
  Dv : ℕ
  Cv : ℕ

namespace Lay
variable (L : Lay)

abbrev Tu : ℕ := UnaryCalc.tapes L.Dv
/-- The tapes after the program's and the record tape. -/
abbrev X : ℕ := 15 + L.Tu + 2 * L.tG + L.tS + L.tW + 2 * L.tF + 2 * L.tC + L.Ua
/-- The layout's tape count. -/
abbrev U : ℕ := WT + 1 + L.X

def oG1 : ℕ := WT + 16 + L.Tu
def oG2 : ℕ := L.oG1 + L.tG
def oS : ℕ := L.oG2 + L.tG
def oW : ℕ := L.oS + L.tS
def oF1 : ℕ := L.oW + L.tW
def oF2 : ℕ := L.oF1 + L.tF
def oC1 : ℕ := L.oF2 + L.tF
def oC2 : ℕ := L.oC1 + L.tC
def oA : ℕ := L.oC2 + L.tC

theorem X_ge : 15 + L.Tu ≤ L.X := by
  show 15 + L.Tu ≤ 15 + L.Tu + 2 * L.tG + L.tS + L.tW + 2 * L.tF + 2 * L.tC + L.Ua; omega

theorem oA_U : L.oA + L.Ua = L.U := by
  simp only [oA, oC2, oC1, oF2, oF1, oW, oS, oG2, oG1, U, X]; omega

theorem offs : WT + 1 ≤ L.oG1 ∧ L.oG1 + L.tG = L.oG2 ∧ L.oG2 + L.tG = L.oS ∧ L.oS + L.tS = L.oW ∧
    L.oW + L.tW = L.oF1 ∧ L.oF1 + L.tF = L.oF2 ∧ L.oF2 + L.tF = L.oC1 ∧ L.oC1 + L.tC = L.oC2 ∧
    L.oC2 + L.tC = L.oA ∧ L.oA + L.Ua = L.U :=
  ⟨by simp only [oG1]; omega, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, L.oA_U⟩

/-! ## Indices -/

/-- A tape of the register program. -/
def wm (j : Fin WT) : Fin L.U := ⟨j.val, by have := j.isLt; show j.val < WT + 1 + L.X; omega⟩
def ws (s : Fin (CN + 1)) : Fin L.U := L.wm (sTape s)
def wc : Fin L.U := L.wm cTape
def wr (r : Fin CR) : Fin L.U := L.wm (rTape r)
/-- The masked phases' record tape. -/
def wrec : Fin L.U := ⟨WT, by have := L.X_ge; show WT < WT + 1 + L.X; omega⟩
def xraw : Fin L.U := ⟨WT + 1, by have := L.X_ge; show WT + 1 < WT + 1 + L.X; omega⟩
def xlg : Fin L.U := ⟨WT + 2, by have := L.X_ge; show WT + 2 < WT + 1 + L.X; omega⟩
def xcp (j : Fin 12) : Fin L.U := ⟨WT + 3 + j.val, by have := j.isLt; have := L.X_ge; show _ < WT + 1 + L.X; omega⟩
def xpw (k : Fin L.Tu) : Fin L.U := ⟨WT + 15 + k.val, by have := k.isLt; have := L.X_ge; show _ < WT + 1 + L.X; omega⟩
def xrec : Fin L.U := ⟨WT + 15 + L.Tu, by have := L.X_ge; show _ < WT + 1 + L.X; omega⟩

theorem ws_val (s : Fin (CN + 1)) : (L.ws s).val = if s.val = 0 then 0 else s.val + 1 := rfl
theorem ws_lt (s : Fin (CN + 1)) : (L.ws s).val < WT := (sTape (nr := CR) s).isLt
theorem wc_val : L.wc.val = 1 := rfl
theorem wr_val (r : Fin CR) : (L.wr r).val = CN + 2 + r.val := rfl

theorem ws_inj {a b : Fin (CN + 1)} (h : L.ws a = L.ws b) : a = b :=
  sTape_inj (nr := CR) (Fin.ext (show (L.ws a).val = (L.ws b).val from congrArg Fin.val h))

theorem ws_ne {a b : Fin (CN + 1)} (h : a ≠ b) : L.ws a ≠ L.ws b := fun e => h (L.ws_inj e)

theorem wc_ne (s : Fin (CN + 1)) : L.wc ≠ L.ws s := by
  intro e; have := congrArg Fin.val e; rw [wc_val, ws_val] at this; split at this <;> omega

theorem wr_ne (r : Fin CR) (s : Fin (CN + 1)) : L.wr r ≠ L.ws s := by
  intro e; have h1 := congrArg Fin.val e; rw [wr_val, ws_val] at h1; have h2 := s.isLt; split at h1 <;> omega

/-! ## The bank before the fill -/

/-- The streams `st` on the program's stream tapes, the cell, the registers and the record blank, every tape from
`lo` on blank. -/
def Inv (B : Fin L.U → List Bool) (st : Fin (CN + 1) → List Bool) (lo : ℕ) : Prop :=
  (∀ s, B (L.ws s) = st s) ∧ B L.wc = [] ∧ (∀ r, B (L.wr r) = []) ∧ B L.wrec = [] ∧
    ∀ x : Fin L.U, lo ≤ x.val → B x = []

/-! ## A writer, docked -/

/-- **One writer stage**: the writer's run from `frame w` on `cIN` to `v` on the blank stream `sX`, its other tapes
in the region `[base, base + t)`. -/
theorem wstage {t s' : ℕ} {M : Machine t s'} {Bud : ℕ} {i o : Fin t} {w v : List Bool} (hio : i ≠ o)
    (h : WriterIfaceJ.WriterRun M Bud i o w v) (sX : Fin (CN + 1)) (hX : sX ≠ cIN) (base : ℕ)
    (hbase : WT + 1 ≤ base) (hb : base + t ≤ L.U) (B : Fin L.U → List Bool) (st : Fin (CN + 1) → List Bool)
    (hI : L.Inv B st base) (hin : st cIN = frame w) (hout : st sX = []) :
    ∃ B', Step (RecoveryFocus.machine (portSl i o (L.ws cIN) (L.ws sX) base hb) M) Bud (fun _ => 0) B
      (fun _ => 0) B' ∧ L.Inv B' (Function.update st sX v) (base + t) := by
  have hWT : WT = 64 := rfl
  have hCN : CN = 22 := rfl
  have hCR : CR = 40 := rfl
  have hrv : L.wrec.val = WT := rfl
  obtain ⟨hs, hc, hr, hrc, hz⟩ := hI
  obtain ⟨B', d, e1, e2, e3⟩ := wdock hio h (L.ws cIN) (L.ws sX) (L.ws_ne (Ne.symm hX)) base hb
    (by have := L.ws_lt cIN; omega) (by have := L.ws_lt sX; omega) (fun _ => 0) B rfl rfl (fun _ _ _ => rfl)
    (by rw [hs, hin]) (by rw [hs, hout]) (fun x h1 _ => hz x h1)
  refine ⟨B', d, ?_, ?_, ?_, ?_, ?_⟩
  · intro s
    by_cases h1 : s = sX
    · subst h1; rw [e2, Function.update_self]
    · rw [Function.update_of_ne h1]
      by_cases h2 : s = cIN
      · subst h2; rw [e1, hin]
      · rw [e3 _ (L.ws_ne h2) (L.ws_ne h1) (Or.inl (by have := L.ws_lt s; omega)), hs]
  · rw [e3 _ (L.wc_ne _) (L.wc_ne _) (Or.inl (by rw [wc_val]; omega)), hc]
  · intro r
    rw [e3 _ (L.wr_ne _ _) (L.wr_ne _ _) (Or.inl (by rw [wr_val]; have := r.isLt; omega)), hr]
  · rw [e3 _ (fun e => by have h1 := congrArg Fin.val e; have h2 := L.ws_lt cIN; omega)
      (fun e => by have h1 := congrArg Fin.val e; have h2 := L.ws_lt sX; omega)
      (Or.inl (by omega)), hrc]
  · intro x hx
    rw [e3 x (fun e => by rw [e] at hx; have := L.ws_lt cIN; omega)
      (fun e => by rw [e] at hx; have := L.ws_lt sX; omega) (Or.inr hx), hz x (by omega)]

end Lay

end NearCubicWires.WireExponent3_5.PrimAsm.C3Mach
