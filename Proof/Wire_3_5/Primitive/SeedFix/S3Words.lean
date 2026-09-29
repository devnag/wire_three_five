import Proof.Wire_3_5.FinalPass.SeamsPt
import Proof.Wire_3_5.Primitive.SeedFix.TabRef
import Proof.Wire_3_5.Primitive.Writers.Enum

/-! # S3, part 0: the SYM per-point evaluator's call words and numbers (P3:3170-3178)

"Evaluate the reported lookups at the sampled pairs" (P3:3046-3048): the SYM per-point evaluator (`Seams.SymPtEval`)
computes `rsumSym = Σ_{e'} R̂_{e'}(c, u, v)` over the list seeds `e'`, where `R̂_{e'}` is, over the tuple's circuits,
stage 8's test of the circuit's corner word (stage 2 on its bottom gates) and the amplified list's reports of its
populations (stage 3, the majority machine on the seed's flat table). The evaluator reads, besides the point, the
call words the front (S5) leaves (`Seams.FrontOut`); they are declared here, before the program:

* **`symWords k : Fin 16 → List Bool`**, word `4t + j` of kind `t` for circuit `j < 4` (`wordOf`):
  `t = 0` the gate table `Corner.gatesW (tabH G_j) G_j` of the bottom gates `G_j = symGates (Cs j)` (the SYM data
  stage format, `DataBlank`); `t = 1` the framed top table `frame (ofFn (Cs j).top)`; `t = 2` the flat tables
  `flatTable Pl (seedOf i) |G_j|` of every list seed `i` in base's executable enumeration (`Enum.flatSeedEquiv`),
  concatenated; `t = 3` the stage-5 template `levelWord M J W (blank rows of length |G_j|)`. Past the tuple
  (`j ≥ a`), `G_j = []` and the top table is empty.
* **`symNums k : Fin 18 → ℕ`**: `0` the tuple size `a`, `1` the seed count `|FlatSeed|`, then number `2 + 4t + j`
  (`numOf`) of kind `t` for circuit `j`: `|G_j|`, `tabH G_j`, the flat table's length `tabLen`, the template's length.

Paper quantities of the main types: the SYM tuple's bottom gates and top tables, the list seeds' flat tables
(list:flatten, P3:1508-1520). -/

set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

namespace NearCubicWires.WireExponent3_5.PrimT.S3
open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Shared
open NearCubicWires.WireExponent3_5.Lists NearCubicWires.WireExponent3_5.FinalPass
open NearCubicWires.WireExponent3_5.FinalPass.Seams (SymCall)

/-- Circuit `j`'s bottom gates (`[]` past the tuple). -/
def gatesJ (k : SymCall) (j : Fin 4) : List (NormalizedThresholdGate k.P.n) :=
  if h : j.val < k.a then Stars.symGates (k.Cs ⟨j.val, h⟩) else []

/-- Circuit `j`'s top table (`[]` past the tuple). -/
def topJ (k : SymCall) (j : Fin 4) : List Bool :=
  if h : j.val < k.a then List.ofFn (k.Cs ⟨j.val, h⟩).top else []

/-- The `i`-th list seed (base's executable walk-sample enumeration). -/
def seedOf (k : SymCall) (i : Fin (Fintype.card k.Pl.FlatSeed)) : k.Pl.FlatSeed :=
  (PrimAsm.Enum.flatSeedEquiv k.Pl).symm i

/-- Circuit `j`'s flat tables, every list seed in the enumeration's order. -/
def tablesJ (k : SymCall) (j : Fin 4) : List Bool :=
  (List.finRange (Fintype.card k.Pl.FlatSeed)).flatMap fun i => Flat.flatTable k.Pl (seedOf k i) (gatesJ k j).length

/-- Circuit `j`'s stage-5 template: blank rows of the population's length. -/
def templJ (k : SymCall) (j : Fin 4) : List Bool :=
  ListEval.levelWord k.Pl.M k.Pl.base.J k.Pl.base.W (fun _ => List.replicate (gatesJ k j).length false)

/-- The call word of kind `t` for circuit `j`. -/
def wordOf (k : SymCall) (t j : Fin 4) : List Bool :=
  if t.val = 0 then Corner.gatesW (tabH (gatesJ k j)) (gatesJ k j)
  else if t.val = 1 then frame (topJ k j)
  else if t.val = 2 then tablesJ k j
  else templJ k j

/-- **S3's call words**: word `4t + j` is kind `t` of circuit `j`. -/
def symWords (k : SymCall) (w : Fin 16) : List Bool :=
  wordOf k ⟨w.val / 4, by omega⟩ ⟨w.val % 4, by omega⟩

/-- The flat table's length (the same at every seed). -/
def tabLen (k : SymCall) (j : Fin 4) : ℕ :=
  (Flat.flatTable k.Pl (seedOf k ⟨0, PrimAsm.Enum.card_flatSeed_pos k.Pl⟩) (gatesJ k j).length).length

/-- The call number of kind `t` for circuit `j`. -/
def numOf (k : SymCall) (t j : Fin 4) : ℕ :=
  if t.val = 0 then (gatesJ k j).length
  else if t.val = 1 then tabH (gatesJ k j)
  else if t.val = 2 then tabLen k j
  else (templJ k j).length

/-- **S3's call numbers**: `a`, the seed count, then number `2 + 4t + j` of kind `t` of circuit `j`. -/
def symNums (k : SymCall) (i : Fin 18) : ℕ :=
  if i.val = 0 then k.a
  else if i.val = 1 then Fintype.card k.Pl.FlatSeed
  else numOf k ⟨(i.val - 2) / 4, by omega⟩ ⟨(i.val - 2) % 4, by omega⟩

/-- The index of word `t` of circuit `j`. -/
def wIdx (t j : Fin 4) : Fin 16 := ⟨4 * t.val + j.val, by omega⟩
/-- The index of number `t` of circuit `j`. -/
def nIdx (t j : Fin 4) : Fin 18 := ⟨2 + 4 * t.val + j.val, by omega⟩

theorem symWords_idx (k : SymCall) (t j : Fin 4) : symWords k (wIdx t j) = wordOf k t j := by
  unfold symWords wIdx
  congr 1
  · ext; simp <;> omega
  · ext; simp <;> omega

theorem symNums_idx (k : SymCall) (t j : Fin 4) : symNums k (nIdx t j) = numOf k t j := by
  unfold symNums nIdx
  rw [if_neg (by simp), if_neg (by simp; omega)]
  congr 1
  · ext; simp <;> omega
  · ext; simp <;> omega

end NearCubicWires.WireExponent3_5.PrimT.S3
