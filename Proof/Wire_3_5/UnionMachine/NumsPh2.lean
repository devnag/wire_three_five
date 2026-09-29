import Proof.Wire_3_5.FinalPass.CoreIfaceM

/-! # NW: the numbers writer `NumsM l`, phase interface v2 (types only)

"The final pass prints `Num/Den`" (P3:3044-3048) with `Den = fpDen r = denOf`: the point count's product
`|centers|·|E × FlatSeed|·Q` at SYM, `|PrimeIndex(cutoff)|·|centers|·|E|·Q` at THR (`NumDen.denRaw`), at least `1`.
The `NumsM l` (`CoreWordsM l 2`) asks for the two words `frame (binary T_f 0)`,
`frame (binary T_f fpDen)` (`T_f = Sd.R.Tf = KT·N^{ZT}`), by a machine per gate at the capacity `K_c F·(|fpIn|+1)^{D_k fe}`
within `C_s F·(|fpIn|+1)^{D_s fe}` steps. Since `|centers| = 2^{n−k}` while `|fpIn| ≥ Q ≥ 2^{⌊(5kh+3)/4⌋}` only, the
denominator is split `fpDen = 2^{e}·V` with `e = n − k` (`eOf`) and `V = vOf r` (`2^{O(k)}·poly(n)`, unary-sized):
the shift is written as zeros in binary.

* **Layout v2** (the donors' bank): `WState (LNS x) LNR`, the C4 cell bank (`LNS x = 160 + x` streams,
  `LNR = 512` registers; the wenc bank of `Machine (LNS x + 2 + LNR)`), `x` extra streams chosen by the assembly (so
  (b)'s port machine `Machine (21 + TI alg + 1)`, whose width depends on the algorithm, docks); streams `sIn x`,
  `sW0 x`, `sW1 x` = `sk x 150, 151, 152` (the input `fpIn`, the two words); registers `rN`, `rM` (the mode bit,
  THR `1`), `rE` (`e`), `rT` (`T_f`), `rV` (`V`) = `505 … 509`; `starBlk` (`480 … 499`, a `Fin 20` block for
  `StarNums.starNumsM`). v1 (`NumsPh`, `WState 7 16`) could host none of the donors (bank sizes).
* **Values**: `eOf`, `mOf`, `vOf` (from `NumDen.denRaw`'s factors), `DenSplit` (`fpDen = max (2^{eOf}·vOf) 1`, the
  assembly's lemma: `denOf = max denRaw 1`, so no positivity of `|PrimeIndex(cutoff)|` is needed).
* **Boundary predicates**: `Resid` (every stream but `sIn` blank, of bounded length), `Entry` (`CoreWordsM`'s entry),
  `AfterC` (`n`, the mode, `e`, `T_f` in registers), `AfterV` (`+ V`), `DBank` (phase (d)'s generic entry), `Final`
  (`CoreWordsM`'s exit at `T_f`, `D`).
* **Phases** (each a machine per gate on the bank, a capacity need `K_n F·(|fpIn|+1)^{D_n fe}` and a step bound;
  runs `Step` between `wenc cap` states at EVERY capacity above the need):
  * **`PhC`** (c): `sIn`'s `n` and mode bit into `rN`, `rM`; `e = n − k` into `rE`, `T_f = KT·N^{ZT}` into `rT`.
    Donors: `PrimAsm.ParseNat.readNatM` (`natWord n` from the framed input), `PrimAsm.StarNums.starNumsM cr fe`
    (`r`, `s`, `k`, …), PA's `UnaryArith` (products, powers).
  * **`PhA`** (a, SYM requests): `V = |E|·|FlatSeed|·Q` into `rV`. Donors: the C4 SYM numbers program
    `PrimT.C4Set.numsSW cr fe ζ Cδ C` (PrimTC4SB, the first stage of `C4Set.bigW`; `C4SymN.sym_bigS` / `caps_of`
    identify its registers as `Q = SeedFix.symCount`, `2^{seedBits (SymDec.gP …)} = |E|`, `2^{FlatNums.fbv …} =
    |FlatSeed|`); `bigW` itself runs at `2·2^{capExp C n} + 2` (`sym_bigS`), so (a) runs `numsSW` alone, at the
    common capacity (its values are below `|fpIn|·poly(n)`).
  * **`PhB`** (b, THR requests): `V = |PrimeIndex(cutoff)|·|E|·Q` into `rV`. Donors: `PrimThrW.PortsE.NumsPort2 alg
    Dexp` (a `Machine (20 + x) s`, out-ports `thrNumVals`: `nPr = (primesUpTo cut).card = |PrimeIndex cut|` by
    `PrimAsm.Enum.primeEquiv`, `cut = thrCutoff P Cs alg den` at `den = 8(|𝒢|+1)n^D = thrCallDen`
    (`PrimThrW.Joins.thrNumVals_den`), cost `PolyBounded (cost m) m Cc Dc`); `Q = SeedFix.thrCount` from the THR
    numbers program (`PrimAsm.ThrN4.bigT_spec`, `ThrCap.thrQ_link`), which reads the v4 data word (`TS4.m3_run`,
    `ThrDataStage4.run3`: `dataWord (hashNums ++ thrCounts)`); `|E| = 2^{seedBits}` (`Filters.card_gapSeed`).
  * **`PhD`** (d, generic): from `T`, `e`, `v` in `rT`, `rE`, `rV`, write `frame (binary T 0)` on `sW0` and
    `frame (binary T (max (2^e·v) 1))` on `sW1` (`v` at width `T − e` followed by `e` zeros; `1` when `v = 0`), clear
    every register; steps `≤ C·(T+v+1)^D`; the word streams must be `[]` at entry (tapes never shrink). Donors: C5's
    binary writers, the RegRat word kit (the output machine).
* **`NumsOfPhases`**: `PhC l → PhA l → PhB l → PhD → NumsM l` (the assembly: (c); branch on `rM`
  (`BlockBranch.branchM`); (a) or (b); (d); `DenSplit`).

Paper quantity of the main types: the final pass's denominator `Den` in `T_f`-bit binary (P3:3044-3048, 3170-3181). -/

set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

namespace NearCubicWires.WireExponent3_5.UnionMachine.NumsPh2
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.BlockPlatform
open NearCubicWires.ExtDecompositionBatch
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Split
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.FinalPass.Seams
open NearCubicWires.WireExponent3_5.FinalPass.PlanFP NearCubicWires.WireExponent3_5.PrimAsm.Plan
open NearCubicWires.WireExponent3_5.FinalPass.Finish NearCubicWires.WireExponent3_5.PrimAsm.SymLayout
open NearCubicWires.RepairOrdinary.SignedSortKey (binary)

/-! ## The layout -/

variable (x : ℕ)

/-- The writer's word states (the C4 cell bank with `x` extra streams). -/
abbrev St : Type := WState (LNS x) LNR

/-- The input stream (`frame fpIn`). -/
def sIn : Fin (LNS x + 1) := PrimAsm.SymLayout.sk x 150
/-- The first word (`frame (binary T_f 0)`). -/
def sW0 : Fin (LNS x + 1) := PrimAsm.SymLayout.sk x 151
/-- The second word (`frame (binary T_f fpDen)`). -/
def sW1 : Fin (LNS x + 1) := PrimAsm.SymLayout.sk x 152

/-- `n`. -/
def rN : Fin LNR := ⟨505, by decide⟩
/-- The mode bit (THR `1`, SYM `0`). -/
def rM : Fin LNR := ⟨506, by decide⟩
/-- The shift `e = n − k`. -/
def rE : Fin LNR := ⟨507, by decide⟩
/-- The width `T_f`. -/
def rT : Fin LNR := ⟨508, by decide⟩
/-- The unshifted value `V`. -/
def rV : Fin LNR := ⟨509, by decide⟩

/-- A `Fin 20` register block for `StarNums.starNumsM` (registers `480 … 499`). -/
def starBlk : Fin 20 ↪ Fin LNR :=
  ⟨fun j => ⟨480 + j.val, by have := j.isLt; show 480 + j.val < 512; omega⟩, fun i j h => by
    have := congrArg Fin.val h
    exact Fin.ext (by simp at this; omega)⟩

theorem sIn_val : (sIn x).val = 150 := rfl
theorem sW0_val : (sW0 x).val = 151 := rfl
theorem sW1_val : (sW1 x).val = 152 := rfl

/-- The output slots of `NumsM`. -/
def sOutN : Fin 2 ↪ Fin (LNS x + 1) :=
  ⟨fun i => if i.val = 0 then sW0 x else sW1 x, by
    intro i j h
    have hi := i.isLt
    have hj := j.isLt
    have e0 := sW0_val x
    have e1 := sW1_val x
    by_cases h0 : i.val = 0 <;> by_cases h1 : j.val = 0 <;> simp only [h0, h1, if_true, if_false] at h <;>
      first | exact Fin.ext (by omega) | (have := congrArg Fin.val h; omega)⟩

/-! ## The values -/

section Values
variable (l : Literals) (F : GateFree l) (kclk coef A a : ℕ) (ha : a ≤ kclk + 1)

/-- **The shift** `e = n − k` (`|centers| = 2^{n−k}`). -/
noncomputable def eOf (r : FReq l F kclk coef A a ha) : ℕ := r.1.n - ((gate0 l F).budget kclk coef A a ha).kOf r.1.n

/-- The mode bit. -/
def mOf (r : FReq l F kclk coef A a ha) : ℕ :=
  match r.1.mode with
  | .thr => 1
  | .sym => 0

/-- **The unshifted value** `V`: `|E|·|FlatSeed|·Q` at SYM, `|PrimeIndex(cutoff)|·|E|·Q` at THR (`1` off-star). -/
noncomputable def vOfReq : PrimRequest → ℕ
  | ⟨n, .sym, _, _, Cs, carriers, translation⟩ =>
      if hs : (callInputs l F kclk coef A a ha).StarAt n then
        Fintype.card (Filters.GapSeed ((callInputs l F kclk coef A a ha).filterParams .sym n)) *
          Fintype.card (Primitive.symListParams (callInputs l F kclk coef A a ha) n _ Cs carriers).FlatSeed *
            ((SeedFix.greedySampler (callInputs l F kclk coef A a ha) (gate0 l F).alg).symS Cs carriers
              translation hs).Q
      else 1
  | ⟨n, .thr, _, _, Cs, carriers, translation⟩ =>
      if hs : (callInputs l F kclk coef A a ha).StarAt n then
        Fintype.card (SupplierPrime.PrimeIndex (Primitive.thrCutoff ((callInputs l F kclk coef A a ha).starParams n hs)
          Cs (gate0 l F).alg (Primitive.thrCallDen (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs))) *
          Fintype.card (Filters.GapSeed ((callInputs l F kclk coef A a ha).filterParams .thr n)) *
            ((SeedFix.greedySampler (callInputs l F kclk coef A a ha) (gate0 l F).alg).thrS Cs carriers
              translation hs).Q
      else 1

/-- `V` at a request of the family. -/
noncomputable def vOf (r : FReq l F kclk coef A a ha) : ℕ := vOfReq l F kclk coef A a ha r.1

/-- **The denominator split** (the assembly's lemma; `denOf = max denRaw 1`, `|centers| = 2^{n−k}`,
`|E × FlatSeed| = |E|·|FlatSeed|`): `fpDen r = max (2^{e}·V) 1`. -/
def DenSplit : Prop :=
  ∀ r : FReq l F kclk coef A a ha,
    fpDen l F kclk coef A a ha r = max (2 ^ eOf l F kclk coef A a ha r * vOf l F kclk coef A a ha r) 1

end Values

/-! ## The boundary predicates -/

section Bank
variable (l : Literals) (F : GateFree l) (kclk coef A a : ℕ) (ha : a ≤ kclk + 1)

/-- **The machine's entry** (`CoreWordsM.run`'s hypotheses). -/
structure Entry (r : FReq l F kclk coef A a ha) (σ : St x) : Prop where
  hin : σ.st (sIn x) = frame (fpIn l F kclk coef A a ha r)
  heads : ∀ i, σ.sh i = 0
  blank : ∀ i, i ≠ (sIn x) → σ.st i = []
  regs : ∀ q, σ.val q = 0
  cell : σ.cell = false

end Bank

/-! ## The phases -/

section Phases

end Phases

/-! ## The assembly's statement -/

end NearCubicWires.WireExponent3_5.UnionMachine.NumsPh2
