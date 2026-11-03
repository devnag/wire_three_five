import Lean
import Proof.Wire_3_5.FinalPass.CoreIface
import Statement_Wire_3_5
import Proof.Wire_3_5.FinalPass.PlanFP
import Proof.Wire_3_5.FinalPass.SdR2
import Proof.Wire_3_5.FinalPass.Seams
import Proof.Wire_3_5.FinalPass.SeamsProg3
import Proof.Wire_3_5.Assembly.Gate0
import Proof.Wire_3_5.Primitive.Writers.Plan
import Proof.Wire_3_5.Assembly.Split
import Proof.Wire_3_5.FinalPass.Asm1Base
import Proof.Wire_3_5.FinalPass.SdR10Base
import Proof.Wire_3_5.FinalPass.SymWordsIface
import Proof.Wire_3_5.FinalPass.CoreIfaceBase


noncomputable section
set_option maxRecDepth 4096


/-! # The core half's word writers at the machine level (P3:3044-3048, 3170-3181)

`CoreWordsW` / `SymWordsW` take one word program per `l`. Two findings widen the contract:
the pool writers' donors are machines (GF2's search, the carrier tables, the sieve), which a word program cannot
embed; and S4's slots 6–7 depend on the filter's error degree `fe = F.filterErrDeg` (the walk length, the seed
width), which `fpIn` does not carry. S5Core docks every writer as a machine `Step` on the writer's encoded bank
(focus + zero padding) at each call family, so the writer is a machine chosen per gate, its layout fixed per `l`, its
degrees on `(l, fe)`, the capacity split from the step bound:

* **`CoreWordsM l m ws`**: the layout, the machine `M F` on the encoded bank `wenc`, the capacity
  `Kc F·(|fpIn|+1)^{Dk fe}` and the step bound `Cs F·(|fpIn|+1)^{Ds fe}`, and the run at every request: from the
  framed input (every other stream blank, heads and registers `0`, cell `false`), a `Step` of `M F` within the step
  bound between the encodings at the capacity; the outputs `ws r k`, the input kept, every other stream `0^ℓ` (`ℓ`
  within the step bound), heads and registers `0`;
* **`SymWordsM l`**: the same at the SYM requests with the SYM slots (`SymWordsW`'s twin);
* **`CoreWordsWF l m ws`** (a word program per gate, degree on `fe`) and the conversions **`CoreWordsWF.toM`**,
  **`CoreWordsW.toM`**, **`SymWordsW.toM`** (a word program is a machine: `WExec.exec`, `Exec.step`);
* **`S4WordsMA l`**, **`S4WordsMB l`**, **`NumsM l`** (`S4WordsWA`, `S4WordsWB`, `NumsW` over `CoreWordsM`), and
  their `toM`s.

Paper quantities of the main types: S4's own words (`s4Core2`), the SYM evaluator's call words, the printed
denominator `fpDen` at the width `W` (P3:3044-3048, 3170-3181). -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.FinalPass.Finish
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.BlockPlatform
open NearCubicWires.ExtDecompositionBatch
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Split
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.FinalPass.Seams
open NearCubicWires.WireExponent3_5.FinalPass.PlanFP NearCubicWires.WireExponent3_5.PrimAsm.Plan
open NearCubicWires.RepairOrdinary.SignedSortKey (binary)

/-- **A core word writer as a machine per gate** at every request of the call families of `l`: `m` output words
`ws r`. -/
structure CoreWordsM (l : Literals) (m : ℕ)
    (ws : ∀ (F : GateFree l) (kclk coef A a : ℕ) (ha : a ≤ kclk + 1), FReq l F kclk coef A a ha → Fin m → List Bool)
    where
  ns : ℕ
  nr : ℕ
  s : GateFree l → ℕ
  M : (F : GateFree l) → Machine (ns + 2 + nr) (s F)
  sIn : Fin (ns + 1)
  sOut : Fin m ↪ Fin (ns + 1)
  out_ne : ∀ k, sOut k ≠ sIn
  Kc : GateFree l → ℕ
  Dk : ℕ → ℕ
  Cs : GateFree l → ℕ
  Ds : ℕ → ℕ
  run : ∀ (F : GateFree l) (kclk coef A a : ℕ) (ha : a ≤ kclk + 1) (r : FReq l F kclk coef A a ha)
    (σ : WState ns nr), σ.st sIn = frame (fpIn l F kclk coef A a ha r) → (∀ i, σ.sh i = 0) →
      (∀ i, i ≠ sIn → σ.st i = []) → (∀ q, σ.val q = 0) → σ.cell = false →
      ∃ (τ : WState ns nr) (n : ℕ), n ≤ Cs F * ((fpIn l F kclk coef A a ha r).length + 1) ^ Ds F.filterErrDeg ∧
        Step (M F) n (wenc (Kc F * ((fpIn l F kclk coef A a ha r).length + 1) ^ Dk F.filterErrDeg) σ).H
          (wenc (Kc F * ((fpIn l F kclk coef A a ha r).length + 1) ^ Dk F.filterErrDeg) σ).A
          (wenc (Kc F * ((fpIn l F kclk coef A a ha r).length + 1) ^ Dk F.filterErrDeg) τ).H
          (wenc (Kc F * ((fpIn l F kclk coef A a ha r).length + 1) ^ Dk F.filterErrDeg) τ).A ∧
        (∀ k : Fin m, τ.st (sOut k) = ws F kclk coef A a ha r k) ∧
        τ.st sIn = frame (fpIn l F kclk coef A a ha r) ∧
        (∀ i, i ≠ sIn → (∀ k, i ≠ sOut k) →
          ∃ ℓ ≤ Cs F * ((fpIn l F kclk coef A a ha r).length + 1) ^ Ds F.filterErrDeg, τ.st i = List.replicate ℓ false) ∧
        (∀ i, τ.sh i = 0) ∧ (∀ q, τ.val q = 0)

/-- **The SYM words writer as a machine per gate** (`SymWordsW`'s twin): the run at the SYM requests, the SYM
slots. -/
structure SymWordsM (l : Literals) where
  ns : ℕ
  nr : ℕ
  s : GateFree l → ℕ
  M : (F : GateFree l) → Machine (ns + 2 + nr) (s F)
  sIn : Fin (ns + 1)
  sOut : Fin 17 ↪ Fin (ns + 1)
  out_ne : ∀ k, sOut k ≠ sIn
  Kc : GateFree l → ℕ
  Dk : ℕ → ℕ
  Cs : GateFree l → ℕ
  Ds : ℕ → ℕ
  run : ∀ (F : GateFree l) (kclk coef A a : ℕ) (ha : a ≤ kclk + 1) (r : FReq l F kclk coef A a ha),
    r.1.mode = .sym → ∀ σ : WState ns nr, σ.st sIn = frame (fpIn l F kclk coef A a ha r) → (∀ i, σ.sh i = 0) →
      (∀ i, i ≠ sIn → σ.st i = []) → (∀ q, σ.val q = 0) → σ.cell = false →
      ∃ (τ : WState ns nr) (n : ℕ), n ≤ Cs F * ((fpIn l F kclk coef A a ha r).length + 1) ^ Ds F.filterErrDeg ∧
        Step (M F) n (wenc (Kc F * ((fpIn l F kclk coef A a ha r).length + 1) ^ Dk F.filterErrDeg) σ).H
          (wenc (Kc F * ((fpIn l F kclk coef A a ha r).length + 1) ^ Dk F.filterErrDeg) σ).A
          (wenc (Kc F * ((fpIn l F kclk coef A a ha r).length + 1) ^ Dk F.filterErrDeg) τ).H
          (wenc (Kc F * ((fpIn l F kclk coef A a ha r).length + 1) ^ Dk F.filterErrDeg) τ).A ∧
        (∀ k : Fin 17, τ.st (sOut k) = frontWordsW2 l F kclk coef A a ha Sw0 r (symSlot k)) ∧
        τ.st sIn = frame (fpIn l F kclk coef A a ha r) ∧
        (∀ i, i ≠ sIn → (∀ k, i ≠ sOut k) →
          ∃ ℓ ≤ Cs F * ((fpIn l F kclk coef A a ha r).length + 1) ^ Ds F.filterErrDeg, τ.st i = List.replicate ℓ false) ∧
        (∀ i, τ.sh i = 0) ∧ (∀ q, τ.val q = 0)

/-- **S4's words, part A, as a machine per gate** (slots `0 … 3`). -/
abbrev S4WordsMA (l : Literals) : Type :=
  CoreWordsM l 4 fun F kclk coef A a ha r k => frontWordsW2 l F kclk coef A a ha Sw0 r (s4SlotA k)

/-- **S4's words, part B, as a machine per gate** (slots `4 … 7`; slots 6–7 read `fe`). -/
abbrev S4WordsMB (l : Literals) : Type :=
  CoreWordsM l 4 fun F kclk coef A a ha r k => frontWordsW2 l F kclk coef A a ha Sw0 r (s4SlotB k)

/-- **The numbers S4 starts from, as a machine per gate** (`FrontOut.nums`'s form; the width's degree `ZT` is on
`(l, fe)`, `Sd.R.ZT_eq`). -/
abbrev NumsM (l : Literals) : Type :=
  CoreWordsM l 2 fun F kclk coef A a ha r i =>
    frame (binary (Sd.R.Tf l F kclk coef A a ha r) ((![0, fpDen l F kclk coef A a ha r] : Fin 2 → ℕ) i))

end NearCubicWires.WireExponent3_5.FinalPass.Finish

end
