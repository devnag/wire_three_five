import Proof.Wire_3_5.FinalPass.HashFree

/-! # C4KW: the HASH setup's kept words writer (types, stage interfaces)

`filt:soft`, P3:2253-2290: the Hb printer runs on a 94-tape bank whose static words before cell `0` are
`C4H.hb0 (C4H.hbX D (capsOf cap) 0 0)` (the word state's streams and registers, the log, the elimination's tapes at
`R0`). The HASH setup leaves them FRAMED on its kept tapes (`C4H.HBank2.hKW`). This module fixes the writer's type
and the types of its four stages, so the stages can be built and docked independently.

* **`kw D cap`**: the 94 kept words; **`kwNum`**, **`kwIns`**: the writer's twelve inputs (`htWord Fs`,
  `popsWord pops`, then `1^ℓ₀, 1^{refMod}, 1^{B*}, 1^t, 1^J, 1^G, 1^N, 1^{nE}, 1^{cap}, 1^{|pops|}`); **`kwT`** (the
  call's numbers), **`kwS`** (the writer's size).
* **`KWPart oS iS`**: a stage writing `frame (kw D cap (oS j))` on its outputs from the inputs `iS` (kept), its
  scratch left as falses, every head back at `0`, within `K·(S+1)^2 + K·(T+1)^{Dg}` steps. Its tapes: the outputs,
  the inputs, the scratch.
* **`KWW`** `:= KWPart id id` (the whole writer: outputs `0 … 93`, inputs `94 … 105`, scratch from `106`).
* The stages: **`PartB1`** (every word but `3, 4, 5, 71`: rulers, unary words, constants, registers, log,
  elimination tapes), **`PartB2`** (`5`: `wtWord (wsOf MP)` from `1^t, 1^J, 1^{B*}`), **`PartB3`** (`71`: the modulus
  word from `1^ℓ₀, 1^{refMod}`), **`PartB4`** (`3, 4`: the framed copies of `htWord Fs`, `popsWord pops`).

Paper quantity of the main types: the Hb printer's static words at the HASH call (P3:2253-2290). -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.PrimT.C4KW
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.RepairOrdinary NearCubicWires.LocalBitMultitape
open NearCubicWires.WireExponent3_5.PrimT.C4H NearCubicWires.ExtDecompositionBatch

noncomputable section

/-- **The kept words** at the HASH call's data `D` and capacity `cap` (`HBank2`'s `KW`, framed there). -/
def kw (D : HashData) (cap : ℕ) : Fin 94 → List Bool := hb0 (hbX D (FinalPass.HashFr.capsOf cap) 0 0)

/-- The writer's unary inputs (`2 … 11`); `0`, `1` are the words `htWord Fs`, `popsWord pops`. -/
def kwNum (D : HashData) (cap : ℕ) : Fin 12 → ℕ :=
  ![0, 0, D.MP.ell0, D.MP.refMod, D.MP.Bstar, D.MP.t, D.MP.J, D.G, D.N, D.nE, cap, D.pops.length]

/-- **The writer's twelve inputs.** -/
def kwIns (D : HashData) (cap : ℕ) (i : Fin 12) : List Bool :=
  if i.val = 0 then HbM.htWord D.Fs else if i.val = 1 then HbM.popsWord D.pops
  else List.replicate (kwNum D cap i) true

/-- The call's numbers the writer computes with. -/
def kwT (D : HashData) : ℕ :=
  D.MP.ell0 + D.MP.refMod + D.MP.Bstar + D.MP.t + D.MP.J + D.G + D.N + D.nE + D.pops.length

/-- The writer's size. -/
def kwS (D : HashData) (cap : ℕ) : ℕ := (HbM.htWord D.Fs).length + (HbM.popsWord D.pops).length + cap + kwT D

/-- A stage's entry bank: its outputs blank, its inputs, its scratch blank. -/
def partIn {no ni : ℕ} (iS : Fin ni → Fin 12) (x : ℕ) (D : HashData) (cap : ℕ) : Fin (no + ni + x) → List Bool :=
  Fin.addCases (Fin.addCases (fun _ : Fin no => []) (fun i => kwIns D cap (iS i))) (fun _ : Fin x => [])

/-- **A stage of the kept words writer**: from its inputs (kept), the framed kept words `oS` on its outputs, its
scratch left as falses, every head back at `0`. -/
structure KWPart {no ni : ℕ} (oS : Fin no → Fin 94) (iS : Fin ni → Fin 12) where
  x : ℕ
  s : ℕ
  M : Machine (no + ni + x) s
  cost : HashData → ℕ → ℕ
  K : ℕ
  Dg : ℕ
  cost_le : ∀ (D : HashData) (cap : ℕ), cost D cap ≤ K * (kwS D cap + 1) ^ 2 + K * (kwT D + 1) ^ Dg
  run : ∀ (D : HashData) (cap : ℕ), ∃ B : Fin (no + ni + x) → List Bool,
    Step M (cost D cap) (fun _ => 0) (partIn (no := no) iS x D cap) (fun _ => 0) B ∧
    (∀ j : Fin no, B (Fin.castAdd x (Fin.castAdd ni j)) = frame (kw D cap (oS j))) ∧
    (∀ i : Fin ni, B (Fin.castAdd x (Fin.natAdd no i)) = kwIns D cap (iS i)) ∧
    (∀ k : Fin x, ∃ m ≤ cost D cap, B (Fin.natAdd (no + ni) k) = List.replicate m false)

/-- **The kept words writer** (docks it in the HASH setup): outputs `0 … 93`, inputs `94 … 105`. -/
abbrev KWW : Type := KWPart (no := 94) (ni := 12) id id

/-! ## The four stages -/

/-- B1's outputs: every kept word but `3, 4, 5, 71`. -/
def oB1 (j : Fin 90) : Fin 94 :=
  ⟨if j.val < 3 then j.val else if j.val < 68 then j.val + 3 else j.val + 4, by split_ifs <;> omega⟩

/-- B1's inputs: `1^ℓ₀, 1^t, 1^J, 1^G, 1^N, 1^{nE}, 1^{cap}, 1^{|pops|}`. -/
def iB1 : Fin 8 → Fin 12 := ![2, 5, 6, 7, 8, 9, 10, 11]

/-- **B1**: the rulers, the unary words, the constants, the registers, the log, the elimination's tapes. -/
abbrev PartB1 : Type := KWPart oB1 iB1

/-- B2's output: `wtWord (wsOf MP)` (kept word `5`). -/
def oB2 : Fin 1 → Fin 94 := ![5]

/-- B2's inputs: `1^t, 1^J, 1^{B*}`. -/
def iB2 : Fin 3 → Fin 12 := ![5, 6, 4]

/-- **B2**: the cleared weights' word `wtWord (wsOf D.MP)`. -/
abbrev PartB2 : Type := KWPart oB2 iB2

/-- B3's output: the elimination's modulus word (kept word `71`). -/
def oB3 : Fin 1 → Fin 94 := ![71]

/-- B3's inputs: `1^ℓ₀, 1^{refMod}`. -/
def iB3 : Fin 2 → Fin 12 := ![2, 3]

/-- **B3**: the modulus word. -/
abbrev PartB3 : Type := KWPart oB3 iB3

/-- B4's outputs: `htWord Fs`, `popsWord pops` (kept words `3`, `4`). -/
def oB4 : Fin 2 → Fin 94 := ![3, 4]

/-- B4's inputs: the two words. -/
def iB4 : Fin 2 → Fin 12 := ![0, 1]

/-- **B4**: the framed copies. -/
abbrev PartB4 : Type := KWPart oB4 iB4

/-! ## Sanity: B2's output word -/

theorem kw_mod (D : HashData) (cap : ℕ) :
    kw D cap 71 = frame (SignedSortKey.binary D.MP.ell0 D.MP.refMod) := rfl

end

end NearCubicWires.WireExponent3_5.PrimT.C4KW
