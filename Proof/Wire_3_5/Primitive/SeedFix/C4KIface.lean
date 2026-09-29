import Proof.Wire_3_5.Primitive.SeedFix.SeedFixTypes

/-! # C4.K, the per-mode contract: one C4 stage per class mode, in `C4Leaf`'s order of choice

"There are `O_D(L²+k+L)` seed-prefix decisions, each with a constant number of exact printer calls. Under the
displayed allowances the printer applies, and the explicit descriptions and their construction give the middle term in
`prim:runtime`" (P3:3170-3173); "Greedily choose a child with no larger value, using at most two printer calls per
hash bit" (P3:2331-2333). `C4Leaf`'s `C4At` has four stages; the front is built (`C4Front.front_req`). The other three
are delivered per mode, each in `C4Leaf`'s order of choice (`fe`, then the floors `E`, `CD`, then `F`, then `c`), and
C4.K combines them (componentwise maximum of the floors, sum of the coefficients):
* **`SymAt`**, **`HashAt`**, **`ThrAt`**: a stage and its run at every call of the mode, within `c·seedClasses E` at the
  ledger's `(n, kOf n, psiOf n)` (`C4At.sym_run`, `hash_run`, `thr_run` verbatim, at `E`, `c`);
* **`ModeLeaf`** (the order of choice) and the three deliverables **`SymLeafC4`**, **`HashLeafC4`**,
  **`ThrLeafC4`**.

Paper quantities of the main types: the fixed seeds `seedWord` and the hash bits (`thrIn`), through the three runs. -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.PrimT.C4K
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Shared
open NearCubicWires.WireExponent3_5.Stars NearCubicWires.WireExponent3_5.Filters NearCubicWires.WireExponent3_5.Lists
open NearCubicWires.WireExponent3_5.FinalPass NearCubicWires.SupplierPipeline
open NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.Cost NearCubicWires.WireExponent3_5.Split NearCubicWires.WireExponent3_5.Primitive
open NearCubicWires.WireExponent3_5.PrimAsm.Plan NearCubicWires.WireExponent3_5.PrimAsm.WriterIface
open NearCubicWires.WireExponent3_5.PrimT.SeedFixTypes

section At
variable (l : Literals) (F : GateFree l) (E : Envelope) (c kclk coef A a : ℕ) (ha : a ≤ kclk + 1)

/-- **The SYM stage at one call family** (`C4At.sym`, `sym_run` at `E`, `c`). -/
def SymAt : Type :=
  Σ' S : Stage3, ∀ (n a' : ℕ) (ha' : a' ≤ 4) (Cs : Fin a' → NormalizedSymmetricThresholdCircuit n)
    (carriers : List (Carrier n)) (translation : List ℕ),
    (callInputs l F kclk coef A a ha).Call (symReq n a' ha' Cs carriers translation) →
    ∀ hs : (callInputs l F kclk coef A a ha).StarAt n,
      Stage3Run S (seedBudget l F E c kclk coef A a ha n) (symReq n a' ha' Cs carriers translation).word
        (symTape (callInputs l F kclk coef A a ha) hs Cs carriers)
        (seedWord (callInputs l F kclk coef A a ha) (gate0 l F).alg (symReq n a' ha' Cs carriers translation))

/-- **The HASH stage at one call family** (`C4At.hash`, `hash_run` at `E`, `c`). -/
def HashAt : Type :=
  Σ' S : Stage3, ∀ (n a' : ℕ) (ha' : a' ≤ 4) (Cs : Fin a' → NormalizedThresholdThresholdCircuit n)
    (carriers : List (Carrier n)) (translation : List ℕ),
    (callInputs l F kclk coef A a ha).Call (thrReq n a' ha' Cs carriers translation) →
    ∀ hs : (callInputs l F kclk coef A a ha).StarAt n,
      Stage3Run S (seedBudget l F E c kclk coef A a ha n) (thrReq n a' ha' Cs carriers translation).word
        (hashTape (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers)
        (frame (thrIn l F kclk coef A a ha n a' ha' Cs carriers translation hs))

/-- **The THR stage at one call family** (`C4At.thr`, `thr_run` at `E`, `c`). -/
def ThrAt : Type :=
  Σ' S : Stage3, ∀ (n a' : ℕ) (ha' : a' ≤ 4) (Cs : Fin a' → NormalizedThresholdThresholdCircuit n)
    (carriers : List (Carrier n)) (translation : List ℕ),
    (callInputs l F kclk coef A a ha).Call (thrReq n a' ha' Cs carriers translation) →
    ∀ hs : (callInputs l F kclk coef A a ha).StarAt n,
      Stage3Run S (seedBudget l F E c kclk coef A a ha n) (thrIn l F kclk coef A a ha n a' ha' Cs carriers translation hs)
        (thrTape (gate0 l F).alg (callInputs l F kclk coef A a ha) hs Cs carriers translation)
        (seedWord (callInputs l F kclk coef A a ha) (gate0 l F).alg (thrReq n a' ha' Cs carriers translation))

end At

/-- **A mode's deliverable in `C4Leaf`'s order of choice**: after the endpoint exponent `fe`, the floors `E`, `CD`;
for every admissible `F` above both, a coefficient `c` and the mode's stage at every clock and source work. -/
def ModeLeaf (l : Literals)
    (P : ∀ (_F : GateFree l) (_E : Envelope) (_c kclk _coef _A a : ℕ), a ≤ kclk + 1 → Type) : Type :=
  ∀ fe : ℕ, Σ E : Envelope, Σ CD : ℕ, ∀ F : GateFree l, F.filterErrDeg = fe → ClassLE E F.E → CD ≤ F.CD →
    Σ c : ℕ, ∀ (kclk coef A a : ℕ) (ha : a ≤ kclk + 1), P F E c kclk coef A a ha

/-- **The SYM part**. -/
abbrev SymLeafC4 (l : Literals) : Type := ModeLeaf l (SymAt l)

/-- **The HASH part** (setup, child family, stage T). -/
abbrev HashLeafC4 (l : Literals) : Type := ModeLeaf l (HashAt l)

/-- **The THR part**. -/
abbrev ThrLeafC4 (l : Literals) : Type := ModeLeaf l (ThrAt l)

end NearCubicWires.WireExponent3_5.PrimT.C4K
