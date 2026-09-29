import Proof.Wire_3_5.FinalPass.CoreIfaceM

/-! # The core half's word writers with arbitrary residues (P3:3044-3048, 3170-3181)

S5Core uses a writer's residues only through their lengths (every register tape is padded to `0^{c+1}` at the end),
so the writers' contract drops the zero residues of `CoreWordsM` / `SymWordsM`: every other stream holds ANY word of
length within the step bound. A writer built on raw donors (the data stage, the carrier tables, the walk and build
stages) then needs no zeroing pass.

* **`CoreWordsMJ l m ws`**, **`SymWordsMJ l`** (`CoreWordsM` / `SymWordsM` with the residues' lengths only);
* **`CoreWordsM.toMJ`**, **`SymWordsM.toMJ`** (zeros are residues);
* **`S4WordsMAJ l`**, **`S4WordsMBJ l`**, **`NumsMJ l`** (the restatements over `CoreWordsMJ`).

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

/-- **A core word writer as a machine per gate, residues of bounded length.** -/
structure CoreWordsMJ (l : Literals) (m : ℕ)
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
          (τ.st i).length ≤ Cs F * ((fpIn l F kclk coef A a ha r).length + 1) ^ Ds F.filterErrDeg) ∧
        (∀ i, τ.sh i = 0) ∧ (∀ q, τ.val q = 0)

/-- **The SYM words writer as a machine per gate, residues of bounded length.** -/
structure SymWordsMJ (l : Literals) where
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
          (τ.st i).length ≤ Cs F * ((fpIn l F kclk coef A a ha r).length + 1) ^ Ds F.filterErrDeg) ∧
        (∀ i, τ.sh i = 0) ∧ (∀ q, τ.val q = 0)

/-- **Zero residues are residues.** -/
def CoreWordsM.toMJ {l : Literals} {m : ℕ}
    {ws : ∀ (F : GateFree l) (kclk coef A a : ℕ) (ha : a ≤ kclk + 1), FReq l F kclk coef A a ha → Fin m → List Bool}
    (Wr : CoreWordsM l m ws) : CoreWordsMJ l m ws where
  ns := Wr.ns
  nr := Wr.nr
  s := Wr.s
  M := Wr.M
  sIn := Wr.sIn
  sOut := Wr.sOut
  out_ne := Wr.out_ne
  Kc := Wr.Kc
  Dk := Wr.Dk
  Cs := Wr.Cs
  Ds := Wr.Ds
  run := fun F kclk coef A a ha r σ hin hsh hbl hv hc => by
    obtain ⟨τ, n, hn, hs, hout, hkeep, hres, hτs, hτv⟩ := Wr.run F kclk coef A a ha r σ hin hsh hbl hv hc
    refine ⟨τ, n, hn, hs, hout, hkeep, fun i h1 h2 => ?_, hτs, hτv⟩
    obtain ⟨ℓ, hℓ, he⟩ := hres i h1 h2
    rw [he, List.length_replicate]; exact hℓ

/-- **S4's words, part A, residues of bounded length.** -/
abbrev S4WordsMAJ (l : Literals) : Type :=
  CoreWordsMJ l 4 fun F kclk coef A a ha r k => frontWordsW2 l F kclk coef A a ha Sw0 r (s4SlotA k)

/-- **S4's words, part B, residues of bounded length.** -/
abbrev S4WordsMBJ (l : Literals) : Type :=
  CoreWordsMJ l 4 fun F kclk coef A a ha r k => frontWordsW2 l F kclk coef A a ha Sw0 r (s4SlotB k)

/-- **The numbers S4 starts from, residues of bounded length.** -/
abbrev NumsMJ (l : Literals) : Type :=
  CoreWordsMJ l 2 fun F kclk coef A a ha r i =>
    frame (binary (Sd.R.Tf l F kclk coef A a ha r) ((![0, fpDen l F kclk coef A a ha r] : Fin 2 → ℕ) i))

end NearCubicWires.WireExponent3_5.FinalPass.Finish
