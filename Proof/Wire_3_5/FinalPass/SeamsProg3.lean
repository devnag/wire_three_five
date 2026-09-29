import Proof.Wire_3_5.FinalPass.SeamsWS
import Proof.Wire_3_5.Primitive.Writers.S5SeamB2

/-! # S4's words, v3: the filter's parameters carried to the seeds phase

The seeds phase rebuilds each filter seed's table (`tableWord (filterTable FP e L)`, P3:2036-2101); its builders need
the call's filter parameters `FP.len`, `FP.cap`, `FP.errExp` (C6's FILTER setup reads them, C5's builder needs
`prefixBits = ⌈log₂(32·cap)⌉`), which the `s4Small` does not carry. They are the call's filter parameters
(P3:2206-2211), so this is a transfer: `s4Small2 = s4Small ++ [FP.len, FP.cap, FP.errExp]`.

* `s4Small2`, `s4Core2` (slot `7` the new list), **`frontWordsOfW2`** / `frontWordsW2` (= `frontWordsW` but slot `7`),
  **`frontWordsW2_agree`** (every other slot agrees; in particular the THR half's slots `8 … 15`, `thr_agree`, so
  `S5ThrB2` is unchanged);
* **`SeedsProg3`** (`SeedsProg2` at `frontWordsW2`), `SeedsProg3.cost_le`; **`SdEntry2`**, **`SeedsWS2`** (S4's
  machine-level seam at `frontWordsW2`);
* **`S5Core3`** (`S5Core2` with its exit at `frontWordsW2`, entry the THR half's exit `ThrExit2`), **`S5CoreB3`** (its
  cost within `s5Bound` and the width bound `W r ≤ Cw·(|fpIn|+1)^{Dw}`).

Paper quantities: the front's words (S4's words with the filter's parameters), the printed numerator and denominator
(P3:3044-3048), the front's and seeds phase's running times. -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.FinalPass.Seams
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.SupplierPipeline
open NearCubicWires.SupplierPrime NearCubicWires.WireExponent3_5.Shared NearCubicWires.WireExponent3_5.Stars
open NearCubicWires.WireExponent3_5.Filters NearCubicWires.WireExponent3_5.Lists NearCubicWires.WireExponent3_5.Primitive
open NearCubicWires.WireExponent3_5.Cost NearCubicWires.WireExponent3_5.FinalPass
open NearCubicWires.WireExponent3_5.FinalPass.PlanFP NearCubicWires.WireExponent3_5.FinalPass.NumDen
open NearCubicWires.WireExponent3_5.PrimAsm.Plan NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimAsm.S5Seam
open NearCubicWires.RepairOrdinary.SignedSortKey (binary)
open NearCubicWires.BlockPlatform NearCubicWires.ExtDecompositionBatch NearCubicWires.WireExponent3_5.Split
open NearCubicWires.SupplierWalk (majorityThreshold)

/-! ## The words -/

/-- **S4's small numbers, v2**: `s4Small`, then the filter's parameters `len`, `cap`, `errExp`. -/
def s4Small2 (P : StarParams) {n : ℕ} (carriers : List (Carrier n)) (FP : GapParams) : List ℕ :=
  s4Small P carriers FP ++ [FP.len, FP.cap, FP.errExp]

/-- **S4's own words, v2**: `s4Core` with slot `7` the numbers `s4Small2`. -/
def s4Core2 (P : StarParams) (σ : P.Translation) (smp : CallSample P) (carriers : List (Carrier P.n))
    (FP : GapParams) (i : Fin 8) : List Bool :=
  if i.val = 7 then PrimAsm.Data.unaryList (s4Small2 P carriers FP) else s4Core P σ smp carriers FP i

section Req
variable {kc : ℕ} {E : Envelope} {B : TimeBudget kc E} (I : PrimitiveInputs B)
  (alg : RepairRepresentation.DecompositionAlgorithm) (Sw : SymWords)

/-- **The front's words at a request, v3**: `frontWordsOfW` with S4's words `s4Core2`. -/
def frontWordsOfW2 : PrimRequest → Fin (17 + Sw.nw) → List Bool
  | ⟨n, .sym, a, ha, Cs, carriers, translation⟩ => fun i =>
      if hs : I.StarAt n then
        if h8 : i.val < 8 then
          s4Core2 (I.starParams n hs) ((I.starParams n hs).translationOfCodes translation)
            ((SeedFix.greedySampler I alg).symS Cs carriers translation hs) carriers (I.filterParams .sym n) ⟨i.val, h8⟩
        else if i.val < 16 then []
        else if h : i.val - 16 < Sw.nw then Sw.words (symCallOf I hs ha Cs carriers) ⟨i.val - 16, h⟩
        else PrimAsm.Data.unaryList (List.ofFn (Sw.nums (symCallOf I hs ha Cs carriers)))
      else []
  | ⟨n, .thr, a, ha, Cs, carriers, translation⟩ => fun i =>
      if hs : I.StarAt n then
        if h8 : i.val < 8 then
          s4Core2 (I.starParams n hs) ((I.starParams n hs).translationOfCodes translation)
            ((SeedFix.greedySampler I alg).thrS Cs carriers translation hs) carriers (I.filterParams .thr n) ⟨i.val, h8⟩
        else if h15 : i.val < 15 then thrWords (thrCallOf I alg hs ha Cs carriers translation) ⟨i.val - 8, by omega⟩
        else if i.val = 15 then
          PrimAsm.Data.unaryList (List.ofFn (thrNums (thrCallOf I alg hs ha Cs carriers translation)))
        else []
      else []

theorem s4Core2_agree (P : StarParams) (σ : P.Translation) (smp : CallSample P) (carriers : List (Carrier P.n))
    (FP : GapParams) (i : Fin 8) (hi : i.val ≠ 7) : s4Core2 P σ smp carriers FP i = s4Core P σ smp carriers FP i :=
  if_neg hi

/-- **Every slot but `7` agrees with `frontWordsOfW`.** -/
theorem frontWordsOfW2_agree (req : PrimRequest) (i : Fin (17 + Sw.nw)) (hi : i.val ≠ 7) :
    frontWordsOfW2 I alg Sw req i = frontWordsOfW I alg Sw req i := by
  obtain ⟨n, mode, a, ha, Cs, carriers, translation⟩ := req
  cases mode <;> simp only [frontWordsOfW2, frontWordsOfW] <;> split_ifs <;> first | rfl |
    exact s4Core2_agree _ _ _ _ _ _ (by simpa using hi)

end Req

section Family
variable (l : Literals) (F : GateFree l) (kclk coef A a : ℕ) (ha : a ≤ kclk + 1) (Sw : SymWords)

/-- The front's words at a request of the family, v3. -/
noncomputable abbrev frontWordsW2 (r : FReq l F kclk coef A a ha) : Fin (17 + Sw.nw) → List Bool :=
  frontWordsOfW2 (callInputs l F kclk coef A a ha) (gate0 l F).alg Sw r.1

theorem frontWordsW2_agree (r : FReq l F kclk coef A a ha) (k : Fin (17 + Sw.nw)) (hk : k.val ≠ 7) :
    frontWordsW2 l F kclk coef A a ha Sw r k = frontWordsW l F kclk coef A a ha Sw r k :=
  frontWordsOfW2_agree _ _ Sw r.1 k hk

/-- **The THR half's slots agree** (so `S5ThrB2` is unchanged). -/
theorem thr_agree (r : FReq l F kclk coef A a ha) (k : Fin (17 + Sw.nw)) (hk : thrSlot k) :
    frontWordsW2 l F kclk coef A a ha Sw r k = frontWordsW l F kclk coef A a ha Sw r k :=
  frontWordsW2_agree l F kclk coef A a ha Sw r k (by have := hk.1; omega)

variable {Sw}

/-- **The internal entry, v2** (at `frontWordsW2`). -/
structure SdEntry2 (L : SdLay Sw) (r : FReq l F kclk coef A a ha) (W : ℕ) (σ : WState L.ns L.nr) : Prop where
  words : ∀ k, σ.st (L.wdS k) = frontWordsW2 l F kclk coef A a ha Sw r k
  num : σ.st L.sN = frame (binary W 0)
  den : σ.st L.sD = frame (binary W (fpDen l F kclk coef A a ha r))
  blank : ∀ i, (∀ k, i ≠ L.wdS k) → i ≠ L.sN → i ≠ L.sD → σ.st i = []
  heads : ∀ i, σ.sh i = 0
  regs : ∀ q, σ.val q = 0
  cell : σ.cell = false

variable (Sw)

/-- **S4 at the machine level, v2** (BridgeT's input at `frontWordsW2`). -/
structure SeedsWS2 where
  L : SdLay Sw
  s : ℕ
  M : Machine (L.ns + 2 + L.nr) s
  Kc : ℕ
  Dc : ℕ
  tab : FReq l F kclk coef A a ha → ℕ
  pt : FReq l F kclk coef A a ha → ℕ
  ov : FReq l F kclk coef A a ha → ℕ
  Cp : ℕ
  Dp : ℕ
  Ct : ℕ
  Dt : ℕ
  Co : ℕ
  Do : ℕ
  pt_le : ∀ r : FReq l F kclk coef A a ha, pt r ≤ Cp * (r.1.n + 1) ^ Dp
  tab_le : ∀ r, tab r ≤ PrimAsm.S5Seam.s5Bound l F kclk coef A a ha Ct Dt r
  ov_le : ∀ r, ov r ≤ PrimAsm.S5Seam.s5Bound l F kclk coef A a ha Co Do r
  run : ∀ (r : FReq l F kclk coef A a ha) (W : ℕ), ptCount l F kclk coef A a ha r * vmax l F kclk coef A a ha r < 2 ^ W →
    ∀ σ : WState L.ns L.nr, SdEntry2 l F kclk coef A a ha L r W σ →
    ∃ τ : WState L.ns L.nr,
      Step M (seedsShape (seedCount l F kclk coef A a ha r) (tab r) (ptCount l F kclk coef A a ha r) (pt r) (ov r))
        (wenc (Kc * ((fpIn l F kclk coef A a ha r).length + 1) ^ Dc) σ).H
        (wenc (Kc * ((fpIn l F kclk coef A a ha r).length + 1) ^ Dc) σ).A
        (wenc (Kc * ((fpIn l F kclk coef A a ha r).length + 1) ^ Dc) τ).H
        (wenc (Kc * ((fpIn l F kclk coef A a ha r).length + 1) ^ Dc) τ).A ∧
      τ.st L.sN = frame (binary W (fpNum l F kclk coef A a ha r)) ∧
      τ.st L.sD = frame (binary W (fpDen l F kclk coef A a ha r)) ∧
      (∀ i, τ.sh i = 0) ∧ (∀ q, τ.val q = 0) ∧ fpNum l F kclk coef A a ha r < 2 ^ W

/-- **The core half, v3**: `S5Core2` with its exit at `frontWordsW2` (from the THR half's exit `ThrExit2`). -/
structure S5Core3 (L : S5Lay Sw.nw) where
  s : ℕ
  M : Machine L.t s
  cost : FReq l F kclk coef A a ha → ℕ
  W : FReq l F kclk coef A a ha → ℕ
  hW : ∀ r, ptCount l F kclk coef A a ha r * vmax l F kclk coef A a ha r < 2 ^ W r
  exitA : FReq l F kclk coef A a ha → Fin L.t → List Bool
  run : ∀ (r : FReq l F kclk coef A a ha) (Ab : Fin L.t → List Bool), ThrExit2 l F kclk coef A a ha Sw L r Ab →
    Step M (cost r) (fun _ => 0) Ab (fun _ => 0) (exitA r)
  out : FrontOut l F kclk coef A a ha L.wd ![L.tN, L.tD] (frontWordsW2 l F kclk coef A a ha Sw)
    (fun r => ![0, fpDen l F kclk coef A a ha r]) W (fun r j => blOf2 L r j) (fun _ _ => 0) exitA

/-- **The core half with its bounds, v3** (the target): the cost within `s5Bound`, the width `W`
polynomial in the input. -/
structure S5CoreB3 (L : S5Lay Sw.nw) extends S5Core3 l F kclk coef A a ha Sw L where
  Cc : ℕ
  Dcc : ℕ
  cost_le : ∀ r, cost r ≤ s5Bound l F kclk coef A a ha Cc Dcc r
  Cw : ℕ
  Dw : ℕ
  W_le : ∀ r, W r ≤ Cw * ((fpIn l F kclk coef A a ha r).length + 1) ^ Dw

end Family

end NearCubicWires.WireExponent3_5.FinalPass.Seams
