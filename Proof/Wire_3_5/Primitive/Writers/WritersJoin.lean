import Lean
import Proof.Wire_3_5.Primitive.Writers.PreLink
import Proof.Wire_3_5.Primitive.Writers.ComposeEnvBase
import Statement_Wire_3_5
import Proof.Wire_3_5.Assembly.Gate0
import Proof.Wire_3_5.Primitive.Writers.Plan
import Proof.Wire_3_5.Primitive.Writers.WriterIfaceJ
import Proof.Wire_3_5.Assembly.Split
import Proof.Wire_3_5.Primitive.Writers.WritersJoinBase


noncomputable section
set_option maxRecDepth 4096


/-! # The writers' join: three separately built writers give the writer node's target

The writer node's target `PreLink.WriterLeafJ2` bundles the SYM, THR and HASH writers (`WritersAtJ`) at ONE floor
envelope `E_W`, one load-constant floor `CD_W` and one coefficient `c_W`. The three writers are built separately, each
with its own floors and coefficient. This file fixes each writer's type and proves the join:

* **`SymLeafJ2`**, **`ThrLeafJ2`**, **`HashLeafJ2`**: one writer each, in `WriterLeafJ2`'s order of choice (`fe`, then
  `E_W`, `CD_W`, then `F`, then `c_W`);
* `writerRun_mono`: a writer's run within `B` steps is a run within any `B' ≥ B`;
* `symMono`, `thrMono`, `hashMono`: a writer within `c_W · classBound E_W` is within
  `c_W' · classBound E_W'` for `E_W ≤ E_W'` and `c_W ≤ c_W'` (every call length has `n ≥ 8` from `StarAt`);
* **`writerLeafJ2_of`**: `SymLeafJ2 l → ThrLeafJ2 l → HashLeafJ2 l → WriterLeafJ2 l`, with the floors
  `envMax (envMax E_S E_T) E_H` and `max (max CD_S CD_T) CD_H` and the coefficient `max (max c_S c_T) c_H`.

Paper quantity of the main types: the preprocessing class `2^{O(Ψ)}q^{O(1)}` (P3:3108, 3112-3114) of each batch
writer's tape (`symTape`, `thrTape`, `hashTape`). -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.PrimAsm.WritersJoin
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.Cost NearCubicWires.WireExponent3_5.Split NearCubicWires.WireExponent3_5.Primitive
open NearCubicWires.WireExponent3_5.PrimAsm.Plan NearCubicWires.WireExponent3_5.PrimAsm.WriterIface
open NearCubicWires.WireExponent3_5.PrimAsm.WriterIfaceJ NearCubicWires.WireExponent3_5.PrimAsm.PreLink
open NearCubicWires.WireExponent3_5.PrimAsm.ComposeEnv

/-! ## Monotonicity -/

section Mono
variable {l : Literals} {F : GateFree l} {EW EW' : Envelope} {cW cW' kclk coef A a : ℕ} {ha : a ≤ kclk + 1}

/-- The SYM writer within a larger budget. -/
def symMono (W : SymWriterAtJ l F EW cW kclk coef A a ha) (h : ClassLE EW EW') (hc : cW ≤ cW') :
    SymWriterAtJ l F EW' cW' kclk coef A a ha :=
  { W.toWriterStage with
    ready := fun n a' ha' Cs c tr hcall hs =>
      writerRun_mono (W.ready n a' ha' Cs c tr hcall hs) (budget_mono h hc (one_le_of_starAt hs) _ _) }

/-- The THR writer within a larger budget. -/
def thrMono (W : ThrWriterAtJ l F EW cW kclk coef A a ha) (h : ClassLE EW EW') (hc : cW ≤ cW') :
    ThrWriterAtJ l F EW' cW' kclk coef A a ha :=
  { W.toWriterStage with
    ready := fun n a' ha' Cs c tr hcall hs =>
      writerRun_mono (W.ready n a' ha' Cs c tr hcall hs) (budget_mono h hc (one_le_of_starAt hs) _ _) }

/-- The HASH writer within a larger budget. -/
def hashMono (W : HashWriterAtJ l F EW cW kclk coef A a ha) (h : ClassLE EW EW') (hc : cW ≤ cW') :
    HashWriterAtJ l F EW' cW' kclk coef A a ha :=
  { W.toWriterStage with
    ready := fun n a' ha' Cs c tr hcall hs =>
      writerRun_mono (W.ready n a' ha' Cs c tr hcall hs) (budget_mono h hc (one_le_of_starAt hs) _ _) }

end Mono

/-! ## Each writer's type -/

/-- **The SYM writer's deliverable**, in `WriterLeafJ2`'s order of choice. -/
def SymLeafJ2 (l : Literals) : Type :=
  ∀ fe : ℕ, Σ EW : Envelope, Σ CDW : ℕ, ∀ F : GateFree l, F.filterErrDeg = fe → ClassLE EW F.E → CDW ≤ F.CD →
    Σ cW : ℕ, ∀ (kclk coef A a : ℕ) (ha : a ≤ kclk + 1), SymWriterAtJ l F EW cW kclk coef A a ha

/-- **The THR writer's deliverable**, in `WriterLeafJ2`'s order of choice. -/
def ThrLeafJ2 (l : Literals) : Type :=
  ∀ fe : ℕ, Σ EW : Envelope, Σ CDW : ℕ, ∀ F : GateFree l, F.filterErrDeg = fe → ClassLE EW F.E → CDW ≤ F.CD →
    Σ cW : ℕ, ∀ (kclk coef A a : ℕ) (ha : a ≤ kclk + 1), ThrWriterAtJ l F EW cW kclk coef A a ha

/-- **The HASH writer's deliverable**, in `WriterLeafJ2`'s order of choice. -/
def HashLeafJ2 (l : Literals) : Type :=
  ∀ fe : ℕ, Σ EW : Envelope, Σ CDW : ℕ, ∀ F : GateFree l, F.filterErrDeg = fe → ClassLE EW F.E → CDW ≤ F.CD →
    Σ cW : ℕ, ∀ (kclk coef A a : ℕ) (ha : a ≤ kclk + 1), HashWriterAtJ l F EW cW kclk coef A a ha

/-! ## The join -/

/-- **The writers' join**: three separately built writers give the writer node's target. -/
noncomputable def writerLeafJ2_of (l : Literals) (S : SymLeafJ2 l) (T : ThrLeafJ2 l) (H : HashLeafJ2 l) :
    WriterLeafJ2 l :=
  fun fe => ⟨envMax (envMax (S fe).1 (T fe).1) (H fe).1, max (max (S fe).2.1 (T fe).2.1) (H fe).2.1,
    fun F hF hE hCD =>
      let s := (S fe).2.2 F hF (classLE_trans (classLE_max3_1 _ _ _) hE) ((le_max3_1 _ _ _).trans hCD)
      let t := (T fe).2.2 F hF (classLE_trans (classLE_max3_2 _ _ _) hE) ((le_max3_2 _ _ _).trans hCD)
      let h := (H fe).2.2 F hF (classLE_trans (classLE_max3_3 _ _ _) hE) ((le_max3_3 _ _ _).trans hCD)
      ⟨max (max s.1 t.1) h.1, fun kclk coef A a ha =>
        { sym := symMono (s.2 kclk coef A a ha) (classLE_max3_1 _ _ _) (le_max3_1 _ _ _)
          thr := thrMono (t.2 kclk coef A a ha) (classLE_max3_2 _ _ _) (le_max3_2 _ _ _)
          hash := hashMono (h.2 kclk coef A a ha) (classLE_max3_3 _ _ _) (le_max3_3 _ _ _) }⟩⟩

end NearCubicWires.WireExponent3_5.PrimAsm.WritersJoin

end
