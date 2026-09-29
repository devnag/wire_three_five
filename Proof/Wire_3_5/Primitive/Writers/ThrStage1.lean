import Proof.Wire_3_5.Primitive.Writers.ThrFin5
import Proof.Wire_3_5.Primitive.Writers.ThrSet4

/-! # c4 THR block, the THR stage on the big bank (`thrLay_run`)

The C4 wrapper (`C4Wrap.wrapM`, `wrap_run`) on the big bank `3 + thrXb L x3`, for any setup
machine `M0`. The setup's exit bank carries the SYM-shaped bank (`C4SymW.SymBank`) on the layout, the marked hash bits
on `hbT` and a blank finisher region. The decision loop of a child family of the shape (`ChShape`) is docked by `symExt` (lifted, `entry_lift` of `sym_entry`), and the THR finisher `finM` by `extF` (`thr_fin`). The stage ends
with `sampleWord kh (seedPairs P s) ++ hbF` on port `2` (**`thrLay_run`**).

Paper quantity of the main type: the THR stage's output, the fixed seed's samples then the hash bits (P3:2932-2937,
3034-3038, 2331-2333). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.style.longLine false

namespace NearCubicWires.WireExponent3_5.PrimAsm.ThrSet
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.BlockPlatform
open NearCubicWires.RepairOrdinary.Streaming (marks)
open NearCubicWires.WireExponent3_5.PrimT NearCubicWires.WireExponent3_5.PrimT.C4Set
open NearCubicWires.WireExponent3_5.PrimAsm.BigBank
open NearCubicWires.RepairOrdinary.SignedSortKey (binary)

variable (L : Lay) (x3 : ℕ) (F : C4Loop.ChildFam) (pd : ℕ) (P : Sampler.SeedParams)
  (ents : List (List SeedFix.SExpr)) (TWd Cap nT : ℕ) (pre post : List Bool) (q uu : ℕ) (ρ : ℕ) (v w : List Bool)
  (Q kh ell cnt d2 : ℕ) (fr dd : Fin 7 → ℕ)

theorem hoffLb (hT : F.T + 1 + 1 + 1 ≤ L.T) : L.oLP + (F.T + 1 + 1 + 1) ≤ 3 + thrXb L x3 := by
  have := C4SymW.hoffL L F hT; have := hxb L x3; omega

/-- **The THR stage on the big bank.** -/
theorem thrLay_run {s0 c0 : ℕ} (M0 : Machine (3 + thrXb L x3) s0) (B' : Fin (3 + thrXb L x3) → List Bool)
    (h0 : Step M0 c0 (fun _ => 0) (SeedFixTypes.stageIn (thrXb L x3) w v) (fun _ => 0) B')
    (hS : C4SymW.ChShape F pd P ents TWd Cap nT pre post q uu)
    (hB : C4SymW.SymBank L pd P ents TWd Cap nT pre post q uu (fun i => B' (liftE (hxb L x3) i)) ρ v Q kh ell cnt d2
      fr dd)
    (hP0 : B' (liftE (hxb L x3) L.gP0) = frame w) (hP2 : B' (liftE (hxb L x3) L.gP2) = [])
    (hMB : B' (liftE (hxb L x3) L.gMB) = frame (binary ell (GF.firstPrimitive ell)))
    (hbl : ∀ i : Fin L.N, L.oLP + L.T ≤ i.val → B' (liftE (hxb L x3) i) = [])
    (hbF : List Bool) (hhb : B' (hbT L x3) = marks hbF)
    (hbl2 : ∀ i : Fin (3 + thrXb L x3), offT L x3 ≤ i.val → B' i = [])
    (hT : F.T + 1 + 1 + 1 ≤ L.T) (htS : 31 ≤ L.tS) (hR : F.cellCost + 1 ≤ 2 ^ ρ) (hkh : 1 ≤ P.kh)
    (s : Fin (8 * P.ell) → Bool) (hG : SeedFix.greedyLoop F.bound F.Rv = List.ofFn s)
    (Bd : ℕ) (hBd : C4Wrap.wrapCost c0 F (2 ^ ρ) (ThrFin.finCost P s hbF) + 1 ≤ Bd) :
    SeedFixTypes.Stage3Run ⟨thrXb L x3, _, C4Wrap.wrapM M0 F L.oLP (hoffLb L x3 F hT)
        (liftX (hxb L x3) (C4SymW.symExt L pd)) ThrFin.finM (offT L x3) (hoffT L x3)
        (ThrFin.extF L (hxb L x3) (hbT L x3))⟩ Bd w v
      (FinalPass.Sample.sampleWord P.kh (C4Iface.seedPairs P s) ++ hbF) := by
  have hE0 := C4SymW.sym_entry L F pd P ents TWd Cap nT pre post q uu (fun i => B' (liftE (hxb L x3) i)) ρ v w Q kh
    ell cnt d2 fr dd hS hB hP0 hP2 hT hR
  have hE := entry_lift (hxb L x3) F (2 ^ ρ) (2 ^ ρ + 1) L.oLP (C4SymW.hoffL L F hT) (hoffLb L x3 F hT)
    (C4SymW.symExt L pd) w v _ B' (fun i => rfl) hE0
  obtain ⟨tout, hf, h6⟩ := ThrFin.finM_step P s hbF hkh
  have hD := ThrFin.thr_fin L (hxb L x3) F pd P ents TWd Cap nT pre post q uu (fun i => B' (liftE (hxb L x3) i)) ρ v
    Q kh ell cnt d2 fr dd hS hB hP2 hMB hbl hT htS s hG (hoffLb L x3 F hT) B' (fun i => rfl) hbF (hbT L x3)
    (by unfold hbT offH; simp; omega) hhb (offT L x3) (by unfold hbT offT; simp; have : BX = 676 := rfl; omega) (hoffT L x3) hbl2
  have r := C4Wrap.wrap_run M0 w v B' h0 F (2 ^ ρ) (2 ^ ρ + 1) L.oLP (hoffLb L x3 F hT)
    (liftX (hxb L x3) (C4SymW.symExt L pd)) hE ThrFin.finM (ThrFin.tinF P s hbF) tout hf (offT L x3) (hoffT L x3)
    (ThrFin.extF L (hxb L x3) (hbT L x3)) 6 hD Bd hBd
  rw [h6] at r
  exact r

end NearCubicWires.WireExponent3_5.PrimAsm.ThrSet
