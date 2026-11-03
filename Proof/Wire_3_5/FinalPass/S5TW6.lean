import Proof.Wire_3_5.FinalPass.S5TP0Base
import Proof.Wire_3_5.Primitive.SeedFix.W6ZI

/-! # S5-THR, part 8: the THR numbers machine W6 docked (P3:2543-2558, 2596-2604, 2150-2157, 2220-2231)

The numbers machine `numsW6 alg Dexp` (`NumsPort4`) docked on the THR half's layout by `w6Map`: port `0` on the input
(`frame (reqW …)`), ports `1`, `2`, `20` on the prep's outputs `1^{|carriers|}`, `1^{cap_T}`, `1^V`, port `17` (the
primes up to the cutoff) on slot `13`, the rest on its block. Its out-ports: the fourteen THR numbers in unary on
`3 … 16`, the primes on `17`, the level records on `18`, the modulus word on `19`.

* `w6_in` (W6's entry bank read off the layout); **`w6_dock`** (the docked run, its out-ports, its scratch bound).

Paper quantities of the main type: the THR call's numbers (`thrNumVals`), the primes, the level records, the
modulus. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false

namespace NearCubicWires.WireExponent3_5.FinalPass.S5T
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimAsm.DockW (dockS updS)
open NearCubicWires.WireExponent3_5.PrimThrW.Nums3 (nums3InPorts nums3OutPorts)
open NearCubicWires.SupplierPipeline

variable (D x6 xt : ℕ) (cap : ℕ)

theorem w6_in (σ : WState (nsL D x6 xt) nrL) (w : List Bool) (ncar capT V : ℕ)
    (hIn : σ.st (w6Map D x6 xt ⟨0, by omega⟩) = frame w)
    (h1 : σ.st (w6Map D x6 xt ⟨1, by omega⟩) = List.replicate ncar true)
    (h2 : σ.st (w6Map D x6 xt ⟨2, by omega⟩) = List.replicate capT true)
    (h20 : σ.st (w6Map D x6 xt ⟨20, by omega⟩) = List.replicate V true)
    (hblk : ∀ j : Fin (21 + x6), j.val ≠ 0 → j.val ≠ 1 → j.val ≠ 2 → j.val ≠ 20 → σ.st (w6Map D x6 xt j) = []) :
    (fun j : Fin (21 + x6) => σ.st (w6Map D x6 xt j)) =
      Fin.addCases (m := 21) (n := x6) (motive := fun _ => List Bool) (nums3InPorts w ncar capT V) (fun _ => []) := by
  funext j
  refine Fin.addCases (fun i => ?_) (fun k => ?_) j
  · rw [Fin.addCases_left]
    unfold nums3InPorts PrimThrW.NumsP.numsInPorts
    have hi := i.isLt
    by_cases a0 : i.val = 0
    · have : (Fin.castAdd x6 i : Fin (21 + x6)) = ⟨0, by omega⟩ := Fin.ext a0
      rw [this, hIn]; simp [a0]
    by_cases a1 : i.val = 1
    · have : (Fin.castAdd x6 i : Fin (21 + x6)) = ⟨1, by omega⟩ := Fin.ext a1
      rw [this, h1]; simp [a1]
    by_cases a2 : i.val = 2
    · have : (Fin.castAdd x6 i : Fin (21 + x6)) = ⟨2, by omega⟩ := Fin.ext a2
      rw [this, h2]; simp [a2]
    by_cases a20 : i.val = 20
    · have : (Fin.castAdd x6 i : Fin (21 + x6)) = ⟨20, by omega⟩ := Fin.ext a20
      rw [this, h20]; simp [a20]
    rw [hblk _ (by simpa using a0) (by simpa using a1) (by simpa using a2) (by simpa using a20)]
    simp [a0, a1, a2, show i.val < 20 by omega]
  · rw [Fin.addCases_right]
    exact hblk _ (by simp) (by simp; omega) (by simp; omega) (by simp; omega)

theorem w6_dock (alg : RepairRepresentation.DecompositionAlgorithm) (Dexp : ℕ)
    (σ : WState (nsL D (PrimT.W6.numsW6 alg Dexp).x xt) nrL) (P : Shared.StarParams) {a' : ℕ}
    (Cs : Fin a' → NormalizedThresholdThresholdCircuit P.n) (codes : List ℕ) (tl : List Bool) (ncar capT V : ℕ)
    (hIn : σ.st (w6Map D _ xt ⟨0, by omega⟩) = frame (PrimAsm.Data.reqW P.n true (PrimAsm.ReqBridge.thrCodes Cs) codes tl))
    (h1 : σ.st (w6Map D _ xt ⟨1, by omega⟩) = List.replicate ncar true)
    (h2 : σ.st (w6Map D _ xt ⟨2, by omega⟩) = List.replicate capT true)
    (h20 : σ.st (w6Map D _ xt ⟨20, by omega⟩) = List.replicate V true)
    (hblk : ∀ j : Fin (21 + (PrimT.W6.numsW6 alg Dexp).x), j.val ≠ 0 → j.val ≠ 1 → j.val ≠ 2 → j.val ≠ 20 →
      σ.st (w6Map D _ xt j) = [])
    (hsh : ∀ i, σ.sh i = 0) (hn : 1 ≤ P.n) (ha : a' ≤ 4) (hd : ∀ i, (Cs i).descriptionBits ≤ (P.n + 1) ^ 26)
    (hnc : ncar ≤ 2) (hcap : 1 ≤ capT) (hok : PrimThrW.TopFront2.TF2Ok Cs codes V)
    (hneed : (PrimT.W6.numsW6 alg Dexp).need (P.n + capT) ≤ V) :
    ∃ J : Fin (PrimT.W6.numsW6 alg Dexp).x → List Bool,
      (∀ j, (J j).length ≤ (PrimT.W6.numsW6 alg Dexp).cost (P.n + V + capT)) ∧
      Step (RecoveryFocus.machine (fun j => sTape (nr := nrL) (w6Map D _ xt j)) (PrimT.W6.numsW6 alg Dexp).M)
        ((PrimT.W6.numsW6 alg Dexp).cost (P.n + V + capT)) (wenc cap σ).H (wenc cap σ).A
        (wenc cap (updS (w6Map D _ xt) σ (fun _ => 0) (Fin.addCases (m := 21) (n := (PrimT.W6.numsW6 alg Dexp).x)
          (motive := fun _ => List Bool) (nums3OutPorts (PrimAsm.Data.reqW P.n true (PrimAsm.ReqBridge.thrCodes Cs)
            codes tl) ncar capT V (PrimThrW.Joins.thrNumVals P Cs alg Dexp ncar capT)) J))).H
        (wenc cap (updS (w6Map D _ xt) σ (fun _ => 0) (Fin.addCases (m := 21) (n := (PrimT.W6.numsW6 alg Dexp).x)
          (motive := fun _ => List Bool) (nums3OutPorts (PrimAsm.Data.reqW P.n true (PrimAsm.ReqBridge.thrCodes Cs)
            codes tl) ncar capT V (PrimThrW.Joins.thrNumVals P Cs alg Dexp ncar capT)) J))).A := by
  obtain ⟨J, hJ, hs⟩ := (PrimT.W6.numsW6 alg Dexp).run P Cs codes tl ncar capT V hn ha hd hnc hcap hok hneed
  refine ⟨J, hJ, dockS cap (w6Map D _ xt) (w6Map_inj D _ xt) σ ?_⟩
  refine hs.congr_in ?_ ?_
  · funext j; exact (hsh _).symm
  · exact (w6_in D _ xt σ _ ncar capT V hIn h1 h2 h20 hblk).symm

end NearCubicWires.WireExponent3_5.FinalPass.S5T
