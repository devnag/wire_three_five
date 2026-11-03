import Proof.Wire_3_5.Primitive.Writers.DataRun
import Proof.Wire_3_5.Primitive.Writers.SymDecStreams

/-! # TopFrontPort3 body, part 1: the arity guard (`gW`, `g_spec`)

P3:3068 (lem:primitive): "Fix a polynomial description envelope, a tuple arity at most four, and an accuracy exponent
`D>0`." The front end (`PortsE.TopFrontPort3`) must cover the empty tuple `a' = 0`, where its count `V` may be as small
as `log n` (`TF2Ok` then bounds only `n`'s bit length), so nothing of size `n` may be written before the arity is
known. The request word is `natWord n ++ [mode] ++ natWord a' ++ …` (`Data.reqW`); the guard skips `n` (cost `O(log n)`),
skips the mode bit and reads `a'` into register `9` (a register neither the preparation nor PA's split uses); the TM
level then branches on register `9`.

* **`gW`**, `gCost`; **`g_spec`**: from the framed request at head `0` and zero registers, the request's head just
  past the arity field and `a'` in register `9`, nothing else changed.

Paper quantity of the main type: the tuple arity `a'` (read from the request word). -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.PrimThrW.TF3Guard
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimAsm
open NearCubicWires.WireExponent3_5.PrimAsm.Data

/-- **The arity guard**: skip `n`, skip the mode bit, read `a'` into register `9` (flags/scratch `2, 3, 6, 7`). -/
def gW : WM DS DR :=
  .seq (ParseNat.skipNatM true sIN 2 3) (.seq (.fwd sIN) (.seq (.fwd sIN) (ParseNat.readNatM true sIN 2 3 9 6 7)))

/-- The guard's cost. -/
def gCost (n a : ℕ) : ℕ :=
  20 * natBitLength n + 20 + 1 + (1 + 1 + (1 + 1 + (natBitLength a + 2) * (40 * 2 ^ natBitLength a + 40)))

/-- The request's head after the guard: past `n`'s field, the mode bit and `a'`'s field (framed marks). -/
def gPos (n a : ℕ) : ℕ :=
  2 * (RepairRepresentation.natWord n).length + 2 + 2 * (RepairRepresentation.natWord a).length

variable (cap : ℕ)

/-- **The guard's run.** -/
theorem g_spec (n : ℕ) (codes cc : List ℕ) (tl : List Bool) (σ : WState DS DR)
    (hIN : σ.st sIN = frame (reqW n true codes cc tl)) (hINh : σ.sh sIN = 0) (hz : ∀ r, σ.val r = 0)
    (hcN : natBitLength n + 1 ≤ cap) (hcA : 2 ^ (natBitLength codes.length + 1) ≤ cap) :
    WExec cap gW σ ((σ.seth sIN (gPos n codes.length)).setv 9 codes.length) (gCost n codes.length) := by
  have hIN' := hIN
  rw [enc_reqW] at hIN'
  set rest := ParseNat.enc true (RepairRepresentation.natWord codes.length) ++
    (ParseNat.enc true (codes.flatMap RepairRepresentation.natWord) ++
      (ParseNat.enc true (RepairRepresentation.natWord cc.length) ++
        (ParseNat.enc true (cc.flatMap RepairRepresentation.natWord) ++ (ParseNat.enc true tl ++ [false])))) with hrest
  have p1 := ParseNat.skipNatM_spec cap true sIN 2 3 (by decide) n [] (ParseNat.enc true [true] ++ rest) σ
    (by rw [hIN']; rfl) (by simp [hINh]) (hz 2) (hz 3) hcN
  set σ1 := σ.seth sIN ([].length + ParseNat.stp true * (RepairRepresentation.natWord n).length) with hσ1
  have p2 := WExec.fwd (cap := cap) sIN σ1
  have p3 := WExec.fwd (cap := cap) sIN (σ1.seth sIN (σ1.sh sIN + 1))
  set σ2 := (σ1.seth sIN (σ1.sh sIN + 1)).seth sIN ((σ1.seth sIN (σ1.sh sIN + 1)).sh sIN + 1) with hσ2
  have p4 := ParseNat.readNatM_spec cap true sIN 2 3 9 6 7 (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) codes.length
    (ParseNat.enc true (RepairRepresentation.natWord n) ++ ParseNat.enc true [true])
    (ParseNat.enc true (codes.flatMap RepairRepresentation.natWord) ++
      (ParseNat.enc true (RepairRepresentation.natWord cc.length) ++
        (ParseNat.enc true (cc.flatMap RepairRepresentation.natWord) ++ (ParseNat.enc true tl ++ [false])))) σ2
    (by simp [hσ2, hσ1, hIN', hrest, List.append_assoc])
    (by simp [hσ2, hσ1, ParseNat.enc_length, ParseNat.stp])
    (by simp [hσ2, hσ1, hz]) (by simp [hσ2, hσ1, hz]) (by simp [hσ2, hσ1, hz]) (by simp [hσ2, hσ1, hz])
    (by simp [hσ2, hσ1, hz]; omega)
  refine WExec.cast cap (WExec.seq p1 (WExec.seq p2 (WExec.seq p3 p4))) ?_ le_rfl
  apply WState.eq
  · funext s
    by_cases hs : s = sIN
    · subst hs
      simp [hσ2, hσ1, gPos, ParseNat.enc_length, ParseNat.stp]
    · simp [hσ2, hσ1, hs]
  · simp [hσ2, hσ1]
  · funext r
    simp [hσ2, hσ1, hz]
  · simp [hσ2, hσ1]

end NearCubicWires.WireExponent3_5.PrimThrW.TF3Guard
