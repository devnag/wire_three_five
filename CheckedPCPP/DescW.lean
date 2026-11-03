import CheckedPCPP.ChecksW
import Codec.Copy
import Codec.Frame

/-!
# H3b, part 3: the checked circuit's framed native descriptor

From `frame (descriptor D.D)` (H2) and the support matrix (H3a), write
`frame (PCPPNative.descriptor (checkedCircuit E D).D)` (the near-cubic-gates paper; `checkedDesc_eq`: the header
`natWord (q + L)`, `natWord (m + |checks|)`, `D`'s node bytes, the check nodes, the output index). Order: read `q` and
`m`, copy `D`'s `m` nodes to a scratch stream `SN` (the `Codec.copyLoop_spec` with three `copyNat` per node), read
the output index `o`, write the checks to a scratch stream `SC` (`ChecksW.checksW_runs`, which also leaves
`m + |checks|` and the final conjunction node in registers), then write the header, copy `SN` and `SC` (`copyMarks`),
the output index and the closing `false` to the output stream.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearCubicGates.Close.CheckedPCPP.DescW

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimAsm.WriteNat
open NearCubicWires.WireExponent3_5.PrimAsm.ParseNat (readNatM readNatM_spec enc stp)
open NearCubicWires.RepairOrdinary.Streaming (marks)
open NearCubicWires.SourceInterfaces NearCubicWires.Bindings.CLW20Lemma311
open NearCubicGates.PublishedSources.PCPP NearCubicGates.Close.Gadget NearCubicGates.Close.Platform
open NearCubicGates.Close.CheckedPCPP.NodeEmit NearCubicGates.Close.CheckedPCPP.ChecksW

variable {ns nr : ℕ} (cap : ℕ)

/-! ## Copying a marked word -/

/-! ## Copying `D`'s nodes -/

theorem enc_true (w : List Bool) : NearCubicWires.WireExponent3_5.PrimAsm.ParseNat.enc true w = marks w := rfl

/-! ## Registers -/

/-- The check writer's registers inside the descriptor writer's (`H 18` is the node-copy counter). -/
def Gof (H : Fin 19 ↪ Fin nr) : Fin 18 ↪ Fin nr :=
  ⟨fun i => H (Fin.castLE (by decide) i), fun a b h => by
    have := H.injective h
    exact Fin.ext (by simpa [Fin.ext_iff] using this)⟩

variable (H : Fin 19 ↪ Fin nr)

theorem GH (a : Fin 18) : Gof H a = H (Fin.castLE (by decide) a) := rfl

theorem pow_bitlen_le (x : ℕ) : 2 ^ natBitLength x ≤ 2 * x + 2 := by
  unfold natBitLength
  rcases Nat.eq_zero_or_pos x with rfl | hx
  · simp
  · have := Nat.pow_log_le_self 2 (show x ≠ 0 by omega)
    rw [pow_succ]; omega

/-- Read one marked `natWord` of `DD` into `G a` (scratch `R 1 … R 4`). -/
def readG (DD : Fin (ns + 1)) (a : Fin 18) : WM ns nr :=
  readNatM true DD (Rw (Gof H) 1) (Rw (Gof H) 2) (Gof H a) (Rw (Gof H) 3) (Rw (Gof H) 4)

/-- The cost bound of one read of a value at most `V`. -/
def readCost (V : ℕ) : ℕ := (V + 3) * (80 * V + 120)

theorem readG_spec (DD : Fin (ns + 1)) (a : Fin 18) (ha : 8 ≤ a.val) (x V : ℕ) (hx : x ≤ V) (pre rest : List Bool)
    (σ : WState ns nr) (hst : σ.st DD = pre ++ marks (natWord x) ++ rest) (hsh : σ.sh DD = pre.length)
    (hcl : ∀ i : Fin 8, i ≠ 7 → σ.val (Rw (Gof H) i) = 0) (hcap : σ.val (Gof H a) + 4 * V + 4 ≤ cap) :
    WExec cap (readG H DD a) σ ((σ.seth DD (pre.length + 2 * (natWord x).length)).setv (Gof H a) (σ.val (Gof H a) + x))
      (readCost V) := by
  have hRG : ∀ i : Fin 8, Rw (Gof H) i ≠ Gof H a := fun i => Rw_ne (Gof H) i a ha
  have hRR : ∀ i j : Fin 8, i ≠ j → Rw (Gof H) i ≠ Rw (Gof H) j := fun i j h => (Rw (Gof H)).injective.ne h
  have hp := pow_bitlen_le x
  have hb := natBitLength_le x
  have e := readNatM_spec cap true DD _ _ _ _ _ (hRR 1 2 (by decide)) (hRG 1) (hRR 1 3 (by decide))
    (hRR 1 4 (by decide)) (hRG 2) (hRR 2 3 (by decide)) (hRR 2 4 (by decide)) (hRG 3)
    (hRR 3 4 (by decide)) (fun h => hRG 4 h.symm) x pre rest σ (by rw [hst, enc_true]) hsh (hcl 1 (by decide)) (hcl 2 (by decide))
    (hcl 3 (by decide)) (hcl 4 (by decide)) (by rw [pow_succ]; omega)
  simp only [stp, if_true] at e
  refine WExec.mono e ?_
  unfold readCost
  have h1 : natBitLength x + 2 ≤ V + 3 := by omega
  have h2 : 40 * 2 ^ natBitLength x + 40 ≤ 80 * V + 120 := by omega
  exact Nat.mul_le_mul h1 h2

theorem frame_eq_marks' : ∀ l : List Bool, RepairOrdinary.frame l = marks l ++ [false]
  | [] => rfl
  | b :: l => by simp [RepairOrdinary.frame, marks, frame_eq_marks' l]

theorem length_le_bytes {n : ℕ} : ∀ nds : List (BooleanNode n),
    nds.length ≤ (nds.flatMap PCPPRequestNodeSchema.native).length
  | [] => le_rfl
  | nd :: nds => by
    have := length_le_bytes nds
    have h3 : 1 ≤ (PCPPRequestNodeSchema.native nd).length := by
      rw [native_len, ChecksW.natWord_len]; omega
    simp only [List.flatMap_cons, List.length_append, List.length_cons]; omega

/-! ## The front: header, `D`'s nodes to `SN`, output index -/

section Front
@[simp] theorem g0 : Gof H 0 = H 0 := rfl
@[simp] theorem g1 : Gof H 1 = H 1 := rfl
@[simp] theorem g2 : Gof H 2 = H 2 := rfl
@[simp] theorem g3 : Gof H 3 = H 3 := rfl
@[simp] theorem g4 : Gof H 4 = H 4 := rfl
@[simp] theorem g5 : Gof H 5 = H 5 := rfl
@[simp] theorem g6 : Gof H 6 = H 6 := rfl
@[simp] theorem g7 : Gof H 7 = H 7 := rfl
@[simp] theorem g8 : Gof H 8 = H 8 := rfl
@[simp] theorem g9 : Gof H 9 = H 9 := rfl
@[simp] theorem g10 : Gof H 10 = H 10 := rfl
@[simp] theorem g11 : Gof H 11 = H 11 := rfl
@[simp] theorem g12 : Gof H 12 = H 12 := rfl
@[simp] theorem g13 : Gof H 13 = H 13 := rfl
@[simp] theorem g14 : Gof H 14 = H 14 := rfl
@[simp] theorem g15 : Gof H 15 = H 15 := rfl
@[simp] theorem g16 : Gof H 16 = H 16 := rfl
@[simp] theorem g17 : Gof H 17 = H 17 := rfl
@[simp] theorem r0 : Rw (Gof H) 0 = H 0 := rfl
@[simp] theorem r1 : Rw (Gof H) 1 = H 1 := rfl
@[simp] theorem r2 : Rw (Gof H) 2 = H 2 := rfl
@[simp] theorem r3 : Rw (Gof H) 3 = H 3 := rfl
@[simp] theorem r4 : Rw (Gof H) 4 = H 4 := rfl
@[simp] theorem r5 : Rw (Gof H) 5 = H 5 := rfl
@[simp] theorem r6 : Rw (Gof H) 6 = H 6 := rfl
@[simp] theorem r7 : Rw (Gof H) 7 = H 7 := rfl

end Front

end NearCubicGates.Close.CheckedPCPP.DescW
