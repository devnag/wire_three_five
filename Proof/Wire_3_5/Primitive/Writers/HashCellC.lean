import Proof.Wire_3_5.Primitive.Writers.HashCellM
import Proof.Wire_3_5.Primitive.Writers.HashCall
import Proof.Wire_3_5.Primitive.SeedFix.C4KW

/-! # HASH setup (C), P2b part 7: the HASH cell at a THR call — the kept words writer's inputs

P3:2253-2290 (the Hb printer's static words, whose writer reads the call's data `D = hashDataOf …`: `htWord Fs`,
`popsWord pops`, then `1^{ℓ₀}, 1^{refMod}, 1^{B_*}, 1^t, 1^J, 1^G, 1^N, 1^{nE}, 1^{cap}, 1^{|pops|}`, the C4KW
`kwIns`): at a THR call, from the request `(thrReq …).word`, the data word `unaryList (hashNums ++ thrCounts)`, `1^V`
and `1^W`, the HASH cell (`cellM`) leaves on its streams exactly ten of the writer's twelve inputs (`kS i`: the
populations on `138`, the numbers machine's `ℓ₀, p, B_*, t, J, A = |pops|` on `151, 152, 147, 149, 148, 146`, part A's
`|thrPool|, 2^{k_h}, nE` on `155, 156, 157`); the other two (`htWord Fs`, the HASH tape, and `1^{cap}`) are already on
the setup's bank. The call's identities: the majorant `D.MP = thrMP M A B_* K` (`thrNumVals_MP`), `|pops| = A`,
`|𝒢| = card ThrEq`, `B_* = a'·4096·cap_aux`, `|thrPool| = 2Σ|X| + M`, `N = 2^{k_h}`, `nE = 2^{seedBits}`.

* `cw`, `cu`, `cv`, `kS`; `tt_eq`, `jj_eq`, **`mp_eq`**, `hng_eq`, **`pops_len`**, `bs_eq`;
* **`CellFit`** (the cell's capacity facts at the call), `callCost`, **`cell_call`**.

Paper quantities of the main type: the kept words writer's inputs `kwIns (hashDataOf …) cap i` (P3:2253-2290). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unusedVariables false

namespace NearCubicWires.WireExponent3_5.PrimAsm.HashCell
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.Filters
open NearCubicWires.WireExponent3_5.PrimAsm.SymLayout NearCubicWires.SupplierPipeline
open NearCubicWires.WireExponent3_5.PrimThrW.Joins
open NearCubicWires.WireExponent3_5.PrimT.HbM (popsWord)

/-- The streams holding the kept words writer's inputs (`0` and `10` are on the setup's bank). -/
def kS : Fin 12 → Fin 161 := ![0, 138, 151, 152, 147, 149, 148, 155, 156, 157, 0, 146]

section Call
variable {kclk : ℕ} {E : Cost.Envelope} {B : Cost.TimeBudget kclk E}
  (alg : RepairRepresentation.DecompositionAlgorithm) (I : PrimitiveInputs B) {n : ℕ} (hs : I.StarAt n) {a' : ℕ}
  (ha' : a' ≤ 4) (Cs : Fin a' → NormalizedThresholdThresholdCircuit n) (carriers : List (Stars.Carrier n))
  (translation : List ℕ)

/-- The call's request word. -/
noncomputable abbrev cw : List Bool := (Primitive.thrReq n a' ha' Cs carriers translation).word

/-- The call's data word (`hashNums`, then the slice lengths). -/
noncomputable abbrev cu : List Bool :=
  PrimAsm.Data.unaryList (ThrData.hashNums (I.starParams n hs) Cs carriers alg I.D (I.filterParams .thr n).cap ++
    ThrData.thrCounts Cs carriers)

/-- The call's THR numbers. -/
noncomputable abbrev cv : ThrNumVals :=
  thrNumVals (I.starParams n hs) Cs alg I.D carriers.length (I.filterParams .thr n).cap

theorem tt_eq : Primitive.thrCallT alg I hs Cs carriers = (cv alg I hs Cs carriers).tt := by
  unfold Primitive.thrCallT
  rw [← thrNumVals_A alg I hs Cs carriers.length (I.filterParams .thr n).cap]
  rfl

theorem jj_eq : Primitive.thrCallJ alg I hs Cs carriers = (cv alg I hs Cs carriers).J := by
  unfold Primitive.thrCallJ
  rw [← thrNumVals_A alg I hs Cs carriers.length (I.filterParams .thr n).cap]
  rfl

/-- **The call's majorant is the numbers machine's**: `D.MP = thrMP M A B_* K`. -/
theorem mp_eq : (PrimT.C4H.hashDataOf alg I hs Cs carriers).MP =
    thrMP (cv alg I hs Cs carriers).M (cv alg I hs Cs carriers).A (cv alg I hs Cs carriers).Bs
      (cv alg I hs Cs carriers).den := by
  show Primitive.thrMajorant _ _ _ _ _ _ _ (Primitive.thrCallT alg I hs Cs carriers)
    (Primitive.thrCallJ alg I hs Cs carriers) = _
  rw [tt_eq, jj_eq]
  exact thrNumVals_MP (I.starParams n hs) Cs carriers (I.filterParams .thr n) alg I.D _

theorem hng_eq : HashPops.hNG alg Cs = (cv alg I hs Cs carriers).nG := by
  show _ = Fintype.card (Primitive.ThrEq (I.starParams n hs) Cs alg)
  rw [Fintype.card_congr (Enum.thrEqEquiv (I.starParams n hs) Cs alg), Fintype.card_fin]
  rfl

/-- **The populations' count is `A`.** -/
theorem pops_len : (PrimT.C4H.hashPopsOf alg I hs Cs carriers).length = (cv alg I hs Cs carriers).A := by
  unfold PrimT.C4H.hashPopsOf
  simp only [List.length_flatMap, List.length_map, List.length_cons, List.length_nil, List.length_finRange]
  simp only [List.map_const', List.sum_replicate, smul_eq_mul, List.length_finRange]
  have h := hng_eq alg I hs Cs carriers
  simp only [HashPops.hNG] at h
  have hA : (cv alg I hs Cs carriers).A =
      (cv alg I hs Cs carriers).nG * ((cv alg I hs Cs carriers).nPr * ((cv alg I hs Cs carriers).dig * 2)) := rfl
  rw [hA, ← h]
  rfl

theorem bs_eq : (cv alg I hs Cs carriers).Bs = a' * (4096 * (WriterIface.auxP alg I hs Cs carriers).cap) := by
  rw [HashCall.auxP_cap]
  simp only [thrNumVals]
  ring

end Call

end NearCubicWires.WireExponent3_5.PrimAsm.HashCell
