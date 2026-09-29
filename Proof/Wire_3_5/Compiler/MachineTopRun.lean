import Proof.Wire_3_5.Compiler.MachineTopHeader

/-! # C3 v2 top level, T6 (part 1): the whole machine on one request (P3:1874-1906, 1728-1737)

Paper: alg:compiler, "There is an explicit signed separated-equation expression congruent to `2^{m−1}V(z)` modulo
`2^{Q'}` [...] Construction takes `(input description size + 𝒮)·poly(n)` deterministic bit operations"
(P3:1886-1906), printed through the separable printer's request (P3:1728-1737). The five stages run in order on one
layout of 74 tapes: T1 unframes the input record (`load_run`), T2 writes the constant tapes (`init_run`), runs the
compiler stages (`subsets_stage`), T4 emits the cut words (`emit_stage`), T5 writes the request word (`header_run`).
**`top_run`**: from the framed input record `c3Input a R` (the other tapes empty, the logs blank), the output tape 1
holds exactly the printer request's word `reqWord dRow (p+1) width cols (c3v2Ref a R)`, the encoding of C3 v2's
reference. The paper quantity is the request word. Layout: 0 the input, 1 the output, 2 the record, 3–13 the fields,
14–48 the compiler stages' tapes 2–36 (their tapes 0 and 1 are the fields on 11 and 10), 49 the zero field, 50 the
empty stack stream, 51 `1^{2·width}`, 52 a flag, 53 the cut stream, 54 the count, 55 the emit machine's entry log,
56 the doubled count, 57–72 the header writer's scratch, 73 the shared log. Main declarations: `stFin`, `gInit`,
`sfRecs`, `words_stream`, `req_word`, the slot maps, `topM`, `topCost`, **`top_run`**. -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.CompilerMachine.Top
open NearCubicWires NearCubicWires.WireExponent3_5.Shared NearCubicWires.WireExponent3_5.Compiler
open NearCubicWires.WireExponent3_5.CompilerMachine NearCubicWires.WireExponent3_5.CompilerMachine.Pool
open NearCubicWires.WireExponent3_5.CompilerMachine.Kit NearCubicWires.WireExponent3_5.CompilerMachine.Emit
open NearCubicWires.WireExponent3_5.CompilerMachine.Req NearCubicWires.WireExponent3_5.CompilerMachine.Poly
open NearCubicWires.WireExponent3_5.CompilerMachine.Masks NearCubicWires.WireExponent3_5.CompilerMachine.Unions
open NearCubicWires.WireExponent3_5.Block NearCubicWires.WireExponent3_5.GF2
open NearCubicWires.RepairRepresentation
open NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary.RecoveryRootRound NearCubicWires.BlockPlatform
open NearCubicWires.RepairOrdinary.MatrixScoreBatch (Cut cutWord signMagnitude fields)

variable (a : DecompositionAlgorithm)

/-- The compiler stages' registers after the last counter value. -/
def stFin (R : C3Req) : TS :=
  stAt R.P.Q (shapeOf (R.D a)) R.V (sSt0 (zeroT R.P.Q (shapeOf (R.D a)).flatten.length)) (2 ^ R.m)

/-- The emit loop's initial state: empty output and count, registers as the compiler stages left them. -/
def gInit (R : C3Req) : Emit.GSt :=
  ⟨⟨[], 0, (stFin a R).ps.LA, (stFin a R).ps.LB, (stFin a R).ps.O, frame (stFin a R).ps.R, frame (stFin a R).ps.R2,
    frame (stFin a R).ps.R3, frame (stFin a R).ps.X, frame (stFin a R).ps.Y, (stFin a R).PJ, (stFin a R).Cu, false, true,
    false, 0⟩, (stFin a R).ps.Ea, (stFin a R).ps.Ec⟩

/-- The request's signed fields, cut after cut. -/
def sfRecs (R : C3Req) : List (List Bool) :=
  (c3v2Ref a R).flatMap fun c => (fields c).map (signMagnitude (R.p + 1))

theorem frames_sfRecs (R : C3Req) :
    (sfRecs a R).flatMap frame = (c3v2Ref a R).flatMap (cutWord (R.p + 1)) := by
  unfold sfRecs
  rw [List.flatMap_assoc]
  apply List.flatMap_congr
  intro c _
  rw [List.flatMap_map]
  rfl

/-- The cut words and their terminator form a stream of signed fields. -/
theorem words_stream (R : C3Req) :
    (c3v2Ref a R).flatMap (cutWord (R.p + 1)) ++ [false] = Kit.streamTape (sfRecs a R) [] := by
  rw [Kit.streamTape, frames_sfRecs]

theorem sfRecs_ne (R : C3Req) : ∀ r ∈ sfRecs a R, r ≠ [] := by
  intro r hr
  simp only [sfRecs, List.mem_flatMap, List.mem_map] at hr
  obtain ⟨_, _, z, _, rfl⟩ := hr
  simp [signMagnitude]

theorem sfRecs_len (R : C3Req) : ∀ r ∈ sfRecs a R, r.length = R.p + 2 := by
  intro r hr
  simp only [sfRecs, List.mem_flatMap, List.mem_map] at hr
  obtain ⟨_, _, z, _, rfl⟩ := hr
  simp [signMagnitude, SignedSortKey.binary_length]

/-- **The written word is the request's word**: the header's gate count is twice the number of stacked occurrences. -/
theorem req_word (R : C3Req) :
    (natWord R.dRow ++ natWord (R.p + 1)) ++ natWord ((cutsRefX (R.D a) (2 ^ R.P.h) R.m R.P.Q R.V).length + (cutsRefX (R.D a) (2 ^ R.P.h) R.m R.P.Q R.V).length) ++ (natWord R.P.width ++ MatrixScorePhi.columnsWord R.P.width R.cols) ++
        (sfRecs a R).flatMap frame = reqWord R.dRow (R.p + 1) R.P.width R.cols (c3v2Ref a R) := by
  rw [frames_sfRecs, reqWord]
  have hl : (c3v2Ref a R).length = (cutsRefX (R.D a) (2 ^ R.P.h) R.m R.P.Q R.V).length + (cutsRefX (R.D a) (2 ^ R.P.h) R.m R.P.Q R.V).length := by
    rw [c3v2Ref, EquationRow.doubled_length]; omega
  rw [hl]
  simp only [List.append_assoc]

def tT1 : Fin (13 + 1) → Fin 74 := ![0, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 73]

theorem tT1_inj : Function.Injective tT1 := by decide

theorem install_tT1 (A : Fin 74 → List Bool) (v : Fin (13 + 1) → List Bool) :
    install tT1 A v = ![v 0, A 1, v 1, v 2, v 3, v 4, v 5, v 6, v 7, v 8, v 9, v 10, v 11, v 12, A 14, A 15, A 16, A 17, A 18, A 19, A 20, A 21, A 22, A 23, A 24, A 25, A 26, A 27, A 28, A 29, A 30, A 31, A 32, A 33, A 34, A 35, A 36, A 37, A 38, A 39, A 40, A 41, A 42, A 43, A 44, A 45, A 46, A 47, A 48, A 49, A 50, A 51, A 52, A 53, A 54, A 55, A 56, A 57, A 58, A 59, A 60, A 61, A 62, A 63, A 64, A 65, A 66, A 67, A 68, A 69, A 70, A 71, A 72, v 13] := by
  funext i
  fin_cases i
  · exact install_slot tT1 tT1_inj A v 0
  · exact install_other tT1 A v 1 (by decide)
  · exact install_slot tT1 tT1_inj A v 1
  · exact install_slot tT1 tT1_inj A v 2
  · exact install_slot tT1 tT1_inj A v 3
  · exact install_slot tT1 tT1_inj A v 4
  · exact install_slot tT1 tT1_inj A v 5
  · exact install_slot tT1 tT1_inj A v 6
  · exact install_slot tT1 tT1_inj A v 7
  · exact install_slot tT1 tT1_inj A v 8
  · exact install_slot tT1 tT1_inj A v 9
  · exact install_slot tT1 tT1_inj A v 10
  · exact install_slot tT1 tT1_inj A v 11
  · exact install_slot tT1 tT1_inj A v 12
  · exact install_other tT1 A v 14 (by decide)
  · exact install_other tT1 A v 15 (by decide)
  · exact install_other tT1 A v 16 (by decide)
  · exact install_other tT1 A v 17 (by decide)
  · exact install_other tT1 A v 18 (by decide)
  · exact install_other tT1 A v 19 (by decide)
  · exact install_other tT1 A v 20 (by decide)
  · exact install_other tT1 A v 21 (by decide)
  · exact install_other tT1 A v 22 (by decide)
  · exact install_other tT1 A v 23 (by decide)
  · exact install_other tT1 A v 24 (by decide)
  · exact install_other tT1 A v 25 (by decide)
  · exact install_other tT1 A v 26 (by decide)
  · exact install_other tT1 A v 27 (by decide)
  · exact install_other tT1 A v 28 (by decide)
  · exact install_other tT1 A v 29 (by decide)
  · exact install_other tT1 A v 30 (by decide)
  · exact install_other tT1 A v 31 (by decide)
  · exact install_other tT1 A v 32 (by decide)
  · exact install_other tT1 A v 33 (by decide)
  · exact install_other tT1 A v 34 (by decide)
  · exact install_other tT1 A v 35 (by decide)
  · exact install_other tT1 A v 36 (by decide)
  · exact install_other tT1 A v 37 (by decide)
  · exact install_other tT1 A v 38 (by decide)
  · exact install_other tT1 A v 39 (by decide)
  · exact install_other tT1 A v 40 (by decide)
  · exact install_other tT1 A v 41 (by decide)
  · exact install_other tT1 A v 42 (by decide)
  · exact install_other tT1 A v 43 (by decide)
  · exact install_other tT1 A v 44 (by decide)
  · exact install_other tT1 A v 45 (by decide)
  · exact install_other tT1 A v 46 (by decide)
  · exact install_other tT1 A v 47 (by decide)
  · exact install_other tT1 A v 48 (by decide)
  · exact install_other tT1 A v 49 (by decide)
  · exact install_other tT1 A v 50 (by decide)
  · exact install_other tT1 A v 51 (by decide)
  · exact install_other tT1 A v 52 (by decide)
  · exact install_other tT1 A v 53 (by decide)
  · exact install_other tT1 A v 54 (by decide)
  · exact install_other tT1 A v 55 (by decide)
  · exact install_other tT1 A v 56 (by decide)
  · exact install_other tT1 A v 57 (by decide)
  · exact install_other tT1 A v 58 (by decide)
  · exact install_other tT1 A v 59 (by decide)
  · exact install_other tT1 A v 60 (by decide)
  · exact install_other tT1 A v 61 (by decide)
  · exact install_other tT1 A v 62 (by decide)
  · exact install_other tT1 A v 63 (by decide)
  · exact install_other tT1 A v 64 (by decide)
  · exact install_other tT1 A v 65 (by decide)
  · exact install_other tT1 A v 66 (by decide)
  · exact install_other tT1 A v 67 (by decide)
  · exact install_other tT1 A v 68 (by decide)
  · exact install_other tT1 A v 69 (by decide)
  · exact install_other tT1 A v 70 (by decide)
  · exact install_other tT1 A v 71 (by decide)
  · exact install_other tT1 A v 72 (by decide)
  · exact install_slot tT1 tT1_inj A v 13

theorem dockH_tT1 (H : Fin 74 → ℕ) (v : Fin (13 + 1) → ℕ) :
    dockH tT1 H v = ![v 0, H 1, v 1, v 2, v 3, v 4, v 5, v 6, v 7, v 8, v 9, v 10, v 11, v 12, H 14, H 15, H 16, H 17, H 18, H 19, H 20, H 21, H 22, H 23, H 24, H 25, H 26, H 27, H 28, H 29, H 30, H 31, H 32, H 33, H 34, H 35, H 36, H 37, H 38, H 39, H 40, H 41, H 42, H 43, H 44, H 45, H 46, H 47, H 48, H 49, H 50, H 51, H 52, H 53, H 54, H 55, H 56, H 57, H 58, H 59, H 60, H 61, H 62, H 63, H 64, H 65, H 66, H 67, H 68, H 69, H 70, H 71, H 72, v 13] := by
  funext i
  fin_cases i
  · exact dockH_slot tT1 tT1_inj H v 0
  · exact dockH_other tT1 H v 1 (by decide)
  · exact dockH_slot tT1 tT1_inj H v 1
  · exact dockH_slot tT1 tT1_inj H v 2
  · exact dockH_slot tT1 tT1_inj H v 3
  · exact dockH_slot tT1 tT1_inj H v 4
  · exact dockH_slot tT1 tT1_inj H v 5
  · exact dockH_slot tT1 tT1_inj H v 6
  · exact dockH_slot tT1 tT1_inj H v 7
  · exact dockH_slot tT1 tT1_inj H v 8
  · exact dockH_slot tT1 tT1_inj H v 9
  · exact dockH_slot tT1 tT1_inj H v 10
  · exact dockH_slot tT1 tT1_inj H v 11
  · exact dockH_slot tT1 tT1_inj H v 12
  · exact dockH_other tT1 H v 14 (by decide)
  · exact dockH_other tT1 H v 15 (by decide)
  · exact dockH_other tT1 H v 16 (by decide)
  · exact dockH_other tT1 H v 17 (by decide)
  · exact dockH_other tT1 H v 18 (by decide)
  · exact dockH_other tT1 H v 19 (by decide)
  · exact dockH_other tT1 H v 20 (by decide)
  · exact dockH_other tT1 H v 21 (by decide)
  · exact dockH_other tT1 H v 22 (by decide)
  · exact dockH_other tT1 H v 23 (by decide)
  · exact dockH_other tT1 H v 24 (by decide)
  · exact dockH_other tT1 H v 25 (by decide)
  · exact dockH_other tT1 H v 26 (by decide)
  · exact dockH_other tT1 H v 27 (by decide)
  · exact dockH_other tT1 H v 28 (by decide)
  · exact dockH_other tT1 H v 29 (by decide)
  · exact dockH_other tT1 H v 30 (by decide)
  · exact dockH_other tT1 H v 31 (by decide)
  · exact dockH_other tT1 H v 32 (by decide)
  · exact dockH_other tT1 H v 33 (by decide)
  · exact dockH_other tT1 H v 34 (by decide)
  · exact dockH_other tT1 H v 35 (by decide)
  · exact dockH_other tT1 H v 36 (by decide)
  · exact dockH_other tT1 H v 37 (by decide)
  · exact dockH_other tT1 H v 38 (by decide)
  · exact dockH_other tT1 H v 39 (by decide)
  · exact dockH_other tT1 H v 40 (by decide)
  · exact dockH_other tT1 H v 41 (by decide)
  · exact dockH_other tT1 H v 42 (by decide)
  · exact dockH_other tT1 H v 43 (by decide)
  · exact dockH_other tT1 H v 44 (by decide)
  · exact dockH_other tT1 H v 45 (by decide)
  · exact dockH_other tT1 H v 46 (by decide)
  · exact dockH_other tT1 H v 47 (by decide)
  · exact dockH_other tT1 H v 48 (by decide)
  · exact dockH_other tT1 H v 49 (by decide)
  · exact dockH_other tT1 H v 50 (by decide)
  · exact dockH_other tT1 H v 51 (by decide)
  · exact dockH_other tT1 H v 52 (by decide)
  · exact dockH_other tT1 H v 53 (by decide)
  · exact dockH_other tT1 H v 54 (by decide)
  · exact dockH_other tT1 H v 55 (by decide)
  · exact dockH_other tT1 H v 56 (by decide)
  · exact dockH_other tT1 H v 57 (by decide)
  · exact dockH_other tT1 H v 58 (by decide)
  · exact dockH_other tT1 H v 59 (by decide)
  · exact dockH_other tT1 H v 60 (by decide)
  · exact dockH_other tT1 H v 61 (by decide)
  · exact dockH_other tT1 H v 62 (by decide)
  · exact dockH_other tT1 H v 63 (by decide)
  · exact dockH_other tT1 H v 64 (by decide)
  · exact dockH_other tT1 H v 65 (by decide)
  · exact dockH_other tT1 H v 66 (by decide)
  · exact dockH_other tT1 H v 67 (by decide)
  · exact dockH_other tT1 H v 68 (by decide)
  · exact dockH_other tT1 H v 69 (by decide)
  · exact dockH_other tT1 H v 70 (by decide)
  · exact dockH_other tT1 H v 71 (by decide)
  · exact dockH_other tT1 H v 72 (by decide)
  · exact dockH_slot tT1 tT1_inj H v 13

def tT2 : Fin 33 → Fin 74 := ![3, 4, 5, 7, 8, 17, 18, 19, 26, 27, 35, 36, 37, 38, 41, 23, 39, 40, 30, 46, 49, 51, 50, 24, 28, 29, 31, 33, 42, 47, 48, 52, 73]

theorem tT2_inj : Function.Injective tT2 := by decide

theorem install_tT2 (A : Fin 74 → List Bool) (v : Fin 33 → List Bool) :
    install tT2 A v = ![A 0, A 1, A 2, v 0, v 1, v 2, A 6, v 3, v 4, A 9, A 10, A 11, A 12, A 13, A 14, A 15, A 16, v 5, v 6, v 7, A 20, A 21, A 22, v 15, v 23, A 25, v 8, v 9, v 24, v 25, v 18, v 26, A 32, v 27, A 34, v 10, v 11, v 12, v 13, v 16, v 17, v 14, v 28, A 43, A 44, A 45, v 19, v 29, v 30, v 20, v 22, v 21, v 31, A 53, A 54, A 55, A 56, A 57, A 58, A 59, A 60, A 61, A 62, A 63, A 64, A 65, A 66, A 67, A 68, A 69, A 70, A 71, A 72, v 32] := by
  funext i
  fin_cases i
  · exact install_other tT2 A v 0 (by decide)
  · exact install_other tT2 A v 1 (by decide)
  · exact install_other tT2 A v 2 (by decide)
  · exact install_slot tT2 tT2_inj A v 0
  · exact install_slot tT2 tT2_inj A v 1
  · exact install_slot tT2 tT2_inj A v 2
  · exact install_other tT2 A v 6 (by decide)
  · exact install_slot tT2 tT2_inj A v 3
  · exact install_slot tT2 tT2_inj A v 4
  · exact install_other tT2 A v 9 (by decide)
  · exact install_other tT2 A v 10 (by decide)
  · exact install_other tT2 A v 11 (by decide)
  · exact install_other tT2 A v 12 (by decide)
  · exact install_other tT2 A v 13 (by decide)
  · exact install_other tT2 A v 14 (by decide)
  · exact install_other tT2 A v 15 (by decide)
  · exact install_other tT2 A v 16 (by decide)
  · exact install_slot tT2 tT2_inj A v 5
  · exact install_slot tT2 tT2_inj A v 6
  · exact install_slot tT2 tT2_inj A v 7
  · exact install_other tT2 A v 20 (by decide)
  · exact install_other tT2 A v 21 (by decide)
  · exact install_other tT2 A v 22 (by decide)
  · exact install_slot tT2 tT2_inj A v 15
  · exact install_slot tT2 tT2_inj A v 23
  · exact install_other tT2 A v 25 (by decide)
  · exact install_slot tT2 tT2_inj A v 8
  · exact install_slot tT2 tT2_inj A v 9
  · exact install_slot tT2 tT2_inj A v 24
  · exact install_slot tT2 tT2_inj A v 25
  · exact install_slot tT2 tT2_inj A v 18
  · exact install_slot tT2 tT2_inj A v 26
  · exact install_other tT2 A v 32 (by decide)
  · exact install_slot tT2 tT2_inj A v 27
  · exact install_other tT2 A v 34 (by decide)
  · exact install_slot tT2 tT2_inj A v 10
  · exact install_slot tT2 tT2_inj A v 11
  · exact install_slot tT2 tT2_inj A v 12
  · exact install_slot tT2 tT2_inj A v 13
  · exact install_slot tT2 tT2_inj A v 16
  · exact install_slot tT2 tT2_inj A v 17
  · exact install_slot tT2 tT2_inj A v 14
  · exact install_slot tT2 tT2_inj A v 28
  · exact install_other tT2 A v 43 (by decide)
  · exact install_other tT2 A v 44 (by decide)
  · exact install_other tT2 A v 45 (by decide)
  · exact install_slot tT2 tT2_inj A v 19
  · exact install_slot tT2 tT2_inj A v 29
  · exact install_slot tT2 tT2_inj A v 30
  · exact install_slot tT2 tT2_inj A v 20
  · exact install_slot tT2 tT2_inj A v 22
  · exact install_slot tT2 tT2_inj A v 21
  · exact install_slot tT2 tT2_inj A v 31
  · exact install_other tT2 A v 53 (by decide)
  · exact install_other tT2 A v 54 (by decide)
  · exact install_other tT2 A v 55 (by decide)
  · exact install_other tT2 A v 56 (by decide)
  · exact install_other tT2 A v 57 (by decide)
  · exact install_other tT2 A v 58 (by decide)
  · exact install_other tT2 A v 59 (by decide)
  · exact install_other tT2 A v 60 (by decide)
  · exact install_other tT2 A v 61 (by decide)
  · exact install_other tT2 A v 62 (by decide)
  · exact install_other tT2 A v 63 (by decide)
  · exact install_other tT2 A v 64 (by decide)
  · exact install_other tT2 A v 65 (by decide)
  · exact install_other tT2 A v 66 (by decide)
  · exact install_other tT2 A v 67 (by decide)
  · exact install_other tT2 A v 68 (by decide)
  · exact install_other tT2 A v 69 (by decide)
  · exact install_other tT2 A v 70 (by decide)
  · exact install_other tT2 A v 71 (by decide)
  · exact install_other tT2 A v 72 (by decide)
  · exact install_slot tT2 tT2_inj A v 32

theorem dockH_tT2 (H : Fin 74 → ℕ) (v : Fin 33 → ℕ) :
    dockH tT2 H v = ![H 0, H 1, H 2, v 0, v 1, v 2, H 6, v 3, v 4, H 9, H 10, H 11, H 12, H 13, H 14, H 15, H 16, v 5, v 6, v 7, H 20, H 21, H 22, v 15, v 23, H 25, v 8, v 9, v 24, v 25, v 18, v 26, H 32, v 27, H 34, v 10, v 11, v 12, v 13, v 16, v 17, v 14, v 28, H 43, H 44, H 45, v 19, v 29, v 30, v 20, v 22, v 21, v 31, H 53, H 54, H 55, H 56, H 57, H 58, H 59, H 60, H 61, H 62, H 63, H 64, H 65, H 66, H 67, H 68, H 69, H 70, H 71, H 72, v 32] := by
  funext i
  fin_cases i
  · exact dockH_other tT2 H v 0 (by decide)
  · exact dockH_other tT2 H v 1 (by decide)
  · exact dockH_other tT2 H v 2 (by decide)
  · exact dockH_slot tT2 tT2_inj H v 0
  · exact dockH_slot tT2 tT2_inj H v 1
  · exact dockH_slot tT2 tT2_inj H v 2
  · exact dockH_other tT2 H v 6 (by decide)
  · exact dockH_slot tT2 tT2_inj H v 3
  · exact dockH_slot tT2 tT2_inj H v 4
  · exact dockH_other tT2 H v 9 (by decide)
  · exact dockH_other tT2 H v 10 (by decide)
  · exact dockH_other tT2 H v 11 (by decide)
  · exact dockH_other tT2 H v 12 (by decide)
  · exact dockH_other tT2 H v 13 (by decide)
  · exact dockH_other tT2 H v 14 (by decide)
  · exact dockH_other tT2 H v 15 (by decide)
  · exact dockH_other tT2 H v 16 (by decide)
  · exact dockH_slot tT2 tT2_inj H v 5
  · exact dockH_slot tT2 tT2_inj H v 6
  · exact dockH_slot tT2 tT2_inj H v 7
  · exact dockH_other tT2 H v 20 (by decide)
  · exact dockH_other tT2 H v 21 (by decide)
  · exact dockH_other tT2 H v 22 (by decide)
  · exact dockH_slot tT2 tT2_inj H v 15
  · exact dockH_slot tT2 tT2_inj H v 23
  · exact dockH_other tT2 H v 25 (by decide)
  · exact dockH_slot tT2 tT2_inj H v 8
  · exact dockH_slot tT2 tT2_inj H v 9
  · exact dockH_slot tT2 tT2_inj H v 24
  · exact dockH_slot tT2 tT2_inj H v 25
  · exact dockH_slot tT2 tT2_inj H v 18
  · exact dockH_slot tT2 tT2_inj H v 26
  · exact dockH_other tT2 H v 32 (by decide)
  · exact dockH_slot tT2 tT2_inj H v 27
  · exact dockH_other tT2 H v 34 (by decide)
  · exact dockH_slot tT2 tT2_inj H v 10
  · exact dockH_slot tT2 tT2_inj H v 11
  · exact dockH_slot tT2 tT2_inj H v 12
  · exact dockH_slot tT2 tT2_inj H v 13
  · exact dockH_slot tT2 tT2_inj H v 16
  · exact dockH_slot tT2 tT2_inj H v 17
  · exact dockH_slot tT2 tT2_inj H v 14
  · exact dockH_slot tT2 tT2_inj H v 28
  · exact dockH_other tT2 H v 43 (by decide)
  · exact dockH_other tT2 H v 44 (by decide)
  · exact dockH_other tT2 H v 45 (by decide)
  · exact dockH_slot tT2 tT2_inj H v 19
  · exact dockH_slot tT2 tT2_inj H v 29
  · exact dockH_slot tT2 tT2_inj H v 30
  · exact dockH_slot tT2 tT2_inj H v 20
  · exact dockH_slot tT2 tT2_inj H v 22
  · exact dockH_slot tT2 tT2_inj H v 21
  · exact dockH_slot tT2 tT2_inj H v 31
  · exact dockH_other tT2 H v 53 (by decide)
  · exact dockH_other tT2 H v 54 (by decide)
  · exact dockH_other tT2 H v 55 (by decide)
  · exact dockH_other tT2 H v 56 (by decide)
  · exact dockH_other tT2 H v 57 (by decide)
  · exact dockH_other tT2 H v 58 (by decide)
  · exact dockH_other tT2 H v 59 (by decide)
  · exact dockH_other tT2 H v 60 (by decide)
  · exact dockH_other tT2 H v 61 (by decide)
  · exact dockH_other tT2 H v 62 (by decide)
  · exact dockH_other tT2 H v 63 (by decide)
  · exact dockH_other tT2 H v 64 (by decide)
  · exact dockH_other tT2 H v 65 (by decide)
  · exact dockH_other tT2 H v 66 (by decide)
  · exact dockH_other tT2 H v 67 (by decide)
  · exact dockH_other tT2 H v 68 (by decide)
  · exact dockH_other tT2 H v 69 (by decide)
  · exact dockH_other tT2 H v 70 (by decide)
  · exact dockH_other tT2 H v 71 (by decide)
  · exact dockH_other tT2 H v 72 (by decide)
  · exact dockH_slot tT2 tT2_inj H v 32

def tT3 : Fin (37 + 1) → Fin 74 := ![11, 10, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 73]

theorem tT3_inj : Function.Injective tT3 := by decide

theorem install_tT3 (A : Fin 74 → List Bool) (v : Fin (37 + 1) → List Bool) :
    install tT3 A v = ![A 0, A 1, A 2, A 3, A 4, A 5, A 6, A 7, A 8, A 9, v 1, v 0, A 12, A 13, v 2, v 3, v 4, v 5, v 6, v 7, v 8, v 9, v 10, v 11, v 12, v 13, v 14, v 15, v 16, v 17, v 18, v 19, v 20, v 21, v 22, v 23, v 24, v 25, v 26, v 27, v 28, v 29, v 30, v 31, v 32, v 33, v 34, v 35, v 36, A 49, A 50, A 51, A 52, A 53, A 54, A 55, A 56, A 57, A 58, A 59, A 60, A 61, A 62, A 63, A 64, A 65, A 66, A 67, A 68, A 69, A 70, A 71, A 72, v 37] := by
  funext i
  fin_cases i
  · exact install_other tT3 A v 0 (by decide)
  · exact install_other tT3 A v 1 (by decide)
  · exact install_other tT3 A v 2 (by decide)
  · exact install_other tT3 A v 3 (by decide)
  · exact install_other tT3 A v 4 (by decide)
  · exact install_other tT3 A v 5 (by decide)
  · exact install_other tT3 A v 6 (by decide)
  · exact install_other tT3 A v 7 (by decide)
  · exact install_other tT3 A v 8 (by decide)
  · exact install_other tT3 A v 9 (by decide)
  · exact install_slot tT3 tT3_inj A v 1
  · exact install_slot tT3 tT3_inj A v 0
  · exact install_other tT3 A v 12 (by decide)
  · exact install_other tT3 A v 13 (by decide)
  · exact install_slot tT3 tT3_inj A v 2
  · exact install_slot tT3 tT3_inj A v 3
  · exact install_slot tT3 tT3_inj A v 4
  · exact install_slot tT3 tT3_inj A v 5
  · exact install_slot tT3 tT3_inj A v 6
  · exact install_slot tT3 tT3_inj A v 7
  · exact install_slot tT3 tT3_inj A v 8
  · exact install_slot tT3 tT3_inj A v 9
  · exact install_slot tT3 tT3_inj A v 10
  · exact install_slot tT3 tT3_inj A v 11
  · exact install_slot tT3 tT3_inj A v 12
  · exact install_slot tT3 tT3_inj A v 13
  · exact install_slot tT3 tT3_inj A v 14
  · exact install_slot tT3 tT3_inj A v 15
  · exact install_slot tT3 tT3_inj A v 16
  · exact install_slot tT3 tT3_inj A v 17
  · exact install_slot tT3 tT3_inj A v 18
  · exact install_slot tT3 tT3_inj A v 19
  · exact install_slot tT3 tT3_inj A v 20
  · exact install_slot tT3 tT3_inj A v 21
  · exact install_slot tT3 tT3_inj A v 22
  · exact install_slot tT3 tT3_inj A v 23
  · exact install_slot tT3 tT3_inj A v 24
  · exact install_slot tT3 tT3_inj A v 25
  · exact install_slot tT3 tT3_inj A v 26
  · exact install_slot tT3 tT3_inj A v 27
  · exact install_slot tT3 tT3_inj A v 28
  · exact install_slot tT3 tT3_inj A v 29
  · exact install_slot tT3 tT3_inj A v 30
  · exact install_slot tT3 tT3_inj A v 31
  · exact install_slot tT3 tT3_inj A v 32
  · exact install_slot tT3 tT3_inj A v 33
  · exact install_slot tT3 tT3_inj A v 34
  · exact install_slot tT3 tT3_inj A v 35
  · exact install_slot tT3 tT3_inj A v 36
  · exact install_other tT3 A v 49 (by decide)
  · exact install_other tT3 A v 50 (by decide)
  · exact install_other tT3 A v 51 (by decide)
  · exact install_other tT3 A v 52 (by decide)
  · exact install_other tT3 A v 53 (by decide)
  · exact install_other tT3 A v 54 (by decide)
  · exact install_other tT3 A v 55 (by decide)
  · exact install_other tT3 A v 56 (by decide)
  · exact install_other tT3 A v 57 (by decide)
  · exact install_other tT3 A v 58 (by decide)
  · exact install_other tT3 A v 59 (by decide)
  · exact install_other tT3 A v 60 (by decide)
  · exact install_other tT3 A v 61 (by decide)
  · exact install_other tT3 A v 62 (by decide)
  · exact install_other tT3 A v 63 (by decide)
  · exact install_other tT3 A v 64 (by decide)
  · exact install_other tT3 A v 65 (by decide)
  · exact install_other tT3 A v 66 (by decide)
  · exact install_other tT3 A v 67 (by decide)
  · exact install_other tT3 A v 68 (by decide)
  · exact install_other tT3 A v 69 (by decide)
  · exact install_other tT3 A v 70 (by decide)
  · exact install_other tT3 A v 71 (by decide)
  · exact install_other tT3 A v 72 (by decide)
  · exact install_slot tT3 tT3_inj A v 37

theorem dockH_tT3 (H : Fin 74 → ℕ) (v : Fin (37 + 1) → ℕ) :
    dockH tT3 H v = ![H 0, H 1, H 2, H 3, H 4, H 5, H 6, H 7, H 8, H 9, v 1, v 0, H 12, H 13, v 2, v 3, v 4, v 5, v 6, v 7, v 8, v 9, v 10, v 11, v 12, v 13, v 14, v 15, v 16, v 17, v 18, v 19, v 20, v 21, v 22, v 23, v 24, v 25, v 26, v 27, v 28, v 29, v 30, v 31, v 32, v 33, v 34, v 35, v 36, H 49, H 50, H 51, H 52, H 53, H 54, H 55, H 56, H 57, H 58, H 59, H 60, H 61, H 62, H 63, H 64, H 65, H 66, H 67, H 68, H 69, H 70, H 71, H 72, v 37] := by
  funext i
  fin_cases i
  · exact dockH_other tT3 H v 0 (by decide)
  · exact dockH_other tT3 H v 1 (by decide)
  · exact dockH_other tT3 H v 2 (by decide)
  · exact dockH_other tT3 H v 3 (by decide)
  · exact dockH_other tT3 H v 4 (by decide)
  · exact dockH_other tT3 H v 5 (by decide)
  · exact dockH_other tT3 H v 6 (by decide)
  · exact dockH_other tT3 H v 7 (by decide)
  · exact dockH_other tT3 H v 8 (by decide)
  · exact dockH_other tT3 H v 9 (by decide)
  · exact dockH_slot tT3 tT3_inj H v 1
  · exact dockH_slot tT3 tT3_inj H v 0
  · exact dockH_other tT3 H v 12 (by decide)
  · exact dockH_other tT3 H v 13 (by decide)
  · exact dockH_slot tT3 tT3_inj H v 2
  · exact dockH_slot tT3 tT3_inj H v 3
  · exact dockH_slot tT3 tT3_inj H v 4
  · exact dockH_slot tT3 tT3_inj H v 5
  · exact dockH_slot tT3 tT3_inj H v 6
  · exact dockH_slot tT3 tT3_inj H v 7
  · exact dockH_slot tT3 tT3_inj H v 8
  · exact dockH_slot tT3 tT3_inj H v 9
  · exact dockH_slot tT3 tT3_inj H v 10
  · exact dockH_slot tT3 tT3_inj H v 11
  · exact dockH_slot tT3 tT3_inj H v 12
  · exact dockH_slot tT3 tT3_inj H v 13
  · exact dockH_slot tT3 tT3_inj H v 14
  · exact dockH_slot tT3 tT3_inj H v 15
  · exact dockH_slot tT3 tT3_inj H v 16
  · exact dockH_slot tT3 tT3_inj H v 17
  · exact dockH_slot tT3 tT3_inj H v 18
  · exact dockH_slot tT3 tT3_inj H v 19
  · exact dockH_slot tT3 tT3_inj H v 20
  · exact dockH_slot tT3 tT3_inj H v 21
  · exact dockH_slot tT3 tT3_inj H v 22
  · exact dockH_slot tT3 tT3_inj H v 23
  · exact dockH_slot tT3 tT3_inj H v 24
  · exact dockH_slot tT3 tT3_inj H v 25
  · exact dockH_slot tT3 tT3_inj H v 26
  · exact dockH_slot tT3 tT3_inj H v 27
  · exact dockH_slot tT3 tT3_inj H v 28
  · exact dockH_slot tT3 tT3_inj H v 29
  · exact dockH_slot tT3 tT3_inj H v 30
  · exact dockH_slot tT3 tT3_inj H v 31
  · exact dockH_slot tT3 tT3_inj H v 32
  · exact dockH_slot tT3 tT3_inj H v 33
  · exact dockH_slot tT3 tT3_inj H v 34
  · exact dockH_slot tT3 tT3_inj H v 35
  · exact dockH_slot tT3 tT3_inj H v 36
  · exact dockH_other tT3 H v 49 (by decide)
  · exact dockH_other tT3 H v 50 (by decide)
  · exact dockH_other tT3 H v 51 (by decide)
  · exact dockH_other tT3 H v 52 (by decide)
  · exact dockH_other tT3 H v 53 (by decide)
  · exact dockH_other tT3 H v 54 (by decide)
  · exact dockH_other tT3 H v 55 (by decide)
  · exact dockH_other tT3 H v 56 (by decide)
  · exact dockH_other tT3 H v 57 (by decide)
  · exact dockH_other tT3 H v 58 (by decide)
  · exact dockH_other tT3 H v 59 (by decide)
  · exact dockH_other tT3 H v 60 (by decide)
  · exact dockH_other tT3 H v 61 (by decide)
  · exact dockH_other tT3 H v 62 (by decide)
  · exact dockH_other tT3 H v 63 (by decide)
  · exact dockH_other tT3 H v 64 (by decide)
  · exact dockH_other tT3 H v 65 (by decide)
  · exact dockH_other tT3 H v 66 (by decide)
  · exact dockH_other tT3 H v 67 (by decide)
  · exact dockH_other tT3 H v 68 (by decide)
  · exact dockH_other tT3 H v 69 (by decide)
  · exact dockH_other tT3 H v 70 (by decide)
  · exact dockH_other tT3 H v 71 (by decide)
  · exact dockH_other tT3 H v 72 (by decide)
  · exact dockH_slot tT3 tT3_inj H v 37

def tT4 : Fin ((29 + 1) + 1) → Fin 74 := ![43, 9, 53, 49, 50, 3, 51, 14, 28, 15, 16, 25, 17, 18, 19, 29, 26, 27, 31, 42, 47, 48, 52, 54, 20, 21, 22, 44, 45, 55, 73]

theorem tT4_inj : Function.Injective tT4 := by decide

theorem install_tT4 (A : Fin 74 → List Bool) (v : Fin ((29 + 1) + 1) → List Bool) :
    install tT4 A v = ![A 0, A 1, A 2, v 5, A 4, A 5, A 6, A 7, A 8, v 1, A 10, A 11, A 12, A 13, v 7, v 9, v 10, v 12, v 13, v 14, v 24, v 25, v 26, A 23, A 24, v 11, v 16, v 17, v 8, v 15, A 30, v 18, A 32, A 33, A 34, A 35, A 36, A 37, A 38, A 39, A 40, A 41, v 19, v 0, v 27, v 28, A 46, v 20, v 21, v 3, v 4, v 6, v 22, v 2, v 23, v 29, A 56, A 57, A 58, A 59, A 60, A 61, A 62, A 63, A 64, A 65, A 66, A 67, A 68, A 69, A 70, A 71, A 72, v 30] := by
  funext i
  fin_cases i
  · exact install_other tT4 A v 0 (by decide)
  · exact install_other tT4 A v 1 (by decide)
  · exact install_other tT4 A v 2 (by decide)
  · exact install_slot tT4 tT4_inj A v 5
  · exact install_other tT4 A v 4 (by decide)
  · exact install_other tT4 A v 5 (by decide)
  · exact install_other tT4 A v 6 (by decide)
  · exact install_other tT4 A v 7 (by decide)
  · exact install_other tT4 A v 8 (by decide)
  · exact install_slot tT4 tT4_inj A v 1
  · exact install_other tT4 A v 10 (by decide)
  · exact install_other tT4 A v 11 (by decide)
  · exact install_other tT4 A v 12 (by decide)
  · exact install_other tT4 A v 13 (by decide)
  · exact install_slot tT4 tT4_inj A v 7
  · exact install_slot tT4 tT4_inj A v 9
  · exact install_slot tT4 tT4_inj A v 10
  · exact install_slot tT4 tT4_inj A v 12
  · exact install_slot tT4 tT4_inj A v 13
  · exact install_slot tT4 tT4_inj A v 14
  · exact install_slot tT4 tT4_inj A v 24
  · exact install_slot tT4 tT4_inj A v 25
  · exact install_slot tT4 tT4_inj A v 26
  · exact install_other tT4 A v 23 (by decide)
  · exact install_other tT4 A v 24 (by decide)
  · exact install_slot tT4 tT4_inj A v 11
  · exact install_slot tT4 tT4_inj A v 16
  · exact install_slot tT4 tT4_inj A v 17
  · exact install_slot tT4 tT4_inj A v 8
  · exact install_slot tT4 tT4_inj A v 15
  · exact install_other tT4 A v 30 (by decide)
  · exact install_slot tT4 tT4_inj A v 18
  · exact install_other tT4 A v 32 (by decide)
  · exact install_other tT4 A v 33 (by decide)
  · exact install_other tT4 A v 34 (by decide)
  · exact install_other tT4 A v 35 (by decide)
  · exact install_other tT4 A v 36 (by decide)
  · exact install_other tT4 A v 37 (by decide)
  · exact install_other tT4 A v 38 (by decide)
  · exact install_other tT4 A v 39 (by decide)
  · exact install_other tT4 A v 40 (by decide)
  · exact install_other tT4 A v 41 (by decide)
  · exact install_slot tT4 tT4_inj A v 19
  · exact install_slot tT4 tT4_inj A v 0
  · exact install_slot tT4 tT4_inj A v 27
  · exact install_slot tT4 tT4_inj A v 28
  · exact install_other tT4 A v 46 (by decide)
  · exact install_slot tT4 tT4_inj A v 20
  · exact install_slot tT4 tT4_inj A v 21
  · exact install_slot tT4 tT4_inj A v 3
  · exact install_slot tT4 tT4_inj A v 4
  · exact install_slot tT4 tT4_inj A v 6
  · exact install_slot tT4 tT4_inj A v 22
  · exact install_slot tT4 tT4_inj A v 2
  · exact install_slot tT4 tT4_inj A v 23
  · exact install_slot tT4 tT4_inj A v 29
  · exact install_other tT4 A v 56 (by decide)
  · exact install_other tT4 A v 57 (by decide)
  · exact install_other tT4 A v 58 (by decide)
  · exact install_other tT4 A v 59 (by decide)
  · exact install_other tT4 A v 60 (by decide)
  · exact install_other tT4 A v 61 (by decide)
  · exact install_other tT4 A v 62 (by decide)
  · exact install_other tT4 A v 63 (by decide)
  · exact install_other tT4 A v 64 (by decide)
  · exact install_other tT4 A v 65 (by decide)
  · exact install_other tT4 A v 66 (by decide)
  · exact install_other tT4 A v 67 (by decide)
  · exact install_other tT4 A v 68 (by decide)
  · exact install_other tT4 A v 69 (by decide)
  · exact install_other tT4 A v 70 (by decide)
  · exact install_other tT4 A v 71 (by decide)
  · exact install_other tT4 A v 72 (by decide)
  · exact install_slot tT4 tT4_inj A v 30

theorem dockH_tT4 (H : Fin 74 → ℕ) (v : Fin ((29 + 1) + 1) → ℕ) :
    dockH tT4 H v = ![H 0, H 1, H 2, v 5, H 4, H 5, H 6, H 7, H 8, v 1, H 10, H 11, H 12, H 13, v 7, v 9, v 10, v 12, v 13, v 14, v 24, v 25, v 26, H 23, H 24, v 11, v 16, v 17, v 8, v 15, H 30, v 18, H 32, H 33, H 34, H 35, H 36, H 37, H 38, H 39, H 40, H 41, v 19, v 0, v 27, v 28, H 46, v 20, v 21, v 3, v 4, v 6, v 22, v 2, v 23, v 29, H 56, H 57, H 58, H 59, H 60, H 61, H 62, H 63, H 64, H 65, H 66, H 67, H 68, H 69, H 70, H 71, H 72, v 30] := by
  funext i
  fin_cases i
  · exact dockH_other tT4 H v 0 (by decide)
  · exact dockH_other tT4 H v 1 (by decide)
  · exact dockH_other tT4 H v 2 (by decide)
  · exact dockH_slot tT4 tT4_inj H v 5
  · exact dockH_other tT4 H v 4 (by decide)
  · exact dockH_other tT4 H v 5 (by decide)
  · exact dockH_other tT4 H v 6 (by decide)
  · exact dockH_other tT4 H v 7 (by decide)
  · exact dockH_other tT4 H v 8 (by decide)
  · exact dockH_slot tT4 tT4_inj H v 1
  · exact dockH_other tT4 H v 10 (by decide)
  · exact dockH_other tT4 H v 11 (by decide)
  · exact dockH_other tT4 H v 12 (by decide)
  · exact dockH_other tT4 H v 13 (by decide)
  · exact dockH_slot tT4 tT4_inj H v 7
  · exact dockH_slot tT4 tT4_inj H v 9
  · exact dockH_slot tT4 tT4_inj H v 10
  · exact dockH_slot tT4 tT4_inj H v 12
  · exact dockH_slot tT4 tT4_inj H v 13
  · exact dockH_slot tT4 tT4_inj H v 14
  · exact dockH_slot tT4 tT4_inj H v 24
  · exact dockH_slot tT4 tT4_inj H v 25
  · exact dockH_slot tT4 tT4_inj H v 26
  · exact dockH_other tT4 H v 23 (by decide)
  · exact dockH_other tT4 H v 24 (by decide)
  · exact dockH_slot tT4 tT4_inj H v 11
  · exact dockH_slot tT4 tT4_inj H v 16
  · exact dockH_slot tT4 tT4_inj H v 17
  · exact dockH_slot tT4 tT4_inj H v 8
  · exact dockH_slot tT4 tT4_inj H v 15
  · exact dockH_other tT4 H v 30 (by decide)
  · exact dockH_slot tT4 tT4_inj H v 18
  · exact dockH_other tT4 H v 32 (by decide)
  · exact dockH_other tT4 H v 33 (by decide)
  · exact dockH_other tT4 H v 34 (by decide)
  · exact dockH_other tT4 H v 35 (by decide)
  · exact dockH_other tT4 H v 36 (by decide)
  · exact dockH_other tT4 H v 37 (by decide)
  · exact dockH_other tT4 H v 38 (by decide)
  · exact dockH_other tT4 H v 39 (by decide)
  · exact dockH_other tT4 H v 40 (by decide)
  · exact dockH_other tT4 H v 41 (by decide)
  · exact dockH_slot tT4 tT4_inj H v 19
  · exact dockH_slot tT4 tT4_inj H v 0
  · exact dockH_slot tT4 tT4_inj H v 27
  · exact dockH_slot tT4 tT4_inj H v 28
  · exact dockH_other tT4 H v 46 (by decide)
  · exact dockH_slot tT4 tT4_inj H v 20
  · exact dockH_slot tT4 tT4_inj H v 21
  · exact dockH_slot tT4 tT4_inj H v 3
  · exact dockH_slot tT4 tT4_inj H v 4
  · exact dockH_slot tT4 tT4_inj H v 6
  · exact dockH_slot tT4 tT4_inj H v 22
  · exact dockH_slot tT4 tT4_inj H v 2
  · exact dockH_slot tT4 tT4_inj H v 23
  · exact dockH_slot tT4 tT4_inj H v 29
  · exact dockH_other tT4 H v 56 (by decide)
  · exact dockH_other tT4 H v 57 (by decide)
  · exact dockH_other tT4 H v 58 (by decide)
  · exact dockH_other tT4 H v 59 (by decide)
  · exact dockH_other tT4 H v 60 (by decide)
  · exact dockH_other tT4 H v 61 (by decide)
  · exact dockH_other tT4 H v 62 (by decide)
  · exact dockH_other tT4 H v 63 (by decide)
  · exact dockH_other tT4 H v 64 (by decide)
  · exact dockH_other tT4 H v 65 (by decide)
  · exact dockH_other tT4 H v 66 (by decide)
  · exact dockH_other tT4 H v 67 (by decide)
  · exact dockH_other tT4 H v 68 (by decide)
  · exact dockH_other tT4 H v 69 (by decide)
  · exact dockH_other tT4 H v 70 (by decide)
  · exact dockH_other tT4 H v 71 (by decide)
  · exact dockH_other tT4 H v 72 (by decide)
  · exact dockH_slot tT4 tT4_inj H v 30

def tT5 : Fin 23 → Fin 74 := ![53, 54, 56, 12, 13, 1, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73]

theorem tT5_inj : Function.Injective tT5 := by decide

theorem install_tT5 (A : Fin 74 → List Bool) (v : Fin 23 → List Bool) :
    install tT5 A v = ![A 0, v 5, A 2, A 3, A 4, A 5, A 6, A 7, A 8, A 9, A 10, A 11, v 3, v 4, A 14, A 15, A 16, A 17, A 18, A 19, A 20, A 21, A 22, A 23, A 24, A 25, A 26, A 27, A 28, A 29, A 30, A 31, A 32, A 33, A 34, A 35, A 36, A 37, A 38, A 39, A 40, A 41, A 42, A 43, A 44, A 45, A 46, A 47, A 48, A 49, A 50, A 51, A 52, v 0, v 1, A 55, v 2, v 6, v 7, v 8, v 9, v 10, v 11, v 12, v 13, v 14, v 15, v 16, v 17, v 18, v 19, v 20, v 21, v 22] := by
  funext i
  fin_cases i
  · exact install_other tT5 A v 0 (by decide)
  · exact install_slot tT5 tT5_inj A v 5
  · exact install_other tT5 A v 2 (by decide)
  · exact install_other tT5 A v 3 (by decide)
  · exact install_other tT5 A v 4 (by decide)
  · exact install_other tT5 A v 5 (by decide)
  · exact install_other tT5 A v 6 (by decide)
  · exact install_other tT5 A v 7 (by decide)
  · exact install_other tT5 A v 8 (by decide)
  · exact install_other tT5 A v 9 (by decide)
  · exact install_other tT5 A v 10 (by decide)
  · exact install_other tT5 A v 11 (by decide)
  · exact install_slot tT5 tT5_inj A v 3
  · exact install_slot tT5 tT5_inj A v 4
  · exact install_other tT5 A v 14 (by decide)
  · exact install_other tT5 A v 15 (by decide)
  · exact install_other tT5 A v 16 (by decide)
  · exact install_other tT5 A v 17 (by decide)
  · exact install_other tT5 A v 18 (by decide)
  · exact install_other tT5 A v 19 (by decide)
  · exact install_other tT5 A v 20 (by decide)
  · exact install_other tT5 A v 21 (by decide)
  · exact install_other tT5 A v 22 (by decide)
  · exact install_other tT5 A v 23 (by decide)
  · exact install_other tT5 A v 24 (by decide)
  · exact install_other tT5 A v 25 (by decide)
  · exact install_other tT5 A v 26 (by decide)
  · exact install_other tT5 A v 27 (by decide)
  · exact install_other tT5 A v 28 (by decide)
  · exact install_other tT5 A v 29 (by decide)
  · exact install_other tT5 A v 30 (by decide)
  · exact install_other tT5 A v 31 (by decide)
  · exact install_other tT5 A v 32 (by decide)
  · exact install_other tT5 A v 33 (by decide)
  · exact install_other tT5 A v 34 (by decide)
  · exact install_other tT5 A v 35 (by decide)
  · exact install_other tT5 A v 36 (by decide)
  · exact install_other tT5 A v 37 (by decide)
  · exact install_other tT5 A v 38 (by decide)
  · exact install_other tT5 A v 39 (by decide)
  · exact install_other tT5 A v 40 (by decide)
  · exact install_other tT5 A v 41 (by decide)
  · exact install_other tT5 A v 42 (by decide)
  · exact install_other tT5 A v 43 (by decide)
  · exact install_other tT5 A v 44 (by decide)
  · exact install_other tT5 A v 45 (by decide)
  · exact install_other tT5 A v 46 (by decide)
  · exact install_other tT5 A v 47 (by decide)
  · exact install_other tT5 A v 48 (by decide)
  · exact install_other tT5 A v 49 (by decide)
  · exact install_other tT5 A v 50 (by decide)
  · exact install_other tT5 A v 51 (by decide)
  · exact install_other tT5 A v 52 (by decide)
  · exact install_slot tT5 tT5_inj A v 0
  · exact install_slot tT5 tT5_inj A v 1
  · exact install_other tT5 A v 55 (by decide)
  · exact install_slot tT5 tT5_inj A v 2
  · exact install_slot tT5 tT5_inj A v 6
  · exact install_slot tT5 tT5_inj A v 7
  · exact install_slot tT5 tT5_inj A v 8
  · exact install_slot tT5 tT5_inj A v 9
  · exact install_slot tT5 tT5_inj A v 10
  · exact install_slot tT5 tT5_inj A v 11
  · exact install_slot tT5 tT5_inj A v 12
  · exact install_slot tT5 tT5_inj A v 13
  · exact install_slot tT5 tT5_inj A v 14
  · exact install_slot tT5 tT5_inj A v 15
  · exact install_slot tT5 tT5_inj A v 16
  · exact install_slot tT5 tT5_inj A v 17
  · exact install_slot tT5 tT5_inj A v 18
  · exact install_slot tT5 tT5_inj A v 19
  · exact install_slot tT5 tT5_inj A v 20
  · exact install_slot tT5 tT5_inj A v 21
  · exact install_slot tT5 tT5_inj A v 22

/-! ## The banks between the stages -/

/-- All heads at cell 0. -/
def topZ : Fin 74 → ℕ := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

/-- The capacities of the logs (`0` for every other tape). -/
def topCapv (cap cap2 cap3 cap4 cap5 capEnt capL : ℕ) : Fin 74 → ℕ :=
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, cap, cap2, cap3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, cap4, cap5, 0, 0, 0, 0, 0, 0, 0, 0, 0, capEnt, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, capL]

/-- The entry bank: the framed input record on tape 0, every other tape blank up to its capacity (the logs blank,
the work tapes empty). -/
def topA0 (R : C3Req) (cap cap2 cap3 cap4 cap5 capEnt capL : ℕ) : Fin 74 → List Bool :=
  fun j => if j.val = 0 then frame (c3Input a R) else ZeroPadding.pad (topCapv cap cap2 cap3 cap4 cap5 capEnt capL j) []

/-- After T1: the record and the fields. -/
def topA1 (R : C3Req) (cap cap2 cap3 cap4 cap5 capEnt capL : ℕ) : Fin 74 → List Bool :=
  ![frame (c3Input a R), [], c3Input a R, List.replicate R.P.Q true, List.replicate (shapeOf (R.D a)).flatten.length true, List.replicate R.m true, List.replicate R.P.h true, List.replicate (R.p + 1) true, List.replicate R.P.width true, (poolRecs a R.P.h R.P.gates R.P.side R.P.width R.P.flips).flatMap frame, Masks.tableTape (Masks.childTable R.P.Q (shapeOf (R.D a))) [], R.V.flatMap Poly.termRec ++ [false], frame (natWord R.dRow ++ natWord (R.p + 1)), frame (natWord R.P.width ++ MatrixScorePhi.columnsWord R.P.width R.cols), [], [], [], [], [], [], List.replicate cap false, List.replicate cap2 false, List.replicate cap3 false, [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], List.replicate cap4 false, List.replicate cap5 false, [], [], [], [], [], [], [], [], [], List.replicate capEnt false, [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], List.replicate capL false]

/-- After T2: the constant tapes. -/
def topA2 (R : C3Req) (cap cap2 cap3 cap4 cap5 capEnt capL : ℕ) : Fin 74 → List Bool :=
  ![frame (c3Input a R), [], c3Input a R, List.replicate R.P.Q true, List.replicate (shapeOf (R.D a)).flatten.length true, List.replicate R.m true, List.replicate R.P.h true, List.replicate (R.p + 1) true, List.replicate R.P.width true, (poolRecs a R.P.h R.P.gates R.P.side R.P.width R.P.flips).flatMap frame, Masks.tableTape (Masks.childTable R.P.Q (shapeOf (R.D a))) [], R.V.flatMap Poly.termRec ++ [false], frame (natWord R.dRow ++ natWord (R.p + 1)), frame (natWord R.P.width ++ MatrixScorePhi.columnsWord R.P.width R.cols), [], [], [], frame (Unions.zeroT R.P.Q (shapeOf (R.D a)).flatten.length), frame (Unions.zeroT R.P.Q (shapeOf (R.D a)).flatten.length), frame (Unions.zeroT R.P.Q (shapeOf (R.D a)).flatten.length), List.replicate cap false, List.replicate cap2 false, List.replicate cap3 false, frame (Unions.ew R.P.Q (shapeOf (R.D a)).flatten.length (0, 0)), [false], [], frame (Unions.zeroT R.P.Q (shapeOf (R.D a)).flatten.length), frame (Unions.zeroT R.P.Q (shapeOf (R.D a)).flatten.length), [false], [false], frame (SignedSortKey.binary R.m 0), [false], [], [false], [], frame (Unions.zeroT R.P.Q (shapeOf (R.D a)).flatten.length), frame (Unions.zeroT R.P.Q (shapeOf (R.D a)).flatten.length), frame (Unions.zeroT R.P.Q (shapeOf (R.D a)).flatten.length), frame (Unions.zeroT R.P.Q (shapeOf (R.D a)).flatten.length), frame (Unions.lastT R.P.Q (shapeOf (R.D a)).flatten.length), frame (Unions.levelT R.P.Q (shapeOf (R.D a)).flatten.length), frame (Unions.zeroT R.P.Q (shapeOf (R.D a)).flatten.length), [false], [], List.replicate cap4 false, List.replicate cap5 false, frame (List.replicate R.m true), [true], [true], frame (List.replicate (R.p + 1) false), Kit.streamTape (List.replicate (2 * (R.P.width + R.P.width + 1)) [true]) [], List.replicate (R.P.width + R.P.width) true, [false], [], [], List.replicate capEnt false, [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], List.replicate capL false]

/-- After: the groups and the compiler stages' registers. -/
def topA3 (R : C3Req) (cap cap2 cap3 cap4 cap5 capEnt capL : ℕ) : Fin 74 → List Bool :=
  ![frame (c3Input a R), [], c3Input a R, List.replicate R.P.Q true, List.replicate (shapeOf (R.D a)).flatten.length true, List.replicate R.m true, List.replicate R.P.h true, List.replicate (R.p + 1) true, List.replicate R.P.width true, (poolRecs a R.P.h R.P.gates R.P.side R.P.width R.P.flips).flatMap frame, Masks.tableTape (Masks.childTable R.P.Q (shapeOf (R.D a))) [], R.V.flatMap Poly.termRec ++ [false], frame (natWord R.dRow ++ natWord (R.p + 1)), frame (natWord R.P.width ++ MatrixScorePhi.columnsWord R.P.width R.cols), (stFin a R).ps.Ea, (stFin a R).ps.LA, (stFin a R).ps.LB, frame (stFin a R).ps.R, frame (stFin a R).ps.R2, frame (stFin a R).ps.R3, List.replicate cap false, List.replicate cap2 false, List.replicate cap3 false, frame (Unions.ew R.P.Q (shapeOf (R.D a)).flatten.length (0, 0)), Kit.streamTape (stFin a R).ps.G (stFin a R).ps.staleG, (stFin a R).ps.O, frame (stFin a R).ps.X, frame (stFin a R).ps.Y, [(stFin a R).ps.Ec], [false], frame (SignedSortKey.binary R.m (2 ^ R.m)), [(stFin a R).PJ], (stFin a R).CW, (stFin a R).Sp, (stFin a R).Op, frame (stFin a R).Gw, frame (stFin a R).Rp, frame (stFin a R).Zu, frame (stFin a R).Z2u, frame (Unions.lastT R.P.Q (shapeOf (R.D a)).flatten.length), frame (Unions.levelT R.P.Q (shapeOf (R.D a)).flatten.length), frame (Unions.zeroT R.P.Q (shapeOf (R.D a)).flatten.length), [(stFin a R).Cu], Poly.groupsRef R.P.Q (shapeOf (R.D a)) R.m R.V ++ [false], List.replicate cap4 false, List.replicate cap5 false, frame (List.replicate R.m true), [false], [true], frame (List.replicate (R.p + 1) false), Kit.streamTape (List.replicate (2 * (R.P.width + R.P.width + 1)) [true]) [], List.replicate (R.P.width + R.P.width) true, [false], [], [], List.replicate capEnt false, [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], List.replicate capL false]

/-- After T4: the cut stream, the count and the emit loop's registers `gf`. -/
def topA4 (R : C3Req) (cap cap2 cap3 cap4 cap5 capEnt capL : ℕ) (gf : Emit.GSt) : Fin 74 → List Bool :=
  ![frame (c3Input a R), [], c3Input a R, List.replicate R.P.Q true, List.replicate (shapeOf (R.D a)).flatten.length true, List.replicate R.m true, List.replicate R.P.h true, List.replicate (R.p + 1) true, List.replicate R.P.width true, (poolRecs a R.P.h R.P.gates R.P.side R.P.width R.P.flips).flatMap frame, Masks.tableTape (Masks.childTable R.P.Q (shapeOf (R.D a))) [], R.V.flatMap Poly.termRec ++ [false], frame (natWord R.dRow ++ natWord (R.p + 1)), frame (natWord R.P.width ++ MatrixScorePhi.columnsWord R.P.width R.cols), gf.rcb, gf.en.re, gf.en.s1, gf.en.rp, gf.en.rn, gf.en.rd, List.replicate cap false, List.replicate cap2 false, List.replicate cap3 false, frame (Unions.ew R.P.Q (shapeOf (R.D a)).flatten.length (0, 0)), Kit.streamTape (stFin a R).ps.G (stFin a R).ps.staleG, gf.en.s2, gf.en.rp1, gf.en.rc, [gf.rpar], [false], frame (SignedSortKey.binary R.m (2 ^ R.m)), [gf.en.pk], (stFin a R).CW, (stFin a R).Sp, (stFin a R).Op, frame (stFin a R).Gw, frame (stFin a R).Rp, frame (stFin a R).Zu, frame (stFin a R).Z2u, frame (Unions.lastT R.P.Q (shapeOf (R.D a)).flatten.length), frame (Unions.levelT R.P.Q (shapeOf (R.D a)).flatten.length), frame (Unions.zeroT R.P.Q (shapeOf (R.D a)).flatten.length), [gf.en.sc], Poly.groupsRef R.P.Q (shapeOf (R.D a)) R.m R.V ++ [false], List.replicate cap4 false, List.replicate cap5 false, frame (List.replicate R.m true), [gf.en.nz], [gf.en.sv], frame (List.replicate (R.p + 1) false), Kit.streamTape (List.replicate (2 * (R.P.width + R.P.width + 1)) [true]) [], List.replicate (R.P.width + R.P.width) true, [gf.en.snv], Kit.streamTape (sfRecs a R) [], List.replicate (cutsRefX (R.D a) (2 ^ R.P.h) R.m R.P.Q R.V).length true, List.replicate capEnt false, [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], List.replicate capL false]

noncomputable def tT1D := RecoveryFocus.machine tT1 loadM
noncomputable def tT2D := RecoveryFocus.machine tT2 initM
noncomputable def tT3D := RecoveryFocus.machine tT3 subsetsStageM
noncomputable def tT4D := RecoveryFocus.machine tT4 emitStageM
noncomputable def tT5D := RecoveryFocus.machine tT5 hdrM

/-- **The C3 v2 machine** (before the final reset): the five stages in order. -/
noncomputable def topM := Composition.machine (Composition.machine (Composition.machine (Composition.machine tT1D tT2D)
  tT3D) tT4D) tT5D

/-! ## The stages on the common layout -/

theorem top_t1 (R : C3Req) (cap cap2 cap3 cap4 cap5 capEnt capL : ℕ) (hL1 : 2 * (c3Input a R).length + 1 ≤ capL)
    (hL1b : loadChainCost (List.replicate R.P.Q true) (List.replicate (shapeOf (R.D a)).flatten.length true) (List.replicate R.m true) (List.replicate R.P.h true) (List.replicate (R.p + 1) true) (List.replicate R.P.width true) ((poolRecs a R.P.h R.P.gates R.P.side R.P.width R.P.flips).flatMap frame) (Masks.tableTape (Masks.childTable R.P.Q (shapeOf (R.D a))) []) (R.V.flatMap Poly.termRec ++ [false]) (frame (natWord R.dRow ++ natWord (R.p + 1))) (frame (natWord R.P.width ++ MatrixScorePhi.columnsWord R.P.width R.cols)) ≤ capL) :
    Step tT1D (loadCost (List.replicate R.P.Q true) (List.replicate (shapeOf (R.D a)).flatten.length true) (List.replicate R.m true) (List.replicate R.P.h true) (List.replicate (R.p + 1) true) (List.replicate R.P.width true) ((poolRecs a R.P.h R.P.gates R.P.side R.P.width R.P.flips).flatMap frame) (Masks.tableTape (Masks.childTable R.P.Q (shapeOf (R.D a))) []) (R.V.flatMap Poly.termRec ++ [false]) (frame (natWord R.dRow ++ natWord (R.p + 1))) (frame (natWord R.P.width ++ MatrixScorePhi.columnsWord R.P.width R.cols))) topZ (topA0 a R cap cap2 cap3 cap4 cap5 capEnt capL) topZ (topA1 a R cap cap2 cap3 cap4 cap5 capEnt capL) := by
  have s := dockRun (load_run (List.replicate R.P.Q true) (List.replicate (shapeOf (R.D a)).flatten.length true) (List.replicate R.m true) (List.replicate R.P.h true) (List.replicate (R.p + 1) true) (List.replicate R.P.width true) ((poolRecs a R.P.h R.P.gates R.P.side R.P.width R.P.flips).flatMap frame) (Masks.tableTape (Masks.childTable R.P.Q (shapeOf (R.D a))) []) (R.V.flatMap Poly.termRec ++ [false]) (frame (natWord R.dRow ++ natWord (R.p + 1))) (frame (natWord R.P.width ++ MatrixScorePhi.columnsWord R.P.width R.cols)) capL hL1 hL1b) tT1 tT1_inj topZ (topA0 a R cap cap2 cap3 cap4 cap5 capEnt capL)
    (by intro j; fin_cases j <;> rfl) (by intro j; fin_cases j <;> rfl)
  rw [install_tT1, dockH_tT1] at s
  exact s.congr rfl rfl

theorem top_t2 (R : C3Req) (hQ : 1 ≤ R.P.Q) (cap cap2 cap3 cap4 cap5 capEnt capL : ℕ)
    (hL2 : initCost (R.P.Q - 1) (shapeOf (R.D a)).flatten.length R.m (R.p + 1) R.P.width ≤ capL) :
    Step tT2D (initCost (R.P.Q - 1) (shapeOf (R.D a)).flatten.length R.m (R.p + 1) R.P.width) topZ (topA1 a R cap cap2 cap3 cap4 cap5 capEnt capL) topZ
      (topA2 a R cap cap2 cap3 cap4 cap5 capEnt capL) := by
  have e2 := init_run (R.P.Q - 1) (shapeOf (R.D a)).flatten.length R.m (R.p + 1) R.P.width capL hL2
  have hq : R.P.Q - 1 + 1 = R.P.Q := by omega
  rw [hq, ← binary_zero R.m] at e2
  have s := dockRun e2 tT2 tT2_inj topZ (topA1 a R cap cap2 cap3 cap4 cap5 capEnt capL)
    (by intro j; fin_cases j <;> rfl) (by intro j; fin_cases j <;> rfl)
  rw [install_tT2, dockH_tT2] at s
  exact s.congr rfl rfl

theorem top_t3 (R : C3Req) (hR : R.Pre a) (cap cap2 cap3 cap4 cap5 capEnt capL : ℕ) (hcaps : SubCaps a R cap cap2 cap3 cap4 cap5)
    (hL3 : subsetsCost a R + 1 + 1 ≤ capL) :
    Step tT3D (2 * (subsetsCost a R + 1 + 1) + 2) topZ (topA2 a R cap cap2 cap3 cap4 cap5 capEnt capL) topZ
      (topA3 a R cap cap2 cap3 cap4 cap5 capEnt capL) := by
  have s := dockRun (subsets_stage a R hR cap cap2 cap3 cap4 cap5 capL hcaps hL3) tT3 tT3_inj topZ (topA2 a R cap cap2 cap3 cap4 cap5 capEnt capL)
    (by intro j; fin_cases j <;> rfl) (by intro j; fin_cases j <;> rfl)
  rw [install_tT3, dockH_tT3] at s
  exact s.congr rfl rfl

theorem top_t4 (R : C3Req) (hR : R.Pre a) (cap cap2 cap3 cap4 cap5 capEnt capL : ℕ)
    (hcap1 : 2 * (R.p + 1) + 1 ≤ cap) (hcapL : 2 * (R.P.h * R.P.Q * R.d) + 1 + 1 + (1 + 1 + 1) ≤ cap)
    (hcapE : 2 * (R.P.Q + (poolChildren a R.P.gates R.P.flips).length + 1) + 1 ≤ cap)
    (hcapS : appendCost 0 (2 * (R.P.width + R.P.width + 1)) 1 ≤ cap)
    (hA1 : mergeAllCost (2 * (R.P.width + R.P.width + 1)) (1 + (poolChildren a R.P.gates R.P.flips).length * R.P.h) R.P.h ≤ cap2)
    (hA2 : skipCost (2 * (R.P.width + R.P.width + 1)) (1 + (poolChildren a R.P.gates R.P.flips).length * R.P.h) R.P.h ≤ cap2)
    (hC : appendCost 0 (2 * (R.P.width + R.P.width + 1)) (1 + (poolChildren a R.P.gates R.P.flips).length * R.P.h + R.P.h) ≤ cap3)
    (hcut0 : cut0Cost (R.p + 1) (R.P.h * R.P.Q * R.d) (R.P.width + R.P.width) ≤ cap4)
    (hcut1 : cut1Cost (R.p + 1) (R.P.h * R.P.Q * R.d) (R.P.width + R.P.width) ≤ cap4)
    (hcoef : coefRawCost R.P.Q (R.p + 1) R.p ≤ cap5)
    (hent : entryCost R.P.Q (R.p + 1) (poolChildren a R.P.gates R.P.flips).length R.P.h R.P.width (R.P.h * R.P.Q * R.d) R.p ≤ capEnt)
    (hL4 : emitCostR a R + 1 + 1 ≤ capL) :
    ∃ gf, Step tT4D (2 * (emitCostR a R + 1 + 1) + 2) topZ (topA3 a R cap cap2 cap3 cap4 cap5 capEnt capL) topZ
      (topA4 a R cap cap2 cap3 cap4 cap5 capEnt capL gf) := by
  obtain ⟨gf, e4⟩ := emit_stage a R hR (gInit a R) rfl rfl cap cap2 cap3 cap4 cap5 capEnt capL hcap1 hcapL hcapE hcapS hA1 hA2 hC hcut0 hcut1 hcoef hent hL4
  rw [words_stream] at e4
  refine ⟨gf, ?_⟩
  have s := dockRun e4 tT4 tT4_inj topZ (topA3 a R cap cap2 cap3 cap4 cap5 capEnt capL)
    (by intro j; fin_cases j <;> rfl) (by intro j; fin_cases j <;> rfl)
  rw [install_tT4, dockH_tT4] at s
  exact s.congr rfl rfl

theorem top_t5 (R : C3Req) (cap cap2 cap3 cap4 cap5 capEnt capL : ℕ) (gf : Emit.GSt)
    (hL5 : w2Cost [true, true] [] (cutsRefX (R.D a) (2 ^ R.P.h) R.m R.P.Q R.V).length ≤ capL) :
    ∃ Hf Af, Step tT5D (hdrCost (sfRecs a R) (R.p + 2) (cutsRefX (R.D a) (2 ^ R.P.h) R.m R.P.Q R.V).length (natWord R.dRow ++ natWord (R.p + 1)) (natWord R.P.width ++ MatrixScorePhi.columnsWord R.P.width R.cols)) topZ
      (topA4 a R cap cap2 cap3 cap4 cap5 capEnt capL gf) Hf Af ∧ Af 1 = reqWord R.dRow (R.p + 1) R.P.width R.cols (c3v2Ref a R) := by
  obtain ⟨Hf, Af, e5, hAf⟩ := header_run (sfRecs a R) (R.p + 2) (cutsRefX (R.D a) (2 ^ R.P.h) R.m R.P.Q R.V).length (sfRecs_ne a R) (sfRecs_len a R)
    (natWord R.dRow ++ natWord (R.p + 1)) (natWord R.P.width ++ MatrixScorePhi.columnsWord R.P.width R.cols) capL hL5
  have s := dockRun e5 tT5 tT5_inj topZ (topA4 a R cap cap2 cap3 cap4 cap5 capEnt capL gf)
    (by intro j; fin_cases j <;> rfl) (by intro j; fin_cases j <;> rfl)
  rw [install_tT5] at s
  refine ⟨_, _, s, ?_⟩
  show Af 5 = _
  rw [hAf, req_word]

/-- The cost of the five stages. -/
def topCost (R : C3Req) : ℕ :=
  loadCost (List.replicate R.P.Q true) (List.replicate (shapeOf (R.D a)).flatten.length true) (List.replicate R.m true) (List.replicate R.P.h true) (List.replicate (R.p + 1) true) (List.replicate R.P.width true) ((poolRecs a R.P.h R.P.gates R.P.side R.P.width R.P.flips).flatMap frame) (Masks.tableTape (Masks.childTable R.P.Q (shapeOf (R.D a))) []) (R.V.flatMap Poly.termRec ++ [false]) (frame (natWord R.dRow ++ natWord (R.p + 1))) (frame (natWord R.P.width ++ MatrixScorePhi.columnsWord R.P.width R.cols)) + 1 +
    initCost (R.P.Q - 1) (shapeOf (R.D a)).flatten.length R.m (R.p + 1) R.P.width + 1 + (2 * (subsetsCost a R + 1 + 1) + 2) + 1 +
    (2 * (emitCostR a R + 1 + 1) + 2) + 1 +
    hdrCost (sfRecs a R) (R.p + 2) (cutsRefX (R.D a) (2 ^ R.P.h) R.m R.P.Q R.V).length (natWord R.dRow ++ natWord (R.p + 1)) (natWord R.P.width ++ MatrixScorePhi.columnsWord R.P.width R.cols)

/-- **The whole machine on one request**: the output tape holds the printer request's word of C3 v2's reference. -/
theorem top_run (R : C3Req) (hR : R.Pre a) (cap cap2 cap3 cap4 cap5 capEnt capL : ℕ)
    (hcaps : SubCaps a R cap cap2 cap3 cap4 cap5)
    (hcap1 : 2 * (R.p + 1) + 1 ≤ cap) (hcapL : 2 * (R.P.h * R.P.Q * R.d) + 1 + 1 + (1 + 1 + 1) ≤ cap)
    (hcapE : 2 * (R.P.Q + (poolChildren a R.P.gates R.P.flips).length + 1) + 1 ≤ cap)
    (hcapS : appendCost 0 (2 * (R.P.width + R.P.width + 1)) 1 ≤ cap)
    (hA1 : mergeAllCost (2 * (R.P.width + R.P.width + 1)) (1 + (poolChildren a R.P.gates R.P.flips).length * R.P.h) R.P.h ≤ cap2)
    (hA2 : skipCost (2 * (R.P.width + R.P.width + 1)) (1 + (poolChildren a R.P.gates R.P.flips).length * R.P.h) R.P.h ≤ cap2)
    (hC : appendCost 0 (2 * (R.P.width + R.P.width + 1)) (1 + (poolChildren a R.P.gates R.P.flips).length * R.P.h + R.P.h) ≤ cap3)
    (hcut0 : cut0Cost (R.p + 1) (R.P.h * R.P.Q * R.d) (R.P.width + R.P.width) ≤ cap4)
    (hcut1 : cut1Cost (R.p + 1) (R.P.h * R.P.Q * R.d) (R.P.width + R.P.width) ≤ cap4)
    (hcoef : coefRawCost R.P.Q (R.p + 1) R.p ≤ cap5)
    (hent : entryCost R.P.Q (R.p + 1) (poolChildren a R.P.gates R.P.flips).length R.P.h R.P.width (R.P.h * R.P.Q * R.d) R.p ≤ capEnt)
    (hL1 : 2 * (c3Input a R).length + 1 ≤ capL) (hL1b : loadChainCost (List.replicate R.P.Q true) (List.replicate (shapeOf (R.D a)).flatten.length true) (List.replicate R.m true) (List.replicate R.P.h true) (List.replicate (R.p + 1) true) (List.replicate R.P.width true) ((poolRecs a R.P.h R.P.gates R.P.side R.P.width R.P.flips).flatMap frame) (Masks.tableTape (Masks.childTable R.P.Q (shapeOf (R.D a))) []) (R.V.flatMap Poly.termRec ++ [false]) (frame (natWord R.dRow ++ natWord (R.p + 1))) (frame (natWord R.P.width ++ MatrixScorePhi.columnsWord R.P.width R.cols)) ≤ capL)
    (hL2 : initCost (R.P.Q - 1) (shapeOf (R.D a)).flatten.length R.m (R.p + 1) R.P.width ≤ capL)
    (hL3 : subsetsCost a R + 1 + 1 ≤ capL) (hL4 : emitCostR a R + 1 + 1 ≤ capL)
    (hL5 : w2Cost [true, true] [] (cutsRefX (R.D a) (2 ^ R.P.h) R.m R.P.Q R.V).length ≤ capL) :
    ∃ Hf Af, Step topM (topCost a R) topZ (topA0 a R cap cap2 cap3 cap4 cap5 capEnt capL) Hf Af ∧
      Af 1 = reqWord R.dRow (R.p + 1) R.P.width R.cols (c3v2Ref a R) := by
  obtain ⟨gf, t4⟩ := top_t4 a R hR cap cap2 cap3 cap4 cap5 capEnt capL hcap1 hcapL hcapE hcapS hA1 hA2 hC hcut0 hcut1 hcoef hent hL4
  obtain ⟨Hf, Af, t5, hAf⟩ := top_t5 a R cap cap2 cap3 cap4 cap5 capEnt capL gf hL5
  exact ⟨Hf, Af, ((((top_t1 a R cap cap2 cap3 cap4 cap5 capEnt capL hL1 hL1b).seq (top_t2 a R hR.2.2.1 cap cap2 cap3 cap4 cap5 capEnt capL hL2)).seq
    (top_t3 a R hR cap cap2 cap3 cap4 cap5 capEnt capL hcaps hL3)).seq t4).seq t5, hAf⟩


end NearCubicWires.WireExponent3_5.CompilerMachine.Top
