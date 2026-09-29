import Proof.Wire_3_5.Compiler.MachineTopEmit

/-! # C3 v2 top level, T5: the printer request's word (P3:1728-1737)

Paper: the separable printer reads the request "`d`, `p`, the gate count, the weight count and the columns of `φ`,
then the cuts" (base's `MatrixScoreBatch.word = header ++ cuts.flatMap (cutWord p)`), with the cuts "the two successor
cuts `1[E_i=0] = 1[E_i≥0] − 1[E_i≥1]`" (P3:1728-1731). The emit stage leaves the cut words (a stream of framed
signed fields) and one count mark per stacked occurrence; the request's gate count is twice that (two successor cuts
per occurrence). This stage writes the request word on a fresh output tape: the first header part (`natWord dRow ++
natWord (p+1)`, unframed from its input field), `natWord` of the doubled count (base's `EquationHeaderAppend`: a
unary count to its canonical header), the second header part (`natWord width ++ columnsWord width cols`), then the
cut words frame by frame (`copyFrames_run`). Layout of 23 tapes: 0 the cut stream, 1 the count, 2 the doubled count,
3 and 4 the framed header parts, 5 the output, 6–21 the header writer's scratch, 22 the log. **`header_run`**. The
paper quantity is the printer's request word. Main declarations: `unframeStep`, `copyFramesM`, **`copyFrames_run`**,
`hdrM`, `hdrCost`, **`header_run`**. -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.CompilerMachine.Top
open NearCubicWires NearCubicWires.WireExponent3_5.CompilerMachine NearCubicWires.WireExponent3_5.CompilerMachine.Pool
open NearCubicWires.WireExponent3_5.CompilerMachine.Kit
open NearCubicWires.WireExponent3_5.Block NearCubicWires.WireExponent3_5.GF2
open NearCubicWires.RepairRepresentation
open NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary.RecoveryRootRound NearCubicWires.BlockPlatform
open NearCubicWires.RepairOrdinary.StablePartition.Workspace (overlay overlay_write overlay_length)

/-- **Unframe** (base's `GeneratedAmplifier.Copy`): the content of the framed field at the source cursor is appended
at the output cursor. -/
theorem unframeStep (pre bits tail out : List Bool) :
    Step GeneratedAmplifier.Copy.machine (2 * bits.length + 1) ![pre.length, out.length] ![pre ++ frame bits ++ tail, out]
      ![pre.length + 2 * bits.length + 1, (out ++ bits).length] ![pre ++ frame bits ++ tail, out ++ bits] := by
  obtain ⟨r, hr, hf, hs⟩ := GeneratedAmplifier.Copy.copy_run pre bits tail out
  exact ⟨r, hr, by rw [hf]; rfl, by rw [hf]; rfl, hs.le⟩

/-- A whole framed field is appended at the output cursor. -/
theorem unframeWhole (bits out : List Bool) :
    Step GeneratedAmplifier.Copy.machine (2 * bits.length + 1) ![0, out.length] ![frame bits, out]
      ![2 * bits.length + 1, (out ++ bits).length] ![frame bits, out ++ bits] := by
  have h := unframeStep [] bits [] out
  simp only [List.nil_append, List.append_nil, List.length_nil, Nat.zero_add] at h
  exact h

/-! ## Copying a stream of frames -/

/-- Copy one frame, then step past its terminator. -/
noncomputable def cfBodyM := Composition.machine CopyO.machine (RecoveryFocus.machine w0 moveM)

/-- **The frame copier**: every frame of the stream is appended to the output. -/
noncomputable def copyFramesM := StreamController.machine cfBodyM 0

theorem foldl_frames (rs : List (List Bool)) :
    ∀ o : List Bool, rs.foldl (fun o r => o ++ frame r) o = o ++ rs.flatMap frame := by
  induction rs with
  | nil => intro o; simp
  | cons r rs ih => intro o; rw [List.foldl_cons, ih]; simp

/-- **The frame copier runs**: a stream of nonempty records of one length `L` is appended frame by frame. -/
theorem copyFrames_run (rs : List (List Bool)) (L : ℕ) (hne : ∀ r ∈ rs, r ≠ []) (hlen : ∀ r ∈ rs, r.length = L)
    (O0 : List Bool) :
    Step copyFramesM (rs.length * ((2 * L + 1) + 1 + 1 + 2) + 1) ![0, O0.length] ![Kit.streamTape rs [], O0]
      ![(rs.flatMap frame).length, (O0 ++ rs.flatMap frame).length]
      ![Kit.streamTape rs [], O0 ++ rs.flatMap frame] := by
  have h := streamRun cfBodyM 0 rs [] hne (fun o r => o ++ frame r) O0
    (fun o p => ![p, o.length]) (fun o => ![Kit.streamTape rs [], overlay o []]) (fun _ => rfl) (fun _ _ => rfl)
    ((2 * L + 1) + 1 + 1) (by
      intro j hj
      have hsplit := streamTape_split rs [] j hj
      have e1 := copyStep ((rs.take j).flatMap frame) rs[j] ((rs.drop (j + 1)).flatMap frame ++ false :: [])
        ((rs.take j).foldl (fun o r => o ++ frame r) O0) []
      rw [← hsplit] at e1
      have e2 := dockRun (moveStep (Kit.streamTape rs []) (((rs.take j).flatMap frame).length + 2 * rs[j].length)) w0
        w0_inj ![((rs.take j).flatMap frame).length + 2 * rs[j].length,
          ((rs.take j).foldl (fun o r => o ++ frame r) O0).length + (2 * rs[j].length + 1)]
        ![Kit.streamTape rs [], overlay ((rs.take j).foldl (fun o r => o ++ frame r) O0 ++ frame rs[j]) []]
        (by intro k; fin_cases k; rfl) (by intro k; fin_cases k; rfl)
      rw [install_w0, dockH_w0] at e2
      have j2 := e1.seq (e2.congr rfl rfl)
      have hL := hlen _ (List.getElem_mem hj)
      have hst : (rs.take (j + 1)).foldl (fun o r => o ++ frame r) O0 =
          (rs.take j).foldl (fun o r => o ++ frame r) O0 ++ frame rs[j] := by
        rw [List.take_add_one, List.getElem?_eq_getElem hj, Option.toList_some, List.foldl_append]; rfl
      rw [hst]
      refine (j2.congr ?_ rfl).enlarge (le_of_eq (by rw [hL]))
      funext k; fin_cases k
      · show ((rs.take j).flatMap frame).length + 2 * rs[j].length + 1 = off rs (j + 1)
        rw [off_succ rs j hj]; rfl
      · show ((rs.take j).foldl (fun o r => o ++ frame r) O0).length + (2 * rs[j].length + 1) =
          ((rs.take j).foldl (fun o r => o ++ frame r) O0 ++ frame rs[j]).length
        rw [List.length_append, frame_length])
  refine (h.congr_in ?_ ?_).congr ?_ ?_
  · funext k; fin_cases k <;> rfl
  · funext k; fin_cases k
    · rfl
    · show overlay O0 [] = O0; rw [overlay_nil_right]
  · funext k; fin_cases k
    · rfl
    · show (rs.foldl (fun o r => o ++ frame r) O0).length = (O0 ++ rs.flatMap frame).length; rw [foldl_frames]
  · funext k; fin_cases k
    · rfl
    · show overlay (rs.foldl (fun o r => o ++ frame r) O0) [] = O0 ++ rs.flatMap frame
      rw [foldl_frames, overlay_nil_right]

/-! ## The request word -/

def hRaw : Fin (2 + 1) → Fin 23 := ![1, 2, 22]
def hU1 : Fin 2 → Fin 23 := ![3, 5]
def hEHA : Fin 18 → Fin 23 := ![2, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 5]
def hU2 : Fin 2 → Fin 23 := ![4, 5]
def hCF : Fin 2 → Fin 23 := ![0, 5]

theorem hRaw_inj : Function.Injective hRaw := by decide

theorem install_hRaw (A : Fin 23 → List Bool) (v : Fin 3 → List Bool) :
    install hRaw A v = ![A 0, v 0, v 1, A 3, A 4, A 5, A 6, A 7, A 8, A 9, A 10, A 11, A 12, A 13, A 14, A 15, A 16, A 17, A 18, A 19, A 20, A 21, v 2] := by
  funext i
  fin_cases i
  · exact install_other hRaw A v 0 (by decide)
  · exact install_slot hRaw hRaw_inj A v 0
  · exact install_slot hRaw hRaw_inj A v 1
  · exact install_other hRaw A v 3 (by decide)
  · exact install_other hRaw A v 4 (by decide)
  · exact install_other hRaw A v 5 (by decide)
  · exact install_other hRaw A v 6 (by decide)
  · exact install_other hRaw A v 7 (by decide)
  · exact install_other hRaw A v 8 (by decide)
  · exact install_other hRaw A v 9 (by decide)
  · exact install_other hRaw A v 10 (by decide)
  · exact install_other hRaw A v 11 (by decide)
  · exact install_other hRaw A v 12 (by decide)
  · exact install_other hRaw A v 13 (by decide)
  · exact install_other hRaw A v 14 (by decide)
  · exact install_other hRaw A v 15 (by decide)
  · exact install_other hRaw A v 16 (by decide)
  · exact install_other hRaw A v 17 (by decide)
  · exact install_other hRaw A v 18 (by decide)
  · exact install_other hRaw A v 19 (by decide)
  · exact install_other hRaw A v 20 (by decide)
  · exact install_other hRaw A v 21 (by decide)
  · exact install_slot hRaw hRaw_inj A v 2

theorem dockH_hRaw (H : Fin 23 → ℕ) (v : Fin 3 → ℕ) :
    dockH hRaw H v = ![H 0, v 0, v 1, H 3, H 4, H 5, H 6, H 7, H 8, H 9, H 10, H 11, H 12, H 13, H 14, H 15, H 16, H 17, H 18, H 19, H 20, H 21, v 2] := by
  funext i
  fin_cases i
  · exact dockH_other hRaw H v 0 (by decide)
  · exact dockH_slot hRaw hRaw_inj H v 0
  · exact dockH_slot hRaw hRaw_inj H v 1
  · exact dockH_other hRaw H v 3 (by decide)
  · exact dockH_other hRaw H v 4 (by decide)
  · exact dockH_other hRaw H v 5 (by decide)
  · exact dockH_other hRaw H v 6 (by decide)
  · exact dockH_other hRaw H v 7 (by decide)
  · exact dockH_other hRaw H v 8 (by decide)
  · exact dockH_other hRaw H v 9 (by decide)
  · exact dockH_other hRaw H v 10 (by decide)
  · exact dockH_other hRaw H v 11 (by decide)
  · exact dockH_other hRaw H v 12 (by decide)
  · exact dockH_other hRaw H v 13 (by decide)
  · exact dockH_other hRaw H v 14 (by decide)
  · exact dockH_other hRaw H v 15 (by decide)
  · exact dockH_other hRaw H v 16 (by decide)
  · exact dockH_other hRaw H v 17 (by decide)
  · exact dockH_other hRaw H v 18 (by decide)
  · exact dockH_other hRaw H v 19 (by decide)
  · exact dockH_other hRaw H v 20 (by decide)
  · exact dockH_other hRaw H v 21 (by decide)
  · exact dockH_slot hRaw hRaw_inj H v 2

theorem hU1_inj : Function.Injective hU1 := by decide

theorem install_hU1 (A : Fin 23 → List Bool) (v : Fin 2 → List Bool) :
    install hU1 A v = ![A 0, A 1, A 2, v 0, A 4, v 1, A 6, A 7, A 8, A 9, A 10, A 11, A 12, A 13, A 14, A 15, A 16, A 17, A 18, A 19, A 20, A 21, A 22] := by
  funext i
  fin_cases i
  · exact install_other hU1 A v 0 (by decide)
  · exact install_other hU1 A v 1 (by decide)
  · exact install_other hU1 A v 2 (by decide)
  · exact install_slot hU1 hU1_inj A v 0
  · exact install_other hU1 A v 4 (by decide)
  · exact install_slot hU1 hU1_inj A v 1
  · exact install_other hU1 A v 6 (by decide)
  · exact install_other hU1 A v 7 (by decide)
  · exact install_other hU1 A v 8 (by decide)
  · exact install_other hU1 A v 9 (by decide)
  · exact install_other hU1 A v 10 (by decide)
  · exact install_other hU1 A v 11 (by decide)
  · exact install_other hU1 A v 12 (by decide)
  · exact install_other hU1 A v 13 (by decide)
  · exact install_other hU1 A v 14 (by decide)
  · exact install_other hU1 A v 15 (by decide)
  · exact install_other hU1 A v 16 (by decide)
  · exact install_other hU1 A v 17 (by decide)
  · exact install_other hU1 A v 18 (by decide)
  · exact install_other hU1 A v 19 (by decide)
  · exact install_other hU1 A v 20 (by decide)
  · exact install_other hU1 A v 21 (by decide)
  · exact install_other hU1 A v 22 (by decide)

theorem dockH_hU1 (H : Fin 23 → ℕ) (v : Fin 2 → ℕ) :
    dockH hU1 H v = ![H 0, H 1, H 2, v 0, H 4, v 1, H 6, H 7, H 8, H 9, H 10, H 11, H 12, H 13, H 14, H 15, H 16, H 17, H 18, H 19, H 20, H 21, H 22] := by
  funext i
  fin_cases i
  · exact dockH_other hU1 H v 0 (by decide)
  · exact dockH_other hU1 H v 1 (by decide)
  · exact dockH_other hU1 H v 2 (by decide)
  · exact dockH_slot hU1 hU1_inj H v 0
  · exact dockH_other hU1 H v 4 (by decide)
  · exact dockH_slot hU1 hU1_inj H v 1
  · exact dockH_other hU1 H v 6 (by decide)
  · exact dockH_other hU1 H v 7 (by decide)
  · exact dockH_other hU1 H v 8 (by decide)
  · exact dockH_other hU1 H v 9 (by decide)
  · exact dockH_other hU1 H v 10 (by decide)
  · exact dockH_other hU1 H v 11 (by decide)
  · exact dockH_other hU1 H v 12 (by decide)
  · exact dockH_other hU1 H v 13 (by decide)
  · exact dockH_other hU1 H v 14 (by decide)
  · exact dockH_other hU1 H v 15 (by decide)
  · exact dockH_other hU1 H v 16 (by decide)
  · exact dockH_other hU1 H v 17 (by decide)
  · exact dockH_other hU1 H v 18 (by decide)
  · exact dockH_other hU1 H v 19 (by decide)
  · exact dockH_other hU1 H v 20 (by decide)
  · exact dockH_other hU1 H v 21 (by decide)
  · exact dockH_other hU1 H v 22 (by decide)

theorem hEHA_inj : Function.Injective hEHA := by decide

theorem install_hEHA (A : Fin 23 → List Bool) (v : Fin 18 → List Bool) :
    install hEHA A v = ![A 0, A 1, v 0, A 3, A 4, v 17, v 1, v 2, v 3, v 4, v 5, v 6, v 7, v 8, v 9, v 10, v 11, v 12, v 13, v 14, v 15, v 16, A 22] := by
  funext i
  fin_cases i
  · exact install_other hEHA A v 0 (by decide)
  · exact install_other hEHA A v 1 (by decide)
  · exact install_slot hEHA hEHA_inj A v 0
  · exact install_other hEHA A v 3 (by decide)
  · exact install_other hEHA A v 4 (by decide)
  · exact install_slot hEHA hEHA_inj A v 17
  · exact install_slot hEHA hEHA_inj A v 1
  · exact install_slot hEHA hEHA_inj A v 2
  · exact install_slot hEHA hEHA_inj A v 3
  · exact install_slot hEHA hEHA_inj A v 4
  · exact install_slot hEHA hEHA_inj A v 5
  · exact install_slot hEHA hEHA_inj A v 6
  · exact install_slot hEHA hEHA_inj A v 7
  · exact install_slot hEHA hEHA_inj A v 8
  · exact install_slot hEHA hEHA_inj A v 9
  · exact install_slot hEHA hEHA_inj A v 10
  · exact install_slot hEHA hEHA_inj A v 11
  · exact install_slot hEHA hEHA_inj A v 12
  · exact install_slot hEHA hEHA_inj A v 13
  · exact install_slot hEHA hEHA_inj A v 14
  · exact install_slot hEHA hEHA_inj A v 15
  · exact install_slot hEHA hEHA_inj A v 16
  · exact install_other hEHA A v 22 (by decide)

theorem dockH_hEHA (H : Fin 23 → ℕ) (v : Fin 18 → ℕ) :
    dockH hEHA H v = ![H 0, H 1, v 0, H 3, H 4, v 17, v 1, v 2, v 3, v 4, v 5, v 6, v 7, v 8, v 9, v 10, v 11, v 12, v 13, v 14, v 15, v 16, H 22] := by
  funext i
  fin_cases i
  · exact dockH_other hEHA H v 0 (by decide)
  · exact dockH_other hEHA H v 1 (by decide)
  · exact dockH_slot hEHA hEHA_inj H v 0
  · exact dockH_other hEHA H v 3 (by decide)
  · exact dockH_other hEHA H v 4 (by decide)
  · exact dockH_slot hEHA hEHA_inj H v 17
  · exact dockH_slot hEHA hEHA_inj H v 1
  · exact dockH_slot hEHA hEHA_inj H v 2
  · exact dockH_slot hEHA hEHA_inj H v 3
  · exact dockH_slot hEHA hEHA_inj H v 4
  · exact dockH_slot hEHA hEHA_inj H v 5
  · exact dockH_slot hEHA hEHA_inj H v 6
  · exact dockH_slot hEHA hEHA_inj H v 7
  · exact dockH_slot hEHA hEHA_inj H v 8
  · exact dockH_slot hEHA hEHA_inj H v 9
  · exact dockH_slot hEHA hEHA_inj H v 10
  · exact dockH_slot hEHA hEHA_inj H v 11
  · exact dockH_slot hEHA hEHA_inj H v 12
  · exact dockH_slot hEHA hEHA_inj H v 13
  · exact dockH_slot hEHA hEHA_inj H v 14
  · exact dockH_slot hEHA hEHA_inj H v 15
  · exact dockH_slot hEHA hEHA_inj H v 16
  · exact dockH_other hEHA H v 22 (by decide)

theorem hU2_inj : Function.Injective hU2 := by decide

theorem install_hU2 (A : Fin 23 → List Bool) (v : Fin 2 → List Bool) :
    install hU2 A v = ![A 0, A 1, A 2, A 3, v 0, v 1, A 6, A 7, A 8, A 9, A 10, A 11, A 12, A 13, A 14, A 15, A 16, A 17, A 18, A 19, A 20, A 21, A 22] := by
  funext i
  fin_cases i
  · exact install_other hU2 A v 0 (by decide)
  · exact install_other hU2 A v 1 (by decide)
  · exact install_other hU2 A v 2 (by decide)
  · exact install_other hU2 A v 3 (by decide)
  · exact install_slot hU2 hU2_inj A v 0
  · exact install_slot hU2 hU2_inj A v 1
  · exact install_other hU2 A v 6 (by decide)
  · exact install_other hU2 A v 7 (by decide)
  · exact install_other hU2 A v 8 (by decide)
  · exact install_other hU2 A v 9 (by decide)
  · exact install_other hU2 A v 10 (by decide)
  · exact install_other hU2 A v 11 (by decide)
  · exact install_other hU2 A v 12 (by decide)
  · exact install_other hU2 A v 13 (by decide)
  · exact install_other hU2 A v 14 (by decide)
  · exact install_other hU2 A v 15 (by decide)
  · exact install_other hU2 A v 16 (by decide)
  · exact install_other hU2 A v 17 (by decide)
  · exact install_other hU2 A v 18 (by decide)
  · exact install_other hU2 A v 19 (by decide)
  · exact install_other hU2 A v 20 (by decide)
  · exact install_other hU2 A v 21 (by decide)
  · exact install_other hU2 A v 22 (by decide)

theorem dockH_hU2 (H : Fin 23 → ℕ) (v : Fin 2 → ℕ) :
    dockH hU2 H v = ![H 0, H 1, H 2, H 3, v 0, v 1, H 6, H 7, H 8, H 9, H 10, H 11, H 12, H 13, H 14, H 15, H 16, H 17, H 18, H 19, H 20, H 21, H 22] := by
  funext i
  fin_cases i
  · exact dockH_other hU2 H v 0 (by decide)
  · exact dockH_other hU2 H v 1 (by decide)
  · exact dockH_other hU2 H v 2 (by decide)
  · exact dockH_other hU2 H v 3 (by decide)
  · exact dockH_slot hU2 hU2_inj H v 0
  · exact dockH_slot hU2 hU2_inj H v 1
  · exact dockH_other hU2 H v 6 (by decide)
  · exact dockH_other hU2 H v 7 (by decide)
  · exact dockH_other hU2 H v 8 (by decide)
  · exact dockH_other hU2 H v 9 (by decide)
  · exact dockH_other hU2 H v 10 (by decide)
  · exact dockH_other hU2 H v 11 (by decide)
  · exact dockH_other hU2 H v 12 (by decide)
  · exact dockH_other hU2 H v 13 (by decide)
  · exact dockH_other hU2 H v 14 (by decide)
  · exact dockH_other hU2 H v 15 (by decide)
  · exact dockH_other hU2 H v 16 (by decide)
  · exact dockH_other hU2 H v 17 (by decide)
  · exact dockH_other hU2 H v 18 (by decide)
  · exact dockH_other hU2 H v 19 (by decide)
  · exact dockH_other hU2 H v 20 (by decide)
  · exact dockH_other hU2 H v 21 (by decide)
  · exact dockH_other hU2 H v 22 (by decide)

theorem hCF_inj : Function.Injective hCF := by decide

theorem install_hCF (A : Fin 23 → List Bool) (v : Fin 2 → List Bool) :
    install hCF A v = ![v 0, A 1, A 2, A 3, A 4, v 1, A 6, A 7, A 8, A 9, A 10, A 11, A 12, A 13, A 14, A 15, A 16, A 17, A 18, A 19, A 20, A 21, A 22] := by
  funext i
  fin_cases i
  · exact install_slot hCF hCF_inj A v 0
  · exact install_other hCF A v 1 (by decide)
  · exact install_other hCF A v 2 (by decide)
  · exact install_other hCF A v 3 (by decide)
  · exact install_other hCF A v 4 (by decide)
  · exact install_slot hCF hCF_inj A v 1
  · exact install_other hCF A v 6 (by decide)
  · exact install_other hCF A v 7 (by decide)
  · exact install_other hCF A v 8 (by decide)
  · exact install_other hCF A v 9 (by decide)
  · exact install_other hCF A v 10 (by decide)
  · exact install_other hCF A v 11 (by decide)
  · exact install_other hCF A v 12 (by decide)
  · exact install_other hCF A v 13 (by decide)
  · exact install_other hCF A v 14 (by decide)
  · exact install_other hCF A v 15 (by decide)
  · exact install_other hCF A v 16 (by decide)
  · exact install_other hCF A v 17 (by decide)
  · exact install_other hCF A v 18 (by decide)
  · exact install_other hCF A v 19 (by decide)
  · exact install_other hCF A v 20 (by decide)
  · exact install_other hCF A v 21 (by decide)
  · exact install_other hCF A v 22 (by decide)

theorem dockH_hCF (H : Fin 23 → ℕ) (v : Fin 2 → ℕ) :
    dockH hCF H v = ![v 0, H 1, H 2, H 3, H 4, v 1, H 6, H 7, H 8, H 9, H 10, H 11, H 12, H 13, H 14, H 15, H 16, H 17, H 18, H 19, H 20, H 21, H 22] := by
  funext i
  fin_cases i
  · exact dockH_slot hCF hCF_inj H v 0
  · exact dockH_other hCF H v 1 (by decide)
  · exact dockH_other hCF H v 2 (by decide)
  · exact dockH_other hCF H v 3 (by decide)
  · exact dockH_other hCF H v 4 (by decide)
  · exact dockH_slot hCF hCF_inj H v 1
  · exact dockH_other hCF H v 6 (by decide)
  · exact dockH_other hCF H v 7 (by decide)
  · exact dockH_other hCF H v 8 (by decide)
  · exact dockH_other hCF H v 9 (by decide)
  · exact dockH_other hCF H v 10 (by decide)
  · exact dockH_other hCF H v 11 (by decide)
  · exact dockH_other hCF H v 12 (by decide)
  · exact dockH_other hCF H v 13 (by decide)
  · exact dockH_other hCF H v 14 (by decide)
  · exact dockH_other hCF H v 15 (by decide)
  · exact dockH_other hCF H v 16 (by decide)
  · exact dockH_other hCF H v 17 (by decide)
  · exact dockH_other hCF H v 18 (by decide)
  · exact dockH_other hCF H v 19 (by decide)
  · exact dockH_other hCF H v 20 (by decide)
  · exact dockH_other hCF H v 21 (by decide)
  · exact dockH_other hCF H v 22 (by decide)


noncomputable def hRawD := RecoveryFocus.machine hRaw (w2RM [true, true] [])
noncomputable def hU1D := RecoveryFocus.machine hU1 GeneratedAmplifier.Copy.machine
noncomputable def hEHAD := RecoveryFocus.machine hEHA EquationHeaderAppend.machine
noncomputable def hU2D := RecoveryFocus.machine hU2 GeneratedAmplifier.Copy.machine
noncomputable def hCFD := RecoveryFocus.machine hCF copyFramesM

/-- The request writer: double the count, the first header part, the gate count, the second part, the cuts. -/
noncomputable def hdrM := Composition.machine (Composition.machine (Composition.machine (Composition.machine hRawD hU1D)
  hEHAD) hU2D) hCFD

/-- The request writer's cost. -/
def hdrCost (rs : List (List Bool)) (L n : ℕ) (h1 h2 : List Bool) : ℕ :=
  (2 * w2Cost [true, true] [] n + 2) + 1 + (2 * h1.length + 1) + 1 + EquationHeaderAppend.budget (n + n) + 1 +
    (2 * h2.length + 1) + 1 + (rs.length * ((2 * L + 1) + 1 + 1 + 2) + 1)

/-- **The printer request's word** (T5): from the cut stream, the count `1^n` and the two framed header parts, the
output tape holds `h1 ++ natWord (n + n) ++ h2 ++ (the cut frames)`. -/
theorem header_run (rs : List (List Bool)) (L n : ℕ) (hne : ∀ r ∈ rs, r ≠ []) (hlen : ∀ r ∈ rs, r.length = L)
    (h1 h2 : List Bool) (cap : ℕ) (hcap : w2Cost [true, true] [] n ≤ cap) :
    ∃ Hf Af, Step hdrM (hdrCost rs L n h1 h2) ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
      ![Kit.streamTape rs [], List.replicate n true, [], frame h1, frame h2, [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], List.replicate cap false] Hf Af ∧
      Af 5 = h1 ++ natWord (n + n) ++ h2 ++ rs.flatMap frame := by
  obtain ⟨act, hrun, ht17, hh17, _, _, _⟩ := EquationHeaderAppend.append_run (n + n) h1
  have eh : Step EquationHeaderAppend.machine (EquationHeaderAppend.budget (n + n)) (EquationHeaderAppend.heads h1)
      (EquationHeaderAppend.tapes (n + n) h1) act.final.heads act.final.tapes := Step.of_run hrun rfl rfl
  have s1 := dockRun (w2_run [true, true] [] n cap hcap (List.replicate (n + n) true) (raw2_word n)) hRaw hRaw_inj
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    ![Kit.streamTape rs [], List.replicate n true, [], frame h1, frame h2, [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], List.replicate cap false]
    (by intro j; fin_cases j <;> rfl) (by intro j; fin_cases j <;> rfl)
  rw [install_hRaw, dockH_hRaw] at s1
  have t1 : Step hRawD (2 * w2Cost [true, true] [] n + 2) ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
      ![Kit.streamTape rs [], List.replicate n true, [], frame h1, frame h2, [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], List.replicate cap false]
      ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
      ![Kit.streamTape rs [], List.replicate n true, List.replicate (n + n) true, frame h1, frame h2, [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], List.replicate cap false] := s1.congr rfl rfl
  have s2 := dockRun (unframeWhole h1 []) hU1 hU1_inj ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    ![Kit.streamTape rs [], List.replicate n true, List.replicate (n + n) true, frame h1, frame h2, [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], List.replicate cap false]
    (by intro j; fin_cases j <;> rfl) (by intro j; fin_cases j <;> rfl)
  rw [install_hU1, dockH_hU1] at s2
  have t2 : Step hU1D (2 * h1.length + 1) ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
      ![Kit.streamTape rs [], List.replicate n true, List.replicate (n + n) true, frame h1, frame h2, [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], List.replicate cap false]
      ![0, 0, 0, 2 * h1.length + 1, 0, h1.length, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
      ![Kit.streamTape rs [], List.replicate n true, List.replicate (n + n) true, frame h1, frame h2, h1, [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], List.replicate cap false] := s2.congr rfl rfl
  have s3 := dockRun eh hEHA hEHA_inj ![0, 0, 0, 2 * h1.length + 1, 0, h1.length, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    ![Kit.streamTape rs [], List.replicate n true, List.replicate (n + n) true, frame h1, frame h2, h1, [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], List.replicate cap false]
    (by intro j; fin_cases j <;> rfl) (by intro j; fin_cases j <;> rfl)
  rw [install_hEHA, dockH_hEHA, ht17, hh17] at s3
  have t3 : Step hEHAD (EquationHeaderAppend.budget (n + n)) ![0, 0, 0, 2 * h1.length + 1, 0, h1.length, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
      ![Kit.streamTape rs [], List.replicate n true, List.replicate (n + n) true, frame h1, frame h2, h1, [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], List.replicate cap false]
      ![0, 0, act.final.heads 0, 2 * h1.length + 1, 0, (h1 ++ natWord (n + n)).length, act.final.heads 1, act.final.heads 2, act.final.heads 3, act.final.heads 4, act.final.heads 5, act.final.heads 6, act.final.heads 7, act.final.heads 8, act.final.heads 9, act.final.heads 10, act.final.heads 11, act.final.heads 12, act.final.heads 13, act.final.heads 14, act.final.heads 15, act.final.heads 16, 0]
      ![Kit.streamTape rs [], List.replicate n true, act.final.tapes 0, frame h1, frame h2, h1 ++ natWord (n + n), act.final.tapes 1, act.final.tapes 2, act.final.tapes 3, act.final.tapes 4, act.final.tapes 5, act.final.tapes 6, act.final.tapes 7, act.final.tapes 8, act.final.tapes 9, act.final.tapes 10, act.final.tapes 11, act.final.tapes 12, act.final.tapes 13, act.final.tapes 14, act.final.tapes 15, act.final.tapes 16, List.replicate cap false] := s3.congr rfl rfl
  have s4 := dockRun (unframeWhole h2 (h1 ++ natWord (n + n))) hU2 hU2_inj ![0, 0, act.final.heads 0, 2 * h1.length + 1, 0, (h1 ++ natWord (n + n)).length, act.final.heads 1, act.final.heads 2, act.final.heads 3, act.final.heads 4, act.final.heads 5, act.final.heads 6, act.final.heads 7, act.final.heads 8, act.final.heads 9, act.final.heads 10, act.final.heads 11, act.final.heads 12, act.final.heads 13, act.final.heads 14, act.final.heads 15, act.final.heads 16, 0]
    ![Kit.streamTape rs [], List.replicate n true, act.final.tapes 0, frame h1, frame h2, h1 ++ natWord (n + n), act.final.tapes 1, act.final.tapes 2, act.final.tapes 3, act.final.tapes 4, act.final.tapes 5, act.final.tapes 6, act.final.tapes 7, act.final.tapes 8, act.final.tapes 9, act.final.tapes 10, act.final.tapes 11, act.final.tapes 12, act.final.tapes 13, act.final.tapes 14, act.final.tapes 15, act.final.tapes 16, List.replicate cap false]
    (by intro j; fin_cases j <;> rfl) (by intro j; fin_cases j <;> rfl)
  rw [install_hU2, dockH_hU2] at s4
  have t4 : Step hU2D (2 * h2.length + 1) ![0, 0, act.final.heads 0, 2 * h1.length + 1, 0, (h1 ++ natWord (n + n)).length, act.final.heads 1, act.final.heads 2, act.final.heads 3, act.final.heads 4, act.final.heads 5, act.final.heads 6, act.final.heads 7, act.final.heads 8, act.final.heads 9, act.final.heads 10, act.final.heads 11, act.final.heads 12, act.final.heads 13, act.final.heads 14, act.final.heads 15, act.final.heads 16, 0]
      ![Kit.streamTape rs [], List.replicate n true, act.final.tapes 0, frame h1, frame h2, h1 ++ natWord (n + n), act.final.tapes 1, act.final.tapes 2, act.final.tapes 3, act.final.tapes 4, act.final.tapes 5, act.final.tapes 6, act.final.tapes 7, act.final.tapes 8, act.final.tapes 9, act.final.tapes 10, act.final.tapes 11, act.final.tapes 12, act.final.tapes 13, act.final.tapes 14, act.final.tapes 15, act.final.tapes 16, List.replicate cap false]
      ![0, 0, act.final.heads 0, 2 * h1.length + 1, 2 * h2.length + 1, (h1 ++ natWord (n + n) ++ h2).length, act.final.heads 1, act.final.heads 2, act.final.heads 3, act.final.heads 4, act.final.heads 5, act.final.heads 6, act.final.heads 7, act.final.heads 8, act.final.heads 9, act.final.heads 10, act.final.heads 11, act.final.heads 12, act.final.heads 13, act.final.heads 14, act.final.heads 15, act.final.heads 16, 0]
      ![Kit.streamTape rs [], List.replicate n true, act.final.tapes 0, frame h1, frame h2, h1 ++ natWord (n + n) ++ h2, act.final.tapes 1, act.final.tapes 2, act.final.tapes 3, act.final.tapes 4, act.final.tapes 5, act.final.tapes 6, act.final.tapes 7, act.final.tapes 8, act.final.tapes 9, act.final.tapes 10, act.final.tapes 11, act.final.tapes 12, act.final.tapes 13, act.final.tapes 14, act.final.tapes 15, act.final.tapes 16, List.replicate cap false] := s4.congr rfl rfl
  have s5 := dockRun (copyFrames_run rs L hne hlen (h1 ++ natWord (n + n) ++ h2)) hCF hCF_inj ![0, 0, act.final.heads 0, 2 * h1.length + 1, 2 * h2.length + 1, (h1 ++ natWord (n + n) ++ h2).length, act.final.heads 1, act.final.heads 2, act.final.heads 3, act.final.heads 4, act.final.heads 5, act.final.heads 6, act.final.heads 7, act.final.heads 8, act.final.heads 9, act.final.heads 10, act.final.heads 11, act.final.heads 12, act.final.heads 13, act.final.heads 14, act.final.heads 15, act.final.heads 16, 0]
    ![Kit.streamTape rs [], List.replicate n true, act.final.tapes 0, frame h1, frame h2, h1 ++ natWord (n + n) ++ h2, act.final.tapes 1, act.final.tapes 2, act.final.tapes 3, act.final.tapes 4, act.final.tapes 5, act.final.tapes 6, act.final.tapes 7, act.final.tapes 8, act.final.tapes 9, act.final.tapes 10, act.final.tapes 11, act.final.tapes 12, act.final.tapes 13, act.final.tapes 14, act.final.tapes 15, act.final.tapes 16, List.replicate cap false]
    (by intro j; fin_cases j <;> rfl) (by intro j; fin_cases j <;> rfl)
  rw [install_hCF, dockH_hCF] at s5
  have t5 : Step hCFD (rs.length * ((2 * L + 1) + 1 + 1 + 2) + 1) ![0, 0, act.final.heads 0, 2 * h1.length + 1, 2 * h2.length + 1, (h1 ++ natWord (n + n) ++ h2).length, act.final.heads 1, act.final.heads 2, act.final.heads 3, act.final.heads 4, act.final.heads 5, act.final.heads 6, act.final.heads 7, act.final.heads 8, act.final.heads 9, act.final.heads 10, act.final.heads 11, act.final.heads 12, act.final.heads 13, act.final.heads 14, act.final.heads 15, act.final.heads 16, 0]
      ![Kit.streamTape rs [], List.replicate n true, act.final.tapes 0, frame h1, frame h2, h1 ++ natWord (n + n) ++ h2, act.final.tapes 1, act.final.tapes 2, act.final.tapes 3, act.final.tapes 4, act.final.tapes 5, act.final.tapes 6, act.final.tapes 7, act.final.tapes 8, act.final.tapes 9, act.final.tapes 10, act.final.tapes 11, act.final.tapes 12, act.final.tapes 13, act.final.tapes 14, act.final.tapes 15, act.final.tapes 16, List.replicate cap false]
      ![(rs.flatMap frame).length, 0, act.final.heads 0, 2 * h1.length + 1, 2 * h2.length + 1, (h1 ++ natWord (n + n) ++ h2 ++ rs.flatMap frame).length, act.final.heads 1, act.final.heads 2, act.final.heads 3, act.final.heads 4, act.final.heads 5, act.final.heads 6, act.final.heads 7, act.final.heads 8, act.final.heads 9, act.final.heads 10, act.final.heads 11, act.final.heads 12, act.final.heads 13, act.final.heads 14, act.final.heads 15, act.final.heads 16, 0]
      ![Kit.streamTape rs [], List.replicate n true, act.final.tapes 0, frame h1, frame h2, h1 ++ natWord (n + n) ++ h2 ++ rs.flatMap frame, act.final.tapes 1, act.final.tapes 2, act.final.tapes 3, act.final.tapes 4, act.final.tapes 5, act.final.tapes 6, act.final.tapes 7, act.final.tapes 8, act.final.tapes 9, act.final.tapes 10, act.final.tapes 11, act.final.tapes 12, act.final.tapes 13, act.final.tapes 14, act.final.tapes 15, act.final.tapes 16, List.replicate cap false] := s5.congr rfl rfl
  exact ⟨_, _, (((t1.seq t2).seq t3).seq t4).seq t5, rfl⟩


end NearCubicWires.WireExponent3_5.CompilerMachine.Top
