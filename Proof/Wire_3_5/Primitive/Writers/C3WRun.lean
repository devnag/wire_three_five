import Proof.Wire_3_5.Primitive.Writers.C3WInner

/-! # C3 request writer, part 13: the writer's run (`C3ReqIface.C3Run`)

Paper quantity: `frame PRE`, `frame POST` of alg:compiler's request (P3:1886-1906), from `frame req.word` and the
numbers `h`, `Q'`, `m`, `pr`, every other tape a residue within the budget. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace NearCubicWires.WireExponent3_5.PrimAsm.C3Mach
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary.RecoveryRootRound NearCubicWires.BlockPlatform NearCubicWires.WireExponent3_5
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimAsm NearCubicWires.WireExponent3_5.PrimAsm.DockW
open NearCubicWires.WireExponent3_5.PrimAsm.C3Phase NearCubicWires.WireExponent3_5.PrimAsm.C3Dock
open NearCubicWires.WireExponent3_5.PrimAsm.C3Asm
open NearCubicWires.WireExponent3_5.ListMachine NearCubicWires.WireExponent3_5.ListMachine.Row
open NearCubicWires.RepairRepresentation (natWord)

namespace Wr5
variable (P : Wr5) (Dv Cv : ℕ) {sA Ua : ℕ} (pA : Machine Ua sA) (iA oA : Fin Ua)

theorem steps_len {t s n' : ℕ} {p : Machine t s} {hi ho : Fin t → ℕ} {ti tf : Fin t → List Bool}
    (h : Step p n' hi ti ho tf) (i : Fin t) (k : ℕ) (hh : hi i ≤ k) (ht : (ti i).length ≤ k) :
    (tf i).length ≤ k + n' := by
  obtain ⟨r, hr, _, hT, _⟩ := h
  have := DecompositionSource.one_tape_support p n' ⟨p.start, hi, ti⟩ r i k hr hh ht
  rw [hT] at this
  omega

/-- **The C3 request writer's run** (`C3ReqIface.C3Run`): `frame PRE` on `sPRE`, `frame POST` on `sPOST`, the request
and the numbers kept, every head at `0`, the residues within the budget. -/
theorem c3_run (w sfx : List Bool) (n h Q m pr : ℕ) (hw : w = natWord n ++ sfx)
    (GF SF WF FF CF : List Bool) (BG BS BW BF BC : ℕ)
    (rG : WriterIfaceJ.WriterRun P.G.M BG P.G.inS P.G.outS w GF)
    (rS : WriterIfaceJ.WriterRun P.S.M BS P.S.inS P.S.outS w SF)
    (rW : WriterIfaceJ.WriterRun P.W.M BW P.W.inS P.W.outS w WF)
    (rF : WriterIfaceJ.WriterRun P.F.M BF P.F.inS P.F.outS w FF)
    (rC : WriterIfaceJ.WriterRun P.C.M BC P.C.inS P.C.outS w CF)
    (g wd wd' : ℕ) (gyr sy : List Bool) (flips : List (List Bool)) (cols : List ℕ)
    (hGF : GF = frame (natWord g ++ gyr)) (hSF : SF = frame sy) (hWF : WF = List.replicate wd true)
    (hne : ∀ f ∈ flips, f ≠ []) (hFF : FF = flips.flatMap frame ++ [false])
    (hCF : CF = frame (natWord wd' ++ cols.flatMap fun x => frame (SignedSortKey.binary wd' x)))
    (hio : iA ≠ oA) (nA : ℕ) (tA : Fin Ua → List Bool)
    (hA : Step pA nA (fun _ => 0) (fun j => if j = iA then frame (CompilerMachine.Top.loadRec
      (List.replicate n true) (frame (natWord g ++ gyr)) (frame sy) (List.replicate wd true)
      (flips.flatMap frame ++ [false]) (List.replicate h true) (List.replicate Q true) [] [] [] []) else [])
      (fun _ => 0) tA)
    (ys : List (List Bool)) (atoms : List (List (List Bool))) (hys : ∀ y ∈ ys, y ≠ [])
    (hat : ∀ E ∈ atoms, ∀ y ∈ E, y ≠ []) (hout : tA oA = ys.flatMap frame ++ false :: atomsStream atoms)
    (hatl : atoms.length = flips.length * g)
    (hpoly : wd + g + 4 * wd' + 2 + cols.length + 1 + 2 ^ (natBitLength g + 1) + 2 ^ (natBitLength wd' + 1) +
      21 * cols.length + 61 ≤ UnaryCalc.value Dv Cv n) (Bud : ℕ)
    (hB : 2 * P.runCost Dv Cv (Ua := Ua) w n h Q m pr BG BS BW BF BC wd g wd' cols.length
          (flips.flatMap frame).length flips.length (natWord g ++ gyr).length sy.length nA (ys.flatMap frame).length
          (atomsStream atoms).length (atoms.map List.length).sum
          (natWord wd' ++ cols.flatMap fun x => frame (SignedSortKey.binary wd' x)).length + 2 ≤ Bud) :
    PrimT.C3ReqIface.C3Run (P.c3M Dv Cv pA iA oA) Bud (P.port Dv Cv cIN) (P.port Dv Cv sH) (P.port Dv Cv sQ)
      (P.port Dv Cv sM) (P.port Dv Cv sP) (P.port Dv Cv sPRE) (P.port Dv Cv sPOST) w h Q m pr
      ([List.replicate Q true, List.replicate (atoms.map List.length).sum true, List.replicate m true,
        List.replicate h true, List.replicate (pr + 1) true, List.replicate wd true, ys.flatMap frame,
        atomsStream atoms].flatMap frame)
      ([frame (natWord cols.length ++ natWord (pr + 1)),
        frame (natWord wd' ++ cols.flatMap fun x => frame (SignedSortKey.binary wd' x))].flatMap frame) := by
  obtain ⟨τ, m', R, si, hpre, hpost, hin, hH, hQ, hM, hP⟩ := P.inner_run Dv Cv pA iA oA w sfx n h Q m pr hw
    GF SF WF FF CF BG BS BW BF BC rG rS rW rF rC g wd wd' gyr sy flips cols hGF hSF hWF hne hFF hCF hio nA tA hA
    ys atoms hys hat hout hatl hpoly
  obtain ⟨mm, sm⟩ := maskBlank si (fun _ => true) (fun _ _ => rfl) 0
  set Tf : Fin ((P.lay Ua Dv Cv).U + 1) → List Bool := Fin.addCases
    ((P.lay Ua Dv Cv).gBank (2 * (P.lay Ua Dv Cv).fillW n h Q m pr + 2) (rs τ) m' R)
    (fun _ : Fin 1 => List.replicate mm false) with hTf
  have e1 : (Fin.addCases (fun _ : Fin (P.lay Ua Dv Cv).U => 0) (fun _ : Fin 1 => 0) :
      Fin ((P.lay Ua Dv Cv).U + 1) → ℕ) = fun _ => 0 := by
    funext i; refine Fin.addCases (fun a => ?_) (fun u => ?_) i <;> simp
  have e3 : (Fin.addCases (fun i => if (fun _ => true) i = true then 0 else (P.lay Ua Dv Cv).gHead (rs τ) i)
      (fun _ : Fin 1 => 0) : Fin ((P.lay Ua Dv Cv).U + 1) → ℕ) = fun _ => 0 := by
    funext i; refine Fin.addCases (fun a => ?_) (fun u => ?_) i <;> simp
  have hstep : Step (P.c3M Dv Cv pA iA oA) Bud (fun _ => 0)
      (PrimT.C3ReqIface.c3In (P.port Dv Cv cIN) (P.port Dv Cv sH) (P.port Dv Cv sQ) (P.port Dv Cv sM)
        (P.port Dv Cv sP) w h Q m pr) (fun _ => 0) Tf :=
    ((sm.congr_in e1 (P.entry_ext Dv Cv w h Q m pr)).congr e3 rfl).enlarge hB
  have hp : ∀ a b : Fin (CN + 1), (P.port Dv Cv (Ua := Ua) a = P.port Dv Cv b) = (a = b) :=
    fun a b => propext ⟨fun h => P.port_inj Dv Cv h, fun h => h ▸ rfl⟩
  have Tport : ∀ s, Tf (P.port Dv Cv s) = τ.st s := by
    intro s
    rw [hTf]
    unfold Wr5.port
    dsimp only
    rw [Fin.addCases_left]
    unfold Lay.ws
    rw [Lay.gBank_wm, wenc_A_s]
    rfl
  let isP : Fin ((P.lay Ua Dv Cv).U + 1) → Prop := fun j => j = P.port Dv Cv cIN ∨ j = P.port Dv Cv sH ∨
    j = P.port Dv Cv sQ ∨ j = P.port Dv Cv sM ∨ j = P.port Dv Cv sP ∨ j = P.port Dv Cv sPRE ∨ j = P.port Dv Cv sPOST
  refine ⟨fun j => if isP j then [] else Tf j, ?_, ?_⟩
  · intro j
    by_cases hj : isP j
    · simp only [hj, if_true, List.length_nil]; omega
    · simp only [hj, if_false]
      have h0 : (PrimT.C3ReqIface.c3In (P.port Dv Cv cIN) (P.port Dv Cv sH) (P.port Dv Cv sQ) (P.port Dv Cv sM)
          (P.port Dv Cv sP) w h Q m pr j).length ≤ 0 := by
        unfold PrimT.C3ReqIface.c3In
        have n1 : j ≠ P.port Dv Cv cIN := fun e => hj (Or.inl e)
        have n2 : j ≠ P.port Dv Cv sH := fun e => hj (Or.inr (Or.inl e))
        have n3 : j ≠ P.port Dv Cv sQ := fun e => hj (Or.inr (Or.inr (Or.inl e)))
        have n4 : j ≠ P.port Dv Cv sM := fun e => hj (Or.inr (Or.inr (Or.inr (Or.inl e))))
        have n5 : j ≠ P.port Dv Cv sP := fun e => hj (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl e)))))
        simp [n1, n2, n3, n4, n5]
      have := steps_len hstep j 0 (le_refl _) h0
      omega
  · have eo : Tf = PrimT.C3ReqIface.c3Out (P.port Dv Cv cIN) (P.port Dv Cv sH) (P.port Dv Cv sQ)
        (P.port Dv Cv sM) (P.port Dv Cv sP) (P.port Dv Cv sPRE) (P.port Dv Cv sPOST) w h Q m pr
        ([List.replicate Q true, List.replicate (atoms.map List.length).sum true, List.replicate m true,
          List.replicate h true, List.replicate (pr + 1) true, List.replicate wd true, ys.flatMap frame,
          atomsStream atoms].flatMap frame)
        ([frame (natWord cols.length ++ natWord (pr + 1)),
          frame (natWord wd' ++ cols.flatMap fun x => frame (SignedSortKey.binary wd' x))].flatMap frame)
        (fun j => if isP j then [] else Tf j) := by
      funext j
      unfold PrimT.C3ReqIface.c3Out
      by_cases j1 : j = P.port Dv Cv sPRE
      · subst j1; rw [if_pos rfl, Tport, hpre, pre_word]
      · rw [if_neg j1]
        by_cases j2 : j = P.port Dv Cv sPOST
        · subst j2; rw [if_pos rfl, Tport, hpost, post_word]
        · rw [if_neg j2]
          by_cases j3 : j = P.port Dv Cv cIN ∨ j = P.port Dv Cv sH ∨ j = P.port Dv Cv sQ ∨ j = P.port Dv Cv sM ∨
              j = P.port Dv Cv sP
          · rw [if_pos j3]
            unfold PrimT.C3ReqIface.c3In
            rcases j3 with rfl | rfl | rfl | rfl | rfl
            · rw [Tport, hin]; rfl
            · rw [Tport, hH]; rfl
            · rw [Tport, hQ]; rfl
            · rw [Tport, hM]; rfl
            · rw [Tport, hP]; rfl
          · rw [if_neg j3]
            have hj : ¬ isP j := by
              rintro (e | e | e | e | e | e | e)
              · exact j3 (Or.inl e)
              · exact j3 (Or.inr (Or.inl e))
              · exact j3 (Or.inr (Or.inr (Or.inl e)))
              · exact j3 (Or.inr (Or.inr (Or.inr (Or.inl e))))
              · exact j3 (Or.inr (Or.inr (Or.inr (Or.inr e))))
              · exact j1 e
              · exact j2 e
            simp only [hj, if_false]
    rw [← eo]
    obtain ⟨r, hr, hH', hT, hs⟩ := hstep
    exact ⟨r, hr, hT, fun i => by rw [hH'], hs⟩

end Wr5

end NearCubicWires.WireExponent3_5.PrimAsm.C3Mach
