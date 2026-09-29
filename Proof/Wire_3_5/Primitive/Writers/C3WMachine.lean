import Proof.Wire_3_5.Primitive.Writers.C3WC3a
import Proof.Wire_3_5.Primitive.SeedFix.C3ReqIface

/-! # C3 request writer, part 11: the machine and its entry bank

Paper quantity: none (the machine of alg:compiler's request writer, P3:1886-1906). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace NearCubicWires.WireExponent3_5.PrimAsm.C3Mach
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary.RecoveryRootRound NearCubicWires.BlockPlatform NearCubicWires.WireExponent3_5
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimAsm NearCubicWires.WireExponent3_5.PrimAsm.DockW
open NearCubicWires.WireExponent3_5.PrimAsm.C3Phase NearCubicWires.WireExponent3_5.PrimAsm.C3Dock

/-- The entry streams: `frame w` on `cIN` and the four unary numbers. -/
def stIn (w : List Bool) (h Q m pr : ℕ) : Fin (CN + 1) → List Bool := fun s =>
  if s = cIN then frame w else if s = sH then List.replicate h true else if s = sQ then List.replicate Q true
  else if s = sM then List.replicate m true else if s = sP then List.replicate pr true else []

namespace Wr5
variable (P : Wr5) (Dv Cv : ℕ) {sA Ua : ℕ} (pA : Machine Ua sA) (iA oA : Fin Ua)

/-- **The C3 request writer before its teardown**: the front, the writers, the fill and the first program, C3a′,
the second program's two phases. -/
noncomputable def innerM :=
  Composition.machine (Composition.machine (Composition.machine (Composition.machine (Composition.machine
    (P.lay Ua Dv Cv).frontM (P.wrM Ua Dv Cv))
    (TapeEmbedding.machine (P.lay Ua Dv Cv).X (phM (Prog.seq fillC wm1.toProg))))
    (RecoveryFocus.machine (portSl iA oA ((P.lay Ua Dv Cv).ws sAIN) ((P.lay Ua Dv Cv).ws sAOUT) (P.lay Ua Dv Cv).oA
      (P.lay Ua Dv Cv).hA) pA))
    (TapeEmbedding.machine (P.lay Ua Dv Cv).X (phM wm2a.toProg)))
    (TapeEmbedding.machine (P.lay Ua Dv Cv).X (phM wm2b.toProg))

/-- **The C3 request writer** (every head back at `0`). -/
noncomputable def c3M := MaskedReset.machine (P.innerM Dv Cv pA iA oA) (fun _ => true)

/-- A port of the writer: a stream tape. -/
def port (s : Fin (CN + 1)) : Fin ((P.lay Ua Dv Cv).U + 1) := Fin.castAdd 1 ((P.lay Ua Dv Cv).ws s)

theorem port_val (s : Fin (CN + 1)) :
    (P.port Dv Cv (Ua := Ua) s).val = if s.val = 0 then 0 else s.val + 1 := rfl

theorem port_inj {a b : Fin (CN + 1)} (h : P.port Dv Cv (Ua := Ua) a = P.port Dv Cv b) : a = b :=
  (P.lay Ua Dv Cv).ws_inj (Fin.castAdd_injective _ _ h)

/-- **The writer as a `C3Stage`**: the request on `cIN`, the numbers on `sH`, `sQ`, `sM`, `sP`, `PRE` on `sPRE`,
`POST` on `sPOST`. -/
noncomputable def stage : PrimT.C3ReqIface.C3Stage :=
  ⟨(P.lay Ua Dv Cv).U + 1, _, P.c3M Dv Cv pA iA oA, P.port Dv Cv cIN, P.port Dv Cv sH, P.port Dv Cv sQ,
    P.port Dv Cv sM, P.port Dv Cv sP, P.port Dv Cv sPRE, P.port Dv Cv sPOST,
    List.Nodup.of_map Fin.val (by show [0, 5, 6, 7, 8, 9, 10].Nodup; decide)⟩

/-- The inner machine's entry bank. -/
def entry (w : List Bool) (h Q m pr : ℕ) : Fin (P.lay Ua Dv Cv).U → List Bool := fun i =>
  PrimT.C3ReqIface.c3In (P.port Dv Cv cIN) (P.port Dv Cv sH) (P.port Dv Cv sQ) (P.port Dv Cv sM) (P.port Dv Cv sP) w h Q m pr
    (Fin.castAdd 1 i)

theorem entry_ext (w : List Bool) (h Q m pr : ℕ) :
    (Fin.addCases (P.entry Dv Cv w h Q m pr) (fun _ : Fin 1 => List.replicate 0 false) :
      Fin ((P.lay Ua Dv Cv).U + 1) → List Bool) =
    PrimT.C3ReqIface.c3In (P.port Dv Cv cIN) (P.port Dv Cv sH) (P.port Dv Cv sQ) (P.port Dv Cv sM) (P.port Dv Cv sP)
      w h Q m pr := by
  funext i
  refine Fin.addCases (fun j => ?_) (fun u => ?_) i
  · rw [Fin.addCases_left]; rfl
  · rw [Fin.addCases_right]
    have hv : (Fin.natAdd (P.lay Ua Dv Cv).U u).val = (P.lay Ua Dv Cv).U := by
      simp only [Fin.val_natAdd]; rw [Subsingleton.elim u 0]; rfl
    have hWT : WT = 64 := rfl
    have hX := (P.lay Ua Dv Cv).X_ge
    have hU : (P.lay Ua Dv Cv).U = WT + 1 + (P.lay Ua Dv Cv).X := rfl
    have ne : ∀ s : Fin (CN + 1), Fin.natAdd (P.lay Ua Dv Cv).U u ≠ P.port Dv Cv s := by
      intro s e
      have := congrArg Fin.val e
      rw [hv, port_val] at this
      have hs := s.isLt
      have hCN : CN = 22 := rfl
      have hCR : CR = 40 := rfl
      split at this <;> omega
    unfold PrimT.C3ReqIface.c3In
    simp [ne]

theorem entry_inv (w : List Bool) (h Q m pr : ℕ) :
    (P.lay Ua Dv Cv).Inv (P.entry Dv Cv w h Q m pr) (stIn w h Q m pr) (WT + 1) := by
  have hWT : WT = 64 := rfl
  have hCN : CN = 22 := rfl
  have hCR : CR = 40 := rfl
  have key : ∀ i : Fin (P.lay Ua Dv Cv).U, (∀ s : Fin (CN + 1), Fin.castAdd 1 i ≠ P.port Dv Cv s) →
      P.entry Dv Cv w h Q m pr i = [] := by
    intro i hi
    unfold entry PrimT.C3ReqIface.c3In
    simp [hi]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro s
    unfold entry PrimT.C3ReqIface.c3In stIn
    have hp : ∀ a b : Fin (CN + 1), (P.port Dv Cv (Ua := Ua) a = P.port Dv Cv b) = (a = b) :=
      fun a b => propext ⟨fun h => P.port_inj Dv Cv h, fun h => h ▸ rfl⟩
    simp only [show Fin.castAdd 1 ((P.lay Ua Dv Cv).ws s) = P.port Dv Cv s from rfl, hp]
  · apply key
    intro s e
    have h1 := congrArg Fin.val e
    simp only [Fin.val_castAdd] at h1
    rw [Lay.wc_val, port_val] at h1
    split at h1 <;> omega
  · intro r
    apply key
    intro s e
    have h1 := congrArg Fin.val e
    simp only [Fin.val_castAdd] at h1
    rw [Lay.wr_val, port_val] at h1
    have h2 := s.isLt
    have h3 := r.isLt
    split at h1 <;> omega
  · apply key
    intro s e
    have h1 := congrArg Fin.val e
    simp only [Fin.val_castAdd] at h1
    rw [show (P.lay Ua Dv Cv).wrec.val = WT from rfl, port_val] at h1
    have h2 := s.isLt
    split at h1 <;> omega
  · intro x hx
    apply key
    intro s e
    have h1 := congrArg Fin.val e
    simp only [Fin.val_castAdd] at h1
    rw [port_val] at h1
    have h2 := s.isLt
    split at h1 <;> omega

end Wr5

end NearCubicWires.WireExponent3_5.PrimAsm.C3Mach
