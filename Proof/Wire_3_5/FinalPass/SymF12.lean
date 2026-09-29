import Proof.Wire_3_5.FinalPass.SymF11
import Proof.Wire_3_5.FinalPass.SymF8

/-! # SWf (the SYM words writer's flat tables), part 12: the flat tables writer at a SYM request

At a SYM request `r` of the family (on-star, carriers `≤ 2`, circuit descriptions `≤ (n+1)^{26}`), the flat list's
numbers are below `X = K₀·(n+2)^{E₀}` with `E₀ = E0P l` on `l` alone and `K₀ = K0P c_r` (PA's `CallIndexR`:
`flatSeed_leR`, `cap_leR`; `M ≤ 4(n+1)^{26}`, `L_c ≤ M`, `errExp = ⌈log₂(n+2)⌉ + 5`), and `n + 2 ≤ 2^m + 1` at the
writer's dimension `m = mOf P`. **`writer_runP`**: the flat tables writer `tabMP W c_r (9E₀) (CWP K₀) E₀ K₀` runs
(`tabP_writer` with `tabP_hyps`) from `frame (reqP n (symPl r) (symL r c))` to `flatWord (symPl r) (symL r c)` within
the shell's budget `budP`.

Paper quantity of the main type: circuit `c`'s flat tables word (`tablesJ`, list:flatten P3:1508-1520) at the
request, on the writer's output. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace NearCubicWires.WireExponent3_5.FinalPass.SymF
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Split
open NearCubicWires.WireExponent3_5.Lists NearCubicWires.WireExponent3_5.Primitive NearCubicWires.WireExponent3_5.Shared
open NearCubicWires.WireExponent3_5.FinalPass.PlanFP NearCubicWires.WireExponent3_5.PrimAsm.Plan
open NearCubicWires.WireExponent3_5.PrimAsm NearCubicWires.WireExponent3_5.PrimT.WalkBank
open NearCubicWires.BlockPlatform NearCubicWires.SupplierPipeline

/-- The atoms' degree (on `l`). -/
noncomputable def E0P (l : Literals) : ℕ := CallIndexR.flatZR l + CallIndexR.capZR l + 27

/-- The atoms' coefficient (on `c_r`). -/
def K0P (cr : ℕ) : ℕ := CallIndexR.flatK cr + 8192 * CallIndexR.capK cr + 1000

theorem n2_le_mP (P : StarParams) : P.n + 2 ≤ 2 ^ NumsX.mOf P + 1 := by
  have h1 : P.n + 2 ≤ 2 ^ Nat.clog 2 (P.n + 2) := Nat.le_pow_clog (by norm_num) _
  have h2 : 2 ^ Nat.clog 2 (P.n + 2) ≤ 2 ^ NumsX.mOf P :=
    Nat.pow_le_pow_right (by norm_num) (by unfold NumsX.mOf; omega)
  omega

variable (W : WalkBankProducer)

/-- **The flat tables writer's budget** at a star call (the shell's cost). -/
noncomputable def budP (cr E0 K0 : ℕ) (P : StarParams) (Pl : FlatListParams) (L : ℕ) : ℕ :=
  2 * ShellT.shellCostG (reqP P.n Pl L) P.n (9 * E0) (CWP K0) 1 64
    (ThrData.thrDataStage2.cost 0 (TabW.noCs P.n) [] (UnaryCalc.value 1 64 P.n) (UnaryCalc.value 1 64 P.n)) 1
    (cr + 18) (TabW.c2Of cr P.n) (NumsX.mOf P) E0 K0 (A2P K0 * (2 ^ NumsX.mOf P + 1) ^ (9 * E0)) + 2

/-- **The flat tables writer's run at the flat list's numbers `≤ K₀·(n+2)^{E₀}`.** -/
theorem writer_atP (cr : ℕ) (P : StarParams) (hrP : P.r = Ledger.rowBr cr P.n) (Pl : FlatListParams) (L K0 E0 : ℕ)
    (hK0 : 1 ≤ K0) (hE0 : 1 ≤ E0) (hM : Pl.M ≤ K0 * (P.n + 2) ^ E0) (hB : Pl.B ≤ K0 * (P.n + 2) ^ E0)
    (hE : Pl.errExp ≤ K0 * (P.n + 2) ^ E0) (hL : L ≤ K0 * (P.n + 2) ^ E0)
    (hK : Fintype.card Pl.FlatSeed ≤ K0 * (P.n + 2) ^ E0) :
    WriterIfaceJ.WriterRun (tabMP W cr (9 * E0) (CWP K0) E0 K0) (budP cr E0 K0 P Pl L)
      (ShellX.shellInX W.x (9 * E0) 1 1 E0) (ShellX.shellOutX W.x (9 * E0) 1 1 E0) (reqP P.n Pl L)
      (flatWord Pl L) := by
  have hQ := n2_le_mP P
  have lift : ∀ v, v ≤ K0 * (P.n + 2) ^ E0 → v ≤ K0 * (2 ^ NumsX.mOf P + 1) ^ E0 := fun v h =>
    h.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hQ _))
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ := tabP_hyps (NumsX.mOf P) Pl P.n L K0 E0 hQ hK0 hE0
    (lift _ hM) (lift _ hB) (lift _ hE) (lift _ hL) (lift _ hK)
  exact tabP_writer W cr P hrP Pl L (9 * E0) (CWP K0) E0 K0 (A1P K0 * (2 ^ NumsX.mOf P + 1) ^ (3 * E0))
    (A2P K0 * (2 ^ NumsX.mOf P + 1) ^ (9 * E0)) _ h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 le_rfl

section Req
variable (l : Literals) (F : GateFree l) (kclk coef A a : ℕ) (ha : a ≤ kclk + 1)

/-- **The flat list's numbers at a SYM request**, below `K0P c_r·(n+2)^{E0P l}`. -/
theorem atoms_symP (r : FReq l F kclk coef A a ha) (hm : r.1.mode = .sym) (c : Fin 4) :
    (symPl l F kclk coef A a ha r).M ≤ K0P F.cr * (r.1.n + 2) ^ E0P l ∧
    (symPl l F kclk coef A a ha r).B ≤ K0P F.cr * (r.1.n + 2) ^ E0P l ∧
    (symPl l F kclk coef A a ha r).errExp ≤ K0P F.cr * (r.1.n + 2) ^ E0P l ∧
    symL l F kclk coef A a ha r c ≤ K0P F.cr * (r.1.n + 2) ^ E0P l ∧
    Fintype.card (symPl l F kclk coef A a ha r).FlatSeed ≤ K0P F.cr * (r.1.n + 2) ^ E0P l := by
  obtain ⟨⟨n, mode, a', ha', Cs, carriers, translation⟩, hcall⟩ := r
  cases mode with
  | thr => exact absurd hm (by simp)
  | sym =>
    have hd : ∀ i, (Cs i).descriptionBits ≤ (n + 1) ^ 26 := hcall.2.2.1
    have hcar : carriers.length ≤ 2 := hcall.2.2.2.1
    set N := n + 2 with hNd
    have hN : 1 ≤ N := by omega
    have pw : ∀ z, z ≤ E0P l → N ^ z ≤ N ^ E0P l := fun z h => Nat.pow_le_pow_right hN h
    have hK1 : 1000 ≤ K0P F.cr := by unfold K0P; omega
    -- the list's `M`, and each population length below it
    have hM0 : ∑ i, (Cs i).bottomCount ≤ 4 * (n + 1) ^ 26 := by
      have h1 : ∑ i, (Cs i).bottomCount ≤ ∑ _i : Fin a', (n + 1) ^ 26 :=
        Finset.sum_le_sum (fun i _ => CallIndex.bottomCount_le (Cs i) (hd i))
      have h2 : ∑ _i : Fin a', (n + 1) ^ 26 = a' * (n + 1) ^ 26 := by simp
      have h3 : a' * (n + 1) ^ 26 ≤ 4 * (n + 1) ^ 26 := Nat.mul_le_mul_right _ ha'
      omega
    have h26 : 4 * (n + 1) ^ 26 ≤ K0P F.cr * N ^ E0P l := by
      have a1 : (n + 1) ^ 26 ≤ N ^ 26 := Nat.pow_le_pow_left (by omega) 26
      have a2 : N ^ 26 ≤ N ^ E0P l := pw 26 (by unfold E0P; omega)
      have a3 : 4 * N ^ E0P l ≤ K0P F.cr * N ^ E0P l := Nat.mul_le_mul_right _ (by omega)
      omega
    have hLc : (if h : c.val < a' then (Stars.symGates (Cs ⟨c.val, h⟩)).length else 0) ≤ ∑ i, (Cs i).bottomCount := by
      split
      · rename_i h
        rw [length_symGates]
        exact Finset.single_le_sum (f := fun i => (Cs i).bottomCount) (fun _ _ => Nat.zero_le _)
          (Finset.mem_univ (⟨c.val, h⟩ : Fin a'))
      · exact Nat.zero_le _
    -- the list's `B`
    have hc := CallIndexR.cap_leR l F.cr .sym n
    have hB : carriers.length * (4096 * Ledger.rowBCap (gateCap l) .sym (Ledger.rowBr F.cr n) (gateSp l n) n) ≤
        K0P F.cr * N ^ E0P l := by
      show carriers.length * (4096 * Ledger.rowBCap (gateCap l) .sym (Ledger.rowBr F.cr n) (gateSp l n) n) ≤ _
      have b1 : carriers.length * (4096 * Ledger.rowBCap (gateCap l) .sym (Ledger.rowBr F.cr n) (gateSp l n) n) ≤
          2 * (4096 * (CallIndexR.capK F.cr * N ^ CallIndexR.capZR l)) :=
        Nat.mul_le_mul hcar (Nat.mul_le_mul_left _ hc)
      have b2 : N ^ CallIndexR.capZR l ≤ N ^ E0P l := pw _ (by unfold E0P; omega)
      have b3 : 2 * (4096 * (CallIndexR.capK F.cr * N ^ CallIndexR.capZR l)) ≤
          8192 * CallIndexR.capK F.cr * N ^ E0P l := by
        rw [show 2 * (4096 * (CallIndexR.capK F.cr * N ^ CallIndexR.capZR l)) =
          8192 * CallIndexR.capK F.cr * N ^ CallIndexR.capZR l by ring]
        exact Nat.mul_le_mul_left _ b2
      have b4 : 8192 * CallIndexR.capK F.cr * N ^ E0P l ≤ K0P F.cr * N ^ E0P l :=
        Nat.mul_le_mul_right _ (by unfold K0P; omega)
      omega
    -- the list's `errExp`
    have hE : 1 * Nat.clog 2 (n + 2) + 5 ≤ K0P F.cr * N ^ E0P l := by
      have e1 : Nat.clog 2 (n + 2) ≤ n + 2 := Nat.clog_le_of_le_pow (Nat.lt_two_pow_self).le
      have e2 : N ≤ N ^ E0P l := by
        calc N = N ^ 1 := (pow_one N).symm
          _ ≤ N ^ E0P l := pw 1 (by unfold E0P; omega)
      have e3 : 6 * N ^ E0P l ≤ K0P F.cr * N ^ E0P l := Nat.mul_le_mul_right _ (by omega)
      omega
    -- the seed count
    have hK := CallIndexR.flatSeed_leR l F kclk coef A a ha n ha' Cs carriers hd hcar
    have hK' : Fintype.card (Primitive.symListParams (callInputs l F kclk coef A a ha) n a' Cs carriers).FlatSeed
        ≤ K0P F.cr * N ^ E0P l := by
      refine le_trans hK ?_
      have k1 : N ^ CallIndexR.flatZR l ≤ N ^ E0P l := pw _ (by unfold E0P; omega)
      exact Nat.mul_le_mul (by unfold K0P; omega) k1
    exact ⟨show ∑ i, (Cs i).bottomCount ≤ _ by omega, hB, hE, show (if h : c.val < a' then _ else 0) ≤ _ by omega, hK'⟩

end Req

end NearCubicWires.WireExponent3_5.FinalPass.SymF
