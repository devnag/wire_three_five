import Lean
import Proof.Wire_3_5.Transfer.LiteralSources
import Outer.Apply
import Outer.Size
import Succinct.Main
import Proof.Foundations.RecoveryScheduleEnvelope
import Proof.Foundations.PolynomialClock
import Bindings.CLW20_Lemma3_11_TM2


/-! # The gate constants in the paper's order (paper v2, "Order of the constants", items (1)–(6))

Realizes, as definitions from the literals and in the paper's order, the constants that the union machine, the ledger
and the recovery read:
* item (1), "Put d_0=2, choose an integer C_clk>d_0+2" (paragraph "Clock, hierarchy verifier, and source lengths"):
  **`kclk`** `= 41`, i.e. `C_clk = kclk + 2 = 43`, a numeral fixed before every other constant; the source exponent
  `d_0 = 2` is the front's (`A·(N+1)^2`);
* the hierarchy at the clock `N^{kclk+2}`: **`gateH l`**, the refuter's hierarchy of the source bundle;
* the oracle exponent: the size cap `oracleSizeBound d q`, `d = 17·c_STV` (**`oracleDeg l`**), lies below
  `(q+1)^G` with **`capExp l`** `= G = 2^{oracleDepth d}` (`oracleSize_le`);
* item (4), "G'=G+1 and λ_a": the description length **`instLength (lenG l) a = a^{G+1}`** (`lenG l = G − 1`,
  `instLength_lenG`); "𝒱_G, c_G and T_G": **`gateSV l`**, the succinct verifier of Lemma H.6 for `gateH l` at that
  length (`succinctVerifier_exists`), and the short PCP **`gateMW l`** (the bundle's `shortPCP`, §H.1 item 1);
* item (5), "A_pad and q(N)": **`gateApad l`** `= Outer.apad` and **`gateWidth l N`** `= q(N)` (`Outer.width`, (57));
* item (6), "e_H, d_G": **`eH l`** `= (G'+1)e_C + G + 1` (Lemma H.7(b); `e_C` the short PCP's size exponent at 𝒱_G),
  the call-count exponent **`unionCallDeg l`** `= 5·e_H·a_p + 1` and the clause degree **`recDG l`** `= a_p·e_H + 1`
  ((58); `a_p` the pointwise PCPP's degree);
* the pointwise PCPP **`gatePCPP l`** (§H.1 item 2, CLW20 Lemma 3.11), unchanged.
Every later constant (`A_pad`, `e_H`, `d_G`) is chosen after `kclk` and `𝒱_G`, as items (4)–(6) order them. -/

set_option autoImplicit false


namespace NearCubicWires.WireExponent3_5.Transfer
open NearCubicWires NearCubicWires.SourceInterfaces NearCubicWires.RepairSource NearCubicWires.RepairRepresentation
open NearCubicWires.RepairOrdinary

/-- **`C_clk − 2`**: the clock is `T(N) = N^{kclk+2} = N^{43}` (order item (1): an integer `C_clk > d_0 + 2`). -/
def kclk : ℕ := 41

theorem kclk_eq : kclk = 41 := rfl

/-- The hierarchy at the clock `N^{kclk+2}`: the refuter's hierarchy of the source bundle (item 3 of §H.1). -/
noncomputable def gateH (l : Literals) : OrdinaryHierarchy (fun n => n ^ (kclk + 2)) :=
  (l.eightSources.hierarchy kclk).hierarchy

/-- The pointwise PCPP algorithm, from the `clw311` literal (§H.1 item 2). -/
noncomputable def gatePCPP (l : Literals) : PointwisePCPPAlgorithm :=
  Classical.choice (_root_.NearCubicWires.Bindings.CLW20Lemma311TM2.clw20_lemma3_11_explicitEnc_tm2_to_import l.clw311)

/-- The short PCP in the ordinary model (§H.1 item 1), from the `mw20` literal. -/
theorem gateMW (l : Literals) : _root_.NearCubicGates.Close.Outer.MWSource :=
  l.eightSources.pcp.shortPCP

/-- The oracle degree `d = 17·c_STV` of the size cap (Case 1's simulation margin). -/
noncomputable def oracleDeg (l : Literals) : ℕ := 17 * l.eightSources.amplification.stvExponent

/-- **`G`**: the exponent of the size cap, `oracleSizeBound d q < (q+1)^G` (`oracleSize_le`). -/
noncomputable def capExp (l : Literals) : ℕ :=
  2 ^ _root_.NearCubicWires.RecoveryScheduleEnvelope.oracleDepth (oracleDeg l)

theorem one_le_capExp (l : Literals) : 1 ≤ capExp l := Nat.one_le_two_pow

/-- The size cap `q^G`: every size at most `oracleSizeBound d q` is below `(q+1)^G`. -/
theorem oracleSize_le (l : Literals) (w o : ℕ)
    (ho : o ≤ _root_.NearCubicWires.RecoveryScheduleEnvelope.oracleSizeBound (oracleDeg l) w) :
    o + 1 ≤ (w + 1) ^ capExp l := by
  have := _root_.NearCubicWires.PolynomialClock.pairIter_add_one_le_pow
    (_root_.NearCubicWires.RecoveryScheduleEnvelope.oracleDepth (oracleDeg l)) w
  unfold _root_.NearCubicWires.RecoveryScheduleEnvelope.oracleSizeBound
    _root_.NearCubicWires.PolynomialClock.pairClock at ho
  unfold capExp
  omega

/-- The parameter of `instLength` (`instLength G ν = ν^{G+2}`) at which `λ_a = a^{G'}`, `G' = G + 1`. -/
noncomputable def lenG (l : Literals) : ℕ := capExp l - 1

/-- **`λ_a = a^{G'}`, `G' = G + 1`** (order item (4); §H.6 "Put G'=G+1, λ_a=a^{G'}"). -/
theorem instLength_lenG (l : Literals) (a : ℕ) :
    _root_.NearCubicGates.Close.Outer.instLength (lenG l) a = a ^ (capExp l + 1) := by
  unfold _root_.NearCubicGates.Close.Outer.instLength lenG
  have := one_le_capExp l
  congr 1
  omega

/-- **`𝒱_G`** (Lemma H.6): the succinct verifier of the hierarchy `gateH l` at the description length `λ_a`. -/
noncomputable def gateSV (l : Literals) : _root_.NearCubicGates.Close.Outer.SuccinctVerifier (gateH l) (lenG l) :=
  Classical.choice (_root_.NearCubicGates.Close.Succinct.succinctVerifier_exists (gateH l) (lenG l))

/-- **`A_pad`** (order item (5); (57)): fixed after the short PCP's constants at `𝒱_G`. -/
noncomputable def gateApad (l : Literals) : ℕ := _root_.NearCubicGates.Close.Outer.apad (gateMW l) (gateSV l)

/-- **`q(N)`** ((57)): the exact width `⌈log₂T(N)⌉ + A_pad⌈log₂(log₂T(N)+2)⌉ + A_pad`. -/
noncomputable def gateWidth (l : Literals) (N : ℕ) : ℕ :=
  _root_.NearCubicGates.Close.Outer.width (gateMW l) (gateSV l) N

/-- `e_C`: the short PCP's size exponent at `𝒱_G`. -/
noncomputable def eC (l : Literals) : ℕ := (_root_.NearCubicGates.Close.Outer.alg (gateMW l) (gateSV l)).sizeExp

/-- **`e_H = (G'+1)e_C + G + 1`** (Lemma H.7(b), order item (6)): `H_Γ` has size at most `q^{e_H}`. -/
noncomputable def eH (l : Literals) : ℕ := (capExp l + 2) * eC l + capExp l + 1

/-- **The union's call-count exponent** at `e_H`: the call count `24K(1+2K(s+1))⁴` of the substituted circuit of size
`O(q^{e_H})` through the PCPP of degree `a_p`. -/
noncomputable def unionCallDeg (l : Literals) : ℕ := 5 * eH l * (gatePCPP l).degree + 1

/-- **`d_G = a_p·e_H`** ((58), order item (6)), plus one: it bounds all PCPP clause counts by `(q+2)^{d_G}`. -/
noncomputable def recDG (l : Literals) : ℕ := eH l * (gatePCPP l).degree + 1

end NearCubicWires.WireExponent3_5.Transfer

