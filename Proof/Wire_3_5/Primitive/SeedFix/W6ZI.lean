import Proof.Wire_3_5.Primitive.SeedFix.W6ZH

/-! # W6, part 35: **`numsW6 : NumsPort4 alg D`**, the THR numbers machine

P3:2543-2558, 2596-2604, 2150-2157, 2220-2231 (the THR call's numbers: `|𝒢|`, `K = 8(|𝒢|+1)n^D`, the prime cutoff, the
primes, `Σp`, `τ₀`, `M`, `A`, `B_*`, `J`, `t`, `e`, `ℓ₀`, the modulus of `GF(2^{ℓ₀})`), P3:3071-3091 ("the
preprocessing … runs in time polynomial in `n`") and P3:3114-3115 ("All powers of `n` are fixed before a fixed `r`"):
* `Cth`, `Eth`, **`thrN_le`**: the call's base is `≤ Cth·(n + cap_T + 1)^{Eth}` (the algorithm's source child bound
  at `(n+1)^{26}`);
* **`needW`** `= Cth^Z (m+1)^{Eth·Z}` (`Z = 48D+700`), `need_ok`: `needW (n + cap_T) ≤ V` gives `N^Z ≤ 2V+2`;
* `numsT`, `numsCost_poly`, `numsW6_run`;
* **`numsW6 alg D : PrimThrW.Nums4.NumsPort4 alg D`**: the numbers machine (`numsM6`) with its polynomial need and cost.

Paper quantities of the main type: the fourteen THR numbers `thrNumVals` on the out-ports (`NumsPort4`), their capacity
`need` and the time `cost`, both polynomial. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedVariables false
set_option linter.style.longLine false

namespace NearCubicWires.WireExponent3_5.PrimT.W6
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairRepresentation NearCubicWires.SupplierPipeline NearCubicWires.SupplierPrime
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Shared
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimAsm

variable (alg : DecompositionAlgorithm)

/-- The base's coefficient. -/
def Cth : ℕ := alg.coefficient * 3 ^ alg.degree + 18

/-- The base's degree. -/
def Eth : ℕ := 26 * alg.degree + 26

/-- **The call's base is polynomial in `n + cap_T`.** -/
theorem thrN_le (P : StarParams) (capT : ℕ) : thrN alg P capT ≤ Cth alg * (P.n + capT + 1) ^ Eth alg := by
  unfold thrN RepairSource.CloseoutRawRows.sourceChildBound Cth Eth
  have hx : 1 ≤ P.n + capT + 1 := by omega
  have h26 : (P.n + 1) ^ 26 ≤ (P.n + capT + 1) ^ 26 := Nat.pow_le_pow_left (by omega) 26
  have h1 : 1 ≤ (P.n + capT + 1) ^ 26 := Nat.one_le_pow _ _ (by omega)
  have h3 : (P.n + 1) ^ 26 + 2 ≤ 3 * (P.n + capT + 1) ^ 26 := by omega
  have hd : ((P.n + 1) ^ 26 + 2) ^ alg.degree ≤ 3 ^ alg.degree * (P.n + capT + 1) ^ (26 * alg.degree) := by
    calc ((P.n + 1) ^ 26 + 2) ^ alg.degree ≤ (3 * (P.n + capT + 1) ^ 26) ^ alg.degree := Nat.pow_le_pow_left h3 _
      _ = 3 ^ alg.degree * (P.n + capT + 1) ^ (26 * alg.degree) := by rw [mul_pow, ← pow_mul]
  have p1 : (P.n + capT + 1) ^ (26 * alg.degree) ≤ (P.n + capT + 1) ^ (26 * alg.degree + 26) :=
    Nat.pow_le_pow_right hx (by omega)
  have p2 : (P.n + capT + 1) ^ 26 ≤ (P.n + capT + 1) ^ (26 * alg.degree + 26) := Nat.pow_le_pow_right hx (by omega)
  have p3 : P.n + capT + 1 ≤ (P.n + capT + 1) ^ (26 * alg.degree + 26) :=
    Nat.le_self_pow (by omega) _
  have p4 : 1 ≤ (P.n + capT + 1) ^ (26 * alg.degree + 26) := Nat.one_le_pow _ _ (by omega)
  have m1 := Nat.mul_le_mul_left alg.coefficient hd
  have m2 := Nat.mul_le_mul_left (alg.coefficient * 3 ^ alg.degree) p1
  have e1 : alg.coefficient * (3 ^ alg.degree * (P.n + capT + 1) ^ (26 * alg.degree)) =
      alg.coefficient * 3 ^ alg.degree * (P.n + capT + 1) ^ (26 * alg.degree) := by ring
  have e2 : (alg.coefficient * 3 ^ alg.degree + 18) * (P.n + capT + 1) ^ (26 * alg.degree + 26) =
      alg.coefficient * 3 ^ alg.degree * (P.n + capT + 1) ^ (26 * alg.degree + 26) +
        18 * (P.n + capT + 1) ^ (26 * alg.degree + 26) := by ring
  omega

/-- **The numbers machine's capacity need**: `Cth^Z (m+1)^{Eth·Z}`, `Z = 48D+700`. -/
def needW (Dexp m : ℕ) : ℕ := Cth alg ^ (48 * Dexp + 700) * (m + 1) ^ (Eth alg * (48 * Dexp + 700))

theorem need_ok (Dexp : ℕ) (P : StarParams) (capT V : ℕ) (h : needW alg Dexp (P.n + capT) ≤ V) :
    (thrN alg P capT) ^ (48 * Dexp + 700) ≤ 2 * V + 2 := by
  have h1 := Nat.pow_le_pow_left (thrN_le alg P capT) (48 * Dexp + 700)
  have e : (Cth alg * (P.n + capT + 1) ^ Eth alg) ^ (48 * Dexp + 700) = needW alg Dexp (P.n + capT) := by
    unfold needW; rw [mul_pow, ← pow_mul]
  omega

/-- **The numbers machine's time** at the cost measure `m` (half the step budget). -/
noncomputable def numsT (Dexp m : ℕ) : ℕ :=
  (tf alg).Cc * (m + 1) ^ (tf alg).Dc + 11 * m + 25 + (10000000000000000000000000000000000000000 * (m + 1) ^ 18 + 64000 * (Dexp * (m + 1) ^ 18))

theorem numsCost_poly (Dexp m : ℕ) : ValidatorPolynomialDomination.PolyBounded (2 * numsT alg Dexp m + 3) m
    (2 * (tf alg).Cc + 2 * 10000000000000000000000000000000000000000 + 128000 * Dexp + 60) ((tf alg).Dc + 18) := by
  unfold ValidatorPolynomialDomination.PolyBounded numsT
  have hx : 1 ≤ m + 1 := by omega
  have a1 : (m + 1) ^ (tf alg).Dc ≤ (m + 1) ^ ((tf alg).Dc + 18) := Nat.pow_le_pow_right hx (by omega)
  have a2 : (m + 1) ^ 18 ≤ (m + 1) ^ ((tf alg).Dc + 18) := Nat.pow_le_pow_right hx (by omega)
  have a3 : m + 1 ≤ (m + 1) ^ ((tf alg).Dc + 18) := Nat.le_self_pow (by omega) _
  have b1 := Nat.mul_le_mul_left (tf alg).Cc a1
  have b2 := Nat.mul_le_mul_left Dexp a2
  have e : (2 * (tf alg).Cc + 2 * 10000000000000000000000000000000000000000 + 128000 * Dexp + 60) * (m + 1) ^ ((tf alg).Dc + 18) =
      2 * ((tf alg).Cc * (m + 1) ^ ((tf alg).Dc + 18)) + 2 * 10000000000000000000000000000000000000000 * (m + 1) ^ ((tf alg).Dc + 18) +
        128000 * (Dexp * (m + 1) ^ ((tf alg).Dc + 18)) + 60 * (m + 1) ^ ((tf alg).Dc + 18) := by ring
  omega

theorem numsW6_T (Dexp : ℕ) (P : StarParams) {a' : ℕ} (Cs : Fin a' → NormalizedThresholdThresholdCircuit P.n)
    (ncar capT V : ℕ) (ha : a' ≤ 4) (hd : ∀ i, (Cs i).descriptionBits ≤ (P.n + 1) ^ 26) (hnc : ncar ≤ 2)
    (hV : (thrN alg P capT) ^ (48 * Dexp + 700) ≤ 2 * V + 2) :
    (tf alg).cost V + 1 + (11 * V + 20 + 1 + 1) + 1 + bodyB alg Dexp P Cs ncar capT V ≤
      numsT alg Dexp (P.n + V + capT) := by
  have hc := (tf alg).cost_poly V
  unfold ValidatorPolynomialDomination.PolyBounded at hc
  have hb := bodyB_le alg Dexp P Cs ncar capT V ha hd hnc hV
  have hVm : V + 1 ≤ P.n + V + capT + 1 := by omega
  have c1 := Nat.mul_le_mul_left (tf alg).Cc (Nat.pow_le_pow_left hVm (tf alg).Dc)
  have c2 : (V + 1) ^ 18 ≤ (P.n + V + capT + 1) ^ 18 := Nat.pow_le_pow_left hVm 18
  have c3 := Nat.mul_le_mul_left Dexp c2
  unfold numsT
  omega

theorem numsW6_run (Dexp : ℕ) (P : StarParams) {a' : ℕ} (Cs : Fin a' → NormalizedThresholdThresholdCircuit P.n)
    (codes : List ℕ) (tl : List Bool) (ncar capT V : ℕ) (hn1 : 1 ≤ P.n) (ha : a' ≤ 4)
    (hd : ∀ i, (Cs i).descriptionBits ≤ (P.n + 1) ^ 26) (hnc : ncar ≤ 2) (hcap : 1 ≤ capT)
    (hok : PrimThrW.TopFront2.TF2Ok Cs codes V) (hneed : needW alg Dexp (P.n + capT) ≤ V) :
    ∃ J : Fin (TI alg + 1) → List Bool, (∀ j, (J j).length ≤ 2 * numsT alg Dexp (P.n + V + capT) + 3) ∧
      Step (numsM6 alg Dexp) (2 * numsT alg Dexp (P.n + V + capT) + 3) (fun _ => 0)
        (Fin.addCases (m := 21) (n := TI alg + 1) (motive := fun _ => List Bool)
          (PrimThrW.Nums3.nums3InPorts (Data.reqW P.n true (ReqBridge.thrCodes Cs) codes tl) ncar capT V) (fun _ => []))
        (fun _ => 0)
        (Fin.addCases (m := 21) (n := TI alg + 1) (motive := fun _ => List Bool)
          (PrimThrW.Nums3.nums3OutPorts (Data.reqW P.n true (ReqBridge.thrCodes Cs) codes tl) ncar capT V
            (PrimThrW.Joins.thrNumVals P Cs alg Dexp ncar capT)) J) := by
  have hV := need_ok alg Dexp P capT V hneed
  refine (nums_run2 alg Dexp P Cs codes tl ncar capT V (numsT alg Dexp (P.n + V + capT)) hn1 ha hd hok hnc hV
    (numsW6_T alg Dexp P Cs ncar capT V ha hd hnc hV)).elim fun J hJ => ?_
  exact ⟨J, hJ.1, step_mono hJ.2 (by omega)⟩

/-- **W6: the THR numbers machine in port form, v4.** -/
noncomputable def numsW6 (Dexp : ℕ) : PrimThrW.Nums4.NumsPort4 alg Dexp where
  x := TI alg + 1
  s := _
  M := numsM6 alg Dexp
  cost := fun m => 2 * numsT alg Dexp m + 3
  Cc := 2 * (tf alg).Cc + 2 * 10000000000000000000000000000000000000000 + 128000 * Dexp + 60
  Dc := (tf alg).Dc + 18
  cost_poly := numsCost_poly alg Dexp
  need := needW alg Dexp
  Cn := Cth alg ^ (48 * Dexp + 700)
  Dn := Eth alg * (48 * Dexp + 700)
  need_poly := fun m => le_refl _
  run := fun P _ Cs codes tl ncar capT V hn ha hd hnc hcap hok hneed =>
    numsW6_run alg Dexp P Cs codes tl ncar capT V hn ha hd hnc hcap hok hneed

end NearCubicWires.WireExponent3_5.PrimT.W6
