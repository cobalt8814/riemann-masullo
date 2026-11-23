module

public import RiemannMasullo.Ch10_TraceSpectral.Sec3
import all RiemannMasullo.Ch10_TraceSpectral.Sec1

/-! # Further assertions in the proofs of §10.3 that are false as printed -/

@[expose] public noncomputable section

open Filter MeasureTheory NumberField Set
open scoped NNReal Topology

namespace RiemannMasullo

set_option quotPrecheck false

attribute [local instance] instIdeleClassMeasurableSpaceSec1 instIdeleClassBorelSpaceSec1
  instIdeleClassT2Sec1 instIdeleClassLocallyCompactSec1 instIdeleClassSecondCountableSec1
  instIdeleClassHaarMeasureSec1

local notation "C𝔽(" F ")" => IdeleClassGroup (𝓞 F) F
local notation "C₁(" F ")" => (ideleClassNorm F).ker
local notation "shift(" b ", " t ")" => ((b : ℝ) : ℂ) + (t : ℂ) * Complex.I
local notation "orderAt(" χ ", " z ")" => meromorphicOrderAt (continuedCompletedHeckeL χ) z
local notation "lineZeros(" χ ", " a ")" => {t : ℝ | 0 < orderAt(χ, shift(a, t))}
local notation "floorCut(" s ")" => Nat.floor ((s - 1) / 2 + 1)

/-- Paper: Theorem 10.3.1.1, interval choice before (10.3.1.15), p. 450.
As printed: the smallest interval containing the selected ordinates in each active character
can be enlarged at both ends by a common positive amount while still containing exactly
those zeros on the line. The finite selections are stated one character at a time.
See `spectralConvolutionFiniteSum` and ERRATA F178. -/
def Printed.spectralLineSelection_exists_isolatingInterval : Prop :=
  ∀ (F : Type) [Field F] [NumberField F]
    (χ : PontryaginDual C₁(F) → PontryaginDual C𝔽(F)), IsSpectralBasepointChoice χ →
    ∀ (a : ℝ) (ω : PontryaginDual C₁(F)) (K : Finset ℝ) (hK : K.Nonempty),
      (K : Set ℝ) ⊆ lineZeros(χ ω, a) →
      ∃ ε : ℝ, 0 < ε ∧
        Icc (K.min' hK - ε) (K.max' hK + ε) ∩ lineZeros(χ ω, a) = (K : Set ℝ)

/-- Paper: Theorem 10.3.1.1, interval choice before (10.3.1.15), p. 450.
Use F = ℚ, the trivial base character and a = 1/2. Let K consist of the first and third
distinct positive critical-line zeta ordinates. The omitted second ordinate lies inside
the closed interval for every ε > 0. -/
theorem Printed.spectralLineSelection_exists_isolatingInterval_false :
    ¬ Printed.spectralLineSelection_exists_isolatingInterval := by sorry

/-- Paper: Theorem 10.3.1.1, count following (10.3.1.16), p. 450.
As printed: in each such interval the number of jets is at most the floor cutoff times the
logarithm of the greater of the absolute values of the endpoints. The count includes all
the orders below the truncated multiplicity of each zero in the interval.
See `spectralConvolutionFiniteSum` and ERRATA F180. -/
def Printed.spectralLineBand_jetCount_le : Prop :=
  ∀ (F : Type) [Field F] [NumberField F]
    (χ : PontryaginDual C₁(F) → PontryaginDual C𝔽(F)), IsSpectralBasepointChoice χ →
    ∀ (a s : ℝ), 1 < s → ∀ (ω : PontryaginDual C₁(F)) (K : Finset ℝ) (hK : K.Nonempty)
      (ε : ℝ), 0 < ε →
      let l := K.min' hK - ε
      let r := K.max' hK + ε
      Icc l r ∩ lineZeros(χ ω, a) = (K : Set ℝ) →
      ((∑ t ∈ K, min ((orderAt(χ ω, shift(a, t))).untop₀.toNat) floorCut(s) : ℕ) : ℝ) ≤
        (floorCut(s) : ℝ) * Real.log (max |l| |r|)

/-- Paper: Theorem 10.3.1.1, count following (10.3.1.16), p. 450.
Use F = ℚ, the trivial base character, a = 1/2 and s = 2. Select every distinct positive
critical-line zeta ordinate at most T, for large T, and enlarge by an isolating ε < 1.
The floor cutoff is one. Riemann–von Mangoldt and the positive proportion of simple
critical-line zeros (Bui–Conrey–Young, Theorem 1.1) give ≫ T log T jets from the simple
zeros alone. The printed upper bound is O(log T). -/
theorem Printed.spectralLineBand_jetCount_le_false :
    ¬ Printed.spectralLineBand_jetCount_le := by sorry

section Plancherel

local instance instNormOneLocallyCompactSec3SpectralProofPrinted
    (F : Type) [Field F] [NumberField F] : LocallyCompactSpace C₁(F) := by
  have hc : IsCompact ((ideleClassNorm F).ker : Set C𝔽(F)) :=
    (isProperMap_ideleClassNorm F).isCompact_preimage isCompact_singleton
  exact hc.isClosed.locallyCompactSpace

local instance instNormOneHaarSec3SpectralProofPrinted (F : Type) [Field F] [NumberField F] :
    (normOneIdeleClassTamagawaMeasure F).IsHaarMeasure :=
  (multiplicativeTamagawaMeasures_existsUnique F).exists.choose_spec.2.2.2.1

local instance instIdeleClassDualMeasurableSpaceSec3SpectralProofPrinted
    (F : Type) [Field F] [NumberField F] : MeasurableSpace (PontryaginDual C𝔽(F)) := borel _

local instance instNormOneDualMeasurableSpaceSec3SpectralProofPrinted
    (F : Type) [Field F] [NumberField F] : MeasurableSpace (PontryaginDual C₁(F)) := borel _

/-- Paper: Theorem 10.3.1.1, Plancherel measure after (10.3.1.25), p. 453.
As printed: in the coordinates induced by the norm section τ, the full Plancherel measure
is the product of ordinary Lebesgue measure in x and the Plancherel measure of the norm-one subgroup.
This is the radial normalization used in the proof of `spectralLineConvolution_trace`
and `spectralStripConvolution_trace` in the paper. See ERRATA F182. -/
def Printed.spectralPlancherelMeasure_eq_radialVolume_prod : Prop :=
  ∀ (F : Type) [Field F] [NumberField F]
    (τ : ℝ≥0ˣ →ₜ* C𝔽(F)), Function.RightInverse τ (ideleClassNorm F) →
    ∀ (e : (Multiplicative ℝ × PontryaginDual C₁(F)) ≃ₜ* PontryaginDual C𝔽(F)),
      (∀ (x : ℝ) (ω : PontryaginDual C₁(F)) (r : ℝ≥0ˣ) (k : C₁(F)),
        e (Multiplicative.ofAdd x, ω) (τ r * k.val) =
          ω k * Circle.exp (x * Real.log (r.val : ℝ))) →
      ∀ (ν₁ : Measure (PontryaginDual C₁(F))) (ν : Measure (PontryaginDual C𝔽(F))),
        IsLCAPlancherelMeasure (normOneIdeleClassTamagawaMeasure F) ν₁ →
        IsLCAPlancherelMeasure (ideleClassTamagawaMeasure F) ν →
        (volume.prod ν₁).map (fun p : ℝ × PontryaginDual C₁(F) ↦
          e (Multiplicative.ofAdd p.1, p.2)) = ν

/-- Paper: Theorem 10.3.1.1, Plancherel measure after (10.3.1.25), p. 453.
Take F = ℚ with its norm section and induced dual isomorphism. Use the Gaussian exp(−y²/2)
in y = log |g|, constant on the norm-one subgroup. With the kernel exp(ixy) its radial
transform is √(2π) exp(−x²/2). The printed measure makes its squared norm 2π times the
original squared norm, since the fixed norm-one Plancherel measure already accounts for
the compact factor. The radial Plancherel measure is dx/(2π). -/
theorem Printed.spectralPlancherelMeasure_eq_radialVolume_prod_false :
    ¬ Printed.spectralPlancherelMeasure_eq_radialVolume_prod := by sorry

end Plancherel

/-- Paper: Theorem 10.3.1.1, after (10.3.1.26), p. 453.
As printed: for each norm-one character and any numbering of its line-zero ordinates by
the natural numbers, the Fourier–Mellin samples of every test decay rapidly. This is the
claim for an infinite zero set. See `spectralLineConvolution_trace` and ERRATA F183. -/
def Printed.spectralLineSamples_rapid_for_any_numbering : Prop :=
  ∀ (F : Type) [Field F] [NumberField F]
    (χ : PontryaginDual C₁(F) → PontryaginDual C𝔽(F)), IsSpectralBasepointChoice χ →
    ∀ (a : ℝ) (φ : BruhatCompactSupport C𝔽(F)) (ω : PontryaginDual C₁(F))
      (e : ℕ ≃ lineZeros(χ ω, a)) (k : ℕ),
      Tendsto (fun n : ℕ ↦ (n : ℂ) ^ k * ∫ g,
        φ.val g * ideleClassNormTwist (χ ω) (shift(0, (e n).val)) g
          ∂ideleClassTamagawaMeasure F) atTop (𝓝 0)

/-- Paper: Theorem 10.3.1.1, after (10.3.1.26), p. 453.
Take F = ℚ, the trivial base character and a = 1/2. Modulate a nonzero smooth radial
bump in y = log |g| by exp(icy). Its entire transform has discrete real zeros. Avoid the
countably many frequencies c for which a sample is zero. Place infinitely many samples
vⱼ at increasing nonadjacent indices nⱼ ≥ 1/|vⱼ|, leaving infinitely many ordinates for
the other indices. Then nⱼ|vⱼ| ≥ 1, which violates decay at k = 1. -/
theorem Printed.spectralLineSamples_rapid_for_any_numbering_false :
    ¬ Printed.spectralLineSamples_rapid_for_any_numbering := by sorry

/-- Paper: Theorem 10.3.2.1, (10.3.2.10)–(11), p. 455.
As printed: for each integration-by-parts order N > 1, one constant bounds all admitted
Mellin derivatives at nonreal strip zeros by the displayed falling factorial over |z|^N.
The order range on p. 455 includes the low orders in (10.3.2.7). The radial Mellin transform
uses the compact character coefficient for the selected component, as on p. 450 after
(10.3.1.17). See `spectralStripConvolution_traceCauchy` and ERRATA F185. -/
def Printed.spectralStripMellinJet_norm_le : Prop :=
  ∀ (F : Type) [Field F] [NumberField F]
    (χ : PontryaginDual C₁(F) → PontryaginDual C𝔽(F)), IsSpectralBasepointChoice χ →
    ∀ (τ : ℝ≥0ˣ →ₜ* C𝔽(F)), Function.RightInverse τ (ideleClassNorm F) →
    ∀ (a α s : ℝ), 0 ≤ α → 1 < s → ∀ (φ : BruhatCompactSupport C𝔽(F)) (N : ℕ), 1 < N →
      let M (ω : PontryaginDual C₁(F)) (z : ℂ) :=
        ∫ r : ℝ≥0ˣ, ((r.val : ℝ) : ℂ) ^ z *
          (∫ k : C₁(F), (ω k : ℂ) * φ.val (τ r * k.val) ∂normOneIdeleClassTamagawaMeasure F)
          ∂positiveRealHaar
      ∃ C : ℝ, 0 < C ∧ ∀ (ω : PontryaginDual C₁(F)) (b t : ℝ),
        b ∈ Icc (-α) α → t ≠ 0 → 0 < orderAt(χ ω, shift(a + b, t)) →
        let mult := (orderAt(χ ω, shift(a + b, t))).untop₀.toNat
        let count := if b = -α ∨ b = α then min mult floorCut(s) else mult
        ∀ i : ℕ, i < count →
          ‖iteratedDeriv i (M ω) (shift(b, t))‖ ≤
            C * (∏ n ∈ Finset.range N, ((i : ℝ) - (n : ℝ))) / ‖shift(b, t)‖ ^ N

/-- Paper: Theorem 10.3.2.1, (10.3.2.10)–(11), p. 455.
Over `F = ℚ` the pointwise bound of the theorem is asserted at every zero of the completed
Hecke L-function in the strip. The trivial norm-one character therefore needs one zero of
the completed zeta function at `1/2 + t * I` with `t ≠ 0`.

Missing input: this is the single-instance form of Hardy's theorem, that the Riemann zeta
function has zeros on the critical line. Nothing in this library asserts that any completed
Hecke L-function has a zero, so the existence is not available at this base; it is the exact
missing input of the refutation. -/
private theorem spectralStripMellinJet_norm_le_false_exists_zero
    (χ : PontryaginDual C₁(ℚ) → PontryaginDual C𝔽(ℚ)) (hχ : IsSpectralBasepointChoice χ) :
    ∃ (ω : PontryaginDual C₁(ℚ)) (t : ℝ), t ≠ 0 ∧
      0 < orderAt(χ ω, shift(1 / 2, t)) ∧
      0 < (orderAt(χ ω, shift(1 / 2, t))).untop₀.toNat := by
  sorry

/-- Paper: Theorem 10.3.2.1, (10.3.2.10)–(11), p. 455.
The compact-character Mellin transform of the printed test is the quantity that the printed
bound controls. At a prescribed frequency it does not vanish for a suitable test: take the
test trivial on the norm-one subgroup, with norm profile a nonzero smooth bump multiplied by
the inverse of the oscillation `r ↦ r ^ (i t)`, so that the Mellin integral at `shift(0, t)`
becomes the integral of the bump against the multiplicative Haar measure, hence is nonzero.
Missing input: the construction of an element of `BruhatCompactSupport` from a norm profile
on the idele class group of `ℚ`, and the identification of `positiveRealHaar` with Lebesgue
measure in the logarithmic coordinate. -/
private theorem spectralStripMellinJet_norm_le_false_exists_mellin
    (τ : ℝ≥0ˣ →ₜ* C𝔽(ℚ)) (ω : PontryaginDual C₁(ℚ)) (t : ℝ) :
    ∃ φ : BruhatCompactSupport C𝔽(ℚ),
      (∫ r : ℝ≥0ˣ, ((r.val : ℝ) : ℂ) ^ (shift(0, t)) *
        (∫ k : C₁(ℚ), (ω k : ℂ) * φ.val (τ r * k.val)
          ∂normOneIdeleClassTamagawaMeasure ℚ) ∂positiveRealHaar) ≠ 0 := by
  sorry

/-- Paper: Theorem 10.3.2.1, (10.3.2.10)–(11), p. 455.
Take F = ℚ, any spectral basepoint choice, a = 1/2, α = 3, s = 2 and N = 2, and test the
bound at the interior parameter b = 0 and at order i = 0. The order-zero multiplicity is at
least one at the zero of `spectralStripMellinJet_norm_le_false_exists_zero`, and the factor
for n = 0 in the falling factorial vanishes, so the right-hand side is zero for every
constant C. A test as in `spectralStripMellinJet_norm_le_false_exists_mellin` has nonzero
Mellin value there. -/
theorem Printed.spectralStripMellinJet_norm_le_false :
    ¬ Printed.spectralStripMellinJet_norm_le := by
  intro h
  obtain ⟨χ, hχ⟩ := exists_spectralBasepointChoice (F := ℚ)
  let q : IdeleGroup (𝓞 ℚ) ℚ →ₜ* C𝔽(ℚ) :=
    ⟨QuotientGroup.mk' _, continuous_quotient_mk'⟩
  let τ : ℝ≥0ˣ →ₜ* C𝔽(ℚ) :=
    q.comp ⟨canonicalIdeleNormSection ℚ, canonicalIdeleNormSection_continuous ℚ⟩
  have hτ : Function.RightInverse τ (ideleClassNorm ℚ) :=
    canonicalIdeleNormSection_rightInverse ℚ
  obtain ⟨ω, t, ht, hord, hmult⟩ := spectralStripMellinJet_norm_le_false_exists_zero χ hχ
  obtain ⟨φ, hφ⟩ := spectralStripMellinJet_norm_le_false_exists_mellin τ ω t
  obtain ⟨C, hC, hbound⟩ :=
    h ℚ χ hχ τ hτ (1 / 2) 3 2 (by norm_num) (by norm_num) φ 2 (by norm_num)
  have hmem : (0 : ℝ) ∈ Set.Icc (-3 : ℝ) 3 := by norm_num
  have hshift : shift((1 : ℝ) / 2 + 0, t) = shift(1 / 2, t) := by norm_num
  have hord' : 0 < orderAt(χ ω, shift(1 / 2 + 0, t)) := by rw [hshift]; exact hord
  have hmult' : 0 < (orderAt(χ ω, shift(1 / 2 + 0, t))).untop₀.toNat := by
    rw [hshift]; exact hmult
  have hif : ¬ ((0 : ℝ) = -3 ∨ (0 : ℝ) = 3) := by norm_num
  have hcount : 0 < (if (0 : ℝ) = -3 ∨ (0 : ℝ) = 3 then
      min (orderAt(χ ω, shift(1 / 2 + 0, t))).untop₀.toNat (floorCut((2 : ℝ)))
      else (orderAt(χ ω, shift(1 / 2 + 0, t))).untop₀.toNat) := by
    simpa only [hif, ite_false] using hmult'
  have hle := hbound ω 0 t hmem ht hord' 0 hcount
  have hprod : (∏ n ∈ Finset.range 2, (((0 : ℕ) : ℝ) - ((n : ℕ) : ℝ))) = 0 := by
    simp [Finset.prod_range_succ]
  rw [hprod, mul_zero, zero_div] at hle
  have hnorm : ‖iteratedDeriv 0 ((fun (ω : PontryaginDual C₁(ℚ)) (z : ℂ) ↦
      ∫ r : ℝ≥0ˣ, ((r.val : ℝ) : ℂ) ^ z *
        (∫ k : C₁(ℚ), (ω k : ℂ) * φ.val (τ r * k.val)
          ∂normOneIdeleClassTamagawaMeasure ℚ) ∂positiveRealHaar) ω) (shift(0, t))‖ ≤ 0 := hle
  have hzero : (∫ r : ℝ≥0ˣ, ((r.val : ℝ) : ℂ) ^ (shift(0, t)) *
        (∫ k : C₁(ℚ), (ω k : ℂ) * φ.val (τ r * k.val)
          ∂normOneIdeleClassTamagawaMeasure ℚ) ∂positiveRealHaar) = 0 := by
    simpa using norm_eq_zero.mp (le_antisymm hnorm (norm_nonneg _))
  exact hφ hzero

end RiemannMasullo
