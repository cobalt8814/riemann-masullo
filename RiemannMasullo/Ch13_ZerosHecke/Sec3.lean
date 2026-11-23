module

public import RiemannMasullo.Ch12_TraceGeometric.Sec5
import all RiemannMasullo.Ch10_TraceSpectral.Sec1
import all RiemannMasullo.AppB_AnalyticNT.Sec4b
import all RiemannMasullo.AppD_SchwartzBruhat.Sec2b
import all RiemannMasullo.AppD_SchwartzBruhat.Sec3b

/-! # The divisor of the Hecke L-function

Masullo, §13.3.1, p. 522. The two sides of the proposed trace formula are
continuous on the Mellin-jet test subspace. The printed equality and codimension
claim are recorded in `Sec3_Printed.lean`.
-/

@[expose] public noncomputable section

open Function IsDedekindDomain MeasureTheory NumberField Set
open scoped NNReal

namespace RiemannMasullo

set_option quotPrecheck false

attribute [local instance] instIdeleClassMeasurableSpaceSec1 instIdeleClassBorelSpaceSec1
  instIdeleClassT2Sec1 instIdeleClassLocallyCompactSec1 instIdeleClassSecondCountableSec1
  instIdeleClassHaarMeasureSec1 instFiniteCompletionUnitsLocallyCompactSec4b
  instNormOneIdeleClassMeasurableSec4b

variable {F : Type*} [Field F] [NumberField F]

local notation "C𝔽" => IdeleClassGroup (𝓞 F) F
local notation "C₁" => (ideleClassNorm F).ker
local notation "U𝔽" => PontryaginDual C𝔽
local notation "D𝔽" => BruhatCompactSupport C𝔽
local notation "μ𝔽" => ideleClassTamagawaMeasure F
local notation "V" => HeightOneSpectrum (𝓞 F)
local notation "ord(" χ ", " s ")" =>
  MeromorphicOn.divisor (continuedCompletedHeckeL (F := F) χ) univ s
local notation "sectionCharacters(" τ ")" => {χ : U𝔽 // ∀ t, χ (τ t) = 1}

-- TODO(paper-gap): §§13.1 and 13.2 are headings with no text on p. 522.
-- TODO(paper-gap): Footnote 1 to Theorem 13.3.1.1 says “Correct statement.” The
-- cited `traceFormula` uses a positive-width strip, full zero orders and tests
-- vanishing on the norm-one classes. The manuscript gives no derivation of the
-- changes to the zero weights, test space or local coefficients.

/-- Paper: (13.3.1.1), p. 522. The spectral multiplicity is the order of the
completed Hecke zero capped at the degree of the number field. -/
def criticalTraceMultiplicity (χ : U𝔽) (s : ℂ) (_hs : 0 < ord(χ, s)) : ℕ :=
  min (ord(χ, s)).toNat (Module.finrank ℚ F)

/-- Paper: (13.3.1.1), p. 522. A zero whose order exceeds the field degree is
counted with weight equal to the degree. -/
theorem criticalTraceMultiplicity_of_degree_le (χ : U𝔽) (s : ℂ) (hs : 0 < ord(χ, s))
    (_h : Module.finrank ℚ F ≤ (ord(χ, s)).toNat) :
    criticalTraceMultiplicity χ s hs = Module.finrank ℚ F := by
  unfold criticalTraceMultiplicity
  exact min_eq_right _h

local notation "momentIntegrand(" χ ", " k ", " φ ")" =>
  (fun g : C𝔽 ↦ (φ : D𝔽).val g * spectralZeroJet (F := F) χ 0 0 k g)

private theorem criticalTraceMoment_isLinearMap_integrable (χ : U𝔽) (k : ℕ) (φ : D𝔽) :
    Integrable (fun g : C𝔽 ↦ (φ : D𝔽).val g * spectralZeroJet (F := F) χ 0 0 k g) μ𝔽 := by
  have hφ : Continuous (φ : D𝔽).val :=
    continuous_schwartzBruhat
      (⟨φ.val, bruhatCompactSupport_mem_schwartz φ.property⟩ : SchwartzBruhat C𝔽)
  have hc : HasCompactSupport (φ : D𝔽).val := φ.property.2
  have hlog : Continuous (fun g : C𝔽 ↦ Real.log ((ideleClassNorm F g).val : ℝ)) :=
    ((NNReal.continuous_coe.comp (Units.continuous_val.comp
      (isProperMap_ideleClassNorm F).continuous))).log fun g ↦
        ne_of_gt (NNReal.coe_pos.mpr (Units.zero_lt _))
  have hj : Continuous (spectralZeroJet (F := F) χ 0 0 k) := by
    unfold spectralZeroJet
    exact (ideleClassNormTwist χ _).continuous.mul
      ((Complex.continuous_ofReal.comp hlog).pow k)
  exact (hφ.mul hj).integrable_of_hasCompactSupport (hc.mul_right)

/-- Paper: (13.3.1.2), p. 522. A fixed character and jet order give a linear
functional by integration against the character times a power of the log norm. -/
theorem criticalTraceMoment_isLinearMap (χ : U𝔽) (k : ℕ) :
    IsLinearMap ℂ (fun φ : D𝔽 ↦ ∫ g, momentIntegrand(χ, k, φ) g ∂μ𝔽) := by
  refine ⟨fun φ ψ ↦ ?_, fun c φ ↦ ?_⟩
  · have e : (fun g : C𝔽 ↦ ((φ + ψ : D𝔽)).val g * spectralZeroJet (F := F) χ 0 0 k g) =
        fun g ↦ φ.val g * spectralZeroJet (F := F) χ 0 0 k g +
          ψ.val g * spectralZeroJet (F := F) χ 0 0 k g := by
      ext g
      exact add_mul _ _ _
    simp only [e]
    exact integral_add (criticalTraceMoment_isLinearMap_integrable χ k φ)
      (criticalTraceMoment_isLinearMap_integrable χ k ψ)
  · have e : (fun g : C𝔽 ↦ ((c • φ : D𝔽)).val g * spectralZeroJet (F := F) χ 0 0 k g) =
        fun g ↦ c * (φ.val g * spectralZeroJet (F := F) χ 0 0 k g) := by
      ext g
      exact mul_assoc _ _ _
    simp only [e]
    exact integral_const_mul c _

/-- Paper: (13.3.1.2), p. 522. The test subspace is the common kernel of the
first `[F : ℚ]` log-norm moments for each unitary character trivial on the section.
Deviation: The degree bounds the jet orders in each character, with no finite
codimension imposed on the common kernel. -/
def criticalTraceTestSubmodule (τ : ℝ≥0ˣ →ₜ* C𝔽) : Submodule ℂ D𝔽 :=
  ⨅ (χ : sectionCharacters(τ)) (k : Fin (Module.finrank ℚ F)),
    ((criticalTraceMoment_isLinearMap χ.val k.val).mk' _).ker

/-- Paper: (13.3.1.2), p. 522. Membership in the test subspace is equivalent to
the printed Mellin-derivative conditions at `−i x₀(χ)` for all unitary characters.
The continuous norm section and the exponent along it are given explicitly. -/
theorem mem_criticalTraceTestSubmodule_iff (τ : ℝ≥0ˣ →ₜ* C𝔽)
    (_hτ : RightInverse τ (ideleClassNorm F)) (φ : D𝔽) :
    φ ∈ criticalTraceTestSubmodule τ ↔
      ∀ (χ : U𝔽) (x : ℝ),
        (∀ t : ℝ≥0ˣ, (χ (τ t) : ℂ) = ((t.val : ℝ) : ℂ) ^ ((x : ℂ) * Complex.I)) →
        ∀ k : Fin (Module.finrank ℚ F),
          iteratedDeriv k.val (fun s : ℂ ↦
            ∫ t : ℝ≥0ˣ, (χ (τ t) : ℂ) * ((t.val : ℝ) : ℂ) ^ s *
              (∫ g : C₁, φ.val (τ t * g.val) * (χ g.val : ℂ)
                ∂normOneIdeleClassTamagawaMeasure F) ∂positiveRealHaar)
            (-((x : ℂ) * Complex.I)) = 0 := by sorry

/-- Paper: Theorem 13.3.1.1, p. 522. The rational Mellin-jet test subspace has
codimension at least two, as witnessed by the trivial character and the character
modulo four on the norm-one classes.
Deviation: This replaces the printed codimension one over `ℚ` by a lower bound. -/
theorem criticalTraceTestSubmodule_rat_codimension_ge_two
    (τ : ℝ≥0ˣ →ₜ* IdeleClassGroup (𝓞 ℚ) ℚ) (_hτ : RightInverse τ (ideleClassNorm ℚ)) :
    2 ≤ Module.rank ℂ (BruhatCompactSupport (IdeleClassGroup (𝓞 ℚ) ℚ) ⧸
      criticalTraceTestSubmodule τ) := by sorry

local notation "lineZeros(" τ ")" =>
  {z : sectionCharacters(τ) × ℂ // 0 < ord(z.1.val, z.2) ∧ z.2.re = 1 / 2}
local notation "mellinAt(" φ ", " χ ", " s ")" =>
  (∫ g : C𝔽, (φ : D𝔽).val g * ideleClassNormTwist (F := F) χ s g ∂μ𝔽)
local notation "zeroTerm(" φ ", " z ")" =>
  ((criticalTraceMultiplicity (z).val.1.val (z).val.2 (z).property.1 : ℂ) *
    mellinAt(φ, (z).val.1.val, (z).val.2 - 1 / 2))

/-- Paper: Theorem 13.3.1.1, (13.3.1.3), p. 522. The capped zero sum over the
critical line converges and gives a continuous linear functional on the test subspace.
Deviation: A norm section lists each quasi-character once by a unitary character
trivial on the section and a complex norm exponent. -/
theorem criticalTraceSpectral_converges (τ : ℝ≥0ˣ →ₜ* C𝔽)
    (_hτ : RightInverse τ (ideleClassNorm F)) :
    ∃ L : criticalTraceTestSubmodule τ →L[ℂ] ℂ,
      ∀ φ : criticalTraceTestSubmodule τ,
        HasSum (fun z : lineZeros(τ) ↦ zeroTerm(φ.val, z)) (L φ) := by sorry

local notation "finiteTerm(" v ", " b ")" =>
  ((Real.log ((v : V).asIdeal.absNorm : ℝ) : ℂ) * finiteConnesWeilPrincipalValue v 1 b)
local notation "finiteUnitMass(" v ")" =>
  ((finiteLocalMultiplicativeTamagawaMeasure F (v : V)
    (HeightOneSpectrum.adicCompletionIntegers F v).units).toReal : ℂ)
local notation "archTests" => ((w : InfinitePlace F) → BruhatCompactSupport w.Completionˣ)
local notation "finiteTests" => ((v : V) → BruhatCompactSupport (v.adicCompletion F)ˣ)
local notation "restrictsAtInfinity(" a ", " φ ")" =>
  (∀ w u, ((a : archTests) w).val u = (φ : D𝔽).val (IdeleClassGroup.ofCompletion (𝓞 F) F w u))
local notation "restrictsAtFinite(" b ", " φ ")" =>
  (∀ v u, ((b : finiteTests) v).val u = (φ : D𝔽).val (IdeleClassGroup.ofAdicCompletion (𝓞 F) F v u))

/-- Paper: Theorem 13.3.1.1, (13.3.1.3)–(13.3.1.5), p. 522. The finite-place
series converges, and the polar terms minus the local principal values form a
continuous linear functional on the test subspace. The local tests are pulled back
along the maps from the local multiplicative groups to the idele classes. -/
theorem criticalTraceGeometric_converges (τ : ℝ≥0ˣ →ₜ* C𝔽)
    (_hτ : RightInverse τ (ideleClassNorm F)) :
    ∃ L : criticalTraceTestSubmodule τ →L[ℂ] ℂ,
      ∀ φ : criticalTraceTestSubmodule τ,
        ∃ (a : archTests) (b : finiteTests),
          restrictsAtInfinity(a, φ.val) ∧ restrictsAtFinite(b, φ.val) ∧
          HasSum (fun v : V ↦ finiteTerm(v, b v))
            (mellinAt(φ.val, 1, -1 / 2) + mellinAt(φ.val, 1, 1 / 2) -
              (∑ w : InfinitePlace F, infiniteConnesWeilPrincipalValue w (a w)) - L φ) := by sorry

private theorem hasSum_fullDivisor_on_criticalTraceTests_vol :
    (((normOneIdeleClassTamagawaMeasure F) univ).toReal : ℂ) ≠ 0 := by
  have hvol := normOneIdeleClassTamagawaMeasure_volume (F := F)
  have hc0 : normOneIdeleClassTamagawaMeasure F univ ≠ 0 := by
    rw [hvol, ne_eq, ENNReal.ofReal_eq_zero, not_le]
    have := NumberField.Units.regulator_pos F
    have := NumberField.classNumber_pos F
    have := NumberField.Units.torsionOrder_pos F
    have : (0 : ℝ) < Real.sqrt (Int.natAbs (NumberField.discr F) : ℝ) :=
      Real.sqrt_pos.mpr (by exact_mod_cast Int.natAbs_pos.mpr (NumberField.discr_ne_zero F))
    positivity
  have hct : normOneIdeleClassTamagawaMeasure F univ ≠ ⊤ := by
    rw [hvol]; exact ENNReal.ofReal_ne_top
  exact Complex.ofReal_ne_zero.mpr (ENNReal.toReal_ne_zero.mpr ⟨hc0, hct⟩)

private theorem hasSum_fullDivisor_on_criticalTraceTests_cpow (p a x s : ℂ) (hx : x ≠ 0) :
    p * (a * x ^ s) * x ^ (-1 / 2 : ℂ) = p * (a * x ^ (s - 1 / 2)) := by
  rw [sub_eq_add_neg, Complex.cpow_add _ _ hx]
  ring_nf

private theorem hasSum_fullDivisor_on_criticalTraceTests_hasSum_congr {ι : Type*}
    {f g : ι → ℂ} {a : ℂ} (h : HasSum f a) (hfg : ∀ i, f i = g i) : HasSum g a :=
  (funext hfg) ▸ h

private theorem hasSum_fullDivisor_on_criticalTraceTests_mul_div (v m I : ℂ) (hv : v ≠ 0) :
    v * (m / v * I) = m * I := by
  field_simp

private theorem hasSum_fullDivisor_on_criticalTraceTests_val {v x p A Fs P1 P2 M1 M2 A' F' : ℂ}
    (hv : v ≠ 0) (hx : x = p - A - Fs) (hp : p = (P1 + P2) / v) (hA : A = A') (hF : Fs = F')
    (h1 : M1 = P1) (h2 : M2 = P2) :
    v * x = M1 + M2 - v * (A' + F') := by
  subst hx hp hA hF h1 h2
  field_simp
  ring

private theorem hasSum_fullDivisor_on_criticalTraceTests_scale (a b : ℝ) (x : ℂ) :
    ((a / b : ℝ) : ℂ) * x = (a : ℂ) * x / (b : ℂ) := by
  rw [div_eq_mul_inv, div_eq_mul_inv, Complex.ofReal_mul, Complex.ofReal_inv]
  ring

/-- Paper: Theorem 13.3.1.1, (13.3.1.3)–(13.3.1.5), p. 522. On the Mellin-jet
test subspace the full zero divisor pairs against the test by the idelic explicit formula.
Deviation: This is the restriction of `idelicExplicitFormula` to the jet subspace.
It sums all completed zeros with full orders and uses the norm-one Tamagawa volume and
the canonical local factors. The capped critical-line equality is refuted in `Sec3_Printed.lean`. -/
theorem hasSum_fullDivisor_on_criticalTraceTests (τ : ℝ≥0ˣ →ₜ* C𝔽)
    (_hτ : RightInverse τ (ideleClassNorm F)) (φ : criticalTraceTestSubmodule τ) :
    let zeros := {z : sectionCharacters(τ) × ℂ // 0 < ord(z.1.val, z.2)}
    let classVolume := ((normOneIdeleClassTamagawaMeasure F univ).toReal : ℂ)
    ∃ (a : archTests) (b : finiteTests),
      restrictsAtInfinity(a, φ.val) ∧ restrictsAtFinite(b, φ.val) ∧
      Summable (fun v : V ↦ finiteTerm(v, b v) / finiteUnitMass(v)) ∧
      HasSum (fun z : zeros ↦ (ord(z.val.1.val, z.val.2) : ℂ) *
          mellinAt(φ.val, z.val.1.val, z.val.2 - 1 / 2))
        (mellinAt(φ.val, 1, -1 / 2) + mellinAt(φ.val, 1, 1 / 2) - classVolume *
          ((∑ w : InfinitePlace F, infiniteConnesWeilPrincipalValue w (a w)) +
            ∑' v : V, finiteTerm(v, b v) / finiteUnitMass(v))) := by
  obtain ⟨spectral, poles, arch, finite, hspec, hpoles, harch, hfin, _, hsupp, hsum, hHas⟩ :=
    idelicExplicitFormula τ _hτ
  choose a ha haPV using fun w => harch w φ.val
  choose b hb hbPV using fun v => hfin v φ.val
  let E : StrongDual ℂ D𝔽 →+ ℂ :=
    { toFun := fun L => L φ.val, map_zero' := rfl, map_add' := fun _ _ => rfl }
  have hEc : Continuous E := continuous_eval_const φ.val
  have hT := hsum.hasSum.map E hEc
  have hS := hHas.map E hEc
  have hvol : (((normOneIdeleClassTamagawaMeasure F) univ).toReal : ℂ) ≠ 0 :=
    hasSum_fullDivisor_on_criticalTraceTests_vol
  have hone (r : ℂ) : mellinAt(φ.val, 1, r) =
      ∫ g, (φ.val : D𝔽).val g * (((ideleClassNorm F g : ℝ≥0) : ℝ) : ℂ) ^ r ∂μ𝔽 := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
    change (φ.val : D𝔽).val g * ((1 : ℂ) * (((ideleClassNorm F g : ℝ≥0) : ℝ) : ℂ) ^ r) =
      (φ.val : D𝔽).val g * (((ideleClassNorm F g : ℝ≥0) : ℝ) : ℂ) ^ r
    rw [one_mul]
  refine ⟨a, b, ha, hb, ?_, ?_⟩
  · have hf : Summable (fun v : V => finite v φ.val) := hT.summable
    refine hf.congr fun v => ?_
    rw [hbPV v, hasSum_fullDivisor_on_criticalTraceTests_scale]
  · have hA : E (∑ w : InfinitePlace F, arch w) =
        ∑ w : InfinitePlace F, infiniteConnesWeilPrincipalValue w (a w) :=
      (map_sum E arch Finset.univ).trans (Finset.sum_congr rfl fun w _ => haPV w)
    have hF : E (∑' v : V, finite v) = ∑' v : V, finiteTerm(v, b v) / finiteUnitMass(v) :=
      hT.tsum_eq.symm.trans (tsum_congr fun v => by
        rw [show (⇑E ∘ finite) v = (finite v) φ.val from rfl, hbPV v,
          hasSum_fullDivisor_on_criticalTraceTests_scale])
    have hx : E (poles - (∑ w, arch w) - (∑' v, finite v)) =
        E poles - E (∑ w, arch w) - E (∑' v, finite v) :=
      (map_sub E _ _).trans (congrArg (· - E _) (map_sub E _ _))
    have hval : (((normOneIdeleClassTamagawaMeasure F) univ).toReal : ℂ) *
        E (poles - (∑ w, arch w) - (∑' v, finite v)) =
        mellinAt(φ.val, 1, -1 / 2) + mellinAt(φ.val, 1, 1 / 2) -
          (((normOneIdeleClassTamagawaMeasure F) univ).toReal : ℂ) *
            ((∑ w : InfinitePlace F, infiniteConnesWeilPrincipalValue w (a w)) +
              ∑' v : V, finiteTerm(v, b v) / finiteUnitMass(v)) :=
      hasSum_fullDivisor_on_criticalTraceTests_val hvol hx (hpoles φ.val) hA hF
        (hone (-1 / 2)) (hone (1 / 2))
    have hZ := hS.mul_left (((normOneIdeleClassTamagawaMeasure F) univ).toReal : ℂ)
    rw [hval] at hZ
    refine hasSum_fullDivisor_on_criticalTraceTests_hasSum_congr hZ fun z => ?_
    rw [show (⇑E ∘ spectral) z = (spectral z) φ.val from rfl, hspec z φ.val]
    refine (hasSum_fullDivisor_on_criticalTraceTests_mul_div _ _ _ hvol).trans ?_
    have hI : (∫ g, (φ.val : D𝔽).val g *
        (ideleClassNormTwist (F := F) z.val.1.val z.val.2) g *
          (((ideleClassNorm F g : ℝ≥0) : ℝ) : ℂ) ^ (-1 / 2 : ℂ) ∂μ𝔽) =
        mellinAt(φ.val, z.val.1.val, z.val.2 - 1 / 2) := by
      refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
      have hn : ((((ideleClassNorm F g : ℝ≥0) : ℝ)) : ℂ) ≠ 0 :=
        Complex.ofReal_ne_zero.mpr (NNReal.coe_pos.mpr (Units.zero_lt _)).ne'
      change (φ.val : D𝔽).val g * (_ * ((((ideleClassNorm F g : ℝ≥0) : ℝ)) : ℂ) ^ z.val.2) *
          ((((ideleClassNorm F g : ℝ≥0) : ℝ)) : ℂ) ^ (-1 / 2 : ℂ) =
        (φ.val : D𝔽).val g *
          (_ * ((((ideleClassNorm F g : ℝ≥0) : ℝ)) : ℂ) ^ (z.val.2 - 1 / 2))
      exact hasSum_fullDivisor_on_criticalTraceTests_cpow _ _ _ _ hn
    rw [hI]
    rfl

-- TODO(paper-gap): The inference to the divisor statement cites “Theorem ??”
-- without identifying the theorem to be combined with Theorem 13.3.1.1.
-- TODO(paper-gap): Theorem 13.3.1.2 has only a title. Footnotes 2 and 3 ask for
-- the statement, proof, and an approximation by tests tending to e^(−s|log t|)
-- for Re(s) > 1.

end RiemannMasullo
