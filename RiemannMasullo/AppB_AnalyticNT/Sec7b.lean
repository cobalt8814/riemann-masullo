module

public import RiemannMasullo.AppB_AnalyticNT.Sec7a
public import RiemannMasullo.AppB_AnalyticNT.Sec5
public import Mathlib.NumberTheory.Harmonic.EulerMascheroni

/-!
# Norm-ordered Euler products on the 1-line

Masullo, §B.7.2, pp. 648–653. The logarithmic series is grouped by prime-power
norm. The Euler products and the prime sum use a strict cutoff on prime norm.
-/

@[expose] public noncomputable section

open Filter IsDedekindDomain NumberField Set
open scoped Topology

namespace RiemannMasullo

variable {F : Type*} [Field F] [NumberField F]

local notation "U[" F "]" => PontryaginDual (IdeleClassGroup (𝓞 F) F)
local notation "V[" F "]" => HeightOneSpectrum (𝓞 F)
local notation "halfPlane" => Complex.re ⁻¹' Ioi (1 : ℝ)

/-- Paper: Equation (B.7.2.2), p. 649. The function `g_n` uses the
oscillatory pole term with its constant term subtracted.
Deviation: At the removable singularity we use the limiting value `log n`
for positive `n`. -/
def heckePrimePowerTailOscillation (t₀ : ℝ) (n : ℕ) (s : ℂ) : ℂ :=
  if s = ⟨1, t₀⟩ then (Real.log n : ℂ)
  else ((n : ℂ) ^ ((⟨1, t₀⟩ : ℂ) - s) - 1) / ((⟨1, t₀⟩ : ℂ) - s)

/-- Paper: Equations (B.7.2.2) and (B.7.2.12), pp. 649–650.
For positive `n`, the oscillatory term tends to `log n` at the pole ordinate.
Deviation: The printed proof gives the opposite sign for `g_n / log n`. -/
theorem heckePrimePowerTailOscillation_tendsto_at_pole
    (t₀ : ℝ) {n : ℕ} (hn : 0 < n) :
    Tendsto (heckePrimePowerTailOscillation t₀ n)
      (𝓝[≠] (⟨1, t₀⟩ : ℂ)) (𝓝 (Real.log n : ℂ)) := by
  sorry

/-- Paper: Remark B.7.2.2, p. 649. Index `k` represents the positive
exponent `k + 1`. The ideal character is zero on ramified prime powers. -/
def heckePrimePowerLogTerm (χ : U[F]) (v : V[F]) (k : ℕ) (s : ℂ) : ℂ :=
  heckeIdealValue (ideleClassNormTwist χ 0) (v.asIdeal ^ (k + 1)) /
    ((k + 1 : ℕ) * ((v.asIdeal ^ (k + 1)).absNorm : ℂ) ^ s)

/-- Paper: Equation (B.7.2.15), p. 651. The exponent-one logarithmic term is
the ordinary prime term of the Hecke Dirichlet series. -/
theorem heckePrimePowerLogTerm_zero (χ : U[F]) (v : V[F]) (s : ℂ) :
    heckePrimePowerLogTerm χ v 0 s =
      heckeIdealValue (ideleClassNormTwist χ 0) v.asIdeal / (v.asIdeal.absNorm : ℂ) ^ s := by
  sorry

/-- Paper: Remark B.7.2.2 and Equation (B.7.2.4), p. 649. Dividing the
norm-grouped von Mangoldt coefficient by the logarithm of the norm gives
the coefficient of the logarithmic Euler series. The norms zero and one
have coefficient zero. -/
def heckePrimePowerLogCoefficient (χ : U[F]) (n : ℕ) : ℂ :=
  heckeLogDerivCoefficient (ideleClassNormTwist χ 0) n / (Real.log n : ℂ)

/-- Paper: Remark B.7.2.2, p. 649. The coefficient at `n` sums
`χ(𝔭^m) / m` over the positive prime powers of norm exactly `n`. -/
theorem heckePrimePowerLogCoefficient_eq_sum (χ : U[F]) (n : ℕ) :
    heckePrimePowerLogCoefficient χ n =
      ∑ᶠ a : {a : V[F] × ℕ // a.1.asIdeal.absNorm ^ (a.2 + 1) = n},
        heckeIdealValue (ideleClassNormTwist χ 0) (a.val.1.asIdeal ^ (a.val.2 + 1)) /
          ((a.val.2 + 1 : ℕ) : ℂ) := by
  classical
  let P (a : {a : V[F] × ℕ // a.1.asIdeal.absNorm ^ (a.2 + 1) = n}) :
      {I : Ideal (𝓞 F) // I ≠ ⊥ ∧ I.absNorm = n} :=
    ⟨a.val.1.asIdeal ^ (a.val.2 + 1), pow_ne_zero _ a.val.1.ne_bot, by
      rw [map_pow]; exact a.property⟩
  have hP : Function.Injective P := by
    rintro ⟨⟨v, k⟩, hk⟩ ⟨⟨w, j⟩, hj⟩ he
    have heq : v.asIdeal ^ (k + 1) = w.asIdeal ^ (j + 1) := congrArg Subtype.val he
    obtain rfl := HeightOneSpectrum.eq_of_dvd_pow ((dvd_pow_self _ k.succ_ne_zero).trans heq.dvd)
    exact Subtype.ext (Prod.ext rfl
      (Nat.succ.inj (pow_injective_of_not_isUnit v.prime.not_isUnit v.ne_bot heq)))
  have : Finite {I : Ideal (𝓞 F) // I ≠ ⊥ ∧ I.absNorm = n} :=
    ((Ring.HasFiniteQuotients.finite_absNorm_eq (S := 𝓞 F) n).subset
      (show {I : Ideal (𝓞 F) | I ≠ ⊥ ∧ I.absNorm = n} ⊆ {I | I.absNorm = n} from
        fun I hI ↦ hI.2)).to_subtype
  have : Finite {a : V[F] × ℕ // a.1.asIdeal.absNorm ^ (a.2 + 1) = n} := Finite.of_injective P hP
  have : Fintype {I : Ideal (𝓞 F) // I ≠ ⊥ ∧ I.absNorm = n} := Fintype.ofFinite _
  have : Fintype {a : V[F] × ℕ // a.1.asIdeal.absNorm ^ (a.2 + 1) = n} := Fintype.ofFinite _
  delta heckePrimePowerLogCoefficient heckeLogDerivCoefficient
  rw [finsum_eq_sum_of_fintype,
    finsum_eq_sum_of_fintype, Finset.sum_div]
  symm
  refine Fintype.sum_of_injective P hP _ _ (fun I hI ↦ ?_) (fun a ↦ ?_)
  · have h : ¬ ∃ v : V[F], ∃ k : ℕ, 0 < k ∧ I.val = v.asIdeal ^ k := by
      rintro ⟨v, _ | k, hk, he⟩
      · exact hk.false
      · refine hI ⟨⟨(v, k), ?_⟩, Subtype.ext he.symm⟩
        have h2 := I.property.2
        rw [he, map_pow] at h2
        exact h2
    simp [heckeIdealVonMangoldt, idealVonMangoldt, h]
  · obtain ⟨⟨v, k⟩, hk⟩ := a
    have hN : (1 : ℝ) < v.asIdeal.absNorm := by
      exact_mod_cast HeightOneSpectrum.one_lt_absNorm v
    have hlog : Complex.log (v.asIdeal.absNorm : ℂ) ≠ 0 := by
      rw [← Complex.ofReal_natCast, ← Complex.ofReal_log (Nat.cast_nonneg _)]
      exact Complex.ofReal_ne_zero.mpr (Real.log_pos hN).ne'
    have hk1 : ((k : ℂ) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero k
    simp only [P, heckeIdealVonMangoldt, idealVonMangoldt_prime_pow v k.succ_pos]
    rw [← hk, Nat.cast_pow, Real.log_pow]
    push_cast
    field_simp

/-- Paper: Remark B.7.2.2, p. 649. This is the Dirichlet term for each
integer norm, with the terms below the cutoff replaced by zero. -/
def heckePrimePowerLogTailTerm (χ : U[F]) (x : ℝ) (s : ℂ) (n : ℕ) : ℂ :=
  if x ≤ (n : ℝ) then LSeries.term (heckePrimePowerLogCoefficient χ) s n else 0

/-- Paper: Remark B.7.2.2, p. 649. At a positive integer norm equal to the
cutoff, the tail includes the full Dirichlet term for that norm. -/
theorem heckePrimePowerLogTailTerm_at_cutoff (χ : U[F]) (s : ℂ) {n : ℕ} (hn : 0 < n) :
    heckePrimePowerLogTailTerm χ n s n =
      heckePrimePowerLogCoefficient χ n / (n : ℂ) ^ s := by
  sorry

/-- Paper: Remark B.7.2.2, p. 649. The logarithmic tail sums the norm-grouped
terms in increasing order of integer norm, starting at the first norm at least `x`. -/
def heckePrimePowerLogTail (χ : U[F]) (x : ℝ) (s : ℂ) : ℂ :=
  tsum (heckePrimePowerLogTailTerm χ x s) (SummationFilter.conditional ℕ)

/-- The norm of a prime-power logarithmic term is at most the inverse real power of the
ideal norm, since the character value has norm at most one and the exponent is positive. -/
private theorem heckePrimePowerLogTerm_norm_le (χ : U[F]) (v : V[F]) (k : ℕ) (s : ℂ) :
    ‖heckePrimePowerLogTerm χ v k s‖ ≤
      ((v.asIdeal ^ (k + 1)).absNorm : ℝ) ^ (-s.re) := by
  have hN : (0 : ℝ) < ((v.asIdeal ^ (k + 1)).absNorm : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr (pow_ne_zero _ v.ne_bot))
  have hχ : ‖heckeIdealValue (ideleClassNormTwist χ 0) (v.asIdeal ^ (k + 1))‖ ≤ 1 := by
    rw [heckeIdealValue_prime_pow _ v (Nat.succ_pos k)]
    split_ifs with h
    · rw [norm_pow, norm_ideleClassNormTwist_zero_localValue, one_pow]
    · simp
  have hk : (1 : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.le_add_left 1 k
  have hpow : (0 : ℝ) < ((v.asIdeal ^ (k + 1)).absNorm : ℝ) ^ s.re :=
    Real.rpow_pos_of_pos hN _
  calc ‖heckePrimePowerLogTerm χ v k s‖
      = ‖heckeIdealValue (ideleClassNormTwist χ 0) (v.asIdeal ^ (k + 1))‖ /
          (((k + 1 : ℕ) : ℝ) * ((v.asIdeal ^ (k + 1)).absNorm : ℝ) ^ s.re) := by
        delta heckePrimePowerLogTerm
        rw [norm_div, norm_mul, Complex.norm_natCast,
          ← Complex.ofReal_natCast ((v.asIdeal ^ (k + 1)).absNorm),
          Complex.norm_cpow_eq_rpow_re_of_pos hN]
    _ ≤ 1 / (((k + 1 : ℕ) : ℝ) * ((v.asIdeal ^ (k + 1)).absNorm : ℝ) ^ s.re) :=
        div_le_div_of_nonneg_right hχ (by positivity)
    _ ≤ 1 / ((v.asIdeal ^ (k + 1)).absNorm : ℝ) ^ s.re :=
        one_div_le_one_div_of_le hpow (le_mul_of_one_le_left hpow.le hk)
    _ = ((v.asIdeal ^ (k + 1)).absNorm : ℝ) ^ (-s.re) := by
        rw [Real.rpow_neg hN.le, one_div]

/-- To the right of one, the prime-power logarithmic terms are summable over all prime
powers, by comparison with the convergent sum of inverse ideal-norm powers. -/
private theorem summable_heckePrimePowerLogTerm_of_one_lt_re (χ : U[F]) (s : halfPlane) :
    Summable (fun a : V[F] × ℕ ↦ heckePrimePowerLogTerm χ a.1 a.2 s) := by
  classical
  let P (a : V[F] × ℕ) : {I : Ideal (𝓞 F) // I ≠ ⊥} :=
    ⟨a.1.asIdeal ^ (a.2 + 1), pow_ne_zero _ a.1.ne_bot⟩
  have hP : Function.Injective P := by
    rintro ⟨v, k⟩ ⟨w, j⟩ he
    have heq : v.asIdeal ^ (k + 1) = w.asIdeal ^ (j + 1) := congrArg Subtype.val he
    obtain rfl := HeightOneSpectrum.eq_of_dvd_pow ((dvd_pow_self _ k.succ_ne_zero).trans heq.dvd)
    exact Prod.ext rfl (Nat.succ.inj (pow_injective_of_not_isUnit v.prime.not_isUnit v.ne_bot heq))
  have hr : 1 < (s : ℂ).re := s.property
  have hs := ((summable_absNorm_rpow F hr).subtype (fun I ↦ I ≠ ⊥)).comp_injective hP
  exact hs.of_norm_bounded (fun a ↦ heckePrimePowerLogTerm_norm_le χ a.1 a.2 s)

/-- The prime powers of a fixed integer norm form a finite set, since their ideals are
nonzero ideals of that norm. -/
private theorem heckePrimePowerLogTail_fiber_finite (n : ℕ) :
    Finite {a : V[F] × ℕ // a.1.asIdeal.absNorm ^ (a.2 + 1) = n} := by
  classical
  let P (a : {a : V[F] × ℕ // a.1.asIdeal.absNorm ^ (a.2 + 1) = n}) :
      {I : Ideal (𝓞 F) // I ≠ ⊥ ∧ I.absNorm = n} :=
    ⟨a.val.1.asIdeal ^ (a.val.2 + 1), pow_ne_zero _ a.val.1.ne_bot, by
      rw [map_pow]; exact a.property⟩
  have hP : Function.Injective P := by
    rintro ⟨⟨v, k⟩, hk⟩ ⟨⟨w, j⟩, hj⟩ he
    have heq : v.asIdeal ^ (k + 1) = w.asIdeal ^ (j + 1) := congrArg Subtype.val he
    obtain rfl := HeightOneSpectrum.eq_of_dvd_pow ((dvd_pow_self _ k.succ_ne_zero).trans heq.dvd)
    exact Subtype.ext (Prod.ext rfl
      (Nat.succ.inj (pow_injective_of_not_isUnit v.prime.not_isUnit v.ne_bot heq)))
  have : Finite {I : Ideal (𝓞 F) // I ≠ ⊥ ∧ I.absNorm = n} :=
    ((Ring.HasFiniteQuotients.finite_absNorm_eq (S := 𝓞 F) n).subset
      (show {I : Ideal (𝓞 F) | I ≠ ⊥ ∧ I.absNorm = n} ⊆ {I | I.absNorm = n} from
        fun I hI ↦ hI.2)).to_subtype
  exact Finite.of_injective P hP

/-- Paper: Remark B.7.2.2, p. 649, and the absolute convergence on p. 653.
To the right of one the same tail is the absolute sum over prime powers
whose norms are at least the cutoff. -/
theorem heckePrimePowerLogTail_hasSum_of_one_lt_re (χ : U[F]) (x : ℝ) (s : halfPlane) :
    HasSum (fun a : {a : V[F] × ℕ // x ≤ ((a.1.asIdeal.absNorm ^ (a.2 + 1) : ℕ) : ℝ)} ↦
      heckePrimePowerLogTerm χ a.val.1 a.val.2 s) (heckePrimePowerLogTail χ x s) := by
  classical
  let S := {a : V[F] × ℕ // x ≤ ((a.1.asIdeal.absNorm ^ (a.2 + 1) : ℕ) : ℝ)}
  let f (a : S) : ℂ := heckePrimePowerLogTerm χ a.val.1 a.val.2 s
  let Nfn (a : S) : ℕ := a.val.1.asIdeal.absNorm ^ (a.val.2 + 1)
  have hsum : Summable f :=
    (summable_heckePrimePowerLogTerm_of_one_lt_re χ s).subtype
      (fun a ↦ x ≤ ((a.1.asIdeal.absNorm ^ (a.2 + 1) : ℕ) : ℝ))
  have hfib := hsum.hasSum.tsum_fiberwise Nfn
  have hterm : (fun n : ℕ ↦ ∑' a : Nfn ⁻¹' {n}, f a) = heckePrimePowerLogTailTerm χ x s := by
    funext n
    by_cases hxn : x ≤ (n : ℝ)
    · by_cases hn : n = 0
      · subst hn
        haveI : IsEmpty (↥(Nfn ⁻¹' {0})) := ⟨fun a ↦ by
          have ha : Nfn a.val = 0 := a.property
          have hpos : 0 < Nfn a.val :=
            pow_pos (Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr a.val.val.1.ne_bot)) _
          exact (Nat.pos_iff_ne_zero.mp hpos) ha⟩
        rw [tsum_empty]
        simp only [heckePrimePowerLogTailTerm, hxn, ↓reduceIte, LSeries.term_zero]
      · simp only [heckePrimePowerLogTailTerm, hxn, ↓reduceIte]
        let T := {a : V[F] × ℕ // a.1.asIdeal.absNorm ^ (a.2 + 1) = n}
        haveI : Finite T := heckePrimePowerLogTail_fiber_finite n
        haveI : Fintype T := Fintype.ofFinite _
        let e : ↥(Nfn ⁻¹' {n}) ≃ T :=
          { toFun := fun a ↦ ⟨a.val.val, a.property⟩
            invFun := fun b ↦ ⟨⟨b.val, by
              have hb : ((b.val.1.asIdeal.absNorm ^ (b.val.2 + 1) : ℕ) : ℝ) = (n : ℝ) := by
                exact_mod_cast b.property
              exact hb.symm ▸ hxn⟩, b.property⟩
            left_inv := fun _ ↦ rfl
            right_inv := fun _ ↦ rfl }
        haveI : Fintype ↥(Nfn ⁻¹' {n}) := Fintype.ofEquiv T e.symm
        rw [tsum_fintype,
          Fintype.sum_equiv e (fun a ↦ f a)
            (fun b ↦ heckePrimePowerLogTerm χ b.val.1 b.val.2 s) (fun _ ↦ rfl)]
        have hpoint (b : T) : heckePrimePowerLogTerm χ b.val.1 b.val.2 s =
            (heckeIdealValue (ideleClassNormTwist χ 0) (b.val.1.asIdeal ^ (b.val.2 + 1)) /
              ((b.val.2 + 1 : ℕ) : ℂ)) / (n : ℂ) ^ (s : ℂ) := by
          delta heckePrimePowerLogTerm
          have hNc : ((b.val.1.asIdeal ^ (b.val.2 + 1)).absNorm : ℂ) = (n : ℂ) := by
            have hp : (b.val.1.asIdeal ^ (b.val.2 + 1)).absNorm =
                b.val.1.asIdeal.absNorm ^ (b.val.2 + 1) := by rw [map_pow]
            rw [hp]
            exact_mod_cast b.property
          rw [hNc, div_div]
        simp_rw [hpoint]
        rw [← Finset.sum_div, ← finsum_eq_sum_of_fintype,
          ← heckePrimePowerLogCoefficient_eq_sum, LSeries.term_of_ne_zero hn]
    · haveI : IsEmpty (↥(Nfn ⁻¹' {n})) := ⟨fun a ↦ by
        have ha : Nfn a.val = n := a.property
        have hx : x ≤ (Nfn a.val : ℝ) := a.val.property
        exact hxn (by rw [ha] at hx; exact hx)⟩
      rw [tsum_empty]
      simp only [heckePrimePowerLogTailTerm, hxn, ↓reduceIte]
  have hfib' : HasSum (heckePrimePowerLogTailTerm χ x s) (∑' a : S, f a) := by
    rw [← hterm]
    exact hfib
  have htail : Summable (heckePrimePowerLogTailTerm χ x s) := ⟨_, hfib'⟩
  have hL : heckePrimePowerLogTail χ x s = ∑' a : S, f a := by
    delta heckePrimePowerLogTail
    rw [tsum_eq_of_summable_unconditional htail, hfib'.tsum_eq]
  rw [hL]
  exact hsum.hasSum

local notation "invLog(" n ")" => ((Real.log ((n : ℕ) : ℝ) : ℂ)⁻¹)

/-- Paper: Equations (B.7.2.1) and (B.7.2.19), pp. 649 and 652. These
are the oscillatory summands weighted by the difference of reciprocal
logarithms at successive norms at or above the cutoff. -/
def heckePrimePowerTailOscillationTerm (t₀ x : ℝ) (s : ℂ) (n : ℕ) : ℂ :=
  if x ≤ (n : ℝ) then
    heckePrimePowerTailOscillation t₀ (n - 1) s * (invLog(n) - invLog(n - 1))
  else 0

/-- Paper: Equations (B.7.2.1) and (B.7.2.19), pp. 649 and 652. The weighted
oscillatory terms are summable on the 1-line away from the pole.
Deviation: The cutoff is greater than two so the reciprocal logarithms
in the tail have nonzero denominators. -/
theorem summable_heckePrimePowerTailOscillationTerm (t₀ x t : ℝ) (hx : 2 < x) (ht : t ≠ t₀) :
    Summable (heckePrimePowerTailOscillationTerm t₀ x ⟨1, t⟩) := by
  sorry

/-- Paper: Theorem B.7.2.1(1), pp. 649–651. For a pure norm character,
the grouped logarithmic tail converges uniformly on compact sets away from
the pole. The oscillatory terms give the displayed main term and the continuous
error is bounded uniformly by `2 ε / log x`.
Deviation: The formula holds for all sufficiently large real cutoffs. Partial summation
uses only integer endpoints, including `M - 1`. The threshold exceeds two. -/
theorem heckePrimePowerLogTail_normTwist (χ : U[F]) (t₀ : ℝ)
    (hχ : ideleClassNormTwist χ 0 = ideleClassNormTwist (1 : U[F]) (-Complex.I * t₀))
    (K : Set ℝ) (hK : IsCompact K) (hpole : t₀ ∉ K) {ε : ℝ} (hε : 0 < ε) :
    ∃ x₀ : ℝ, 2 < x₀ ∧ ∀ x ≥ x₀,
      TendstoUniformlyOn
        (fun N : ℕ ↦ fun t : ℝ ↦
          ∑ n ∈ Finset.range N, heckePrimePowerLogTailTerm χ x ⟨1, t⟩ n)
        (fun t : ℝ ↦ heckePrimePowerLogTail χ x ⟨1, t⟩) atTop K ∧
      ∃ error : ℝ → ℂ, ContinuousOn error K ∧ ∀ t ∈ K,
        ‖error t‖ ≤ 2 * ε / Real.log x ∧
        heckePrimePowerLogTail χ x ⟨1, t⟩ =
          -heckePrimePowerTailOscillation t₀ (⌈x⌉₊ - 1) ⟨1, t⟩ * invLog(⌈x⌉₊ - 1) +
            error t - ∑' n : ℕ, heckePrimePowerTailOscillationTerm t₀ x ⟨1, t⟩ n := by
  sorry

/-- Paper: Theorem B.7.2.1(2), pp. 649–651. For a character nontrivial on
the norm-one subgroup the grouped tail converges uniformly on each compact set
on the 1-line. Its limit is continuous and uniformly smaller than `2 ε / log x`.
Deviation: The compact set of ordinates refers to `1 + iK`, as in the
equation and the convergence clause. -/
theorem heckePrimePowerLogTail_of_nontrivial_on_normOne (χ : U[F])
    (hχ : χ.toMonoidHom.comp (ideleClassNorm F).ker.subtype ≠ 1)
    (K : Set ℝ) (hK : IsCompact K) {ε : ℝ} (hε : 0 < ε) :
    ∃ x₀ : ℝ, 1 < x₀ ∧ ∀ x ≥ x₀,
      TendstoUniformlyOn
        (fun N : ℕ ↦ fun t : ℝ ↦
          ∑ n ∈ Finset.range N, heckePrimePowerLogTailTerm χ x ⟨1, t⟩ n)
        (fun t : ℝ ↦ heckePrimePowerLogTail χ x ⟨1, t⟩) atTop K ∧
      ContinuousOn (fun t : ℝ ↦ heckePrimePowerLogTail χ x ⟨1, t⟩) K ∧
      ∀ t ∈ K, ‖heckePrimePowerLogTail χ x ⟨1, t⟩‖ < 2 * ε / Real.log x := by
  sorry

-- TODO(paper-gap): The proof on p. 651 uses a uniform bound for the Perron error
-- on the entire 1-line. The compact-set estimates of §B.7.1 suffice here.

/-- Paper: Equation (B.7.2.15), p. 651. This finite set contains the
finite places whose prime ideals have norm strictly below `x`. -/
def heckePrimesBelow (F : Type*) [Field F] [NumberField F] (x : ℝ) : Finset (V[F]) :=
  (Ring.HasFiniteQuotients.finite_absNorm_heightOneSpectrum_le (S := 𝓞 F)
    (⌈x⌉₊ - 1)).toFinset

/-- Paper: Equation (B.7.2.15), p. 651. The strict cutoff excludes primes of
norm exactly `x`, including when `x` is an integer. -/
theorem heckePrimesBelow_mem_iff (v : V[F]) (x : ℝ) :
    v ∈ heckePrimesBelow F x ↔ (v.asIdeal.absNorm : ℝ) < x := by
  sorry

/-- Paper: Corollary B.7.2.3, p. 651. For a character nontrivial on the
norm-one subgroup, the prime sum converges locally uniformly on the 1-line. -/
theorem heckePrimeSum_tendstoLocallyUniformly_of_nontrivial_on_normOne (χ : U[F])
    (hχ : χ.toMonoidHom.comp (ideleClassNorm F).ker.subtype ≠ 1) :
    ∃ limit : ℝ → ℂ, TendstoLocallyUniformly
      (fun x : ℝ ↦ fun t : ℝ ↦
        ∑ v ∈ heckePrimesBelow F x, heckePrimePowerLogTerm χ v 0 ⟨1, t⟩)
      limit atTop := by
  sorry

/-- Paper: Corollary B.7.2.3, p. 651. For a pure norm character, the
prime sum converges locally uniformly on the 1-line away from the pole. -/
theorem heckePrimeSum_tendstoLocallyUniformlyOn_normTwist (χ : U[F]) (t₀ : ℝ)
    (hχ : ideleClassNormTwist χ 0 = ideleClassNormTwist (1 : U[F]) (-Complex.I * t₀)) :
    ∃ limit : ℝ → ℂ, TendstoLocallyUniformlyOn
      (fun x : ℝ ↦ fun t : ℝ ↦
        ∑ v ∈ heckePrimesBelow F x, heckePrimePowerLogTerm χ v 0 ⟨1, t⟩)
      limit atTop ({t₀}ᶜ : Set ℝ) := by
  sorry

/-- Paper: Equation (B.7.2.17), p. 652. The reciprocal partial Euler product
uses the finite Euler factors with prime norm strictly below the cutoff.
Deviation: The strict cutoff extends the definition to real `x`. -/
def reciprocalHeckeEulerProductBelow (χ : U[F]) (x : ℝ) (s : ℂ) : ℂ :=
  reciprocalPartialHeckeEulerProduct χ (heckePrimesBelow F x) s

/-- Paper: Equation (B.7.2.17), p. 652. Each prime below the strict cutoff
contributes its linear Euler polynomial, with coefficient zero at ramified primes. -/
theorem reciprocalHeckeEulerProductBelow_eq_prod (χ : U[F]) (x : ℝ) (s : ℂ) :
    reciprocalHeckeEulerProductBelow χ x s =
      ∏ v ∈ heckePrimesBelow F x,
        (1 - heckeIdealValue (ideleClassNormTwist χ 0) v.asIdeal *
          (v.asIdeal.absNorm : ℂ) ^ (-s)) := by
  sorry

/-- Paper: Equation (B.7.2.19), p. 652. This is the oscillatory part of
the logarithmic tail for a pure norm character, evaluated at ordinate `t`.
Deviation: The first term uses `t₀ - t` in its denominator, as required by
Equation (B.7.2.1). Its use is on the complement of the pole ordinate. -/
def heckeEulerProductOscillation (t₀ x t : ℝ) : ℂ :=
  -heckePrimePowerTailOscillation t₀ (⌈x⌉₊ - 1) ⟨1, t⟩ * invLog(⌈x⌉₊ - 1) -
    ∑' n : ℕ, heckePrimePowerTailOscillationTerm t₀ x ⟨1, t⟩ n

/-- Paper: Equation (B.7.2.19), p. 652. On compact sets away from the pole,
the endpoint term minus the finite correction sums converges uniformly to `G_x`.
Deviation: The cutoff is greater than two so `log (M - 1)` is nonzero. -/
theorem heckeEulerProductOscillation_tendstoUniformlyOn (t₀ x : ℝ) (hx : 2 < x)
    (K : Set ℝ) (hK : IsCompact K) (hpole : t₀ ∉ K) :
    TendstoUniformlyOn (fun N : ℕ ↦ fun t : ℝ ↦
      -heckePrimePowerTailOscillation t₀ (⌈x⌉₊ - 1) ⟨1, t⟩ * invLog(⌈x⌉₊ - 1) -
        ∑ n ∈ Finset.range N, heckePrimePowerTailOscillationTerm t₀ x ⟨1, t⟩ n)
      (heckeEulerProductOscillation t₀ x) atTop K := by
  sorry

/-- Paper: Theorem B.7.2.4(1), Equation (B.7.2.19), p. 652. The oscillatory
part is real analytic away from the pole ordinate.
Deviation: The cutoff is greater than two so `log (M - 1)` is nonzero. -/
theorem heckeEulerProductOscillation_analyticOnNhd (t₀ x : ℝ) (hx : 2 < x) :
    AnalyticOnNhd ℝ (heckeEulerProductOscillation t₀ x) ({t₀}ᶜ : Set ℝ) := by
  sorry

/-- Paper: Equation (B.7.2.19), p. 652. The oscillatory part is uniformly
`O(1 / log x)` on any compact set of ordinates away from the pole. -/
theorem heckeEulerProductOscillation_bound (t₀ : ℝ)
    (K : Set ℝ) (hK : IsCompact K) (hpole : t₀ ∉ K) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ x : ℝ in atTop, ∀ t ∈ K,
      ‖heckeEulerProductOscillation t₀ x t‖ ≤ C / Real.log x := by
  sorry

/-- Paper: Theorem B.7.2.4(1), p. 652. The correction `H_x` is minus
the logarithmic terms whose primes lie below the cutoff but whose powers
have reached or exceeded it. Such powers have exponent at least two. -/
def heckeEulerProductLogCorrection (χ : U[F]) (x : ℝ) (s : ℂ) : ℂ :=
  -(∑' a : {a : V[F] × ℕ // (a.1.asIdeal.absNorm : ℝ) < x ∧
      x ≤ ((a.1.asIdeal.absNorm ^ (a.2 + 2) : ℕ) : ℝ)},
      heckePrimePowerLogTerm χ a.val.1 (a.val.2 + 1) s)

/-- Paper: Theorem B.7.2.4(1), p. 652. The positive majorant over prime powers
of exponent at least two is summable for an abscissa greater than one half. -/
theorem summable_heckeHigherPrimePowerWeights (F : Type*) [Field F] [NumberField F]
    {σ : ℝ} (hσ : 1 / 2 < σ) :
    Summable (fun a : V[F] × ℕ ↦
      (1 : ℝ) / ((a.2 + 2 : ℕ) * (((a.1.asIdeal.absNorm ^ (a.2 + 2) : ℕ) : ℝ) ^ σ))) := by
  sorry

/-- Paper: Theorem B.7.2.4(1), p. 652. The series defining the correction
converges absolutely and uniformly on half-planes strictly to the right of one half.
Its sum is the negative of `H_x`. -/
theorem heckeEulerProductLogCorrection_hasSumUniformlyOn (χ : U[F]) (x : ℝ)
    {σ : ℝ} (hσ : 1 / 2 < σ) :
    HasSumUniformlyOn
      (fun (a : {a : V[F] × ℕ // (a.1.asIdeal.absNorm : ℝ) < x ∧
        x ≤ ((a.1.asIdeal.absNorm ^ (a.2 + 2) : ℕ) : ℝ)}) s ↦
        heckePrimePowerLogTerm χ a.val.1 (a.val.2 + 1) s)
      (fun s ↦ -heckeEulerProductLogCorrection χ x s) {s : ℂ | σ ≤ s.re} := by
  sorry

/-- Paper: Theorem B.7.2.4(1), p. 652. The correction has norm at most
the tail of the positive majorant with prime-power norm at least `x`.
Deviation: The absolute majorant is evaluated at the real part of `s`. -/
theorem heckeEulerProductLogCorrection_norm_le (χ : U[F]) (x : ℝ) (s : ℂ)
    (hs : 1 / 2 < s.re) :
    ‖heckeEulerProductLogCorrection χ x s‖ ≤
      ∑' a : {a : V[F] × ℕ // x ≤ ((a.1.asIdeal.absNorm ^ (a.2 + 2) : ℕ) : ℝ)},
        (1 : ℝ) / ((a.val.2 + 2 : ℕ) *
          (((a.val.1.asIdeal.absNorm ^ (a.val.2 + 2) : ℕ) : ℝ) ^ s.re)) := by
  sorry

/-- Paper: Theorem B.7.2.4(1), p. 652. The correction tends to zero
uniformly on the whole 1-line. -/
theorem heckeEulerProductLogCorrection_tendstoUniformly (χ : U[F]) :
    TendstoUniformly (fun x : ℝ ↦ fun t : ℝ ↦ heckeEulerProductLogCorrection χ x ⟨1, t⟩)
      (fun _ ↦ 0) atTop := by
  sorry

/-- Paper: Theorem B.7.2.4(1), p. 652. Off the pole, multiplying the
reciprocal partial product by the continued finite L-function gives the
exponential of the oscillation, the cutoff correction and a small continuous error.
Deviation: Uses the sign-corrected oscillation from Equation (B.7.2.19).
The cutoff threshold is greater than two. Real cutoffs have the same strict
norm rule as integer cutoffs. -/
theorem reciprocalHeckeEulerProductBelow_mul_normTwist (χ : U[F]) (t₀ : ℝ)
    (hχ : ideleClassNormTwist χ 0 = ideleClassNormTwist (1 : U[F]) (-Complex.I * t₀))
    (L : ℂ → ℂ) (hL : MeromorphicNFOn L univ) (hSeries : ∀ s : halfPlane, L s = finiteHeckeL χ s)
    (K : Set ℝ) (hK : IsCompact K) (hpole : t₀ ∉ K) {ε : ℝ} (hε : 0 < ε) :
    ∃ x₀ : ℝ, 2 < x₀ ∧ ∀ x ≥ x₀,
      ∃ error : ℝ → ℂ, ContinuousOn error K ∧ ∀ t ∈ K,
        ‖error t‖ ≤ 2 * ε / Real.log x ∧
        reciprocalHeckeEulerProductBelow χ x ⟨1, t⟩ * L ⟨1, t⟩ =
          Complex.exp (error t + heckeEulerProductOscillation t₀ x t +
            heckeEulerProductLogCorrection χ x ⟨1, t⟩) := by
  sorry

/-- Paper: Theorem B.7.2.4(1), Equation (B.7.2.20), p. 652. The product
with the finite L-function tends uniformly to one on compact sets away from the pole. -/
theorem reciprocalHeckeEulerProductBelow_mul_tendstoUniformlyOn_normTwist
    (χ : U[F]) (t₀ : ℝ)
    (hχ : ideleClassNormTwist χ 0 = ideleClassNormTwist (1 : U[F]) (-Complex.I * t₀))
    (L : ℂ → ℂ) (hL : MeromorphicNFOn L univ) (hSeries : ∀ s : halfPlane, L s = finiteHeckeL χ s)
    (K : Set ℝ) (hK : IsCompact K) (hpole : t₀ ∉ K) :
    TendstoUniformlyOn
      (fun x : ℝ ↦ fun t : ℝ ↦ reciprocalHeckeEulerProductBelow χ x ⟨1, t⟩ * L ⟨1, t⟩)
      (fun _ ↦ 1) atTop K := by
  sorry

/-- Paper: Theorem B.7.2.4(2), Equation (B.7.2.21), p. 652. For a
character nontrivial on the norm-one subgroup the product with the finite
L-function has an exponential comparison on every compact set of ordinates.
Deviation: Uses `+ H_x` from the definition of the correction, in agreement
with (B.7.2.18). Real cutoffs have the same strict norm rule as integer cutoffs. -/
theorem reciprocalHeckeEulerProductBelow_mul_of_nontrivial_on_normOne (χ : U[F])
    (hχ : χ.toMonoidHom.comp (ideleClassNorm F).ker.subtype ≠ 1)
    (L : ℂ → ℂ) (hL : MeromorphicNFOn L univ) (hSeries : ∀ s : halfPlane, L s = finiteHeckeL χ s)
    (K : Set ℝ) (hK : IsCompact K) {ε : ℝ} (hε : 0 < ε) :
    ∃ x₀ : ℝ, 1 < x₀ ∧ ∀ x ≥ x₀,
      ∃ error : ℝ → ℂ, ContinuousOn error K ∧ ∀ t ∈ K,
        ‖error t‖ ≤ 2 * ε / Real.log x ∧
        reciprocalHeckeEulerProductBelow χ x ⟨1, t⟩ * L ⟨1, t⟩ =
          Complex.exp (error t + heckeEulerProductLogCorrection χ x ⟨1, t⟩) := by
  sorry

/-- Paper: Theorem B.7.2.4(2), Equation (B.7.2.22), p. 652. For a
character nontrivial on the norm-one subgroup the product with the finite
L-function tends uniformly to one on every compact set of ordinates. -/
theorem reciprocalHeckeEulerProductBelow_mul_tendstoUniformlyOn_of_nontrivial_on_normOne
    (χ : U[F]) (hχ : χ.toMonoidHom.comp (ideleClassNorm F).ker.subtype ≠ 1)
    (L : ℂ → ℂ) (hL : MeromorphicNFOn L univ) (hSeries : ∀ s : halfPlane, L s = finiteHeckeL χ s)
    (K : Set ℝ) (hK : IsCompact K) :
    TendstoUniformlyOn
      (fun x : ℝ ↦ fun t : ℝ ↦ reciprocalHeckeEulerProductBelow χ x ⟨1, t⟩ * L ⟨1, t⟩)
      (fun _ ↦ 1) atTop K := by
  sorry

/-- Paper: Equation (B.7.2.23), p. 653. At a regular nonzero point of the
continued L-function on or to the right of the 1-line, the norm-ordered
logarithmic tail and its correction give the reciprocal product comparison.
Deviation: Uses `+ H_x` and exponentiates to avoid selecting a logarithm branch.
The convergence of the ordered sum is explicit. -/
theorem reciprocalHeckeEulerProductBelow_mul_eq_exp_logTail (χ : U[F]) {x : ℝ} (hx : 1 < x)
    (L : ℂ → ℂ) (hL : MeromorphicNFOn L univ) (hSeries : ∀ s : halfPlane, L s = finiteHeckeL χ s)
    (s : ℂ) (hs : 1 ≤ s.re) (hregular : meromorphicOrderAt L s = 0) :
    Summable (heckePrimePowerLogTailTerm χ x s) (SummationFilter.conditional ℕ) ∧
      reciprocalHeckeEulerProductBelow χ x s * L s =
        Complex.exp (heckePrimePowerLogTail χ x s + heckeEulerProductLogCorrection χ x s) := by
  sorry

/-- Paper: Equation (B.7.2.23), p. 653. The logarithmic tail restricted to
primes of norm at least `x`, grouped by prime-power norm, is the full
prime-power tail plus the cutoff correction.
Deviation: Adds `H_x`, which already carries the minus sign. -/
theorem heckePrimePowerLogTail_add_correction (χ : U[F]) (x : ℝ) (s : ℂ)
    (hs : 1 / 2 < s.re)
    (hsum : Summable (heckePrimePowerLogTailTerm χ x s) (SummationFilter.conditional ℕ)) :
    HasSum (fun n : ℕ ↦
      ∑ᶠ a : {a : V[F] × ℕ // x ≤ (a.1.asIdeal.absNorm : ℝ) ∧
        a.1.asIdeal.absNorm ^ (a.2 + 1) = n},
        heckePrimePowerLogTerm χ a.val.1 a.val.2 s)
      (heckePrimePowerLogTail χ x s + heckeEulerProductLogCorrection χ x s)
      (SummationFilter.conditional ℕ) := by
  sorry

/-- Paper: Corollary B.7.2.5, Equation (B.7.2.24), p. 653. For a character
nontrivial on the norm-one subgroup, the prime-norm-ordered Euler product
converges locally uniformly to the continued finite L-function on the 1-line. -/
theorem heckeEulerProductBelow_tendstoLocallyUniformly_of_nontrivial_on_normOne
    (χ : U[F]) (hχ : χ.toMonoidHom.comp (ideleClassNorm F).ker.subtype ≠ 1)
    (L : ℂ → ℂ) (hL : MeromorphicNFOn L univ) (hSeries : ∀ s : halfPlane, L s = finiteHeckeL χ s) :
    TendstoLocallyUniformly
      (fun x : ℝ ↦ fun t : ℝ ↦ ∏ v ∈ heckePrimesBelow F x, finiteHeckeEulerFactor χ v ⟨1, t⟩)
      (fun t : ℝ ↦ L ⟨1, t⟩) atTop := by
  sorry

/-- Paper: Corollary B.7.2.5, Equation (B.7.2.24), p. 653. For a pure
norm character, the prime-norm-ordered Euler product converges locally uniformly
to the continued finite L-function off the pole ordinate. -/
theorem heckeEulerProductBelow_tendstoLocallyUniformlyOn_normTwist (χ : U[F]) (t₀ : ℝ)
    (hχ : ideleClassNormTwist χ 0 = ideleClassNormTwist (1 : U[F]) (-Complex.I * t₀))
    (L : ℂ → ℂ) (hL : MeromorphicNFOn L univ) (hSeries : ∀ s : halfPlane, L s = finiteHeckeL χ s) :
    TendstoLocallyUniformlyOn
      (fun x : ℝ ↦ fun t : ℝ ↦ ∏ v ∈ heckePrimesBelow F x, finiteHeckeEulerFactor χ v ⟨1, t⟩)
      (fun t : ℝ ↦ L ⟨1, t⟩) atTop ({t₀}ᶜ : Set ℝ) := by
  sorry

/-- Paper: Remark B.7.2.6, Equation (B.7.2.25), p. 653. At the pole
ordinate the reciprocal product for a pure norm character equals the untwisted
Mertens product. -/
theorem reciprocalHeckeEulerProductBelow_at_pole_eq_prod (χ : U[F]) (t₀ x : ℝ)
    (hχ : ideleClassNormTwist χ 0 = ideleClassNormTwist (1 : U[F]) (-Complex.I * t₀)) :
    reciprocalHeckeEulerProductBelow χ x ⟨1, t₀⟩ =
      ∏ v ∈ heckePrimesBelow F x, (1 - (v.asIdeal.absNorm : ℂ)⁻¹) := by
  sorry

/-- Paper: Remark B.7.2.6, Equation (B.7.2.25), p. 653. Multiplying
the Mertens product at the pole ordinate by the logarithm of the cutoff gives
a limit of `exp (-γ)` divided by the norm-one class volume. -/
theorem reciprocalHeckeEulerProductBelow_mertens (χ : U[F]) (t₀ : ℝ)
    (hχ : ideleClassNormTwist χ 0 = ideleClassNormTwist (1 : U[F]) (-Complex.I * t₀)) :
    Tendsto (fun x : ℝ ↦ (Real.log x : ℂ) * reciprocalHeckeEulerProductBelow χ x ⟨1, t₀⟩)
      atTop (𝓝 ((Real.exp (-Real.eulerMascheroniConstant) /
        (normOneIdeleClassTamagawaMeasure F univ).toReal : ℝ) : ℂ)) := by
  sorry

/-- Paper: Remark B.7.2.7, p. 653. For a pure norm character the reciprocal
partial products tend locally uniformly on the 1-line to the reciprocal of the
continued finite L-function. Its reciprocal takes the removable value zero at the pole.
Deviation: Local uniform convergence holds across the pole ordinate as well (R27). -/
theorem reciprocalHeckeEulerProductBelow_tendstoLocallyUniformly_normTwist (χ : U[F]) (t₀ : ℝ)
    (hχ : ideleClassNormTwist χ 0 = ideleClassNormTwist (1 : U[F]) (-Complex.I * t₀))
    (L : ℂ → ℂ) (hL : MeromorphicNFOn L univ) (hSeries : ∀ s : halfPlane, L s = finiteHeckeL χ s) :
    TendstoLocallyUniformly (fun x : ℝ ↦ fun t : ℝ ↦ reciprocalHeckeEulerProductBelow χ x ⟨1, t⟩)
      (fun t : ℝ ↦ (L ⟨1, t⟩)⁻¹) atTop := by
  sorry

end RiemannMasullo
