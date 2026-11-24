module

public import RiemannMasullo.AppB_AnalyticNT.Sec7a
public import RiemannMasullo.AppB_AnalyticNT.Sec5
public import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Topology.Algebra.InfiniteSum.TsumUniformlyOn
import RiemannMasullo.ForMathlib.NumberTheory.NumberField.Completion.FinitePlace

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
  have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  have hd : HasDerivAt (fun z : ℂ ↦ (n : ℂ) ^ z) (Real.log n : ℂ) 0 := by
    have h := (hasDerivAt_id (0 : ℂ)).const_cpow (c := (n : ℂ)) (Or.inl hn')
    simpa [Complex.natCast_log] using h
  have hmap : Tendsto (fun s : ℂ ↦ (⟨1, t₀⟩ : ℂ) - s) (𝓝[≠] (⟨1, t₀⟩ : ℂ)) (𝓝[≠] 0) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · have h : Tendsto (fun s : ℂ ↦ (⟨1, t₀⟩ : ℂ) - s) (𝓝 (⟨1, t₀⟩ : ℂ)) (𝓝 0) := by
        have h' :=
          (tendsto_const_nhds (x := (⟨1, t₀⟩ : ℂ)) (f := 𝓝 (⟨1, t₀⟩ : ℂ))).sub tendsto_id
        rw [sub_self] at h'
        exact h'
      exact h.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with s hs
      exact sub_ne_zero.mpr (Ne.symm hs)
  refine ((hasDerivAt_iff_tendsto_slope.mp hd).comp hmap).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with s hs
  have hs' : s ≠ ⟨1, t₀⟩ := hs
  simp [heckePrimePowerTailOscillation, hs', slope_def_field]

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
  simp [heckePrimePowerLogTerm]

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
  simp only [heckePrimePowerLogTailTerm, le_refl, ↓reduceIte]
  rw [LSeries.term_of_ne_zero hn.ne']

/-- Paper: Remark B.7.2.2, p. 649. The logarithmic tail sums the norm-grouped
terms in increasing order of integer norm, starting at the first norm at least `x`. -/
def heckePrimePowerLogTail (χ : U[F]) (x : ℝ) (s : ℂ) : ℂ :=
  tsum (heckePrimePowerLogTailTerm χ x s) (SummationFilter.conditional ℕ)

/-- Paper: Remark B.7.2.2, p. 649, and the absolute convergence on p. 653.
To the right of one the same tail is the absolute sum over prime powers
whose norms are at least the cutoff. -/
theorem heckePrimePowerLogTail_hasSum_of_one_lt_re (χ : U[F]) (x : ℝ) (s : halfPlane) :
    HasSum (fun a : {a : V[F] × ℕ // x ≤ ((a.1.asIdeal.absNorm ^ (a.2 + 1) : ℕ) : ℝ)} ↦
      heckePrimePowerLogTerm χ a.val.1 a.val.2 s) (heckePrimePowerLogTail χ x s) := by
  sorry

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
  have hz0 : 0 < |t₀ - t| := abs_pos.mpr (sub_ne_zero.mpr (Ne.symm ht))
  have hnz : ‖(⟨1, t₀⟩ : ℂ) - ⟨1, t⟩‖ = |t₀ - t| := by
    have hz : (⟨1, t₀⟩ : ℂ) - ⟨1, t⟩ = ((t₀ - t : ℝ) : ℂ) * Complex.I := by
      apply Complex.ext <;> simp
    rw [hz, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
  have hg (k : ℕ) (hk : 0 < k) :
      ‖heckePrimePowerTailOscillation t₀ k ⟨1, t⟩‖ ≤ 2 / |t₀ - t| := by
    have hne : (⟨1, t⟩ : ℂ) ≠ ⟨1, t₀⟩ := fun h ↦ ht (congrArg Complex.im h)
    have hre : ((⟨1, t₀⟩ : ℂ) - ⟨1, t⟩).re = 0 := by simp
    delta heckePrimePowerTailOscillation
    simp only [hne, ↓reduceIte]
    rw [norm_div, hnz]
    gcongr
    refine (norm_sub_le _ _).trans ?_
    rw [Complex.norm_natCast_cpow_of_pos hk, hre, Real.rpow_zero, norm_one]
    norm_num
  let e : ℕ → ℝ := fun m ↦ (Real.log ((m + 2 : ℕ) : ℝ))⁻¹
  have he (m : ℕ) : e m = (Real.log ((m + 2 : ℕ) : ℝ))⁻¹ := rfl
  have he1 (m : ℕ) : e (m + 1) = (Real.log ((m + 3 : ℕ) : ℝ))⁻¹ := rfl
  have he0 (m : ℕ) : 0 ≤ e m :=
    inv_nonneg.mpr (Real.log_nonneg (by norm_cast; omega))
  have hanti' (m : ℕ) :
      (Real.log ((m + 3 : ℕ) : ℝ))⁻¹ ≤ (Real.log ((m + 2 : ℕ) : ℝ))⁻¹ := by
    apply inv_anti₀ (Real.log_pos (by norm_cast; omega))
    exact Real.log_le_log (by positivity) (by norm_cast; omega)
  have hanti (m : ℕ) : e (m + 1) ≤ e m := by
    rw [he1, he]
    exact hanti' m
  have hd : Summable fun m ↦ e m - e (m + 1) := by
    refine summable_of_sum_range_le (c := e 0) (fun m ↦ sub_nonneg.mpr (hanti m))
      fun n ↦ ?_
    rw [Finset.sum_range_sub']
    linarith [he0 n]
  rw [← summable_nat_add_iff 3]
  refine Summable.of_norm_bounded (hd.mul_left (2 / |t₀ - t|)) fun m ↦ ?_
  have hc : ‖((Real.log ((m + 3 : ℕ) : ℝ) : ℂ))⁻¹ - ((Real.log ((m + 3 - 1 : ℕ) : ℝ) : ℂ))⁻¹‖ =
      e m - e (m + 1) := by
    rw [show m + 3 - 1 = m + 2 by omega, he, he1, ← Complex.ofReal_inv, ← Complex.ofReal_inv,
      ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, abs_sub_comm,
      abs_of_nonneg (sub_nonneg.mpr (hanti' m))]
  delta heckePrimePowerTailOscillationTerm
  split_ifs
  · rw [norm_mul, hc]
    exact mul_le_mul_of_nonneg_right (hg _ (by omega)) (sub_nonneg.mpr (hanti m))
  · rw [norm_zero]
    exact mul_nonneg (by positivity) (sub_nonneg.mpr (hanti m))

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

/-- Summation by parts on an integer interval: the weighted sum of first differences
telescopes to boundary terms plus a sum against the successive weight differences. -/
private theorem abel_Ico_identity (R w : ℕ → ℂ) {M N : ℕ} (hM : 1 ≤ M) (hN : M ≤ N) :
    ∑ n ∈ Finset.Ico M (N + 1), (R (n - 1) - R n) * w n =
      R (M - 1) * w M - R N * w N +
        ∑ n ∈ Finset.Ico M N, R n * (w (n + 1) - w n) := by
  induction N, hN using Nat.le_induction with
  | base =>
      rw [Finset.sum_Ico_succ_top (le_refl M)]
      simp
      ring
  | succ N hN ih =>
      rw [Finset.sum_Ico_succ_top (show M ≤ N by omega),
        Finset.sum_Ico_succ_top (show M ≤ N + 1 by omega), ih]
      simp only [Nat.add_sub_cancel]
      ring

/-- Uniform Abel summation for a tail with weights `1 / log n`. If `b n = R (n-1) - R n`
for `n ≥ M` and the remainders `R n` are bounded by `δ` on `K` for `n ≥ M - 1`, then the
weighted tail from `M` has a sum `T` whose partial sums converge uniformly on `K`; the sum
is continuous there and bounded by `2 δ / log M`. -/
private theorem abelTail_uniform (b : ℕ → ℝ → ℂ) (R : ℕ → ℝ → ℂ) (K : Set ℝ)
    {δ : ℝ} (hδ : 0 ≤ δ) {M : ℕ} (hM : 2 ≤ M)
    (hR : ∀ n ≥ M - 1, ∀ t ∈ K, ‖R n t‖ ≤ δ)
    (hb : ∀ n ≥ M, ∀ t, b n t = R (n - 1) t - R n t)
    (hcont : ∀ n, ContinuousOn (b n) K) :
    ∃ T : ℝ → ℂ,
      (∀ t ∈ K, HasSum (fun n : ℕ ↦ if (M : ℝ) ≤ n then b n t / Real.log n else 0)
        (T t) (SummationFilter.conditional ℕ)) ∧
      TendstoUniformlyOn
        (fun N : ℕ ↦ fun t ↦ ∑ n ∈ Finset.range N,
          if (M : ℝ) ≤ n then b n t / Real.log n else 0) T atTop K ∧
      ContinuousOn T K ∧
      ∀ t ∈ K, ‖T t‖ ≤ 2 * δ / Real.log M := by
  classical
  let w : ℕ → ℝ := fun n ↦ (Real.log n)⁻¹
  have hlog2 (n : ℕ) (hn : 2 ≤ n) : 0 < Real.log n := Real.log_pos (by exact_mod_cast hn)
  have hanti (n : ℕ) (hn : 2 ≤ n) : w (n + 1) ≤ w n := by
    apply inv_anti₀ (hlog2 n hn)
    exact Real.log_le_log (by positivity) (by exact_mod_cast Nat.le_succ n)
  have hΔnn (n : ℕ) (hn : 2 ≤ n) : 0 ≤ w n - w (n + 1) := sub_nonneg.mpr (hanti n hn)
  -- The telescoping weight differences sum to the first weight.
  have htele (P : ℕ) (hP : 2 ≤ P) :
      HasSum (fun k : ℕ ↦ (w (k + P) - w (k + 1 + P) : ℝ)) (w P) := by
    have hnn (k : ℕ) : 0 ≤ w (k + P) - w (k + 1 + P) := by
      have := hanti (k + P) (by omega)
      simpa [show k + 1 + P = (k + P) + 1 by omega] using this
    have hsum : Summable (fun k ↦ w (k + P) - w (k + 1 + P)) := by
      refine summable_of_sum_range_le (c := w P) hnn fun n ↦ ?_
      rw [Finset.sum_range_sub', zero_add]
      exact sub_le_self _ (inv_nonneg.mpr (Real.log_nonneg (by norm_cast; omega)))
    have ht : Tendsto (fun n ↦ ∑ k ∈ Finset.range n, (w (k + P) - w (k + 1 + P)))
        atTop (𝓝 (w P)) := by
      have heq : (fun n ↦ ∑ k ∈ Finset.range n, (w (k + P) - w (k + 1 + P))) =
          fun n ↦ w P - w (n + P) := by
        funext n
        rw [Finset.sum_range_sub', zero_add]
      rw [heq]
      have hinv : Tendsto (fun n : ℕ ↦ w (n + P)) atTop (𝓝 0) :=
        tendsto_inv_atTop_zero.comp (Real.tendsto_log_atTop.comp
          (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat P)))
      simpa [sub_zero] using (tendsto_const_nhds (x := w P)).sub hinv
    exact hsum.hasSum_iff_tendsto_nat.mpr ht
  have hΔr (P : ℕ) (hP : 2 ≤ P) :
      Summable (fun k : ℕ ↦ (w (k + P) - w (k + P + 1) : ℝ)) := by
    convert (htele P hP).summable using 1
    funext k
    simp only [show k + 1 + P = k + P + 1 by omega]
  have hΔc (P : ℕ) (hP : 2 ≤ P) :
      Summable (fun k : ℕ ↦ ((w (k + P) - w (k + P + 1) : ℝ) : ℂ)) :=
    Complex.summable_ofReal.mpr (hΔr P hP)
  -- The remainder-weighted difference series is summable, with a uniform tail bound.
  have hRΔ (t : ℝ) (ht : t ∈ K) (P : ℕ) (hP : M ≤ P) :
      Summable (fun k : ℕ ↦ R (k + P) t * ((w (k + P) - w (k + P + 1) : ℝ) : ℂ)) := by
    refine Summable.of_norm_bounded ((hΔr P (by omega)).mul_left δ) fun k ↦ ?_
    have hd := hΔnn (k + P) (by omega)
    calc ‖R (k + P) t * ((w (k + P) - w (k + P + 1) : ℝ) : ℂ)‖
        = ‖R (k + P) t‖ * (w (k + P) - w (k + P + 1)) := by
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hd]
      _ ≤ δ * (w (k + P) - w (k + P + 1)) :=
          mul_le_mul_of_nonneg_right (hR (k + P) (by omega) t ht) hd
  have htailbound (P : ℕ) (hP : M ≤ P) (t : ℝ) (ht : t ∈ K) :
      ‖∑' k : ℕ, R (k + P) t * ((w (k + P) - w (k + P + 1) : ℝ) : ℂ)‖ ≤ δ * w P := by
    refine (norm_tsum_le_tsum_norm (hRΔ t ht P hP).norm).trans ?_
    refine (Summable.tsum_le_tsum (fun k ↦ ?_) (hRΔ t ht P hP).norm
      ((hΔr P (by omega)).mul_left δ)).trans ?_
    · have hd := hΔnn (k + P) (by omega)
      calc ‖R (k + P) t * ((w (k + P) - w (k + P + 1) : ℝ) : ℂ)‖
          = ‖R (k + P) t‖ * (w (k + P) - w (k + P + 1)) := by
            rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hd]
        _ ≤ δ * (w (k + P) - w (k + P + 1)) :=
            mul_le_mul_of_nonneg_right (hR (k + P) (by omega) t ht) hd
    · have := (htele P (by omega)).const_smul δ
      have hcast : (fun k ↦ δ • (w (k + P) - w (k + 1 + P))) =
          fun k ↦ δ * (w (k + P) - w (k + P + 1)) := by
        funext k
        simp only [smul_eq_mul, show k + 1 + P = k + P + 1 by omega]
      rw [hcast] at this
      rw [this.tsum_eq, smul_eq_mul]
  let T : ℝ → ℂ := fun t ↦ R (M - 1) t * (w M : ℂ) -
    ∑' k : ℕ, R (k + M) t * ((w (k + M) - w (k + M + 1) : ℝ) : ℂ)
  have hTbound (t : ℝ) (ht : t ∈ K) : ‖T t‖ ≤ 2 * δ / Real.log M := by
    have hwM : 0 ≤ w M := inv_nonneg.mpr (Real.log_nonneg (by norm_cast; omega))
    have h1 : ‖R (M - 1) t * (w M : ℂ)‖ ≤ δ * w M := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hwM]
      exact mul_le_mul_of_nonneg_right (hR (M - 1) (by omega) t ht) hwM
    calc ‖T t‖ ≤ ‖R (M - 1) t * (w M : ℂ)‖ +
        ‖∑' k : ℕ, R (k + M) t * ((w (k + M) - w (k + M + 1) : ℝ) : ℂ)‖ := norm_sub_le _ _
      _ ≤ δ * w M + δ * w M := add_le_add h1 (htailbound M (le_refl M) t ht)
      _ = 2 * δ / Real.log M := by simp only [w]; ring
  -- Partial sums of the weighted tail, expressed through the remainders.
  have hpartial (P : ℕ) (hP : M + 1 ≤ P) (t : ℝ) :
      ∑ n ∈ Finset.range P, (if (M : ℝ) ≤ n then b n t / Real.log n else 0) =
        R (M - 1) t * (w M : ℂ) - R (P - 1) t * (w (P - 1) : ℂ) -
          ∑ n ∈ Finset.Ico M (P - 1), R n t * ((w n - w (n + 1) : ℝ) : ℂ) := by
    calc ∑ n ∈ Finset.range P, (if (M : ℝ) ≤ n then b n t / Real.log n else 0)
        = ∑ n ∈ Finset.Ico M P, b n t * (w n : ℂ) := by
          have hfilter : (Finset.range P).filter (fun n : ℕ ↦ (M : ℝ) ≤ n) = Finset.Ico M P := by
            ext n
            simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico, Nat.cast_le]
            omega
          rw [← Finset.sum_filter, hfilter]
          apply Finset.sum_congr rfl
          intro n hn
          simp only [w, div_eq_mul_inv, Complex.ofReal_inv]
      _ = R (M - 1) t * (w M : ℂ) - R (P - 1) t * (w (P - 1) : ℂ) -
          ∑ n ∈ Finset.Ico M (P - 1), R n t * ((w n - w (n + 1) : ℝ) : ℂ) := by
          have hid := abel_Ico_identity (fun n ↦ R n t) (fun n ↦ (w n : ℂ))
            (by omega : 1 ≤ M) (show M ≤ P - 1 by omega)
          rw [show (P - 1) + 1 = P by omega] at hid
          have hsum : ∑ n ∈ Finset.Ico M P, b n t * (w n : ℂ) =
              ∑ n ∈ Finset.Ico M P, (R (n - 1) t - R n t) * (w n : ℂ) := by
            apply Finset.sum_congr rfl
            intro n hn
            rw [hb n (Finset.mem_Ico.mp hn).1 t]
          rw [hsum, hid]
          have hneg : ∑ n ∈ Finset.Ico M (P - 1), R n t * (↑(w (n + 1)) - ↑(w n)) =
              -∑ n ∈ Finset.Ico M (P - 1), R n t * ((w n - w (n + 1) : ℝ) : ℂ) := by
            have hfun : (fun n ↦ R n t * (↑(w (n + 1)) - ↑(w n))) =
                (fun n ↦ -(R n t * ((w n - w (n + 1) : ℝ) : ℂ))) := by
              funext n
              push_cast
              ring
            rw [hfun, Finset.sum_neg_distrib]
          rw [hneg]
          ring
  have hdiff (P : ℕ) (hP : M + 1 ≤ P) (t : ℝ) (ht : t ∈ K) :
      T t - ∑ n ∈ Finset.range P, (if (M : ℝ) ≤ n then b n t / Real.log n else 0) =
        R (P - 1) t * (w (P - 1) : ℂ) -
          ∑' k : ℕ, R (k + (P - 1)) t * ((w (k + (P - 1)) - w (k + (P - 1) + 1) : ℝ) : ℂ) := by
    simp only [T]
    rw [hpartial P hP t]
    have hsplit := Summable.sum_add_tsum_nat_add (P - 1 - M) (hRΔ t ht M (le_refl M))
    have hshift : ∑ k ∈ Finset.range (P - 1 - M),
        R (k + M) t * ((w (k + M) - w (k + M + 1) : ℝ) : ℂ) =
        ∑ n ∈ Finset.Ico M (P - 1), R n t * ((w n - w (n + 1) : ℝ) : ℂ) := by
      have hbij : Finset.Ico M (P - 1) = (Finset.range (P - 1 - M)).image (· + M) := by
        ext n
        simp only [Finset.mem_Ico, Finset.mem_image, Finset.mem_range]
        constructor
        · rintro ⟨h1, h2⟩
          refine ⟨n - M, ?_, by omega⟩
          omega
        · rintro ⟨k, hk, rfl⟩
          omega
      rw [hbij, Finset.sum_image]
      · intro a _ b _ hab
        simp only at hab
        exact Nat.add_right_cancel hab
    have hcast : (fun k ↦ R (k + (P - 1 - M) + M) t *
        ((w (k + (P - 1 - M) + M) - w (k + (P - 1 - M) + M + 1) : ℝ) : ℂ)) =
        fun k ↦ R (k + (P - 1)) t * ((w (k + (P - 1)) - w (k + (P - 1) + 1) : ℝ) : ℂ) := by
      funext k
      simp only [show k + (P - 1 - M) + M = k + (P - 1) by omega]
    rw [hcast] at hsplit
    rw [← hsplit, hshift]
    ring
  have hdiffbound (P : ℕ) (hP : M + 1 ≤ P) (t : ℝ) (ht : t ∈ K) :
      ‖T t - ∑ n ∈ Finset.range P, (if (M : ℝ) ≤ n then b n t / Real.log n else 0)‖ ≤
        2 * δ * w (P - 1) := by
    rw [hdiff P hP t ht]
    refine (norm_sub_le _ _).trans ?_
    have hw : 0 ≤ w (P - 1) := inv_nonneg.mpr (Real.log_nonneg (by norm_cast; omega))
    have h1 : ‖R (P - 1) t * (w (P - 1) : ℂ)‖ ≤ δ * w (P - 1) := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hw]
      exact mul_le_mul_of_nonneg_right (hR (P - 1) (by omega) t ht) hw
    have h2 := htailbound (P - 1) (by omega) t ht
    linarith
  have hTUO : TendstoUniformlyOn
      (fun P : ℕ ↦ fun t ↦ ∑ n ∈ Finset.range P,
        if (M : ℝ) ≤ n then b n t / Real.log n else 0) T atTop K := by
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε' hε'
    have hw : Tendsto (fun P : ℕ ↦ 2 * δ * w (P - 1)) atTop (𝓝 0) := by
      have hlog : Tendsto (fun P : ℕ ↦ Real.log ((P - 1 : ℕ) : ℝ)) atTop atTop :=
        Real.tendsto_log_atTop.comp
          (tendsto_natCast_atTop_atTop.comp (tendsto_sub_atTop_nat 1))
      have hinv : Tendsto (fun P : ℕ ↦ w (P - 1)) atTop (𝓝 0) :=
        tendsto_inv_atTop_zero.comp hlog
      simpa using tendsto_const_nhds.mul hinv
    obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hw ε' hε'
    filter_upwards [Filter.eventually_ge_atTop (max N (M + 1))] with P hP
    have hPN : N ≤ P := le_trans (le_max_left _ _) hP
    have hPM : M + 1 ≤ P := le_trans (le_max_right _ _) hP
    intro t ht
    have hbound := hdiffbound P hPM t ht
    have hε : 2 * δ * w (P - 1) < ε' := by
      have hnn : 0 ≤ 2 * δ * w (P - 1) :=
        mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hδ)
          (inv_nonneg.mpr (Real.log_nonneg (by norm_cast; omega)))
      have := hN P hPN
      rwa [Real.dist_eq, sub_zero, abs_of_nonneg hnn] at this
    have hdist : dist (T t) (∑ n ∈ Finset.range P,
        if (M : ℝ) ≤ n then b n t / Real.log n else 0) ≤ 2 * δ * w (P - 1) := by
      rw [dist_eq_norm]
      exact hdiffbound P hPM t ht
    have hlt : dist (T t) (∑ n ∈ Finset.range P,
        if (M : ℝ) ≤ n then b n t / Real.log n else 0) < ε' := lt_of_le_of_lt hdist hε
    simpa [dist_comm] using hlt
  have hcontP (P : ℕ) : ContinuousOn
      (fun t ↦ ∑ n ∈ Finset.range P, if (M : ℝ) ≤ n then b n t / Real.log n else 0) K := by
    induction P with
    | zero =>
        simp
        exact continuousOn_const
    | succ P ih =>
        simp only [Finset.sum_range_succ]
        refine ih.add ?_
        by_cases hMn : (M : ℝ) ≤ P
        · simp only [hMn, ↓reduceIte]
          exact (hcont P).div continuousOn_const fun t ht ↦
            Complex.ofReal_ne_zero.mpr (ne_of_gt (hlog2 P (by
              have hMP : M ≤ P := by exact_mod_cast hMn
              omega)))
        · simp only [hMn, ↓reduceIte]
          exact continuousOn_const
  refine ⟨T, ?_, hTUO, hTUO.continuousOn ?_, hTbound⟩
  · intro t ht
    have hp := hTUO.tendsto_at ht
    rw [HasSum, SummationFilter.conditional_filter_eq_map_range, Filter.tendsto_map'_iff]
    exact hp
  · exact (Filter.Eventually.of_forall hcontP).frequently

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
  classical
  obtain ⟨L, hL, hSeries⟩ := finiteHeckeL_exists_continuation χ
  let φ : ℝ → ℂ := fun t ↦ ⟨1, t⟩
  have hφc : Continuous φ := by
    have : φ = fun t : ℝ ↦ (1 : ℂ) + (t : ℂ) * Complex.I := by
      funext t
      simp [φ, Complex.ext_iff]
    rw [this]
    continuity
  have hKline : φ '' K ⊆ Complex.re ⁻¹' ({1} : Set ℝ) := by
    rintro _ ⟨t, ht, rfl⟩
    rfl
  obtain ⟨err, herr, herr0⟩ := heckeLogDerivPolynomial_of_nontrivial_on_normOne χ hχ L hL hSeries
    (φ '' K) (hK.image hφc) hKline (b := 1 / 2) (by norm_num)
  -- Extract a uniform bound on the Perron remainder at integer cutoffs.
  rw [Metric.tendstoUniformlyOn_iff] at herr0
  have hev := herr0 (ε / 2) (half_pos hε)
  have hev' : ∃ X : ℝ, ∀ x ≥ X, x ∈ perronCutoffSet (1 / 2) →
      ∀ t ∈ K, ‖err x (φ t)‖ < ε / 2 := by
    rw [Filter.eventually_iff, Filter.mem_inf_iff_superset] at hev
    obtain ⟨a, ha, bset, hbset, hab⟩ := hev
    rw [Filter.mem_principal] at hbset
    obtain ⟨X, hX⟩ := Filter.eventually_atTop.mp ha
    refine ⟨X, fun x hx hxJ t ht ↦ ?_⟩
    have := hab (Set.mem_inter (hX x hx) (hbset hxJ)) (φ t) ⟨t, ht, rfl⟩
    simpa [dist_eq_norm] using this
  obtain ⟨X, hX⟩ := hev'
  refine ⟨max X 2 + 2, by linarith [le_max_right X 2], fun x hx ↦ ?_⟩
  have hx1 : 1 < x := by linarith [le_max_right X 2]
  set M := ⌈x⌉₊ with hMdef
  have hM4 : 4 ≤ M := by
    have : (4 : ℝ) ≤ M := by linarith [le_max_right X 2, Nat.le_ceil x]
    exact_mod_cast this
  have hM2 : 2 ≤ M := by omega
  have hMx : x ≤ M := Nat.le_ceil x
  let b : ℕ → ℝ → ℂ := fun n t ↦
    LSeries.term (heckeLogDerivCoefficient (ideleClassNormTwist χ 0)) (φ t) n
  let R : ℕ → ℝ → ℂ := fun n t ↦ if 2 ≤ n then -err (n : ℝ) (φ t) else 0
  have hR : ∀ n ≥ M - 1, ∀ t ∈ K, ‖R n t‖ ≤ ε / 2 := by
    intro n hn t ht
    have hn2 : 2 ≤ n := by omega
    have hnX : (n : ℝ) ≥ X := by
      have hcast : ((M - 1 : ℕ) : ℝ) = (M : ℝ) - 1 := by
        rw [Nat.cast_sub (show 1 ≤ M by omega), Nat.cast_one]
      have hmn : ((M - 1 : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      linarith [le_max_left X 2, Nat.le_ceil x]
    have hnJ : (n : ℝ) ∈ perronCutoffSet (1 / 2) :=
      (perronCutoffSet_integer_half_integer (by norm_num : (0 : ℝ) < 1 / 2) n).1
    simp only [R, hn2, ↓reduceIte, norm_neg]
    exact le_of_lt (hX (n : ℝ) hnX hnJ t ht)
  have hb : ∀ n ≥ M, ∀ t, b n t = R (n - 1) t - R n t := by
    intro n hn t
    have hn3 : 3 ≤ n := by omega
    have hn1 : 1 < (n : ℝ) := by exact_mod_cast (by omega : 1 < n)
    have hn1' : 1 < ((n - 1 : ℕ) : ℝ) := by
      have : 2 ≤ n - 1 := by omega
      exact_mod_cast (by omega : 1 < n - 1)
    have hpoly (j : ℕ) (hj : 1 < (j : ℝ)) :
        heckeLogDerivPolynomial χ (j : ℝ) (φ t) = -logDeriv L (φ t) + err (j : ℝ) (φ t) :=
      (herr (j : ℝ) hj).2 (φ t) (by simp [φ])
    have hpoly_nat (j : ℕ) : heckeLogDerivPolynomial χ (j : ℝ) (φ t) =
        ∑ k ∈ Finset.Icc 1 j,
          LSeries.term (heckeLogDerivCoefficient (ideleClassNormTwist χ 0)) (φ t) k := by
      simp [heckeLogDerivPolynomial]
    have hdiff : b n t = heckeLogDerivPolynomial χ (n : ℝ) (φ t) -
        heckeLogDerivPolynomial χ ((n - 1 : ℕ) : ℝ) (φ t) := by
      simp only [b]
      rw [hpoly_nat, hpoly_nat]
      have hsum : ∑ k ∈ Finset.Icc 1 n,
          LSeries.term (heckeLogDerivCoefficient (ideleClassNormTwist χ 0)) (φ t) k =
          ∑ k ∈ Finset.Icc 1 (n - 1),
            LSeries.term (heckeLogDerivCoefficient (ideleClassNormTwist χ 0)) (φ t) k +
          LSeries.term (heckeLogDerivCoefficient (ideleClassNormTwist χ 0)) (φ t) n := by
        conv_lhs => rw [show n = (n - 1) + 1 by omega,
          Finset.sum_Icc_succ_top (show 1 ≤ (n - 1) + 1 by omega)]
        rw [show (n - 1) + 1 = n by omega]
      rw [hsum]
      ring
    rw [hdiff, hpoly n hn1, hpoly (n - 1) hn1']
    simp only [R, show 2 ≤ n - 1 by omega, show 2 ≤ n by omega, ↓reduceIte]
    ring
  have hcont : ∀ n, ContinuousOn (b n) K := by
    intro n
    by_cases hn0 : n = 0
    · subst hn0
      have : b 0 = fun _ ↦ 0 := by
        funext t
        simp [b, LSeries.term_zero]
      rw [this]
      exact continuousOn_const
    · have hb' : b n = fun t ↦
        heckeLogDerivCoefficient (ideleClassNormTwist χ 0) n / (n : ℂ) ^ (φ t) := by
        funext t
        simp only [b]
        rw [LSeries.term_of_ne_zero hn0]
      rw [hb']
      refine ContinuousOn.div continuousOn_const ?_ fun t ht ↦ ?_
      · exact hφc.continuousOn.const_cpow (Or.inl (Nat.cast_ne_zero.mpr hn0))
      · exact Complex.cpow_ne_zero_iff.mpr (Or.inl (Nat.cast_ne_zero.mpr hn0))
  obtain ⟨T, hThas, hTUO, hTcont, hTbound⟩ :=
    abelTail_uniform b R K (half_pos hε).le hM2 hR hb hcont
  have hcong (t : ℝ) : (fun n : ℕ ↦ if (M : ℝ) ≤ n then b n t / Real.log n else 0) =
      heckePrimePowerLogTailTerm χ x (φ t) := by
    funext n
    simp only [heckePrimePowerLogTailTerm, b]
    by_cases hn : x ≤ (n : ℝ)
    · have hMn : (M : ℝ) ≤ n := by
        rw [hMdef, Nat.cast_le]
        exact Nat.ceil_le.mpr hn
      have hn0 : n ≠ 0 := by
        rintro rfl
        norm_num at hn
        linarith
      simp only [hn, hMn, ↓reduceIte]
      rw [LSeries.term_of_ne_zero hn0, LSeries.term_of_ne_zero hn0, heckePrimePowerLogCoefficient]
      rw [div_div, div_div, mul_comm (Real.log n : ℂ)]
    · have hMn : ¬(M : ℝ) ≤ n := by
        rw [hMdef, Nat.cast_le]
        exact fun h ↦ hn (Nat.ceil_le.mp h)
      simp only [hn, hMn, ↓reduceIte]
  have htail_eq (t : ℝ) (ht : t ∈ K) : heckePrimePowerLogTail χ x (φ t) = T t := by
    have := (hThas t ht).congr_fun (congrFun (hcong t).symm)
    delta heckePrimePowerLogTail
    exact this.tsum_eq
  have hTUO' : TendstoUniformlyOn
      (fun N : ℕ ↦ fun t : ℝ ↦
        ∑ n ∈ Finset.range N, heckePrimePowerLogTailTerm χ x ⟨1, t⟩ n)
      (fun t : ℝ ↦ heckePrimePowerLogTail χ x ⟨1, t⟩) atTop K := by
    have := hTUO.congr (Filter.Eventually.of_forall fun N ↦ by
      intro t ht
      apply Finset.sum_congr rfl
      intro n hn
      exact congrFun (hcong t) n)
    exact this.congr_right (fun t ht ↦ (htail_eq t ht).symm)
  have hcont' : ContinuousOn (fun t : ℝ ↦ heckePrimePowerLogTail χ x ⟨1, t⟩) K :=
    hTcont.congr (fun t ht ↦ htail_eq t ht)
  have hbound (t : ℝ) (ht : t ∈ K) : ‖heckePrimePowerLogTail χ x (φ t)‖ < 2 * ε / Real.log x := by
    rw [htail_eq t ht]
    have hlogx : 0 < Real.log x := Real.log_pos hx1
    have hlogM : Real.log x ≤ Real.log M := Real.log_le_log (by linarith) hMx
    calc ‖T t‖ ≤ 2 * (ε / 2) / Real.log M := hTbound t ht
      _ = ε / Real.log M := by ring
      _ ≤ ε / Real.log x := by gcongr
      _ < 2 * ε / Real.log x := by
        have hpos : 0 < ε / Real.log x := div_pos hε hlogx
        rw [show (2 : ℝ) * ε / Real.log x = 2 * (ε / Real.log x) by ring]
        linarith
  exact ⟨hTUO', hcont', fun t ht ↦ hbound t ht⟩

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
  have hN : v.asIdeal.absNorm ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff]
    exact v.ne_bot
  simp only [heckePrimesBelow, Set.Finite.mem_toFinset, Set.mem_ofPred_eq]
  rw [← Nat.lt_ceil]
  omega

/-- The norm of a prime-power logarithmic term on the 1-line is bounded by the
corresponding higher-power weight, keeping the exponent denominator. -/
private theorem heckePrimePowerLogTerm_norm_le_weight (χ : U[F]) (v : V[F]) (k : ℕ) (t : ℝ) :
    ‖heckePrimePowerLogTerm χ v k ⟨1, t⟩‖ ≤
      1 / (((k + 1 : ℕ) : ℝ) * ((v.asIdeal ^ (k + 1)).absNorm : ℝ)) := by
  have hN : 0 < ((v.asIdeal ^ (k + 1)).absNorm : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr (pow_ne_zero _ v.ne_bot))
  have hχ : ‖heckeIdealValue (ideleClassNormTwist χ 0) (v.asIdeal ^ (k + 1))‖ ≤ 1 := by
    rw [heckeIdealValue_prime_pow _ v (Nat.succ_pos k)]
    split_ifs with h
    · rw [norm_pow, norm_ideleClassNormTwist_zero_localValue, one_pow]
    · simp
  calc ‖heckePrimePowerLogTerm χ v k ⟨1, t⟩‖
      = ‖heckeIdealValue (ideleClassNormTwist χ 0) (v.asIdeal ^ (k + 1))‖ /
          (((k + 1 : ℕ) : ℝ) * ((v.asIdeal ^ (k + 1)).absNorm : ℝ)) := by
        delta heckePrimePowerLogTerm
        rw [norm_div, norm_mul, Complex.norm_natCast,
          ← Complex.ofReal_natCast ((v.asIdeal ^ (k + 1)).absNorm),
          Complex.norm_cpow_eq_rpow_re_of_pos hN]
        simp
    _ ≤ 1 / (((k + 1 : ℕ) : ℝ) * ((v.asIdeal ^ (k + 1)).absNorm : ℝ)) := by
        gcongr

/-- The prime powers of a fixed integer norm form a finite set. -/
private theorem heckePrimePowerFiber_finite (n : ℕ) :
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

/-- The higher prime-power terms grouped by norm are summable on the 1-line, with a
majorant independent of the ordinate. -/
private theorem heckeHigherPrimePowerGrouped_bound (χ : U[F]) :
    ∃ M : ℕ → ℝ, Summable M ∧
      ∀ (n : ℕ) (t : ℝ),
        ‖∑ᶠ a : {a : V[F] × ℕ // 1 ≤ a.2 ∧ a.1.asIdeal.absNorm ^ (a.2 + 1) = n},
          heckePrimePowerLogTerm χ a.val.1 a.val.2 ⟨1, t⟩‖ ≤ M n := by
  classical
  let N : V[F] × ℕ → ℕ := fun a ↦ a.1.asIdeal.absNorm ^ (a.2 + 1)
  let A := {a : V[F] × ℕ // 1 ≤ a.2}
  let w : A → ℝ := fun a ↦
    1 / (((a.val.2 + 1 : ℕ) : ℝ) * ((a.val.1.asIdeal ^ (a.val.2 + 1)).absNorm : ℝ))
  have hw : Summable w := by
    -- summability of the higher-power majorant at abscissa 1 (self-contained)
    have hu : Summable fun v : V[F] ↦ (v.asIdeal.absNorm : ℝ) ^ (-(2 : ℝ)) :=
      (summable_absNorm_rpow F (by norm_num : 1 < (2 : ℝ))).comp_injective
        (fun _ _ he ↦ HeightOneSpectrum.ext he)
    have hg : Summable fun k : ℕ ↦ ((2 : ℝ) ^ (-(1 : ℝ))) ^ k :=
      summable_geometric_of_lt_one (by positivity) (by norm_num)
    have hW : Summable fun a : V[F] × ℕ ↦
        (1 : ℝ) / ((a.2 + 2 : ℕ) * (((a.1.asIdeal.absNorm ^ (a.2 + 2) : ℕ) : ℝ) ^ (1 : ℝ))) := by
      refine Summable.of_nonneg_of_le (fun a ↦ by positivity) (fun a ↦ ?_)
        (hu.mul_of_nonneg hg (fun v ↦ Real.rpow_nonneg (Nat.cast_nonneg _) _)
          (fun k ↦ pow_nonneg (by positivity) k))
      obtain ⟨v, k⟩ := a
      dsimp only
      have hN : (2 : ℝ) ≤ v.asIdeal.absNorm := by
        exact_mod_cast HeightOneSpectrum.one_lt_absNorm v
      have hN0 : (0 : ℝ) < v.asIdeal.absNorm := by linarith
      have hpow : ((v.asIdeal.absNorm ^ (k + 2) : ℕ) : ℝ) ^ (1 : ℝ) =
          (v.asIdeal.absNorm : ℝ) ^ 2 * (v.asIdeal.absNorm : ℝ) ^ k := by
        rw [Real.rpow_one, Nat.cast_pow, show (k + 2 : ℕ) = 2 + k by omega, pow_add]
      rw [hpow]
      have hA : 0 < (v.asIdeal.absNorm : ℝ) ^ 2 := pow_pos hN0 2
      have hB : 0 < (2 : ℝ) ^ k := pow_pos (by norm_num) k
      have hle : (2 : ℝ) ^ k ≤ (v.asIdeal.absNorm : ℝ) ^ k :=
        pow_le_pow_left₀ (by norm_num) hN k
      have h1 : (1 : ℝ) ≤ ((k + 2 : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ k + 2)
      calc 1 / (((k + 2 : ℕ) : ℝ) *
            ((v.asIdeal.absNorm : ℝ) ^ 2 * (v.asIdeal.absNorm : ℝ) ^ k))
          ≤ 1 / ((v.asIdeal.absNorm : ℝ) ^ 2 * (2 : ℝ) ^ k) := by
            apply one_div_le_one_div_of_le (mul_pos hA hB)
            calc (v.asIdeal.absNorm : ℝ) ^ 2 * (2 : ℝ) ^ k
                ≤ (v.asIdeal.absNorm : ℝ) ^ 2 * (v.asIdeal.absNorm : ℝ) ^ k :=
                  mul_le_mul_of_nonneg_left hle hA.le
              _ ≤ ((k + 2 : ℕ) : ℝ) *
                  ((v.asIdeal.absNorm : ℝ) ^ 2 * (v.asIdeal.absNorm : ℝ) ^ k) :=
                  le_mul_of_one_le_left (by positivity) h1
        _ = (v.asIdeal.absNorm : ℝ) ^ (-(2 : ℝ)) * ((2 : ℝ) ^ (-(1 : ℝ))) ^ k := by
            rw [Real.rpow_neg hN0.le, Real.rpow_neg (by norm_num), one_div, mul_inv]
            simp [inv_pow]
    have h1 := hW.comp_injective (i := fun a : A ↦ (a.val.1, a.val.2 - 1)) (fun a b h ↦ by
      cases a with | mk a ha =>
      cases b with | mk b hb =>
      simp only [Prod.mk.injEq] at h
      exact Subtype.ext (Prod.ext h.1 (by
        have := congrArg (· + 1) h.2
        simpa [Nat.sub_add_cancel (show 1 ≤ a.2 by omega),
          Nat.sub_add_cancel (show 1 ≤ b.2 by omega)] using this)))
    refine h1.congr (fun a ↦ ?_)
    cases a with | mk a ha =>
    simp only [w, Function.comp_apply]
    rw [show a.2 - 1 + 2 = a.2 + 1 by omega, Real.rpow_one, map_pow]
  let Nfn : A → ℕ := fun a ↦ N a.val
  have hfib := hw.hasSum.tsum_fiberwise Nfn
  refine ⟨fun n ↦ ∑' a : Nfn ⁻¹' {n}, w a, hfib.summable, fun n t ↦ ?_⟩
  haveI : Finite {a : V[F] × ℕ // N a = n} := by
    simpa [N] using heckePrimePowerFiber_finite n
  haveI : Finite {a : V[F] × ℕ // 1 ≤ a.2 ∧ N a = n} :=
    Finite.of_injective (fun a ↦ (⟨a.val, a.property.2⟩ : {a : V[F] × ℕ // N a = n}))
      (fun a b h ↦ by
        cases a; cases b
        simpa using h)
  haveI : Fintype {a : V[F] × ℕ // 1 ≤ a.2 ∧ N a = n} := Fintype.ofFinite _
  let e : {a : V[F] × ℕ // 1 ≤ a.2 ∧ N a = n} ≃ (Nfn ⁻¹' {n}) :=
    { toFun := fun a ↦ ⟨⟨a.val, a.property.1⟩, a.property.2⟩
      invFun := fun a ↦ ⟨a.val.val, a.val.property, a.property⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl }
  haveI : Fintype (Nfn ⁻¹' {n}) := Fintype.ofEquiv _ e
  have hfin : ∑ᶠ a : {a : V[F] × ℕ // 1 ≤ a.2 ∧ N a = n},
      heckePrimePowerLogTerm χ a.val.1 a.val.2 ⟨1, t⟩ =
      ∑ a : {a : V[F] × ℕ // 1 ≤ a.2 ∧ N a = n},
        heckePrimePowerLogTerm χ a.val.1 a.val.2 ⟨1, t⟩ :=
    finsum_eq_sum_of_fintype _
  rw [hfin]
  calc ‖∑ a : {a : V[F] × ℕ // 1 ≤ a.2 ∧ N a = n},
        heckePrimePowerLogTerm χ a.val.1 a.val.2 ⟨1, t⟩‖
      ≤ ∑ a : {a : V[F] × ℕ // 1 ≤ a.2 ∧ N a = n},
        ‖heckePrimePowerLogTerm χ a.val.1 a.val.2 ⟨1, t⟩‖ := norm_sum_le _ _
    _ ≤ ∑ a : {a : V[F] × ℕ // 1 ≤ a.2 ∧ N a = n}, w (e a) := by
        apply Finset.sum_le_sum
        intro a _
        exact heckePrimePowerLogTerm_norm_le_weight χ a.val.1 a.val.2 t
    _ = ∑ a : Nfn ⁻¹' {n}, w a :=
        Fintype.sum_equiv e (fun a ↦ w (e a)) (fun a ↦ w a) (fun _ ↦ rfl)
    _ = ∑' a : Nfn ⁻¹' {n}, w a := by
        rw [tsum_fintype]

/-- The norm-grouped logarithmic coefficient splits into its exponent-one (prime) part
and its higher prime-power part. -/
private theorem heckePrimePowerLogCoefficient_split (χ : U[F]) (n : ℕ) (t : ℝ) :
    LSeries.term (heckePrimePowerLogCoefficient χ) ⟨1, t⟩ n =
      (∑ᶠ v : {v : V[F] // v.asIdeal.absNorm = n}, heckePrimePowerLogTerm χ v.val 0 ⟨1, t⟩) +
      ∑ᶠ a : {a : V[F] × ℕ // 1 ≤ a.2 ∧ a.1.asIdeal.absNorm ^ (a.2 + 1) = n},
        heckePrimePowerLogTerm χ a.val.1 a.val.2 ⟨1, t⟩ := by
  classical
  by_cases hn0 : n = 0
  · subst hn0
    haveI h1 : IsEmpty {v : V[F] // v.asIdeal.absNorm = 0} :=
      ⟨fun v ↦ by
        have := Ideal.absNorm_eq_zero_iff.not.mpr v.val.ne_bot
        exact this v.property⟩
    haveI h2 : IsEmpty {a : V[F] × ℕ // 1 ≤ a.2 ∧ a.1.asIdeal.absNorm ^ (a.2 + 1) = 0} :=
      ⟨fun a ↦ by
        have : 0 < a.val.1.asIdeal.absNorm ^ (a.val.2 + 1) :=
          pow_pos (Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr a.val.1.ne_bot)) _
        omega⟩
    simp [LSeries.term_zero, finsum_of_isEmpty]
  · rw [LSeries.term_of_ne_zero hn0, heckePrimePowerLogCoefficient_eq_sum]
    let N : V[F] × ℕ → ℕ := fun a ↦ a.1.asIdeal.absNorm ^ (a.2 + 1)
    let S := {a : V[F] × ℕ // N a = n}
    haveI : Finite S := by
      simpa [N, S] using heckePrimePowerFiber_finite n
    haveI : Fintype S := Fintype.ofFinite _
    let f (a : S) : ℂ :=
      heckeIdealValue (ideleClassNormTwist χ 0) (a.val.1.asIdeal ^ (a.val.2 + 1)) /
        ((a.val.2 + 1 : ℕ) : ℂ)
    have hconv : ∑ᶠ a : {a : V[F] × ℕ // a.1.asIdeal.absNorm ^ (a.2 + 1) = n},
        heckeIdealValue (ideleClassNormTwist χ 0) (a.val.1.asIdeal ^ (a.val.2 + 1)) /
          ((a.val.2 + 1 : ℕ) : ℂ) = ∑ a : S, f a := by
      rw [finsum_eq_sum_of_fintype]
    rw [hconv, Finset.sum_div]
    have hpoint (a : S) : f a / (n : ℂ) ^ (⟨1, t⟩ : ℂ) =
        heckePrimePowerLogTerm χ a.val.1 a.val.2 ⟨1, t⟩ := by
      delta heckePrimePowerLogTerm
      simp only [f]
      rw [show ((a.val.1.asIdeal ^ (a.val.2 + 1)).absNorm : ℂ) = (n : ℂ) by
        rw [map_pow]; exact_mod_cast a.property]
      ring
    simp_rw [hpoint]
    have hsplit : ∑ a : S, heckePrimePowerLogTerm χ a.val.1 a.val.2 ⟨1, t⟩ =
        ∑ a ∈ (Finset.univ : Finset S).filter (fun a ↦ a.val.2 = 0),
          heckePrimePowerLogTerm χ a.val.1 a.val.2 ⟨1, t⟩ +
        ∑ a ∈ (Finset.univ : Finset S).filter (fun a ↦ 1 ≤ a.val.2),
          heckePrimePowerLogTerm χ a.val.1 a.val.2 ⟨1, t⟩ := by
      have : ∑ a : S, heckePrimePowerLogTerm χ a.val.1 a.val.2 ⟨1, t⟩ =
          ∑ a : S, (if a.val.2 = 0 then heckePrimePowerLogTerm χ a.val.1 a.val.2 ⟨1, t⟩ else 0) +
          ∑ a : S, (if 1 ≤ a.val.2 then heckePrimePowerLogTerm χ a.val.1 a.val.2 ⟨1, t⟩ else 0) := by
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro a _
        by_cases h : a.val.2 = 0 <;> simp [h] <;> omega
      rw [this, ← Finset.sum_filter, ← Finset.sum_filter]
    -- reindex the k ≥ 1 part
    have h1 : ∑ a ∈ (Finset.univ : Finset S).filter (fun a ↦ 1 ≤ a.val.2),
        heckePrimePowerLogTerm χ a.val.1 a.val.2 ⟨1, t⟩ =
        ∑ᶠ a : {a : V[F] × ℕ // 1 ≤ a.2 ∧ N a = n},
          heckePrimePowerLogTerm χ a.val.1 a.val.2 ⟨1, t⟩ := by
      haveI : Finite {a : V[F] × ℕ // 1 ≤ a.2 ∧ N a = n} :=
        Finite.of_injective (fun a ↦ (⟨a.val, a.property.2⟩ : S)) (fun a b h ↦ by
          cases a; cases b; simpa using h)
      haveI : Fintype {a : V[F] × ℕ // 1 ≤ a.2 ∧ N a = n} := Fintype.ofFinite _
      rw [finsum_eq_sum_of_fintype]
      symm
      apply Finset.sum_bij (fun (a : {a : V[F] × ℕ // 1 ≤ a.2 ∧ N a = n}) _ ↦
        (⟨a.val, a.property.2⟩ : S))
      · intro a _
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact a.property.1
      · intro a _ b _ h
        exact Subtype.ext (congrArg (fun s : S ↦ s.val) h)
      · intro b hb
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb
        refine ⟨⟨b.val, hb, b.property⟩, ?_, rfl⟩
        simp
      · intro a _
        rfl
    -- reindex the k = 0 part
    have h0 : ∑ a ∈ (Finset.univ : Finset S).filter (fun a ↦ a.val.2 = 0),
        heckePrimePowerLogTerm χ a.val.1 a.val.2 ⟨1, t⟩ =
        ∑ᶠ v : {v : V[F] // v.asIdeal.absNorm = n}, heckePrimePowerLogTerm χ v.val 0 ⟨1, t⟩ := by
      haveI : Finite {v : V[F] // v.asIdeal.absNorm = n} :=
        Finite.of_injective (fun v ↦ (⟨(v.val, 0), by simpa [N] using v.property⟩ : S))
          (fun v w h ↦ Subtype.ext (congrArg (fun a : S ↦ a.val.1) h))
      haveI : Fintype {v : V[F] // v.asIdeal.absNorm = n} := Fintype.ofFinite _
      rw [finsum_eq_sum_of_fintype]
      symm
      apply Finset.sum_bij (fun (v : {v : V[F] // v.asIdeal.absNorm = n}) _ ↦
        (⟨(v.val, 0), by simpa [N] using v.property⟩ : S))
      · intro v _
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      · intro v _ w _ h
        exact Subtype.ext (congrArg (fun a : S ↦ a.val.1) h)
      · intro b hb
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb
        have hb2 : b.val.2 = 0 := hb
        refine ⟨⟨b.val.1, ?_⟩, ?_, ?_⟩
        · have := b.property
          simp only [N, hb2, zero_add, pow_one] at this ⊢
          exact this
        · simp
        · ext <;> simp [hb2]
      · intro v _
        rfl
    rw [hsplit, h0, h1]

/-- The exponent-one part of the norm-grouped sum below the cutoff is the prime sum
over `heckePrimesBelow`. -/
private theorem heckePrimeSum_below_reindex (χ : U[F]) (x : ℝ) (t : ℝ) :
    ∑ n ∈ Finset.range ⌈x⌉₊,
      ∑ᶠ v : {v : V[F] // v.asIdeal.absNorm = n}, heckePrimePowerLogTerm χ v.val 0 ⟨1, t⟩ =
    ∑ v ∈ heckePrimesBelow F x, heckePrimePowerLogTerm χ v 0 ⟨1, t⟩ := by
  classical
  have hfib := Finset.sum_fiberwise_of_maps_to (g := fun v : V[F] ↦ v.asIdeal.absNorm)
    (s := heckePrimesBelow F x) (t := Finset.range ⌈x⌉₊)
    (fun v hv ↦ by
      rw [Finset.mem_range]
      exact Nat.lt_ceil.mpr ((heckePrimesBelow_mem_iff v x).mp hv))
    (fun v ↦ heckePrimePowerLogTerm χ v 0 ⟨1, t⟩)
  rw [← hfib]
  apply Finset.sum_congr rfl
  intro n hn
  have hinner : ∑ v ∈ (heckePrimesBelow F x).filter (fun v ↦ v.asIdeal.absNorm = n),
      heckePrimePowerLogTerm χ v 0 ⟨1, t⟩ =
      ∑ᶠ v : {v : V[F] // v.asIdeal.absNorm = n}, heckePrimePowerLogTerm χ v.val 0 ⟨1, t⟩ := by
    haveI : Finite {v : V[F] // v.asIdeal.absNorm = n} :=
      Finite.of_injective (fun v ↦ (⟨v.val, by
        rw [heckePrimesBelow_mem_iff, v.property]
        exact Nat.lt_ceil.mp (Finset.mem_range.mp hn)⟩ :
        {v : V[F] // v ∈ heckePrimesBelow F x}))
        (fun v w h ↦ Subtype.ext (congrArg
          (fun w : {v : V[F] // v ∈ heckePrimesBelow F x} ↦ w.val) h))
    haveI : Fintype {v : V[F] // v.asIdeal.absNorm = n} := Fintype.ofFinite _
    rw [finsum_eq_sum_of_fintype]
    symm
    apply Finset.sum_bij (fun (v : {v : V[F] // v.asIdeal.absNorm = n}) _ ↦ v.val)
    · intro v _
      simp only [Finset.mem_filter]
      exact ⟨by
        rw [heckePrimesBelow_mem_iff, v.property]
        exact Nat.lt_ceil.mp (Finset.mem_range.mp hn), v.property⟩
    · intro v _ w _ h
      exact Subtype.ext h
    · intro b hb
      simp only [Finset.mem_filter] at hb
      refine ⟨⟨b, hb.2⟩, ?_, rfl⟩
      simp
    · intro v _
      rfl
  exact hinner.symm

/-- The higher prime-power norm-grouped partial sums converge uniformly on the whole
1-line to their infinite sum. -/
private theorem heckeHigherPrimePowerSum_tendstoUniformly (χ : U[F]) :
    TendstoUniformly
      (fun x : ℝ ↦ fun t : ℝ ↦ ∑ n ∈ Finset.range ⌈x⌉₊,
        ∑ᶠ a : {a : V[F] × ℕ // 1 ≤ a.2 ∧ a.1.asIdeal.absNorm ^ (a.2 + 1) = n},
          heckePrimePowerLogTerm χ a.val.1 a.val.2 ⟨1, t⟩)
      (fun t : ℝ ↦ ∑' n : ℕ,
        ∑ᶠ a : {a : V[F] × ℕ // 1 ≤ a.2 ∧ a.1.asIdeal.absNorm ^ (a.2 + 1) = n},
          heckePrimePowerLogTerm χ a.val.1 a.val.2 ⟨1, t⟩)
      atTop := by
  classical
  obtain ⟨M, hMsum, hMbound⟩ := heckeHigherPrimePowerGrouped_bound χ
  let h_n : ℕ → ℝ → ℂ := fun n t ↦
    ∑ᶠ a : {a : V[F] × ℕ // 1 ≤ a.2 ∧ a.1.asIdeal.absNorm ^ (a.2 + 1) = n},
      heckePrimePowerLogTerm χ a.val.1 a.val.2 ⟨1, t⟩
  have hsum (t : ℝ) : Summable (fun n ↦ h_n n t) :=
    Summable.of_norm_bounded hMsum (fun n ↦ hMbound n t)
  have htail : Tendsto (fun N₀ : ℕ ↦ ∑' k, M (k + N₀)) atTop (𝓝 0) := by
    have h_eq : (fun N₀ ↦ ∑' k, M (k + N₀)) =
        fun N₀ ↦ ∑' n, M n - ∑ n ∈ Finset.range N₀, M n := by
      funext N₀
      rw [← Summable.sum_add_tsum_nat_add N₀ hMsum]
      abel
    rw [h_eq]
    simpa using (tendsto_const_nhds (x := ∑' n, M n)).sub hMsum.hasSum.tendsto_sum_nat
  have hcomp : Tendsto (fun x : ℝ ↦ ∑' k, M (k + ⌈x⌉₊)) atTop (𝓝 0) :=
    htail.comp tendsto_nat_ceil_atTop
  rw [Metric.tendstoUniformly_iff]
  intro ε hε
  obtain ⟨X, hX⟩ := Metric.tendsto_atTop.mp hcomp ε hε
  filter_upwards [Filter.eventually_ge_atTop X] with x hx
  intro t
  have hdiff : (∑' n, h_n n t) - ∑ n ∈ Finset.range ⌈x⌉₊, h_n n t =
      ∑' k, h_n (k + ⌈x⌉₊) t := by
    rw [← Summable.sum_add_tsum_nat_add ⌈x⌉₊ (hsum t)]
    abel
  have hshift (t : ℝ) : Summable (fun k ↦ h_n (k + ⌈x⌉₊) t) :=
    (hsum t).comp_injective (fun a b h ↦ by simpa using h)
  have hdist : dist (∑' n, h_n n t) (∑ n ∈ Finset.range ⌈x⌉₊, h_n n t) ≤
      ∑' k, M (k + ⌈x⌉₊) := by
    rw [dist_eq_norm, hdiff]
    calc ‖∑' k, h_n (k + ⌈x⌉₊) t‖
        ≤ ∑' k, ‖h_n (k + ⌈x⌉₊) t‖ := norm_tsum_le_tsum_norm (hshift t).norm
      _ ≤ ∑' k, M (k + ⌈x⌉₊) :=
          Summable.tsum_le_tsum (fun k ↦ hMbound (k + ⌈x⌉₊) t) (hshift t).norm
            (hMsum.comp_injective (fun a b h ↦ by simpa using h))
  exact lt_of_le_of_lt hdist
    (lt_of_le_of_lt (le_abs_self _) (by simpa [Real.dist_eq] using hX x hx))

/-- Paper: Corollary B.7.2.3, p. 651. For a character nontrivial on the
norm-one subgroup, the prime sum converges locally uniformly on the 1-line. -/
theorem heckePrimeSum_tendstoLocallyUniformly_of_nontrivial_on_normOne (χ : U[F])
    (hχ : χ.toMonoidHom.comp (ideleClassNorm F).ker.subtype ≠ 1) :
    ∃ limit : ℝ → ℂ, TendstoLocallyUniformly
      (fun x : ℝ ↦ fun t : ℝ ↦
        ∑ v ∈ heckePrimesBelow F x, heckePrimePowerLogTerm χ v 0 ⟨1, t⟩)
      limit atTop := by
  classical
  let c : ℕ → ℝ → ℂ := fun n t ↦ LSeries.term (heckePrimePowerLogCoefficient χ) ⟨1, t⟩ n
  let h_n : ℕ → ℝ → ℂ := fun n t ↦
    ∑ᶠ a : {a : V[F] × ℕ // 1 ≤ a.2 ∧ a.1.asIdeal.absNorm ^ (a.2 + 1) = n},
      heckePrimePowerLogTerm χ a.val.1 a.val.2 ⟨1, t⟩
  let H : ℝ → ℂ := fun t ↦ ∑' n, h_n n t
  let limit : ℝ → ℂ := fun t ↦
    tsum (fun n ↦ c n t) (SummationFilter.conditional ℕ) - H t
  refine ⟨limit, ?_⟩
  rw [tendstoLocallyUniformly_iff_forall_isCompact]
  intro K hK
  obtain ⟨x₀, hx₀, hbase⟩ :=
    heckePrimePowerLogTail_of_nontrivial_on_normOne χ hχ K hK (ε := 1) (by norm_num)
  let P : ℝ → ℝ → ℂ := fun x t ↦ ∑ n ∈ Finset.range ⌈x⌉₊, c n t
  let H_x : ℝ → ℝ → ℂ := fun x t ↦ ∑ n ∈ Finset.range ⌈x⌉₊, h_n n t
  let G : ℝ → ℝ → ℂ := fun x t ↦
    ∑ v ∈ heckePrimesBelow F x, heckePrimePowerLogTerm χ v 0 ⟨1, t⟩
  have hGH (x : ℝ) (t : ℝ) : G x t = P x t - H_x x t := by
    simp only [G, P, H_x, h_n, c]
    have hsplit : ∑ n ∈ Finset.range ⌈x⌉₊,
        LSeries.term (heckePrimePowerLogCoefficient χ) ⟨1, t⟩ n =
        (∑ n ∈ Finset.range ⌈x⌉₊,
          ∑ᶠ v : {v : V[F] // v.asIdeal.absNorm = n}, heckePrimePowerLogTerm χ v.val 0 ⟨1, t⟩) +
        ∑ n ∈ Finset.range ⌈x⌉₊,
          ∑ᶠ a : {a : V[F] × ℕ // 1 ≤ a.2 ∧ a.1.asIdeal.absNorm ^ (a.2 + 1) = n},
            heckePrimePowerLogTerm χ a.val.1 a.val.2 ⟨1, t⟩ := by
      have : ∑ n ∈ Finset.range ⌈x⌉₊,
          LSeries.term (heckePrimePowerLogCoefficient χ) ⟨1, t⟩ n =
          ∑ n ∈ Finset.range ⌈x⌉₊,
            ((∑ᶠ v : {v : V[F] // v.asIdeal.absNorm = n},
              heckePrimePowerLogTerm χ v.val 0 ⟨1, t⟩) +
            ∑ᶠ a : {a : V[F] × ℕ // 1 ≤ a.2 ∧ a.1.asIdeal.absNorm ^ (a.2 + 1) = n},
              heckePrimePowerLogTerm χ a.val.1 a.val.2 ⟨1, t⟩) := by
        apply Finset.sum_congr rfl
        intro n hn
        exact heckePrimePowerLogCoefficient_split χ n t
      rw [this, Finset.sum_add_distrib]
    rw [hsplit, heckePrimeSum_below_reindex χ x t]
    abel
  have htailHas (x : ℝ) (hx : x₀ ≤ x) (t : ℝ) (ht : t ∈ K) :
      HasSum (fun n : ℕ ↦ if x ≤ (n : ℝ) then c n t else 0)
        (heckePrimePowerLogTail χ x ⟨1, t⟩) (SummationFilter.conditional ℕ) := by
    have := (hbase x hx).1.tendsto_at ht
    rw [HasSum, SummationFilter.conditional_filter_eq_map_range, Filter.tendsto_map'_iff]
    convert this using 1
    funext N
    apply Finset.sum_congr rfl
    intro n hn
    simp [c, heckePrimePowerLogTailTerm]
  have htotal (x : ℝ) (hx : x₀ ≤ x) (t : ℝ) (ht : t ∈ K) :
      tsum (fun n ↦ c n t) (SummationFilter.conditional ℕ) =
        P x t + heckePrimePowerLogTail χ x ⟨1, t⟩ := by
    have hfin : HasSum (fun n : ℕ ↦ if (n : ℝ) < x then c n t else 0) (P x t)
        (SummationFilter.conditional ℕ) := by
      have hsupp : Summable (fun n : ℕ ↦ if (n : ℝ) < x then c n t else 0) :=
        summable_of_ne_finset_zero (s := Finset.range ⌈x⌉₊) (by
          intro n hn
          have : ¬(n : ℝ) < x := by
            rw [← Nat.lt_ceil]
            exact fun h ↦ hn (Finset.mem_range.mpr h)
          simp [this])
      have hh := hsupp.hasSum.mono_left
        (SummationFilter.le_atTop (L := SummationFilter.conditional ℕ))
      have htsum : ∑' n : ℕ, (if (n : ℝ) < x then c n t else 0) = P x t := by
        rw [tsum_eq_sum (by
          intro n hn
          have : ¬(n : ℝ) < x := by
            rw [← Nat.lt_ceil]
            exact fun h ↦ hn (Finset.mem_range.mpr h)
          simp [this])]
        simp only [P]
        apply Finset.sum_congr rfl
        intro n hn
        have : (n : ℝ) < x := Nat.lt_ceil.mp (Finset.mem_range.mp hn)
        simp [this]
      rw [← htsum]
      exact hh
    have hadd := hfin.add (htailHas x hx t ht)
    have hpoint : (fun n : ℕ ↦ (if (n : ℝ) < x then c n t else 0) +
        (if x ≤ (n : ℝ) then c n t else 0)) = fun n ↦ c n t := by
      funext n
      by_cases h : (n : ℝ) < x <;> simp [h] <;> linarith
    rw [hpoint] at hadd
    exact hadd.tsum_eq
  have hGlim (x : ℝ) (hx : x₀ ≤ x) (t : ℝ) (ht : t ∈ K) :
      G x t - limit t = (H t - H_x x t) - heckePrimePowerLogTail χ x ⟨1, t⟩ := by
    rw [hGH]
    simp only [limit, H]
    rw [htotal x hx t ht]
    abel
  have hHconv : TendstoUniformlyOn H_x H atTop K :=
    (heckeHigherPrimePowerSum_tendstoUniformly χ).tendstoUniformlyOn
  have htail0 : TendstoUniformlyOn
      (fun x t ↦ heckePrimePowerLogTail χ x ⟨1, t⟩) (fun _ ↦ 0) atTop K := by
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    obtain ⟨x₁, hx₁, h₁⟩ :=
      heckePrimePowerLogTail_of_nontrivial_on_normOne χ hχ K hK (ε := ε / 2) (half_pos hε)
    filter_upwards [Filter.eventually_ge_atTop (max x₁ (Real.exp 1))] with x hx
    intro t ht
    have hx₁' : x₁ ≤ x := le_trans (le_max_left _ _) hx
    have hbound := (h₁ x hx₁').2.2 t ht
    have hlog : 1 ≤ Real.log x := by
      rw [← Real.log_exp 1]
      exact Real.log_le_log (by positivity) (le_trans (le_max_right _ _) hx)
    calc dist 0 (heckePrimePowerLogTail χ x ⟨1, t⟩)
        = ‖heckePrimePowerLogTail χ x ⟨1, t⟩‖ := by rw [dist_eq_norm, zero_sub, norm_neg]
      _ < 2 * (ε / 2) / Real.log x := hbound
      _ = ε / Real.log x := by ring
      _ ≤ ε := by
          rw [div_le_iff₀ (by linarith)]
          nlinarith
  have hdiff0 : TendstoUniformlyOn
      (fun x t ↦ (H t - H_x x t) - heckePrimePowerLogTail χ x ⟨1, t⟩) (fun _ ↦ 0) atTop K := by
    have hconstH : TendstoUniformlyOn (fun _ t ↦ H t) H (atTop : Filter ℝ) K := by
      rw [Metric.tendstoUniformlyOn_iff]
      intro ε hε
      refine Filter.Eventually.of_forall (fun x t ht ↦ ?_)
      simpa using hε
    have h1 : TendstoUniformlyOn (fun x t ↦ H t - H_x x t) (fun _ ↦ 0) atTop K :=
      (hconstH.sub hHconv).congr_right (fun t ht ↦ by simp)
    exact (h1.sub htail0).congr_right (fun t ht ↦ by simp)
  have htarget : TendstoUniformlyOn
      (fun x t ↦ limit t + ((H t - H_x x t) - heckePrimePowerLogTail χ x ⟨1, t⟩))
      limit atTop K := by
    have hconstlimit : TendstoUniformlyOn (fun _ t ↦ limit t) limit (atTop : Filter ℝ) K := by
      rw [Metric.tendstoUniformlyOn_iff]
      intro ε hε
      refine Filter.Eventually.of_forall (fun x t ht ↦ ?_)
      simpa using hε
    exact (hconstlimit.add hdiff0).congr_right (fun t ht ↦ by simp)
  refine htarget.congr ?_
  filter_upwards [Filter.eventually_ge_atTop x₀] with x hx
  intro t ht
  have h := hGlim x hx t ht
  simp only [G] at h
  dsimp only
  rw [← h]
  abel

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
  classical
  unfold reciprocalHeckeEulerProductBelow reciprocalPartialHeckeEulerProduct
  refine Finset.prod_congr rfl fun v _ ↦ ?_
  have h := heckeIdealValue_prime_pow (ideleClassNormTwist χ 0) v (k := 1) one_pos
  rw [pow_one] at h
  rw [h, finiteHeckeEulerFactor]
  by_cases hv : (ideleClassNormTwist χ 0).IsUnramifiedAt v <;> simp [hv]

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
  have hσ0 : 0 < σ := by linarith
  have hu : Summable fun v : V[F] ↦ (v.asIdeal.absNorm : ℝ) ^ (-(2 * σ)) :=
    (summable_absNorm_rpow F (by linarith)).comp_injective
      (fun _ _ he ↦ HeightOneSpectrum.ext he)
  have hr0 : 0 ≤ (2 : ℝ) ^ (-σ) := Real.rpow_nonneg (by norm_num) _
  have hr1 : (2 : ℝ) ^ (-σ) < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have hg : Summable fun k : ℕ ↦ ((2 : ℝ) ^ (-σ)) ^ k := summable_geometric_of_lt_one hr0 hr1
  refine Summable.of_nonneg_of_le (fun a ↦ by positivity) (fun a ↦ ?_)
    (hu.mul_of_nonneg hg (fun v ↦ Real.rpow_nonneg (Nat.cast_nonneg _) _)
      (fun k ↦ pow_nonneg hr0 k))
  obtain ⟨v, k⟩ := a
  dsimp only
  have hN : (2 : ℝ) ≤ v.asIdeal.absNorm := by exact_mod_cast HeightOneSpectrum.one_lt_absNorm v
  have hN0 : (0 : ℝ) < v.asIdeal.absNorm := by linarith
  have hpow : ((v.asIdeal.absNorm ^ (k + 2) : ℕ) : ℝ) ^ σ =
      (v.asIdeal.absNorm : ℝ) ^ (2 * σ) * ((v.asIdeal.absNorm : ℝ) ^ σ) ^ k := by
    rw [Nat.cast_pow, ← Real.rpow_natCast, ← Real.rpow_mul hN0.le, ← Real.rpow_natCast (_ ^ σ),
      ← Real.rpow_mul hN0.le, ← Real.rpow_add hN0]
    congr 1
    push_cast
    ring
  rw [hpow]
  have hA : 0 < (v.asIdeal.absNorm : ℝ) ^ (2 * σ) := Real.rpow_pos_of_pos hN0 _
  have hB : 0 < ((2 : ℝ) ^ σ) ^ k := pow_pos (Real.rpow_pos_of_pos (by norm_num) _) k
  have hle : ((2 : ℝ) ^ σ) ^ k ≤ ((v.asIdeal.absNorm : ℝ) ^ σ) ^ k :=
    pow_le_pow_left₀ (Real.rpow_nonneg (by norm_num) _)
      (Real.rpow_le_rpow (by norm_num) hN hσ0.le) k
  have h1 : (1 : ℝ) ≤ ((k + 2 : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ k + 2)
  calc 1 / (((k + 2 : ℕ) : ℝ) *
        ((v.asIdeal.absNorm : ℝ) ^ (2 * σ) * ((v.asIdeal.absNorm : ℝ) ^ σ) ^ k))
      ≤ 1 / ((v.asIdeal.absNorm : ℝ) ^ (2 * σ) * ((2 : ℝ) ^ σ) ^ k) := by
        apply one_div_le_one_div_of_le (mul_pos hA hB)
        calc (v.asIdeal.absNorm : ℝ) ^ (2 * σ) * ((2 : ℝ) ^ σ) ^ k
            ≤ (v.asIdeal.absNorm : ℝ) ^ (2 * σ) * ((v.asIdeal.absNorm : ℝ) ^ σ) ^ k :=
              mul_le_mul_of_nonneg_left hle hA.le
          _ ≤ _ := le_mul_of_one_le_left (by positivity) h1
    _ = (v.asIdeal.absNorm : ℝ) ^ (-(2 * σ)) * ((2 : ℝ) ^ (-σ)) ^ k := by
        rw [Real.rpow_neg hN0.le, Real.rpow_neg (by norm_num), inv_pow, one_div, mul_inv]

/-- Each term of the correction is bounded by the positive majorant, because the
character values have norm at most one. -/
private theorem heckeEulerProductLogCorrection_hasSumUniformlyOn_term_le (χ : U[F]) (v : V[F])
    (k : ℕ) (s : ℂ) :
    ‖heckePrimePowerLogTerm χ v (k + 1) s‖ ≤
      (1 : ℝ) / ((k + 2 : ℕ) * (((v.asIdeal.absNorm ^ (k + 2) : ℕ) : ℝ) ^ s.re)) := by
  classical
  have h1 := HeightOneSpectrum.one_lt_absNorm v
  have hval : ‖heckeIdealValue (ideleClassNormTwist χ 0) (v.asIdeal ^ (k + 2))‖ ≤ 1 := by
    rw [heckeIdealValue_prime_pow _ v (Nat.succ_pos _)]
    split_ifs
    · rw [norm_pow, norm_ideleClassNormTwist_zero_localValue, one_pow]
    · simp
  show ‖heckeIdealValue (ideleClassNormTwist χ 0) (v.asIdeal ^ (k + 2)) /
      (((k + 2 : ℕ) : ℂ) * ((v.asIdeal ^ (k + 2)).absNorm : ℂ) ^ s)‖ ≤ _
  rw [map_pow, norm_div, norm_mul, Complex.norm_natCast,
    Complex.norm_natCast_cpow_of_pos (by positivity)]
  gcongr

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
  have hu := (summable_heckeHigherPrimePowerWeights F hσ).comp_injective
    (Subtype.val_injective (p := fun a : V[F] × ℕ ↦ (a.1.asIdeal.absNorm : ℝ) < x ∧
      x ≤ ((a.1.asIdeal.absNorm ^ (a.2 + 2) : ℕ) : ℝ)))
  have hb : ∀ (a : {a : V[F] × ℕ // (a.1.asIdeal.absNorm : ℝ) < x ∧
      x ≤ ((a.1.asIdeal.absNorm ^ (a.2 + 2) : ℕ) : ℝ)}) (s : ℂ), s ∈ {s : ℂ | σ ≤ s.re} →
      ‖heckePrimePowerLogTerm χ a.val.1 (a.val.2 + 1) s‖ ≤
        (1 : ℝ) / ((a.val.2 + 2 : ℕ) *
          (((a.val.1.asIdeal.absNorm ^ (a.val.2 + 2) : ℕ) : ℝ) ^ σ)) := by
    intro a s hs
    have h1 : (1 : ℝ) ≤ ((a.val.1.asIdeal.absNorm ^ (a.val.2 + 2) : ℕ) : ℝ) := by
      have := HeightOneSpectrum.one_lt_absNorm a.val.1
      exact_mod_cast Nat.one_le_pow _ _ (by omega)
    refine (heckeEulerProductLogCorrection_hasSumUniformlyOn_term_le χ a.val.1 a.val.2 s).trans ?_
    have hp : (0 : ℝ) < ((a.val.1.asIdeal.absNorm ^ (a.val.2 + 2) : ℕ) : ℝ) ^ σ :=
      Real.rpow_pos_of_pos (by linarith) _
    apply one_div_le_one_div_of_le (by positivity)
    exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le h1 hs) (by positivity)
  convert HasSumUniformlyOn.of_norm_le_summable hu hb using 1
  funext s
  delta heckeEulerProductLogCorrection
  rw [neg_neg]

/-- Paper: Theorem B.7.2.4(1), p. 652. The correction has norm at most
the tail of the positive majorant with prime-power norm at least `x`.
Deviation: The absolute majorant is evaluated at the real part of `s`. -/
theorem heckeEulerProductLogCorrection_norm_le (χ : U[F]) (x : ℝ) (s : ℂ)
    (hs : 1 / 2 < s.re) :
    ‖heckeEulerProductLogCorrection χ x s‖ ≤
      ∑' a : {a : V[F] × ℕ // x ≤ ((a.1.asIdeal.absNorm ^ (a.2 + 2) : ℕ) : ℝ)},
        (1 : ℝ) / ((a.val.2 + 2 : ℕ) *
          (((a.val.1.asIdeal.absNorm ^ (a.val.2 + 2) : ℕ) : ℝ) ^ s.re)) := by
  let w : V[F] × ℕ → ℝ := fun a ↦
    (1 : ℝ) / ((a.2 + 2 : ℕ) * (((a.1.asIdeal.absNorm ^ (a.2 + 2) : ℕ) : ℝ) ^ s.re))
  have hW : Summable w := summable_heckeHigherPrimePowerWeights F hs
  have hw0 : ∀ a, 0 ≤ w a := fun a ↦ by simp only [w]; positivity
  let S1 : Set (V[F] × ℕ) := {a | (a.1.asIdeal.absNorm : ℝ) < x ∧
    x ≤ ((a.1.asIdeal.absNorm ^ (a.2 + 2) : ℕ) : ℝ)}
  let S2 : Set (V[F] × ℕ) := {a | x ≤ ((a.1.asIdeal.absNorm ^ (a.2 + 2) : ℕ) : ℝ)}
  have hsub : S1 ⊆ S2 := fun a ha ↦ ha.2
  have hs1 : Summable (fun a : S1 ↦ w a) := hW.comp_injective Subtype.val_injective
  delta heckeEulerProductLogCorrection
  rw [norm_neg]
  calc ‖∑' a : S1, heckePrimePowerLogTerm χ a.val.1 (a.val.2 + 1) s‖
      ≤ ∑' a : S1, w a :=
        tsum_of_norm_bounded hs1.hasSum fun a ↦
          heckeEulerProductLogCorrection_hasSumUniformlyOn_term_le χ a.val.1 a.val.2 s
    _ = ∑' a, S1.indicator w a := tsum_subtype S1 w
    _ ≤ ∑' a, S2.indicator w a :=
        Summable.tsum_le_tsum (fun a ↦ Set.indicator_le_indicator_of_subset hsub hw0 a)
          (hW.indicator _) (hW.indicator _)
    _ = ∑' a : S2, w a := (tsum_subtype S2 w).symm

/-- Paper: Theorem B.7.2.4(1), p. 652. The correction tends to zero
uniformly on the whole 1-line. -/
theorem heckeEulerProductLogCorrection_tendstoUniformly (χ : U[F]) :
    TendstoUniformly (fun x : ℝ ↦ fun t : ℝ ↦ heckeEulerProductLogCorrection χ x ⟨1, t⟩)
      (fun _ ↦ 0) atTop := by
  let w : V[F] × ℕ → ℝ := fun a ↦
    (1 : ℝ) / ((a.2 + 2 : ℕ) * (((a.1.asIdeal.absNorm ^ (a.2 + 2) : ℕ) : ℝ) ^ (1 : ℝ)))
  have hW : Summable w := summable_heckeHigherPrimePowerWeights F (by norm_num)
  have hw0 : ∀ a, 0 ≤ w a := fun a ↦ by simp only [w]; positivity
  let S (x : ℝ) : Set (V[F] × ℕ) := {a | x ≤ ((a.1.asIdeal.absNorm ^ (a.2 + 2) : ℕ) : ℝ)}
  have hT : Tendsto (fun x ↦ ∑' a, (S x).indicator w a) atTop (𝓝 0) := by
    have h := tendsto_tsum_of_dominated_convergence (𝓕 := atTop)
      (f := fun x a ↦ (S x).indicator w a) (g := fun _ ↦ (0 : ℝ)) hW (fun a ↦ ?_)
      (Eventually.of_forall fun x a ↦ ?_)
    · simpa using h
    · apply tendsto_const_nhds.congr'
      filter_upwards [eventually_gt_atTop
        ((a.1.asIdeal.absNorm ^ (a.2 + 2) : ℕ) : ℝ)] with x hx
      exact (Set.indicator_of_notMem (fun h : x ≤ _ ↦ absurd h (not_le.mpr hx)) w).symm
    · rw [Real.norm_of_nonneg (Set.indicator_nonneg (fun a _ ↦ hw0 a) a)]
      exact Set.indicator_le_self' (fun a _ ↦ hw0 a) a
  rw [Metric.tendstoUniformly_iff]
  intro ε hε
  filter_upwards [hT.eventually (gt_mem_nhds hε)] with x hx t
  rw [dist_zero_left]
  refine lt_of_le_of_lt ?_ hx
  exact (heckeEulerProductLogCorrection_norm_le χ x ⟨1, t⟩ (by norm_num)).trans_eq
    (tsum_subtype (S x) w)

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

/-- The finite Euler factor of a norm twist of the trivial character at `s` is the
reciprocal of `1 - N(v)^(-(s + a))`. -/
private theorem reciprocalHeckeEulerProductBelow_at_pole_eq_prod_factor (χ : U[F]) (a : ℂ)
    (hχ : ideleClassNormTwist χ 0 = ideleClassNormTwist (1 : U[F]) a) (v : V[F]) (s : ℂ) :
    finiteHeckeEulerFactor χ v s = (1 - (v.asIdeal.absNorm : ℂ) ^ (-(s + a)))⁻¹ := by
  classical
  have hval (u : (v.adicCompletion F)ˣ) :
      (ideleClassNormTwist (1 : U[F]) a).restrict v u =
        (‖(u : v.adicCompletion F)‖ : ℂ) ^ a := by
    rw [HeckeCharacter.restrict, MulChar.ofUnitHom_coe]
    change 1 * (((ideleClassNorm F (IdeleClassGroup.ofAdicCompletion (𝓞 F) F v u) : NNReal) :
      ℝ) : ℂ) ^ a = _
    rw [one_mul, ideleClassNorm_ofAdicCompletion]
    rfl
  have hu : (ideleClassNormTwist (1 : U[F]) a).IsUnramifiedAt v := by
    apply HeckeCharacter.isUnramifiedAt_iff.mpr
    intro x
    let u := Units.map (v.adicCompletionIntegers F).subtype.toMonoidHom x
    change (ideleClassNormTwist (1 : U[F]) a).restrict v u = 1
    rw [hval u, show ‖(u : v.adicCompletion F)‖ = 1 from ?_, Complex.ofReal_one, Complex.one_cpow]
    apply Valued.toNormedField.norm_eq_one_iff.mpr
    exact HeightOneSpectrum.adicCompletionIntegers.mem_units_iff_valued_eq_one.mp
      (show u ∈ (v.adicCompletionIntegers F).units from ⟨x.val.property, x.inv.property⟩)
  let val : Valuation (v.adicCompletion F) (WithZero (Multiplicative ℤ)) := Valued.v
  obtain ⟨π, hπ⟩ := val.exists_isUniformizer_of_isCyclic_of_nontrivial
  let u := Units.mk0 (π : v.adicCompletion F) hπ.ne_zero
  have hnorm : ‖(u : v.adicCompletion F)‖ = (v.asIdeal.absNorm : ℝ)⁻¹ :=
    norm_uniformizer_adicCompletion v _ hπ
  have hN : (v.asIdeal.absNorm : ℂ) ≠ 0 := by
    exact_mod_cast (zero_lt_one.trans (HeightOneSpectrum.one_lt_absNorm v)).ne'
  rw [finiteHeckeEulerFactor, hχ, ite_eq_left hu, hu.localValue_eq u hπ, hval, hnorm,
    Complex.ofReal_inv, Complex.inv_cpow_ofReal_nonneg (Nat.cast_nonneg _) a,
    ← Complex.cpow_neg, Complex.ofReal_natCast, ← Complex.cpow_add _ _ hN, neg_add, add_comm (-a)]

/-- Paper: Remark B.7.2.6, Equation (B.7.2.25), p. 653. At the pole
ordinate the reciprocal product for a pure norm character equals the untwisted
Mertens product. -/
theorem reciprocalHeckeEulerProductBelow_at_pole_eq_prod (χ : U[F]) (t₀ x : ℝ)
    (hχ : ideleClassNormTwist χ 0 = ideleClassNormTwist (1 : U[F]) (-Complex.I * t₀)) :
    reciprocalHeckeEulerProductBelow χ x ⟨1, t₀⟩ =
      ∏ v ∈ heckePrimesBelow F x, (1 - (v.asIdeal.absNorm : ℂ)⁻¹) := by
  refine Finset.prod_congr rfl fun v _ ↦ ?_
  have h1 : -((⟨1, t₀⟩ : ℂ) + -Complex.I * t₀) = -1 := by
    apply Complex.ext <;> simp
  rw [reciprocalHeckeEulerProductBelow_at_pole_eq_prod_factor χ _ hχ, inv_inv, h1,
    Complex.cpow_neg_one]

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
