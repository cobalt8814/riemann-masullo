module

public import RiemannMasullo.AppB_AnalyticNT.Sec6
public import Mathlib.Algebra.Order.Round
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import RiemannMasullo.AppB_AnalyticNT.Sec3
import RiemannMasullo.ForMathlib.NumberTheory.NumberField.Completion.FinitePlace
import RiemannMasullo.ForMathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic

/-!
# Logarithmic derivatives and Perron's formula on the 1-line

Masullo, §B.7.1, pp. 643–648. The finite Hecke L-function on the boundary is
represented by a meromorphic continuation in normal form, as in §B.6.
-/

@[expose] public noncomputable section

open Filter IsDedekindDomain NumberField Set
open scoped Asymptotics Topology NNReal

namespace RiemannMasullo

variable {F : Type*} [Field F] [NumberField F]

local notation "U[" F "]" => PontryaginDual (IdeleClassGroup (𝓞 F) F)
local notation "halfPlane" => Complex.re ⁻¹' Ioi (1 : ℝ)
local notation "oneLine" => Complex.re ⁻¹' ({1} : Set ℝ)

/-- Paper: Equation (B.7.1.1), p. 643. The twisted ideal von Mangoldt series
converges absolutely to the negative logarithmic derivative to the right of one. -/
theorem finiteHeckeL_negLogDeriv_hasSum_ideals (χ : U[F]) (L : ℂ → ℂ)
    (hL : MeromorphicNFOn L univ) (hSeries : ∀ s : halfPlane, L s = finiteHeckeL χ s)
    (s : halfPlane) :
    HasSum (fun I : {I : Ideal (𝓞 F) // I ≠ ⊥} ↦
      heckeIdealVonMangoldt (ideleClassNormTwist χ 0) I.val /
        (I.val.absNorm : ℂ) ^ (s : ℂ)) (-logDeriv L s) := by
  sorry

/-- Paper: Equations (B.7.1.4)–(B.7.1.5), p. 644. This is the normalized integral
of `f(s+w) x^w / w` up the segment from `c - iT` to `c + iT`. The factor
`i` in the path derivative cancels the `i` in the normalization. -/
def truncatedPerronIntegral (f : ℂ → ℂ) (s : ℂ) (x c T : ℝ) : ℂ :=
  (∫ t in -T..T, f (s + ⟨c, t⟩) * (x : ℂ) ^ (⟨c, t⟩ : ℂ) / (⟨c, t⟩ : ℂ)) /
    (2 * (Real.pi : ℂ))

/-- Paper: Equation (B.7.1.7), p. 645. At the endpoint, the integral of the
constant series at cutoff one gives the arctangent factor. -/
theorem truncatedPerronIntegral_one (s : ℂ) {c T : ℝ} (hc : 0 < c) :
    truncatedPerronIntegral (fun _ ↦ 1) s 1 c T = (Real.arctan (T / c) / Real.pi : ℝ) := by
  have hz : ∀ t : ℝ, (⟨c, t⟩ : ℂ) ≠ 0 := fun t h ↦ hc.ne' (congrArg Complex.re h)
  have hinv : ∀ t : ℝ, 1 / (⟨c, t⟩ : ℂ) =
      ((c / (c ^ 2 + t ^ 2) : ℝ) : ℂ) - Complex.I * ((t / (c ^ 2 + t ^ 2) : ℝ) : ℂ) := by
    intro t
    rw [one_div]
    apply Complex.ext <;>
      simp only [Complex.inv_re, Complex.inv_im, Complex.normSq_mk, Complex.sub_re,
        Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
        Complex.ofReal_re, Complex.ofReal_im] <;>
      ring
  have hderiv : ∀ t : ℝ, HasDerivAt
      (fun t : ℝ ↦ (Real.arctan (t / c) : ℂ) - Complex.I * (Real.log (c ^ 2 + t ^ 2) / 2 : ℝ))
      (1 / (⟨c, t⟩ : ℂ)) t := by
    intro t
    have hpos : 0 < c ^ 2 + t ^ 2 := by positivity
    have h1 := ((hasDerivAt_id' t).div_const c).arctan.ofReal_comp
    have h2 := ((((hasDerivAt_pow 2 t).const_add (c ^ 2)).log hpos.ne').div_const 2).ofReal_comp
    convert h1.sub (h2.const_mul Complex.I) using 1
    rw [hinv t]
    congr 3
    · field_simp
    · field_simp
      ring
  have hcont : Continuous fun t : ℝ ↦ 1 / (⟨c, t⟩ : ℂ) := by
    refine continuous_const.div ?_ hz
    rw [show Complex.mk c = fun t : ℝ ↦ (c : ℂ) + (t : ℂ) * Complex.I from
      funext fun t ↦ Complex.mk_eq_add_mul_I c t]
    fun_prop
  have hπ : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  show (∫ t in -T..T, (1 : ℂ) * ((1 : ℝ) : ℂ) ^ (⟨c, t⟩ : ℂ) / (⟨c, t⟩ : ℂ)) /
    (2 * (Real.pi : ℂ)) = _
  simp only [Complex.ofReal_one, Complex.one_cpow, one_mul]
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ ↦ hderiv t)
    (hcont.intervalIntegrable _ _)]
  simp only [neg_div, Real.arctan_neg, neg_sq, Complex.ofReal_neg]
  push_cast
  field_simp
  ring

/-- Paper: Lemma B.7.1.1, pp. 644–645. This sums the Dirichlet terms for positive
integers up to the real cutoff, with half weight when the cutoff is an integer. -/
def perronHalfWeightedSum (a : ℕ → ℂ) (s : ℂ) (x : ℝ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 ⌊x⌋₊,
    if (n : ℝ) = x then LSeries.term a s n / 2 else LSeries.term a s n

/-- Paper: Equation (B.7.1.5), p. 644. At a positive integer cutoff, the terms
strictly below the cutoff have full weight and the last term has half weight. -/
theorem perronHalfWeightedSum_nat (a : ℕ → ℂ) (s : ℂ) {m : ℕ} (hm : 0 < m) :
    perronHalfWeightedSum a s m =
      (∑ n ∈ Finset.Ico 1 m, LSeries.term a s n) + LSeries.term a s m / 2 := by
  show (∑ n ∈ Finset.Icc 1 ⌊(m : ℝ)⌋₊,
      if (n : ℝ) = m then LSeries.term a s n / 2 else LSeries.term a s n) = _
  rw [Nat.floor_natCast, Finset.Icc_eq_cons_Ico hm, Finset.sum_cons, ite_eq_left rfl, add_comm]
  congr 1
  refine Finset.sum_congr rfl fun n hn ↦ ite_eq_right ?_
  exact_mod_cast (Finset.mem_Ico.mp hn).2.ne

/-- A horizontal edge at height `±T`: the integral of `y^w / w` is at most the integral
of `y^u / T`. -/
private theorem truncatedPerron_error_horizontal {y T τ a b : ℝ} (hy : 0 < y) (hy1 : y ≠ 1)
    (hT : 0 < T) (hτ : |τ| = T) (hab : a ≤ b) :
    ‖∫ u in a..b, (y : ℂ) ^ (⟨u, τ⟩ : ℂ) / (⟨u, τ⟩ : ℂ)‖ ≤
      (y ^ b - y ^ a) / (T * Real.log y) := by
  have hlog : Real.log y ≠ 0 := Real.log_ne_zero_of_pos_of_ne_one hy hy1
  have hpt : ∀ u : ℝ, u ∈ Ioc a b →
      ‖(y : ℂ) ^ (⟨u, τ⟩ : ℂ) / (⟨u, τ⟩ : ℂ)‖ ≤ y ^ u / T := by
    intro u _
    have hn : T ≤ ‖(⟨u, τ⟩ : ℂ)‖ := by
      have h := Complex.abs_im_le_norm (⟨u, τ⟩ : ℂ)
      rwa [show (⟨u, τ⟩ : ℂ).im = τ from rfl, hτ] at h
    rw [norm_div, Complex.norm_cpow_eq_rpow_re_of_pos hy, show (⟨u, τ⟩ : ℂ).re = u from rfl]
    exact div_le_div_of_nonneg_left (Real.rpow_pos_of_pos hy u).le hT hn
  have hderiv : ∀ u ∈ uIcc a b,
      HasDerivAt (fun u : ℝ ↦ y ^ u / (T * Real.log y)) (y ^ u / T) u := by
    intro u _
    have h1 := (Real.hasStrictDerivAt_const_rpow hy u).hasDerivAt.div_const (T * Real.log y)
    refine h1.congr_deriv ?_
    field_simp
  have hcont : Continuous fun u : ℝ ↦ y ^ u / T :=
    (Real.continuous_const_rpow hy.ne').div_const T
  have hle : ‖∫ u in a..b, (y : ℂ) ^ (⟨u, τ⟩ : ℂ) / (⟨u, τ⟩ : ℂ)‖ ≤ ∫ u in a..b, y ^ u / T :=
    intervalIntegral.norm_integral_le_of_norm_le hab (Eventually.of_forall hpt)
      (hcont.intervalIntegrable _ _)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv (hcont.intervalIntegrable _ _)]
    at hle
  rwa [← sub_div] at hle

/-- The rectangle identity bounds one vertical edge by the other three. -/
private theorem truncatedPerron_error_rect_norm {A₁ A₂ V J : ℂ}
    (h : A₁ - A₂ + Complex.I • V - Complex.I • J = 0) : ‖J‖ ≤ ‖A₁‖ + ‖A₂‖ + ‖V‖ := by
  have hJ : Complex.I * J = A₁ - A₂ + Complex.I * V := by
    simp only [smul_eq_mul] at h
    linear_combination (-1 : ℂ) * h
  calc ‖J‖ = ‖Complex.I * J‖ := by rw [norm_mul, Complex.norm_I, one_mul]
    _ = ‖A₁ - A₂ + Complex.I * V‖ := by rw [hJ]
    _ ≤ ‖A₁‖ + ‖A₂‖ + ‖V‖ := by
        refine (norm_add_le _ _).trans (add_le_add (norm_sub_le _ _) ?_)
        rw [norm_mul, Complex.norm_I, one_mul]

/-- Perron's kernel for `y < 1`: shifting the segment to the right. -/
private theorem truncatedPerron_error_lt_one {y c T : ℝ} (hy : 0 < y) (hy1 : y < 1)
    (hc : 0 < c) (hT : 0 < T) :
    ‖∫ t in -T..T, (y : ℂ) ^ (⟨c, t⟩ : ℂ) / (⟨c, t⟩ : ℂ)‖ ≤
      2 * y ^ c / (T * |Real.log y|) := by
  have hlog : Real.log y < 0 := Real.log_neg hy hy1
  refine le_of_forall_pos_le_add fun ε hε ↦ ?_
  obtain ⟨U, hUc, hUε⟩ : ∃ U : ℝ, c < U ∧ 2 * T / ε ≤ U :=
    ⟨max (c + 1) (2 * T / ε), lt_max_of_lt_left (lt_add_one c), le_max_right _ _⟩
  have hU0 : 0 < U := hc.trans hUc
  have H : DifferentiableOn ℂ (fun w : ℂ ↦ (y : ℂ) ^ w / w)
      (uIcc (⟨c, -T⟩ : ℂ).re (⟨U, T⟩ : ℂ).re ×ℂ uIcc (⟨c, -T⟩ : ℂ).im (⟨U, T⟩ : ℂ).im) := by
    intro w hw
    have hre : c ≤ w.re := by
      have h1 : w.re ∈ uIcc c U := hw.1
      rw [uIcc_of_le hUc.le] at h1
      exact h1.1
    have hw0 : w ≠ 0 := fun h ↦ by
      rw [h, Complex.zero_re] at hre
      linarith
    exact ((differentiableAt_id.const_cpow
      (Or.inl (Complex.ofReal_ne_zero.mpr hy.ne'))).div differentiableAt_id
        hw0).differentiableWithinAt
  have rect := Complex.integral_boundary_rect_eq_zero_of_differentiableOn _ _ _ H
  dsimp only at rect
  simp only [← Complex.mk_eq_add_mul_I] at rect
  have hJ := truncatedPerron_error_rect_norm rect
  have hA₁ := truncatedPerron_error_horizontal hy hy1.ne hT (τ := -T)
    (by rw [abs_neg, abs_of_pos hT]) hUc.le
  have hA₂ := truncatedPerron_error_horizontal hy hy1.ne hT (τ := T) (abs_of_pos hT) hUc.le
  have hV : ‖∫ t in -T..T, (y : ℂ) ^ (⟨U, t⟩ : ℂ) / (⟨U, t⟩ : ℂ)‖ ≤ 1 / U * |T - -T| := by
    apply intervalIntegral.norm_integral_le_of_norm_le_const
    intro t _
    have hn : U ≤ ‖(⟨U, t⟩ : ℂ)‖ := by
      have h := Complex.abs_re_le_norm (⟨U, t⟩ : ℂ)
      rwa [show (⟨U, t⟩ : ℂ).re = U from rfl, abs_of_pos hU0] at h
    rw [norm_div, Complex.norm_cpow_eq_rpow_re_of_pos hy, show (⟨U, t⟩ : ℂ).re = U from rfl]
    exact div_le_div₀ zero_le_one (Real.rpow_le_one hy.le hy1.le hU0.le) hU0 hn
  have hTl : 0 < T * -Real.log y := mul_pos hT (by linarith)
  have hb : (y ^ U - y ^ c) / (T * Real.log y) ≤ y ^ c / (T * |Real.log y|) := by
    have e : (y ^ U - y ^ c) / (T * Real.log y) = (y ^ c - y ^ U) / (T * -Real.log y) := by
      rw [mul_neg, ← neg_sub (y ^ U) (y ^ c), neg_div_neg_eq]
    rw [e, abs_of_neg hlog]
    exact div_le_div_of_nonneg_right (by linarith [Real.rpow_pos_of_pos hy U]) hTl.le
  have hε' : 1 / U * |T - -T| ≤ ε := by
    rw [sub_neg_eq_add, abs_of_pos (by linarith), one_div, inv_mul_le_iff₀ hU0]
    have := (div_le_iff₀ hε).mp hUε
    linarith
  have hsplit : 2 * y ^ c / (T * |Real.log y|) =
      y ^ c / (T * |Real.log y|) + y ^ c / (T * |Real.log y|) := by ring
  rw [hsplit]
  linarith

/-- Along a path that avoids the origin, the divided difference of `y^w` at `0` splits
into `y^w / w` and `1 / w`. -/
private theorem truncatedPerron_error_dslope_path {y : ℝ} (hy : 0 < y) {γ : ℝ → ℂ}
    (hγ : Continuous γ) (h0 : ∀ u, γ u ≠ 0) (a b : ℝ) :
    ∫ u in a..b, dslope (fun w : ℂ ↦ (y : ℂ) ^ w) 0 (γ u) =
      (∫ u in a..b, (y : ℂ) ^ (γ u) / γ u) - ∫ u in a..b, 1 / γ u := by
  have hy0 : (y : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hy.ne'
  have h1 : Continuous fun u : ℝ ↦ (y : ℂ) ^ (γ u) / γ u :=
    (hγ.const_cpow (Or.inl hy0)).div hγ h0
  have h2 : Continuous fun u : ℝ ↦ 1 / γ u := continuous_const.div hγ h0
  rw [← intervalIntegral.integral_sub (h1.intervalIntegrable _ _) (h2.intervalIntegrable _ _)]
  refine intervalIntegral.integral_congr fun u _ ↦ ?_
  change dslope (fun w : ℂ ↦ (y : ℂ) ^ w) 0 (γ u) = (y : ℂ) ^ (γ u) / γ u - 1 / γ u
  rw [dslope_of_ne _ (h0 u), slope_def_field, Complex.cpow_zero, sub_zero, sub_div]

/-- The integral of `1 / w` along a horizontal segment off the real axis. -/
private theorem truncatedPerron_error_inv_horizontal {τ a b : ℝ} (hτ : τ ≠ 0) :
    ∫ u in a..b, 1 / (⟨u, τ⟩ : ℂ) =
      ((Real.log (b ^ 2 + τ ^ 2) / 2 - Real.log (a ^ 2 + τ ^ 2) / 2 : ℝ) : ℂ) -
        Complex.I * ((Real.arctan (b / τ) - Real.arctan (a / τ) : ℝ) : ℂ) := by
  have hτ2 : 0 < τ ^ 2 := by positivity
  have hpos : ∀ u : ℝ, 0 < u ^ 2 + τ ^ 2 := fun u ↦ by positivity
  have hz : ∀ u : ℝ, (⟨u, τ⟩ : ℂ) ≠ 0 := fun u h ↦ hτ (congrArg Complex.im h)
  have hinv : ∀ u : ℝ, 1 / (⟨u, τ⟩ : ℂ) =
      ((u / (u ^ 2 + τ ^ 2) : ℝ) : ℂ) - Complex.I * ((τ / (u ^ 2 + τ ^ 2) : ℝ) : ℂ) := by
    intro u
    rw [one_div]
    apply Complex.ext <;>
      simp only [Complex.inv_re, Complex.inv_im, Complex.normSq_mk, Complex.sub_re,
        Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
        Complex.ofReal_re, Complex.ofReal_im] <;>
      ring
  have hderiv : ∀ u ∈ uIcc a b, HasDerivAt
      (fun u : ℝ ↦ ((Real.log (u ^ 2 + τ ^ 2) / 2 : ℝ) : ℂ) -
        Complex.I * ((Real.arctan (u / τ) : ℝ) : ℂ)) (1 / (⟨u, τ⟩ : ℂ)) u := by
    intro u _
    have hne := (hpos u).ne'
    have h1 : HasDerivAt (fun u : ℝ ↦ ((Real.log (u ^ 2 + τ ^ 2) / 2 : ℝ) : ℂ))
        ((u / (u ^ 2 + τ ^ 2) : ℝ) : ℂ) u := by
      have h := (((hasDerivAt_pow 2 u).add_const (τ ^ 2)).log hne).div_const 2
      refine (h.congr_deriv ?_).ofReal_comp
      rw [show (2 - 1 : ℕ) = 1 from rfl, pow_one, Nat.cast_ofNat]
      field_simp
    have h2 : HasDerivAt (fun u : ℝ ↦ ((Real.arctan (u / τ) : ℝ) : ℂ))
        ((τ / (u ^ 2 + τ ^ 2) : ℝ) : ℂ) u := by
      have h := ((hasDerivAt_id' u).div_const τ).arctan
      refine (h.congr_deriv ?_).ofReal_comp
      field_simp
      ring
    rw [hinv u]
    exact h1.sub (h2.const_mul Complex.I)
  have hcont : Continuous fun u : ℝ ↦ 1 / (⟨u, τ⟩ : ℂ) := by
    refine continuous_const.div ?_ hz
    rw [show (fun u : ℝ ↦ (⟨u, τ⟩ : ℂ)) = fun u : ℝ ↦ (u : ℂ) + (τ : ℂ) * Complex.I from
      funext fun u ↦ Complex.mk_eq_add_mul_I u τ]
    fun_prop
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv (hcont.intervalIntegrable _ _)]
  push_cast
  ring

/-- Perron's kernel for `y > 1`: shifting the segment to the left across the pole at `0`. -/
private theorem truncatedPerron_error_gt_one {y c T : ℝ} (hy1 : 1 < y) (hc : 0 < c)
    (hT : 0 < T) :
    ‖(2 * Real.pi : ℂ) - ∫ t in -T..T, (y : ℂ) ^ (⟨c, t⟩ : ℂ) / (⟨c, t⟩ : ℂ)‖ ≤
      2 * y ^ c / (T * Real.log y) := by
  have hy : 0 < y := zero_lt_one.trans hy1
  have hy0 : (y : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hy.ne'
  have hlog : 0 < Real.log y := Real.log_pos hy1
  refine le_of_forall_pos_le_add fun ε hε ↦ ?_
  obtain ⟨U, hU0, hUε⟩ : ∃ U : ℝ, 0 < U ∧ 6 * T / ε ≤ U :=
    ⟨max 1 (6 * T / ε), lt_max_of_lt_left one_pos, le_max_right _ _⟩
  have hdiff : Differentiable ℂ (dslope (fun w : ℂ ↦ (y : ℂ) ^ w) 0) := by
    have h1 : Differentiable ℂ fun w : ℂ ↦ (y : ℂ) ^ w :=
      differentiable_id.const_cpow (Or.inl hy0)
    have h2 := (Complex.differentiableOn_dslope (c := (0 : ℂ)) univ_mem).mpr h1.differentiableOn
    exact differentiableOn_univ.mp h2
  have rect := Complex.integral_boundary_rect_eq_zero_of_differentiableOn
    (dslope (fun w : ℂ ↦ (y : ℂ) ^ w) 0) ⟨-U, -T⟩ ⟨c, T⟩ hdiff.differentiableOn
  dsimp only at rect
  simp only [← Complex.mk_eq_add_mul_I] at rect
  have hmkh : ∀ τ : ℝ, Continuous fun u : ℝ ↦ (⟨u, τ⟩ : ℂ) := fun τ ↦ by
    rw [show (fun u : ℝ ↦ (⟨u, τ⟩ : ℂ)) = fun u : ℝ ↦ (u : ℂ) + (τ : ℂ) * Complex.I from
      funext fun u ↦ Complex.mk_eq_add_mul_I u τ]
    fun_prop
  have hmkv : ∀ ρ : ℝ, Continuous fun t : ℝ ↦ (⟨ρ, t⟩ : ℂ) := fun ρ ↦ by
    rw [show (fun t : ℝ ↦ (⟨ρ, t⟩ : ℂ)) = fun t : ℝ ↦ (ρ : ℂ) + (t : ℂ) * Complex.I from
      funext fun t ↦ Complex.mk_eq_add_mul_I ρ t]
    fun_prop
  have hTne : T ≠ 0 := hT.ne'
  rw [truncatedPerron_error_dslope_path hy (hmkh (-T))
      (fun u h ↦ hTne (neg_eq_zero.mp (congrArg Complex.im h))) (-U) c,
    truncatedPerron_error_dslope_path hy (hmkh T)
      (fun u h ↦ hTne (congrArg Complex.im h)) (-U) c,
    truncatedPerron_error_dslope_path hy (hmkv c)
      (fun t h ↦ hc.ne' (congrArg Complex.re h)) (-T) T,
    truncatedPerron_error_inv_horizontal (neg_ne_zero.mpr hTne),
    truncatedPerron_error_inv_horizontal hTne] at rect
  have hS : ∫ t in -T..T, 1 / (⟨c, t⟩ : ℂ) = ((2 * Real.arctan (T / c) : ℝ) : ℂ) := by
    have h : (∫ t in -T..T, (1 : ℂ) * ((1 : ℝ) : ℂ) ^ (⟨c, t⟩ : ℂ) / (⟨c, t⟩ : ℂ)) /
        (2 * (Real.pi : ℂ)) = ((Real.arctan (T / c) / Real.pi : ℝ) : ℂ) :=
      truncatedPerronIntegral_one (0 : ℂ) hc
    simp only [Complex.ofReal_one, Complex.one_cpow, one_mul] at h
    have hπ : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
    rw [div_eq_iff (mul_ne_zero two_ne_zero hπ)] at h
    rw [h]
    push_cast
    field_simp
  have hpi1 : Real.arctan (T / c) = Real.pi / 2 - Real.arctan (c / T) := by
    rw [← Real.arctan_inv_of_pos (div_pos hc hT), inv_div]
  have hpi2 : Real.arctan (U / T) = Real.pi / 2 - Real.arctan (T / U) := by
    rw [← Real.arctan_inv_of_pos (div_pos hT hU0), inv_div]
  rw [hS] at rect
  simp only [div_neg, neg_div, Real.arctan_neg, neg_sq] at rect
  rw [hpi1, hpi2] at rect
  have key : Complex.I * ((2 * Real.pi : ℂ) -
      ∫ t in -T..T, (y : ℂ) ^ (⟨c, t⟩ : ℂ) / (⟨c, t⟩ : ℂ)) =
      (∫ u in -U..c, (y : ℂ) ^ (⟨u, -T⟩ : ℂ) / (⟨u, -T⟩ : ℂ)) -
      (∫ u in -U..c, (y : ℂ) ^ (⟨u, T⟩ : ℂ) / (⟨u, T⟩ : ℂ)) +
      Complex.I * ((2 * Real.arctan (T / U) : ℝ) : ℂ) -
      Complex.I * ∫ t in -T..T, dslope (fun w : ℂ ↦ (y : ℂ) ^ w) 0 (⟨-U, t⟩ : ℂ) := by
    simp only [smul_eq_mul] at rect
    push_cast at rect ⊢
    linear_combination (-1 : ℂ) * rect
  have hP₁ := truncatedPerron_error_horizontal hy hy1.ne' hT (τ := -T)
    (by rw [abs_neg, abs_of_pos hT]) (show -U ≤ c by linarith)
  have hP₂ := truncatedPerron_error_horizontal hy hy1.ne' hT (τ := T) (abs_of_pos hT)
    (show -U ≤ c by linarith)
  have hW : ‖∫ t in -T..T, dslope (fun w : ℂ ↦ (y : ℂ) ^ w) 0 (⟨-U, t⟩ : ℂ)‖ ≤
      2 / U * |T - -T| := by
    apply intervalIntegral.norm_integral_le_of_norm_le_const
    intro t _
    have hne : (⟨-U, t⟩ : ℂ) ≠ 0 := fun h ↦ hU0.ne' (neg_eq_zero.mp (congrArg Complex.re h))
    have hn : U ≤ ‖(⟨-U, t⟩ : ℂ)‖ := by
      have h := Complex.abs_re_le_norm (⟨-U, t⟩ : ℂ)
      rwa [show (⟨-U, t⟩ : ℂ).re = -U from rfl, abs_neg, abs_of_pos hU0] at h
    rw [dslope_of_ne _ hne, slope_def_field, Complex.cpow_zero, sub_zero, norm_div]
    refine div_le_div₀ zero_le_two ((norm_sub_le _ _).trans ?_) hU0 hn
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hy, show (⟨-U, t⟩ : ℂ).re = -U from rfl, norm_one]
    linarith [Real.rpow_le_one_of_one_le_of_nonpos hy1.le (by linarith : -U ≤ 0)]
  have hat : Real.arctan (T / U) ≤ T / U := Real.arctan_le_self (div_pos hT hU0).le
  have hat0 : 0 ≤ Real.arctan (T / U) := Real.arctan_nonneg.mpr (div_pos hT hU0).le
  have hb : (y ^ c - y ^ (-U)) / (T * Real.log y) ≤ y ^ c / (T * Real.log y) :=
    div_le_div_of_nonneg_right (by linarith [Real.rpow_pos_of_pos hy (-U)])
      (mul_pos hT hlog).le
  have hε' : 2 / U * |T - -T| + 2 * (T / U) ≤ ε := by
    rw [sub_neg_eq_add, abs_of_pos (by linarith)]
    have h6 := (div_le_iff₀ hε).mp hUε
    have e : 2 / U * (T + T) + 2 * (T / U) = 6 * T / U := by
      field_simp
      ring
    rw [e, div_le_iff₀ hU0]
    linarith
  have hnorm : ‖(2 * Real.pi : ℂ) - ∫ t in -T..T, (y : ℂ) ^ (⟨c, t⟩ : ℂ) / (⟨c, t⟩ : ℂ)‖ =
      ‖Complex.I * ((2 * Real.pi : ℂ) -
        ∫ t in -T..T, (y : ℂ) ^ (⟨c, t⟩ : ℂ) / (⟨c, t⟩ : ℂ))‖ := by
    rw [norm_mul, Complex.norm_I, one_mul]
  rw [hnorm, key]
  have hI2 : ‖Complex.I * ((2 * Real.arctan (T / U) : ℝ) : ℂ)‖ = 2 * Real.arctan (T / U) := by
    rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_of_nonneg (by linarith)]
  have hIW : ‖Complex.I * ∫ t in -T..T, dslope (fun w : ℂ ↦ (y : ℂ) ^ w) 0 (⟨-U, t⟩ : ℂ)‖ =
      ‖∫ t in -T..T, dslope (fun w : ℂ ↦ (y : ℂ) ^ w) 0 (⟨-U, t⟩ : ℂ)‖ := by
    rw [norm_mul, Complex.norm_I, one_mul]
  have htri := (norm_sub_le
    ((∫ u in -U..c, (y : ℂ) ^ (⟨u, -T⟩ : ℂ) / (⟨u, -T⟩ : ℂ)) -
      (∫ u in -U..c, (y : ℂ) ^ (⟨u, T⟩ : ℂ) / (⟨u, T⟩ : ℂ)) +
      Complex.I * ((2 * Real.arctan (T / U) : ℝ) : ℂ))
    (Complex.I * ∫ t in -T..T, dslope (fun w : ℂ ↦ (y : ℂ) ^ w) 0 (⟨-U, t⟩ : ℂ)))
  have htri2 := (norm_add_le
    ((∫ u in -U..c, (y : ℂ) ^ (⟨u, -T⟩ : ℂ) / (⟨u, -T⟩ : ℂ)) -
      (∫ u in -U..c, (y : ℂ) ^ (⟨u, T⟩ : ℂ) / (⟨u, T⟩ : ℂ)))
    (Complex.I * ((2 * Real.arctan (T / U) : ℝ) : ℂ)))
  have htri3 := (norm_sub_le
    (∫ u in -U..c, (y : ℂ) ^ (⟨u, -T⟩ : ℂ) / (⟨u, -T⟩ : ℂ))
    (∫ u in -U..c, (y : ℂ) ^ (⟨u, T⟩ : ℂ) / (⟨u, T⟩ : ℂ)))
  rw [hI2] at htri2
  rw [hIW] at htri
  have hsplit : 2 * y ^ c / (T * Real.log y) =
      y ^ c / (T * Real.log y) + y ^ c / (T * Real.log y) := by ring
  rw [hsplit]
  linarith

/-- Perron's kernel with the three cases combined. -/
private theorem truncatedPerron_error_kernel {y c T : ℝ} (hy : 0 < y) (hc : 0 < c)
    (hT : 0 < T) :
    ‖(if 1 < y then (1 : ℂ) else if y = 1 then 1 / 2 else 0) -
        (∫ t in -T..T, (y : ℂ) ^ (⟨c, t⟩ : ℂ) / (⟨c, t⟩ : ℂ)) / (2 * (Real.pi : ℂ))‖ ≤
      if y = 1 then c / (Real.pi * T) else y ^ c / (Real.pi * T * |Real.log y|) := by
  have hπ : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hn2π : ‖(2 * (Real.pi : ℂ))‖ = 2 * Real.pi := by
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le, Complex.norm_ofNat]
  have h2π0 : 0 < 2 * Real.pi := by positivity
  rcases lt_trichotomy y 1 with hlt | rfl | hgt
  · rw [ite_eq_right (not_lt.mpr hlt.le), ite_eq_right hlt.ne, ite_eq_right hlt.ne, zero_sub,
      norm_neg, norm_div, hn2π, div_le_iff₀ h2π0]
    have h := truncatedPerron_error_lt_one hy hlt hc hT
    have hlog : 0 < |Real.log y| := abs_pos.mpr (Real.log_neg hy hlt).ne
    have e : y ^ c / (Real.pi * T * |Real.log y|) * (2 * Real.pi) =
        2 * y ^ c / (T * |Real.log y|) := by
      field_simp
    rw [e]
    exact h
  · rw [ite_eq_right (lt_irrefl _), ite_eq_left rfl, ite_eq_left rfl]
    have h : (∫ t in -T..T, (1 : ℂ) * ((1 : ℝ) : ℂ) ^ (⟨c, t⟩ : ℂ) / (⟨c, t⟩ : ℂ)) /
        (2 * (Real.pi : ℂ)) = ((Real.arctan (T / c) / Real.pi : ℝ) : ℂ) :=
      truncatedPerronIntegral_one (0 : ℂ) hc
    simp only [one_mul] at h
    rw [h]
    have hpi1 : Real.arctan (T / c) = Real.pi / 2 - Real.arctan (c / T) := by
      rw [← Real.arctan_inv_of_pos (div_pos hc hT), inv_div]
    have e : (1 / 2 : ℂ) - ((Real.arctan (T / c) / Real.pi : ℝ) : ℂ) =
        ((Real.arctan (c / T) / Real.pi : ℝ) : ℂ) := by
      rw [hpi1]
      push_cast
      field_simp
      ring
    rw [e, Complex.norm_real, Real.norm_of_nonneg
      (div_nonneg (Real.arctan_nonneg.mpr (div_pos hc hT).le) Real.pi_pos.le),
      div_le_div_iff₀ Real.pi_pos (mul_pos Real.pi_pos hT)]
    have h1 := Real.arctan_le_self (div_pos hc hT).le
    have h2 : Real.arctan (c / T) * T ≤ c := by
      calc Real.arctan (c / T) * T ≤ c / T * T := mul_le_mul_of_nonneg_right h1 hT.le
        _ = c := div_mul_cancel₀ c hT.ne'
    nlinarith [Real.pi_pos]
  · rw [ite_eq_left hgt, ite_eq_right hgt.ne']
    have h := truncatedPerron_error_gt_one hgt hc hT
    have hlog : 0 < Real.log y := Real.log_pos hgt
    have e : (1 : ℂ) - (∫ t in -T..T, (y : ℂ) ^ (⟨c, t⟩ : ℂ) / (⟨c, t⟩ : ℂ)) /
        (2 * (Real.pi : ℂ)) =
        ((2 * Real.pi : ℂ) - ∫ t in -T..T, (y : ℂ) ^ (⟨c, t⟩ : ℂ) / (⟨c, t⟩ : ℂ)) /
          (2 * (Real.pi : ℂ)) := by
      field_simp
    rw [e, norm_div, hn2π, abs_of_pos hlog, div_le_iff₀ h2π0]
    have e2 : y ^ c / (Real.pi * T * Real.log y) * (2 * Real.pi) =
        2 * y ^ c / (T * Real.log y) := by
      field_simp
    rw [e2]
    exact h

/-- Shifting the exponent by `c` rescales the norm of a Dirichlet term. -/
private theorem truncatedPerron_error_norm_term (a : ℕ → ℂ) (s : ℂ) {x c : ℝ} (hx : 0 < x)
    (n : ℕ) :
    ‖LSeries.term a s n‖ * (x / n) ^ c = x ^ c * ‖LSeries.term a (s + (c : ℂ)) n‖ := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  · have hn0 : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
    rw [LSeries.norm_term_eq, LSeries.norm_term_eq, ite_eq_right hn, ite_eq_right hn,
      Complex.add_re, Complex.ofReal_re, Real.div_rpow hx.le hn0.le, Real.rpow_add hn0]
    have h1 := (Real.rpow_pos_of_pos hn0 s.re).ne'
    have h2 := (Real.rpow_pos_of_pos hn0 c).ne'
    field_simp

/-- Term by term integration of the Dirichlet series against Perron's kernel. -/
private theorem truncatedPerron_error_hasSum (a : ℕ → ℂ) (s : ℂ) {x c T : ℝ} (hx : 0 < x)
    (hc : 0 < c) (ha : LSeriesSummable a (s + (c : ℂ))) :
    HasSum (fun n : ℕ ↦ LSeries.term a s n *
        ((∫ t in -T..T, ((x / n : ℝ) : ℂ) ^ (⟨c, t⟩ : ℂ) / (⟨c, t⟩ : ℂ)) /
          (2 * (Real.pi : ℂ))))
      (truncatedPerronIntegral (LSeries a) s x c T) := by
  have hmk : Continuous fun t : ℝ ↦ (⟨c, t⟩ : ℂ) := by
    rw [show (fun t : ℝ ↦ (⟨c, t⟩ : ℂ)) = fun t : ℝ ↦ (c : ℂ) + (t : ℂ) * Complex.I from
      funext fun t ↦ Complex.mk_eq_add_mul_I c t]
    fun_prop
  have hz : ∀ t : ℝ, (⟨c, t⟩ : ℂ) ≠ 0 := fun t h ↦ hc.ne' (congrArg Complex.re h)
  have hF : ∀ (n : ℕ) (t : ℝ),
      LSeries.term a (s + ⟨c, t⟩) n * (x : ℂ) ^ (⟨c, t⟩ : ℂ) / (⟨c, t⟩ : ℂ) =
        LSeries.term a s n * (((x / n : ℝ) : ℂ) ^ (⟨c, t⟩ : ℂ) / (⟨c, t⟩ : ℂ)) := by
    intro n t
    rcases eq_or_ne n 0 with rfl | hn
    · simp
    · have hn0 : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
      have hnC : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn
      have hdiv : ((x / n : ℝ) : ℂ) ^ (⟨c, t⟩ : ℂ) =
          (x : ℂ) ^ (⟨c, t⟩ : ℂ) / (n : ℂ) ^ (⟨c, t⟩ : ℂ) := by
        rw [div_eq_mul_inv x, Complex.ofReal_mul,
          Complex.mul_cpow_ofReal_nonneg hx.le (inv_nonneg.mpr hn0.le), Complex.ofReal_inv,
          Complex.ofReal_natCast, Complex.inv_cpow _ _
            (by rw [Complex.natCast_arg]; exact Real.pi_ne_zero.symm), div_eq_mul_inv]
      have h1 : (n : ℂ) ^ s ≠ 0 := fun h ↦ hnC ((Complex.cpow_eq_zero_iff _ _).mp h).1
      have h2 : (n : ℂ) ^ (⟨c, t⟩ : ℂ) ≠ 0 := fun h ↦
        hnC ((Complex.cpow_eq_zero_iff _ _).mp h).1
      have h3 := hz t
      rw [LSeries.term_of_ne_zero hn, LSeries.term_of_ne_zero hn, Complex.cpow_add _ _ hnC,
        hdiv]
      field_simp
  have hsum : HasSum (fun n : ℕ ↦ ∫ t in -T..T,
        LSeries.term a s n * (((x / n : ℝ) : ℂ) ^ (⟨c, t⟩ : ℂ) / (⟨c, t⟩ : ℂ)))
      (∫ t in -T..T, LSeries a (s + ⟨c, t⟩) * (x : ℂ) ^ (⟨c, t⟩ : ℂ) / (⟨c, t⟩ : ℂ)) := by
    refine intervalIntegral.hasSum_integral_of_dominated_convergence
      (fun n _ ↦ x ^ c * ‖LSeries.term a (s + (c : ℂ)) n‖ / c) (fun n ↦ ?_) (fun n ↦ ?_)
      ?_ ?_ ?_
    · exact (continuous_const.mul
        ((hmk.const_cpow (Or.inr hz)).div hmk hz)).aestronglyMeasurable
    · refine Eventually.of_forall fun t _ ↦ ?_
      rcases eq_or_ne n 0 with rfl | hn
      · simp
      · have hn0 : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
        have hnorm : c ≤ ‖(⟨c, t⟩ : ℂ)‖ := by
          have h := Complex.abs_re_le_norm (⟨c, t⟩ : ℂ)
          rwa [show (⟨c, t⟩ : ℂ).re = c from rfl, abs_of_pos hc] at h
        rw [norm_mul, norm_div, Complex.norm_cpow_eq_rpow_re_of_pos (div_pos hx hn0),
          show (⟨c, t⟩ : ℂ).re = c from rfl, ← truncatedPerron_error_norm_term a s hx n,
          mul_div_assoc]
        exact mul_le_mul_of_nonneg_left
          (div_le_div_of_nonneg_left (Real.rpow_pos_of_pos (div_pos hx hn0) c).le hc hnorm)
          (norm_nonneg _)
    · exact Eventually.of_forall fun t _ ↦ (ha.norm.mul_left (x ^ c)).div_const c
    · exact intervalIntegrable_const
    · refine Eventually.of_forall fun t _ ↦ ?_
      have hre : (s + (c : ℂ)).re = (s + ⟨c, t⟩).re := by simp
      have hs' : LSeriesSummable a (s + ⟨c, t⟩) := (LSeriesSummable_iff_of_re_eq_re hre).mp ha
      have h0 : HasSum (LSeries.term a (s + ⟨c, t⟩)) (LSeries a (s + ⟨c, t⟩)) :=
        hs'.LSeriesHasSum
      have h := (h0.mul_right ((x : ℂ) ^ (⟨c, t⟩ : ℂ))).div_const (⟨c, t⟩ : ℂ)
      simpa only [hF] using h
  have h2 := hsum.div_const (2 * (Real.pi : ℂ))
  have h3 : (fun n : ℕ ↦ LSeries.term a s n *
      ((∫ t in -T..T, ((x / n : ℝ) : ℂ) ^ (⟨c, t⟩ : ℂ) / (⟨c, t⟩ : ℂ)) /
        (2 * (Real.pi : ℂ)))) = fun n : ℕ ↦ (∫ t in -T..T,
        LSeries.term a s n * (((x / n : ℝ) : ℂ) ^ (⟨c, t⟩ : ℂ) / (⟨c, t⟩ : ℂ))) /
        (2 * (Real.pi : ℂ)) := funext fun n ↦ by
    rw [intervalIntegral.integral_const_mul, mul_div_assoc]
  rw [h3]
  exact h2

/-- The half-weighted cutoff sum as a series with Perron's limiting weights. -/
private theorem truncatedPerron_error_hasSum_weights (a : ℕ → ℂ) (s : ℂ) {x : ℝ}
    (hx : 0 < x) :
    HasSum (fun n : ℕ ↦ LSeries.term a s n *
        (if 1 < x / n then (1 : ℂ) else if x / n = 1 then 1 / 2 else 0))
      (perronHalfWeightedSum a s x) := by
  have key : ∀ n : ℕ, n ∉ Finset.Icc 1 ⌊x⌋₊ → LSeries.term a s n *
      (if 1 < x / n then (1 : ℂ) else if x / n = 1 then 1 / 2 else 0) = 0 := by
    intro n hn
    rcases eq_or_ne n 0 with rfl | hn0
    · simp
    · have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn0
      have hlt : ⌊x⌋₊ < n := by
        by_contra h
        exact hn (Finset.mem_Icc.mpr ⟨hn1, not_lt.mp h⟩)
      have hxn : x < n := (Nat.floor_lt hx.le).mp hlt
      have hnpos : (0 : ℝ) < n := by exact_mod_cast hn1
      have h1 : x / n < 1 := (div_lt_one hnpos).mpr hxn
      rw [ite_eq_right (not_lt.mpr h1.le), ite_eq_right h1.ne, mul_zero]
  have hval : perronHalfWeightedSum a s x = ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, LSeries.term a s n *
      (if 1 < x / n then (1 : ℂ) else if x / n = 1 then 1 / 2 else 0) := by
    change (∑ n ∈ Finset.Icc 1 ⌊x⌋₊,
      if (n : ℝ) = x then LSeries.term a s n / 2 else LSeries.term a s n) = _
    refine Finset.sum_congr rfl fun n hn ↦ ?_
    obtain ⟨hn1, hn2⟩ := Finset.mem_Icc.mp hn
    have hnpos : (0 : ℝ) < n := by exact_mod_cast hn1
    have hle : (n : ℝ) ≤ x := (Nat.cast_le.mpr hn2).trans (Nat.floor_le hx.le)
    by_cases hnx : (n : ℝ) = x
    · have h1 : x / n = 1 := by
        rw [← hnx]
        exact div_self hnpos.ne'
      rw [ite_eq_left hnx, ite_eq_right (by rw [h1]; exact lt_irrefl _), ite_eq_left h1]
      ring
    · have hlt : (n : ℝ) < x := lt_of_le_of_ne hle hnx
      rw [ite_eq_right hnx, ite_eq_left ((one_lt_div hnpos).mpr hlt), mul_one]
  rw [hval]
  exact hasSum_sum_of_ne_finset_zero key

/-- The error series is summable: far from the cutoff the logarithm is at least one. -/
private theorem truncatedPerron_error_summable (a : ℕ → ℂ) (s : ℂ) {x c : ℝ} (hx : 0 < x)
    (ha : LSeriesSummable a (s + (c : ℂ))) :
    Summable fun n : ℕ ↦ if n = 0 ∨ (n : ℝ) = x then 0
      else ‖LSeries.term a (s + (c : ℂ)) n‖ / |Real.log (x / n)| := by
  refine Summable.of_norm_bounded_eventually_nat ha.norm ?_
  filter_upwards [eventually_gt_atTop ⌈Real.exp 1 * x⌉₊] with n hn
  have hn' : Real.exp 1 * x < n := Nat.lt_of_ceil_lt hn
  have hnpos : (0 : ℝ) < n := (mul_pos (Real.exp_pos 1) hx).trans hn'
  have hlog : Real.log (x / n) ≤ -1 := by
    rw [Real.log_le_iff_le_exp (div_pos hx hnpos), div_le_iff₀ hnpos, Real.exp_neg,
      ← div_eq_inv_mul, le_div_iff₀ (Real.exp_pos 1)]
    linarith
  have habs : 1 ≤ |Real.log (x / n)| := by
    rw [abs_of_neg (by linarith)]
    linarith
  split_ifs
  · simp
  · rw [Real.norm_of_nonneg (div_nonneg (norm_nonneg _) (abs_nonneg _))]
    exact div_le_self (norm_nonneg _) habs

/-- Paper: Equations (B.7.1.6)–(B.7.1.7), pp. 644–645. The truncated Perron
error is bounded by a sum weighted by the inverse logarithmic distance from
the cutoff. An exact endpoint contributes the separate arctangent error.
Deviation: This includes both endpoint cases and assumes absolute convergence
at the specific line of integration, which suffices for this bound. -/
theorem truncatedPerron_error (a : ℕ → ℂ) (s : ℂ) {x c T : ℝ}
    (hx : 0 < x) (hc : 0 < c) (hT : 1 ≤ T) (ha : LSeriesSummable a (s + (c : ℂ))) :
    ‖perronHalfWeightedSum a s x - truncatedPerronIntegral (LSeries a) s x c T‖ ≤
      x ^ c / (Real.pi * T) *
        (∑' n : ℕ, if n = 0 ∨ (n : ℝ) = x then 0
          else ‖LSeries.term a (s + (c : ℂ)) n‖ / |Real.log (x / n)|) +
      (if (⌊x⌋₊ : ℝ) = x then
        c * ‖LSeries.term a s ⌊x⌋₊‖ / (Real.pi * T) else 0) := by
  have hT0 : 0 < T := zero_lt_one.trans_le hT
  have hπT : 0 < Real.pi * T := mul_pos Real.pi_pos hT0
  have hD := (truncatedPerron_error_hasSum_weights a s hx).sub
    (truncatedPerron_error_hasSum a s (T := T) hx hc ha)
  have he : HasSum (fun n : ℕ ↦ if (n : ℝ) = x then
      c * ‖LSeries.term a s n‖ / (Real.pi * T) else 0)
      (if (⌊x⌋₊ : ℝ) = x then c * ‖LSeries.term a s ⌊x⌋₊‖ / (Real.pi * T) else 0) := by
    refine hasSum_single ⌊x⌋₊ fun n hn ↦ ite_eq_right fun h ↦ hn ?_
    rw [← h, Nat.floor_natCast]
  have hg := ((truncatedPerron_error_summable a s hx ha).hasSum.mul_left
    (x ^ c / (Real.pi * T))).add he
  refine hD.norm_le_of_bounded hg fun n ↦ ?_
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  · have hnpos : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
    have hk := truncatedPerron_error_kernel (div_pos hx hnpos) hc hT0
    rw [← mul_sub, norm_mul]
    by_cases hnx : (n : ℝ) = x
    · have h1 : x / n = 1 := by
        rw [← hnx]
        exact div_self hnpos.ne'
      have hk' := hk.trans_eq (ite_eq_left h1)
      rw [ite_eq_left (Or.inr hnx), mul_zero, zero_add, ite_eq_left hnx]
      calc ‖LSeries.term a s n‖ * _ ≤ ‖LSeries.term a s n‖ * (c / (Real.pi * T)) :=
            mul_le_mul_of_nonneg_left hk' (norm_nonneg _)
        _ = c * ‖LSeries.term a s n‖ / (Real.pi * T) := by ring
    · have h1 : x / n ≠ 1 := fun h ↦ hnx ((div_eq_one_iff_eq hnpos.ne').mp h).symm
      have hk' := hk.trans_eq (ite_eq_right h1)
      rw [ite_eq_right (not_or.mpr ⟨hn, hnx⟩), ite_eq_right hnx, add_zero]
      calc ‖LSeries.term a s n‖ * _
          ≤ ‖LSeries.term a s n‖ *
            ((x / n) ^ c / (Real.pi * T * |Real.log (x / n)|)) :=
            mul_le_mul_of_nonneg_left hk' (norm_nonneg _)
        _ = ‖LSeries.term a s n‖ * (x / n) ^ c / (Real.pi * T * |Real.log (x / n)|) := by
            ring
        _ = x ^ c / (Real.pi * T) *
            (‖LSeries.term a (s + (c : ℂ)) n‖ / |Real.log (x / n)|) := by
            rw [truncatedPerron_error_norm_term a s hx n]
            ring

/-- A big-O bound along the natural numbers by a positive majorant holds at every index. -/
private theorem truncatedPerron_error_noninteger_coeff (a : ℕ → ℂ) (ψ : ℕ → ℝ)
    (hψ : ∀ n, 0 < ψ n) (hcoeff : a =O[atTop] ψ) :
    ∃ C : ℝ, 0 < C ∧ ∀ n, ‖a n‖ ≤ C * ψ n := by
  obtain ⟨C, hC⟩ :=
    (Asymptotics.isBigO_nat_atTop_iff fun n h ↦ absurd h (hψ n).ne').mp hcoeff
  refine ⟨max C 1, lt_max_of_lt_right one_pos, fun n ↦ (hC n).trans ?_⟩
  rw [Real.norm_of_nonneg (hψ n).le]
  exact mul_le_mul_of_nonneg_right (le_max_left _ _) (hψ n).le

/-- The absolute series is `O((σ - 1)^(-α))` on the whole interval `(1, 2]`. -/
private theorem truncatedPerron_error_noninteger_abs (a : ℕ → ℂ) (α : ℝ) (hα : 0 < α)
    (ha : ∀ s : ℂ, 1 < s.re → LSeriesSummable a s)
    (habs : (fun σ : ℝ ↦ ∑' n : ℕ, ‖LSeries.term a (σ : ℂ) n‖) =O[𝓝[>] 1]
      (fun σ : ℝ ↦ ((σ - 1) ^ α)⁻¹)) :
    ∃ C : ℝ, 0 < C ∧ ∀ σ : ℝ, σ ∈ Ioc 1 2 →
      ∑' n : ℕ, ‖LSeries.term a (σ : ℂ) n‖ ≤ C / (σ - 1) ^ α := by
  obtain ⟨c, hc⟩ := habs.bound
  obtain ⟨u, hu1, hu⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp hc
  have hu1' : (1 : ℝ) < u := hu1
  have hσ₁ : (1 : ℝ) < (1 + u) / 2 := by linarith
  have hA0 : ∀ σ : ℝ, 0 ≤ ∑' n : ℕ, ‖LSeries.term a (σ : ℂ) n‖ := fun σ ↦
    tsum_nonneg fun n ↦ norm_nonneg _
  refine ⟨max c 0 + (∑' n : ℕ, ‖LSeries.term a (((1 + u) / 2 : ℝ) : ℂ) n‖) + 1,
    by linarith [le_max_right c 0, hA0 ((1 + u) / 2)], fun σ hσ ↦ ?_⟩
  have hpos : 0 < (σ - 1) ^ α := Real.rpow_pos_of_pos (by linarith [hσ.1]) α
  have hle1 : (σ - 1) ^ α ≤ 1 :=
    Real.rpow_le_one (by linarith [hσ.1]) (by linarith [hσ.2]) hα.le
  have hinv : 1 ≤ ((σ - 1) ^ α)⁻¹ := (one_le_inv₀ hpos).mpr hle1
  rw [div_eq_mul_inv]
  by_cases hσu : σ < u
  · have h := hu ⟨hσ.1, hσu⟩
    change ‖∑' n : ℕ, ‖LSeries.term a (σ : ℂ) n‖‖ ≤ c * ‖((σ - 1) ^ α)⁻¹‖ at h
    rw [Real.norm_of_nonneg (hA0 σ), Real.norm_of_nonneg (inv_nonneg.mpr hpos.le)] at h
    refine h.trans (mul_le_mul_of_nonneg_right ?_ (inv_nonneg.mpr hpos.le))
    linarith [le_max_left c 0, hA0 ((1 + u) / 2)]
  · have hle : ((1 + u) / 2 : ℝ) ≤ σ := by linarith [not_lt.mp hσu]
    have hmono : ∑' n : ℕ, ‖LSeries.term a (σ : ℂ) n‖ ≤
        ∑' n : ℕ, ‖LSeries.term a (((1 + u) / 2 : ℝ) : ℂ) n‖ :=
      Summable.tsum_le_tsum
        (fun n ↦ LSeries.norm_term_le_of_re_le_re a
          (by rw [Complex.ofReal_re, Complex.ofReal_re]; exact hle) n)
        (ha _ (by rw [Complex.ofReal_re]; exact hσ.1)).norm
        (ha _ (by rw [Complex.ofReal_re]; exact hσ₁)).norm
    have h0 := hA0 ((1 + u) / 2)
    have hC : 0 ≤ max c 0 + (∑' n : ℕ, ‖LSeries.term a (((1 + u) / 2 : ℝ) : ℂ) n‖) + 1 := by
      linarith [le_max_right c 0]
    calc ∑' n : ℕ, ‖LSeries.term a (σ : ℂ) n‖
        ≤ (max c 0 + (∑' n : ℕ, ‖LSeries.term a (((1 + u) / 2 : ℝ) : ℂ) n‖) + 1) * 1 := by
          linarith [le_max_right c 0]
      _ ≤ _ := mul_le_mul_of_nonneg_left hinv hC

/-- The harmonic sum below `m` is at most `2 log m`. -/
private theorem truncatedPerron_error_noninteger_harmonic (m : ℕ) :
    ∑ k ∈ Finset.Ico 1 m, (1 : ℝ) / k ≤ 2 * Real.log m := by
  rcases Nat.eq_zero_or_pos m with rfl | hm0
  · simp
  have hm : 1 ≤ m := hm0
  clear hm0
  induction m, hm using Nat.le_induction with
  | base => simp
  | succ m hm ih =>
    rw [Finset.sum_Ico_succ_top hm]
    have hm0 : (0 : ℝ) < m := Nat.cast_pos.mpr hm
    have hm1 : (1 : ℝ) ≤ m := Nat.one_le_cast.mpr hm
    have h1 : Real.log ((m : ℝ) / (m + 1)) ≤ (m : ℝ) / (m + 1) - 1 :=
      Real.log_le_sub_one_of_pos (by positivity)
    rw [Real.log_div hm0.ne' (by positivity)] at h1
    have h2 : (m : ℝ) / (m + 1) - 1 = -(1 / (m + 1)) := by
      field_simp
      ring
    have h3 : (1 : ℝ) / (2 * m) ≤ 1 / (m + 1) :=
      one_div_le_one_div_of_le (by positivity) (by linarith)
    have h4 : (1 : ℝ) / (2 * m) = 1 / m / 2 := by
      field_simp
    push_cast
    linarith

/-- Reciprocal distances to `N` on either side of `N` are dominated by harmonic sums. -/
private theorem truncatedPerron_error_noninteger_near (N K : ℕ) (B : ℝ) (hB : 0 ≤ B) :
    ∃ S : ℝ, S ≤ B * (2 * Real.log N + 2 * Real.log K) ∧
      HasSum (fun n : ℕ ↦ (if n ∈ Finset.Ico 1 N then B / ((N - n : ℕ) : ℝ) else 0) +
        (if n ∈ Finset.Ico (1 + N) (K + N) then B / ((n - N : ℕ) : ℝ) else 0)) S := by
  have hsum : ∀ m : ℕ, ∑ k ∈ Finset.Ico 1 m, B / (k : ℝ) ≤ B * (2 * Real.log m) := by
    intro m
    have e : ∑ k ∈ Finset.Ico 1 m, B / (k : ℝ) = B * ∑ k ∈ Finset.Ico 1 m, (1 : ℝ) / k := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun k _ ↦ by rw [mul_one_div]
    rw [e]
    exact mul_le_mul_of_nonneg_left (truncatedPerron_error_noninteger_harmonic m) hB
  have h1 : HasSum (fun n : ℕ ↦ if n ∈ Finset.Ico 1 N then B / ((N - n : ℕ) : ℝ) else 0)
      (∑ k ∈ Finset.Ico 1 N, B / (k : ℝ)) := by
    have e : ∑ k ∈ Finset.Ico 1 N, B / (k : ℝ) = ∑ n ∈ Finset.Ico 1 N,
        (if n ∈ Finset.Ico 1 N then B / ((N - n : ℕ) : ℝ) else 0) := by
      have r := Finset.sum_Ico_reflect (fun j : ℕ ↦ B / (j : ℝ)) 1 (Nat.le_succ N)
      simp only [Nat.add_sub_cancel_left, Nat.add_sub_cancel] at r
      rw [← r]
      exact Finset.sum_congr rfl fun n hn ↦ (ite_eq_left hn).symm
    rw [e]
    exact hasSum_sum_of_ne_finset_zero fun n hn ↦ ite_eq_right hn
  have h2 : HasSum
      (fun n : ℕ ↦ if n ∈ Finset.Ico (1 + N) (K + N) then B / ((n - N : ℕ) : ℝ) else 0)
      (∑ k ∈ Finset.Ico 1 K, B / (k : ℝ)) := by
    have e : ∑ k ∈ Finset.Ico 1 K, B / (k : ℝ) = ∑ n ∈ Finset.Ico (1 + N) (K + N),
        (if n ∈ Finset.Ico (1 + N) (K + N) then B / ((n - N : ℕ) : ℝ) else 0) := by
      have r := Finset.sum_Ico_add' (fun n : ℕ ↦ B / ((n - N : ℕ) : ℝ)) 1 K N
      simp only [Nat.add_sub_cancel] at r
      rw [r]
      exact Finset.sum_congr rfl fun n hn ↦ (ite_eq_left hn).symm
    rw [e]
    exact hasSum_sum_of_ne_finset_zero fun n hn ↦ ite_eq_right hn
  exact ⟨_, by linarith [hsum N, hsum K], h1.add h2⟩

/-- Away from the cutoff by a factor of two the logarithmic distance is at least `log 2`. -/
private theorem truncatedPerron_error_noninteger_far {x y : ℝ} (hx : 0 < x) (hy : 0 < y)
    (h : 2 * y ≤ x ∨ 2 * x ≤ y) : Real.log 2 ≤ |Real.log (x / y)| := by
  rcases h with h | h
  · exact (Real.log_le_log two_pos ((le_div_iff₀ hy).mpr h)).trans (le_abs_self _)
  · have h1 : Real.log 2 ≤ Real.log (y / x) := Real.log_le_log two_pos ((le_div_iff₀ hx).mpr h)
    have h2 : Real.log (x / y) = -Real.log (y / x) := by
      rw [← Real.log_inv, inv_div]
    rw [h2, abs_neg]
    exact h1.trans (le_abs_self _)

/-- Within a factor of two of the cutoff the logarithmic distance dominates the distance. -/
private theorem truncatedPerron_error_noninteger_log {x y : ℝ} (hx : 0 < x) (hy : 0 < y)
    (h : y < 2 * x) : |x - y| / (2 * x) ≤ |Real.log (x / y)| := by
  rcases le_total y x with hyx | hxy
  · have h1 : 1 - (x / y)⁻¹ ≤ Real.log (x / y) := Real.one_sub_inv_le_log_of_pos (div_pos hx hy)
    rw [inv_div] at h1
    have h2 : 0 ≤ Real.log (x / y) := Real.log_nonneg ((one_le_div hy).mpr hyx)
    rw [abs_of_nonneg (sub_nonneg.mpr hyx), abs_of_nonneg h2]
    have h3 : (x - y) / (2 * x) ≤ 1 - y / x := by
      rw [div_le_iff₀ (by positivity)]
      have e : (1 - y / x) * (2 * x) = 2 * (x - y) := by
        field_simp
      rw [e]
      linarith
    exact h3.trans h1
  · have h1 : 1 - (y / x)⁻¹ ≤ Real.log (y / x) := Real.one_sub_inv_le_log_of_pos (div_pos hy hx)
    rw [inv_div] at h1
    have h2 : Real.log (x / y) = -Real.log (y / x) := by
      rw [← Real.log_inv, inv_div]
    have h3 : 0 ≤ Real.log (y / x) := Real.log_nonneg ((one_le_div hx).mpr hxy)
    rw [h2, abs_neg, abs_of_nonneg h3, abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr hxy)]
    have h4 : (y - x) / (2 * x) ≤ 1 - x / y := by
      rw [div_le_iff₀ (by positivity)]
      have e : (1 - x / y) * (2 * x) = (y - x) * (2 * x / y) := by
        field_simp
      rw [e]
      have h5 : 1 ≤ 2 * x / y := (one_le_div hy).mpr h.le
      nlinarith [sub_nonneg.mpr hxy]
    exact h4.trans h1

/-- The scalar inequality that assembles the bound at a noninteger cutoff. -/
private theorem truncatedPerron_error_noninteger_scalar
    {C₁ C₂ P Q D L L₂ T p ψ₁ ψ₂ X d ρ W E : ℝ}
    (hC₁ : 0 < C₁) (hC₂ : 0 < C₂) (hP : 0 < P) (hQ : 0 < Q) (hD : 0 < D) (hL : 0 ≤ L)
    (hL₂ : 0 < L₂) (hT : 0 < T) (hp : 0 < p) (hψ₁ : 0 < ψ₁) (hψ₂ : 0 < ψ₂) (hX : 0 < X)
    (hd : 0 < d) (hρ : 0 < ρ)
    (hW : ψ₂ * W ≤ 10 * ψ₂ * L + 8 * ρ * (ψ₁ / d))
    (hE : E ≤ C₂ / D / L₂ + (4 * (C₁ * ψ₁) / Q * (2 * X) / d +
      4 * (C₁ * ψ₂) / Q * (2 * X) * 2 * W)) :
    P / (p * T) * E + 0 ≤
      (C₂ / (p * L₂) + 160 * (C₁ / p) + (8 + 128 * ρ) * (C₁ / p)) *
        (P / (T * D) + ψ₂ * (X * P / Q) * L / T + ψ₁ * (X * P / Q) / (T * d)) := by
  have h1 : P / (p * T) * E ≤ P / (p * T) * (C₂ / D / L₂ +
      (4 * (C₁ * ψ₁) / Q * (2 * X) / d + 4 * (C₁ * ψ₂) / Q * (2 * X) * 2 * W)) :=
    mul_le_mul_of_nonneg_left hE (by positivity)
  have e1 : P / (p * T) * (C₂ / D / L₂ +
      (4 * (C₁ * ψ₁) / Q * (2 * X) / d + 4 * (C₁ * ψ₂) / Q * (2 * X) * 2 * W)) =
      C₂ / (p * L₂) * (P / (T * D)) + 8 * (C₁ / p) * (ψ₁ * (X * P / Q) / (T * d)) +
        16 * (C₁ / p) * (X * P / Q / T) * (ψ₂ * W) := by
    field_simp
    ring
  have h2 : 16 * (C₁ / p) * (X * P / Q / T) * (ψ₂ * W) ≤
      16 * (C₁ / p) * (X * P / Q / T) * (10 * ψ₂ * L + 8 * ρ * (ψ₁ / d)) :=
    mul_le_mul_of_nonneg_left hW (by positivity)
  have e2 : 16 * (C₁ / p) * (X * P / Q / T) * (10 * ψ₂ * L + 8 * ρ * (ψ₁ / d)) =
      160 * (C₁ / p) * (ψ₂ * (X * P / Q) * L / T) +
        128 * ρ * (C₁ / p) * (ψ₁ * (X * P / Q) / (T * d)) := by
    field_simp
    ring
  have hU : 0 ≤ P / (T * D) := by positivity
  have hV : 0 ≤ ψ₂ * (X * P / Q) * L / T := by positivity
  have hZ : 0 ≤ ψ₁ * (X * P / Q) / (T * d) := by positivity
  have hA : 0 ≤ C₂ / (p * L₂) := by positivity
  have hB : 0 ≤ C₁ / p := by positivity
  have key : ∀ A B U V Z r : ℝ, 0 ≤ A → 0 ≤ B → 0 ≤ U → 0 ≤ V → 0 ≤ Z → 0 ≤ r →
      A * U + 8 * B * Z + (160 * B * V + 128 * r * B * Z) ≤
        (A + 160 * B + (8 + 128 * r) * B) * (U + V + Z) := by
    intro A B U V Z r hA hB hU hV hZ hr
    nlinarith [mul_nonneg hA hV, mul_nonneg hA hZ, mul_nonneg hB hU, mul_nonneg hB hZ,
      mul_nonneg hB hV, mul_nonneg (mul_nonneg hr hB) hU, mul_nonneg (mul_nonneg hr hB) hV]
  have h3 := key _ _ _ _ _ _ hA hB hU hV hZ hρ.le
  rw [e1] at h1
  rw [e2] at h2
  linarith

/-- The harmonic weights at a noninteger cutoff are absorbed by the logarithm of the cutoff
when it is at least two, and by the term of the nearest integer otherwise. -/
private theorem truncatedPerron_error_noninteger_weight (ψ : ℕ → ℝ) (hψ : ∀ n, 0 < ψ n)
    (hmono : Monotone ψ) {x : ℝ} (hx : 0 < x) (N : ℕ) (hd : 0 < |x - (N : ℝ)|)
    (hN : |x - (N : ℝ)| ≤ 1 / 2) :
    ψ ⌊2 * x⌋₊ * (2 * Real.log N + 2 * Real.log (⌊2 * x⌋₊ + 1 : ℕ)) ≤
      10 * ψ ⌊2 * x⌋₊ * |Real.log x| + 8 * (ψ 3 / ψ 0) * (ψ N / |x - (N : ℝ)|) := by
  have hψ₂ : 0 < ψ ⌊2 * x⌋₊ := hψ _
  have hψN : 0 < ψ N := hψ _
  have hρ : 0 < ψ 3 / ψ 0 := div_pos (hψ 3) (hψ 0)
  have hNle : (N : ℝ) ≤ x + 1 / 2 := by linarith [(abs_le.mp hN).1]
  have hKle : ((⌊2 * x⌋₊ + 1 : ℕ) : ℝ) ≤ 2 * x + 1 := by
    push_cast
    linarith [Nat.floor_le (by positivity : (0 : ℝ) ≤ 2 * x)]
  have hr0 : 0 ≤ 8 * (ψ 3 / ψ 0) * (ψ N / |x - (N : ℝ)|) := by positivity
  have hl0 : 0 ≤ 10 * ψ ⌊2 * x⌋₊ * |Real.log x| := by positivity
  rcases le_or_gt 2 x with hx2 | hx2
  · have hlx : 0 ≤ Real.log x := Real.log_nonneg (by linarith)
    have h2x : 2 * x ≤ x * x := mul_le_mul_of_nonneg_right hx2 hx.le
    have h3x : 2 * x * x ≤ x * x * x := mul_le_mul_of_nonneg_right h2x hx.le
    have h1 : Real.log N ≤ 2 * Real.log x := by
      rcases Nat.eq_zero_or_pos N with rfl | hNpos
      · rw [Nat.cast_zero, Real.log_zero]
        linarith
      · have h5 : (N : ℝ) ≤ x ^ 2 := by
          rw [sq]
          linarith
        have h6 := Real.log_le_log (Nat.cast_pos.mpr hNpos) h5
        rwa [Real.log_pow, Nat.cast_ofNat] at h6
    have h2 : Real.log (⌊2 * x⌋₊ + 1 : ℕ) ≤ 3 * Real.log x := by
      have h5 : ((⌊2 * x⌋₊ + 1 : ℕ) : ℝ) ≤ x ^ 3 := by
        have h7 : x ^ 3 = x * x * x := by ring
        rw [h7]
        linarith
      have h6 := Real.log_le_log (Nat.cast_pos.mpr (Nat.succ_pos _)) h5
      rwa [Real.log_pow, Nat.cast_ofNat] at h6
    rw [abs_of_nonneg hlx]
    have h3 : ψ ⌊2 * x⌋₊ * (2 * Real.log N + 2 * Real.log (⌊2 * x⌋₊ + 1 : ℕ)) ≤
        ψ ⌊2 * x⌋₊ * (10 * Real.log x) :=
      mul_le_mul_of_nonneg_left (by linarith) hψ₂.le
    linarith
  · have h1 : Real.log N ≤ 5 / 2 :=
      (Real.log_le_self (Nat.cast_nonneg N)).trans (by linarith)
    have h2 : Real.log (⌊2 * x⌋₊ + 1 : ℕ) ≤ 5 :=
      (Real.log_le_self (Nat.cast_nonneg _)).trans (by linarith)
    have hfl : ⌊2 * x⌋₊ ≤ 3 := by
      have h5 : ⌊2 * x⌋₊ < 4 := (Nat.floor_lt (by positivity)).mpr (by push_cast; linarith)
      omega
    have h3 : ψ ⌊2 * x⌋₊ * 15 ≤ ψ 3 / ψ 0 * ψ N * 15 := by
      have h5 : ψ 3 = ψ 3 / ψ 0 * ψ 0 := (div_mul_cancel₀ (ψ 3) (hψ 0).ne').symm
      have h6 : ψ ⌊2 * x⌋₊ ≤ ψ 3 / ψ 0 * ψ N := by
        calc ψ ⌊2 * x⌋₊ ≤ ψ 3 := hmono hfl
          _ = ψ 3 / ψ 0 * ψ 0 := h5
          _ ≤ ψ 3 / ψ 0 * ψ N := mul_le_mul_of_nonneg_left (hmono (Nat.zero_le N)) hρ.le
      linarith
    have h4 : ψ ⌊2 * x⌋₊ * (2 * Real.log N + 2 * Real.log (⌊2 * x⌋₊ + 1 : ℕ)) ≤
        ψ ⌊2 * x⌋₊ * 15 := mul_le_mul_of_nonneg_left (by linarith) hψ₂.le
    have hd2 : 2 * ψ N ≤ ψ N / |x - (N : ℝ)| := by
      rw [le_div_iff₀ hd]
      have h7 : ψ N * |x - (N : ℝ)| ≤ ψ N * (1 / 2) := mul_le_mul_of_nonneg_left hN hψN.le
      linarith
    have h5 : ψ 3 / ψ 0 * (2 * ψ N) ≤ ψ 3 / ψ 0 * (ψ N / |x - (N : ℝ)|) :=
      mul_le_mul_of_nonneg_left hd2 hρ.le
    linarith

/-- The pointwise comparison of the error series with a far part, the term of the nearest
integer and reciprocal distances to it. -/
private theorem truncatedPerron_error_noninteger_pointwise (a : ℕ → ℂ) (ψ : ℕ → ℝ)
    (hψ : ∀ n, 0 < ψ n) (hmono : Monotone ψ) {C₁ : ℝ} (hC₁ : 0 < C₁)
    (hcoef : ∀ n, ‖a n‖ ≤ C₁ * ψ n) (s : ℂ) {x c : ℝ} (N : ℕ) (hx : 0 < x)
    (hσ : s.re + c ∈ Ioc 1 2) (hN : |x - (N : ℝ)| ≤ 1 / 2) (n : ℕ) :
    (if n = 0 ∨ (n : ℝ) = x then 0
        else ‖LSeries.term a (s + (c : ℂ)) n‖ / |Real.log (x / n)|) ≤
      ‖LSeries.term a (s + (c : ℂ)) n‖ / Real.log 2 +
        ((if n = N then 4 * (C₁ * ψ N) / x ^ (s.re + c) * (2 * x) / |x - (N : ℝ)| else 0) +
          ((if n ∈ Finset.Ico 1 N then
              4 * (C₁ * ψ ⌊2 * x⌋₊) / x ^ (s.re + c) * (2 * x) * 2 / ((N - n : ℕ) : ℝ)
            else 0) +
            (if n ∈ Finset.Ico (1 + N) (⌊2 * x⌋₊ + 1 + N) then
              4 * (C₁ * ψ ⌊2 * x⌋₊) / x ^ (s.re + c) * (2 * x) * 2 / ((n - N : ℕ) : ℝ)
            else 0))) := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hσre : (s + (c : ℂ)).re = s.re + c := by
    rw [Complex.add_re, Complex.ofReal_re]
  have hψ₂ : 0 < ψ ⌊2 * x⌋₊ := hψ _
  have hψN : 0 < ψ N := hψ _
  have hQ : 0 < x ^ (s.re + c) := Real.rpow_pos_of_pos hx _
  have hK0 : 0 ≤ 4 * (C₁ * ψ ⌊2 * x⌋₊) / x ^ (s.re + c) * (2 * x) := by positivity
  have hB0 : 0 ≤ 4 * (C₁ * ψ ⌊2 * x⌋₊) / x ^ (s.re + c) * (2 * x) * 2 := by positivity
  have hBN : 0 ≤ 4 * (C₁ * ψ N) / x ^ (s.re + c) * (2 * x) / |x - (N : ℝ)| := by positivity
  have ht : 0 ≤ ‖LSeries.term a (s + (c : ℂ)) n‖ := norm_nonneg _
  have hgn : 0 ≤ ‖LSeries.term a (s + (c : ℂ)) n‖ / Real.log 2 := div_nonneg ht hlog2.le
  have h0n : 0 ≤ (if n = N then
      4 * (C₁ * ψ N) / x ^ (s.re + c) * (2 * x) / |x - (N : ℝ)| else 0) := by
    split_ifs
    · exact hBN
    · exact le_rfl
  have h1n : 0 ≤ (if n ∈ Finset.Ico 1 N then
      4 * (C₁ * ψ ⌊2 * x⌋₊) / x ^ (s.re + c) * (2 * x) * 2 / ((N - n : ℕ) : ℝ) else 0) := by
    split_ifs
    · exact div_nonneg hB0 (Nat.cast_nonneg _)
    · exact le_rfl
  have h2n : 0 ≤ (if n ∈ Finset.Ico (1 + N) (⌊2 * x⌋₊ + 1 + N) then
      4 * (C₁ * ψ ⌊2 * x⌋₊) / x ^ (s.re + c) * (2 * x) * 2 / ((n - N : ℕ) : ℝ) else 0) := by
    split_ifs
    · exact div_nonneg hB0 (Nat.cast_nonneg _)
    · exact le_rfl
  by_cases h0 : n = 0 ∨ (n : ℝ) = x
  · rw [ite_eq_left h0]
    linarith
  rw [ite_eq_right h0]
  obtain ⟨hn0, hnx⟩ := not_or.mp h0
  have hnpos : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn0)
  by_cases hfar : 2 * (n : ℝ) ≤ x ∨ 2 * x ≤ n
  · have hl : Real.log 2 ≤ |Real.log (x / n)| :=
      truncatedPerron_error_noninteger_far hx hnpos hfar
    have hle : ‖LSeries.term a (s + (c : ℂ)) n‖ / |Real.log (x / n)| ≤
        ‖LSeries.term a (s + (c : ℂ)) n‖ / Real.log 2 :=
      div_le_div_of_nonneg_left ht hlog2 hl
    linarith
  · obtain ⟨hl1, hl2⟩ := not_or.mp hfar
    have hn2 : (n : ℝ) < 2 * x := not_le.mp hl2
    have hx2 : x < 2 * n := not_le.mp hl1
    have hlogb := truncatedPerron_error_noninteger_log hx hnpos hn2
    have hdist : 0 < |x - n| := abs_pos.mpr (sub_ne_zero.mpr (Ne.symm hnx))
    have h4 : x ^ (s.re + c) / 4 ≤ (n : ℝ) ^ (s.re + c) := by
      have h1 : (x / 2) ^ (s.re + c) ≤ (n : ℝ) ^ (s.re + c) :=
        Real.rpow_le_rpow (by positivity) (by linarith) (by linarith [hσ.1])
      have h2 : (2 : ℝ) ^ (s.re + c) ≤ 4 := by
        calc (2 : ℝ) ^ (s.re + c) ≤ (2 : ℝ) ^ (2 : ℝ) :=
              Real.rpow_le_rpow_of_exponent_le one_le_two hσ.2
          _ = 4 := by
              rw [Real.rpow_two]
              norm_num
      rw [Real.div_rpow hx.le zero_le_two] at h1
      have h3 : 0 < (2 : ℝ) ^ (s.re + c) := by positivity
      exact (div_le_div_of_nonneg_left hQ.le h3 h2).trans h1
    have hterm_le : ∀ ψ' : ℝ, ψ n ≤ ψ' →
        ‖LSeries.term a (s + (c : ℂ)) n‖ / |Real.log (x / n)| ≤
          4 * (C₁ * ψ') / x ^ (s.re + c) * (2 * x) / |x - n| := by
      intro ψ' hψ'
      have han : ‖a n‖ ≤ C₁ * ψ' :=
        (hcoef n).trans (mul_le_mul_of_nonneg_left hψ' hC₁.le)
      have hψ'0 : 0 ≤ C₁ * ψ' := (norm_nonneg _).trans han
      have htK : ‖LSeries.term a (s + (c : ℂ)) n‖ ≤ 4 * (C₁ * ψ') / x ^ (s.re + c) := by
        rw [LSeries.norm_term_eq, ite_eq_right hn0, hσre]
        calc ‖a n‖ / (n : ℝ) ^ (s.re + c)
            ≤ C₁ * ψ' / (x ^ (s.re + c) / 4) := div_le_div₀ hψ'0 han (by positivity) h4
          _ = 4 * (C₁ * ψ') / x ^ (s.re + c) := by
              field_simp
      calc ‖LSeries.term a (s + (c : ℂ)) n‖ / |Real.log (x / n)|
          ≤ 4 * (C₁ * ψ') / x ^ (s.re + c) / (|x - n| / (2 * x)) :=
            div_le_div₀ (by positivity) htK (by positivity) hlogb
        _ = _ := by
            field_simp
    by_cases hnN : n = N
    · have h1 := hterm_le (ψ N) (by rw [hnN])
      have e : |x - (n : ℝ)| = |x - (N : ℝ)| := by rw [hnN]
      rw [e] at h1
      rw [ite_eq_left hnN]
      linarith
    · have hfl : n ≤ ⌊2 * x⌋₊ := Nat.le_floor hn2.le
      have h1 := hterm_le (ψ ⌊2 * x⌋₊) (hmono hfl)
      have hNn : (1 : ℝ) ≤ |(n : ℝ) - N| := by
        have h5 : (1 : ℤ) ≤ |(n : ℤ) - N| :=
          Int.one_le_abs (sub_ne_zero.mpr (by exact_mod_cast hnN))
        exact_mod_cast h5
      have hxn : |(n : ℝ) - N| / 2 ≤ |x - n| := by
        have h3 : |(n : ℝ) - N| ≤ |x - N| + |x - n| := by
          have h5 : (n : ℝ) - N = (x - N) - (x - n) := by ring
          rw [h5]
          exact abs_sub _ _
        linarith
      have h2 : 4 * (C₁ * ψ ⌊2 * x⌋₊) / x ^ (s.re + c) * (2 * x) / |x - n| ≤
          4 * (C₁ * ψ ⌊2 * x⌋₊) / x ^ (s.re + c) * (2 * x) * 2 / |(n : ℝ) - N| := by
        calc 4 * (C₁ * ψ ⌊2 * x⌋₊) / x ^ (s.re + c) * (2 * x) / |x - n|
            ≤ 4 * (C₁ * ψ ⌊2 * x⌋₊) / x ^ (s.re + c) * (2 * x) / (|(n : ℝ) - N| / 2) :=
              div_le_div_of_nonneg_left hK0 (by positivity) hxn
          _ = _ := by
              field_simp
      rcases lt_or_gt_of_ne hnN with hlt | hgt
      · have hmem : n ∈ Finset.Ico 1 N :=
          Finset.mem_Ico.mpr ⟨Nat.one_le_iff_ne_zero.mpr hn0, hlt⟩
        rw [ite_eq_left hmem]
        have e : ((N - n : ℕ) : ℝ) = |(n : ℝ) - N| := by
          rw [Nat.cast_sub hlt.le, abs_sub_comm,
            abs_of_pos (sub_pos.mpr (Nat.cast_lt.mpr hlt))]
        rw [e]
        linarith
      · have hmem : n ∈ Finset.Ico (1 + N) (⌊2 * x⌋₊ + 1 + N) :=
          Finset.mem_Ico.mpr ⟨by omega, by omega⟩
        rw [ite_eq_left hmem]
        have e : ((n - N : ℕ) : ℝ) = |(n : ℝ) - N| := by
          rw [Nat.cast_sub hgt.le, abs_of_pos (sub_pos.mpr (Nat.cast_lt.mpr hgt))]
        rw [e]
        linarith

/-- Paper: Lemma B.7.1.1, Equation (B.7.1.4), p. 644.
The truncated Perron error at a noninteger cutoff has a far contribution,
a near contribution and a contribution from a nearest integer.
Deviation: The simplified estimate is uniform for `1 < s.re + c ≤ 2`.
Its constant may depend on the coefficient sequence and majorant.
The imaginary part of `s` is independent of the integration height.
The expression `ψ(2x)` is evaluated at the natural floor of `2x`. -/
theorem truncatedPerron_error_noninteger (a : ℕ → ℂ) (ψ : ℕ → ℝ)
    (hψ : ∀ n, 0 < ψ n) (hmono : Monotone ψ) (α : ℝ) (hα : 0 < α)
    (ha : ∀ s : ℂ, 1 < s.re → LSeriesSummable a s)
    (hcoeff : a =O[atTop] ψ)
    (habs : (fun σ : ℝ ↦ ∑' n : ℕ, ‖LSeries.term a (σ : ℂ) n‖) =O[𝓝[>] 1]
      (fun σ : ℝ ↦ ((σ - 1) ^ α)⁻¹)) :
    ∃ C : ℝ, 0 < C ∧ ∀ (s : ℂ) (x c T : ℝ) (N : ℕ),
      0 < x → 0 < c → 1 ≤ T → s.re + c ∈ Ioc 1 2 →
      x ∉ Set.range (Int.cast : ℤ → ℝ) → |x - (N : ℝ)| ≤ 1 / 2 →
      ‖perronHalfWeightedSum a s x - truncatedPerronIntegral (LSeries a) s x c T‖ ≤
        C * (x ^ c / (T * (s.re + c - 1) ^ α) +
          ψ ⌊2 * x⌋₊ * x ^ (1 - s.re) * |Real.log x| / T +
          ψ N * x ^ (1 - s.re) / (T * |x - (N : ℝ)|)) := by
  obtain ⟨C₁, hC₁, hcoef⟩ := truncatedPerron_error_noninteger_coeff a ψ hψ hcoeff
  obtain ⟨C₂, hC₂, hA⟩ := truncatedPerron_error_noninteger_abs a α hα ha habs
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hρ : 0 < ψ 3 / ψ 0 := div_pos (hψ 3) (hψ 0)
  refine ⟨C₂ / (Real.pi * Real.log 2) + 160 * (C₁ / Real.pi) +
    (8 + 128 * (ψ 3 / ψ 0)) * (C₁ / Real.pi), by positivity, ?_⟩
  intro s x c T N hx hc hT hσ hxint hN
  have hT0 : 0 < T := zero_lt_one.trans_le hT
  have hσre : (s + (c : ℂ)).re = s.re + c := by
    rw [Complex.add_re, Complex.ofReal_re]
  have hsum : LSeriesSummable a (s + (c : ℂ)) := ha _ (by rw [hσre]; exact hσ.1)
  have hQ : 0 < x ^ (s.re + c) := Real.rpow_pos_of_pos hx _
  have hD : 0 < (s.re + c - 1) ^ α := Real.rpow_pos_of_pos (by linarith [hσ.1]) α
  have hxN : x ≠ (N : ℝ) := fun h ↦ hxint ⟨(N : ℤ), by rw [Int.cast_natCast, h]⟩
  have hd : 0 < |x - (N : ℝ)| := abs_pos.mpr (sub_ne_zero.mpr hxN)
  have h := truncatedPerron_error a s hx hc hT hsum
  rw [ite_eq_right (fun h' ↦ hxint ⟨(⌊x⌋₊ : ℤ), by rw [Int.cast_natCast]; exact h'⟩)] at h
  refine h.trans ?_
  have hB0 : 0 ≤ 4 * (C₁ * ψ ⌊2 * x⌋₊) / x ^ (s.re + c) * (2 * x) * 2 := by
    have hψ₂ : 0 < ψ ⌊2 * x⌋₊ := hψ _
    positivity
  obtain ⟨S, hS, hSsum⟩ := truncatedPerron_error_noninteger_near N (⌊2 * x⌋₊ + 1)
    (4 * (C₁ * ψ ⌊2 * x⌋₊) / x ^ (s.re + c) * (2 * x) * 2) hB0
  have hg := hsum.norm.hasSum.div_const (Real.log 2)
  have hf := (truncatedPerron_error_summable a s hx hsum).hasSum
  have hNsum := hasSum_ite_eq N (4 * (C₁ * ψ N) / x ^ (s.re + c) * (2 * x) / |x - (N : ℝ)|)
  have hE := hasSum_le
    (truncatedPerron_error_noninteger_pointwise a ψ hψ hmono hC₁ hcoef s N hx hσ hN)
    hf (hg.add (hNsum.add hSsum))
  have hterm : ∀ n, ‖LSeries.term a (s + (c : ℂ)) n‖ =
      ‖LSeries.term a ((s.re + c : ℝ) : ℂ) n‖ := fun n ↦ by
    rw [LSeries.norm_term_eq, LSeries.norm_term_eq, Complex.ofReal_re, hσre]
  have hA' := hA (s.re + c) hσ
  rw [← tsum_congr hterm] at hA'
  have hE' : (∑' n : ℕ, if n = 0 ∨ (n : ℝ) = x then 0
      else ‖LSeries.term a (s + (c : ℂ)) n‖ / |Real.log (x / n)|) ≤
      C₂ / (s.re + c - 1) ^ α / Real.log 2 +
        (4 * (C₁ * ψ N) / x ^ (s.re + c) * (2 * x) / |x - (N : ℝ)| +
          4 * (C₁ * ψ ⌊2 * x⌋₊) / x ^ (s.re + c) * (2 * x) * 2 *
            (2 * Real.log N + 2 * Real.log (⌊2 * x⌋₊ + 1 : ℕ))) := by
    have h5 := div_le_div_of_nonneg_right hA' hlog2.le
    linarith only [h5, hE, hS]
  have e1 : x ^ (1 - s.re) = x * x ^ c / x ^ (s.re + c) := by
    rw [show 1 - s.re = 1 + c - (s.re + c) by ring, Real.rpow_sub hx, Real.rpow_add hx,
      Real.rpow_one]
  rw [e1]
  exact truncatedPerron_error_noninteger_scalar hC₁ hC₂ (Real.rpow_pos_of_pos hx c) hQ hD
    (abs_nonneg _) hlog2 hT0 Real.pi_pos (hψ N) (hψ _) hx hd hρ
    (truncatedPerron_error_noninteger_weight ψ hψ hmono hx N hd hN) hE'

/-- The scalar inequality that assembles the bound at an integer cutoff. -/
private theorem truncatedPerron_error_integer_scalar {C₁ C₂ P Q R D L L₂ T c p ψ₁ ψ₂ M E t : ℝ}
    (hC₁ : 0 < C₁) (hC₂ : 0 < C₂) (hP : 0 < P) (hQ : 0 < Q) (hR : 0 < R) (hD : 0 < D)
    (hL : 0 ≤ L) (hL₂ : 0 < L₂) (hT : 0 < T) (hc : 0 < c) (hp : 0 < p) (hψ₁ : 0 < ψ₁)
    (hψ₂ : 0 < ψ₂) (hM : 0 < M)
    (hE : E ≤ C₂ / D / L₂ + 4 * (C₁ * ψ₂) / Q * (2 * M) * (4 * L))
    (ht : t ≤ C₁ * ψ₁ / R) :
    P / (p * T) * E + c * t / (p * T) ≤
      (C₂ / (p * L₂) + 32 * C₁ / p) *
        (P / (T * D) + ψ₂ * (M * P / Q) * L / T + ψ₁ * c * R⁻¹ / T) := by
  have h1 : P / (p * T) * E ≤
      P / (p * T) * (C₂ / D / L₂ + 4 * (C₁ * ψ₂) / Q * (2 * M) * (4 * L)) :=
    mul_le_mul_of_nonneg_left hE (by positivity)
  have h2 : c * t / (p * T) ≤ c * (C₁ * ψ₁ / R) / (p * T) :=
    div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left ht hc.le) (by positivity)
  have e1 : P / (p * T) * (C₂ / D / L₂ + 4 * (C₁ * ψ₂) / Q * (2 * M) * (4 * L)) =
      C₂ / (p * L₂) * (P / (T * D)) + 32 * C₁ / p * (ψ₂ * (M * P / Q) * L / T) := by
    field_simp
    ring
  have e2 : c * (C₁ * ψ₁ / R) / (p * T) = C₁ / p * (ψ₁ * c * R⁻¹ / T) := by
    field_simp
  have hX : 0 ≤ P / (T * D) := by positivity
  have hY : 0 ≤ ψ₂ * (M * P / Q) * L / T := by positivity
  have hZ : 0 ≤ ψ₁ * c * R⁻¹ / T := by positivity
  have hA : 0 ≤ C₂ / (p * L₂) := by positivity
  have hB : 0 ≤ C₁ / p := by positivity
  have e3 : 32 * C₁ / p = 32 * (C₁ / p) := by ring
  rw [e3]
  rw [e1, e3] at h1
  rw [e2] at h2
  nlinarith [mul_nonneg hA hY, mul_nonneg hA hZ, mul_nonneg hB hX, mul_nonneg hB hZ,
    mul_nonneg hB hY]

/-- Paper: Lemma B.7.1.1, Equation (B.7.1.5), p. 644. The truncated
Perron error at an integer cutoff includes the half-weight endpoint error.
Deviation: The simplified estimate is uniform for `1 < s.re + c ≤ 2`.
Its constant may depend on the coefficient
sequence and majorant. The imaginary part of `s` is independent of the
integration height. -/
theorem truncatedPerron_error_integer (a : ℕ → ℂ) (ψ : ℕ → ℝ)
    (hψ : ∀ n, 0 < ψ n) (hmono : Monotone ψ) (α : ℝ) (hα : 0 < α)
    (ha : ∀ s : ℂ, 1 < s.re → LSeriesSummable a s)
    (hcoeff : a =O[atTop] ψ)
    (habs : (fun σ : ℝ ↦ ∑' n : ℕ, ‖LSeries.term a (σ : ℂ) n‖) =O[𝓝[>] 1]
      (fun σ : ℝ ↦ ((σ - 1) ^ α)⁻¹)) :
    ∃ C : ℝ, 0 < C ∧ ∀ (s : ℂ) (m : ℕ) (c T : ℝ),
      0 < m → 0 < c → 1 ≤ T → s.re + c ∈ Ioc 1 2 →
      ‖perronHalfWeightedSum a s m - truncatedPerronIntegral (LSeries a) s m c T‖ ≤
        C * ((m : ℝ) ^ c / (T * (s.re + c - 1) ^ α) +
          ψ (2 * m) * (m : ℝ) ^ (1 - s.re) * Real.log m / T +
          ψ m * c * (m : ℝ) ^ (-s.re) / T) := by
  obtain ⟨C₁, hC₁, hcoef⟩ := truncatedPerron_error_noninteger_coeff a ψ hψ hcoeff
  obtain ⟨C₂, hC₂, hA⟩ := truncatedPerron_error_noninteger_abs a α hα ha habs
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  refine ⟨C₂ / (Real.pi * Real.log 2) + 32 * C₁ / Real.pi, by positivity, ?_⟩
  intro s m c T hm hc hT hσ
  have hm0 : (0 : ℝ) < m := Nat.cast_pos.mpr hm
  have hT0 : 0 < T := zero_lt_one.trans_le hT
  have hσre : (s + (c : ℂ)).re = s.re + c := by
    rw [Complex.add_re, Complex.ofReal_re]
  have hsum : LSeriesSummable a (s + (c : ℂ)) := ha _ (by rw [hσre]; exact hσ.1)
  have hψ₂ : 0 < ψ (2 * m) := hψ _
  have hQ : 0 < (m : ℝ) ^ (s.re + c) := Real.rpow_pos_of_pos hm0 _
  have hD : 0 < (s.re + c - 1) ^ α := Real.rpow_pos_of_pos (by linarith [hσ.1]) α
  have h := truncatedPerron_error a s hm0 hc hT hsum
  rw [Nat.floor_natCast, ite_eq_left rfl] at h
  refine h.trans ?_
  -- the error series
  have hK0 : 0 ≤ 4 * (C₁ * ψ (2 * m)) / (m : ℝ) ^ (s.re + c) := by positivity
  have hB0 : 0 ≤ 4 * (C₁ * ψ (2 * m)) / (m : ℝ) ^ (s.re + c) * (2 * m) := by positivity
  obtain ⟨S, hS0, hSsum⟩ := truncatedPerron_error_noninteger_near m m
    (4 * (C₁ * ψ (2 * m)) / (m : ℝ) ^ (s.re + c) * (2 * m)) hB0
  have hS : S ≤ 4 * (C₁ * ψ (2 * m)) / (m : ℝ) ^ (s.re + c) * (2 * m) * (4 * Real.log m) :=
    hS0.trans_eq (by ring)
  have hg := hsum.norm.hasSum.div_const (Real.log 2)
  have hf := (truncatedPerron_error_summable a s hm0 hsum).hasSum
  have hE := hasSum_le (fun n ↦ ?_) hf (hg.add hSsum)
  · have hterm : ∀ n, ‖LSeries.term a (s + (c : ℂ)) n‖ =
        ‖LSeries.term a ((s.re + c : ℝ) : ℂ) n‖ := fun n ↦ by
      rw [LSeries.norm_term_eq, LSeries.norm_term_eq, Complex.ofReal_re, hσre]
    have hA' := hA (s.re + c) hσ
    rw [← tsum_congr hterm] at hA'
    have hE' : (∑' n : ℕ, if n = 0 ∨ (n : ℝ) = (m : ℝ) then 0
        else ‖LSeries.term a (s + (c : ℂ)) n‖ / |Real.log ((m : ℝ) / n)|) ≤
        C₂ / (s.re + c - 1) ^ α / Real.log 2 +
          4 * (C₁ * ψ (2 * m)) / (m : ℝ) ^ (s.re + c) * (2 * m) * (4 * Real.log m) := by
      have := div_le_div_of_nonneg_right hA' hlog2.le
      linarith
    have ht : ‖LSeries.term a s m‖ ≤ C₁ * ψ m / (m : ℝ) ^ s.re := by
      rw [LSeries.norm_term_eq, ite_eq_right hm.ne']
      exact div_le_div_of_nonneg_right (hcoef m) (Real.rpow_pos_of_pos hm0 _).le
    have e1 : (m : ℝ) ^ (1 - s.re) = (m : ℝ) * (m : ℝ) ^ c / (m : ℝ) ^ (s.re + c) := by
      rw [show 1 - s.re = 1 + c - (s.re + c) by ring, Real.rpow_sub hm0, Real.rpow_add hm0,
        Real.rpow_one]
    have e2 : (m : ℝ) ^ (-s.re) = ((m : ℝ) ^ s.re)⁻¹ := Real.rpow_neg hm0.le _
    rw [e1, e2]
    exact truncatedPerron_error_integer_scalar hC₁ hC₂ (Real.rpow_pos_of_pos hm0 c) hQ
      (Real.rpow_pos_of_pos hm0 s.re) hD (Real.log_natCast_nonneg m) hlog2 hT0 hc Real.pi_pos
      (hψ m) hψ₂ hm0 hE' ht
  · -- the pointwise comparison
    have ht : 0 ≤ ‖LSeries.term a (s + (c : ℂ)) n‖ := norm_nonneg _
    have hgn : 0 ≤ ‖LSeries.term a (s + (c : ℂ)) n‖ / Real.log 2 := div_nonneg ht hlog2.le
    have h1n : 0 ≤ (if n ∈ Finset.Ico 1 m then
        4 * (C₁ * ψ (2 * m)) / (m : ℝ) ^ (s.re + c) * (2 * m) / ((m - n : ℕ) : ℝ) else 0) := by
      split_ifs
      · exact div_nonneg hB0 (Nat.cast_nonneg _)
      · exact le_rfl
    have h2n : 0 ≤ (if n ∈ Finset.Ico (1 + m) (m + m) then
        4 * (C₁ * ψ (2 * m)) / (m : ℝ) ^ (s.re + c) * (2 * m) / ((n - m : ℕ) : ℝ) else 0) := by
      split_ifs
      · exact div_nonneg hB0 (Nat.cast_nonneg _)
      · exact le_rfl
    by_cases h0 : n = 0 ∨ (n : ℝ) = (m : ℝ)
    · rw [ite_eq_left h0]
      linarith
    rw [ite_eq_right h0]
    obtain ⟨hn0, hnm⟩ := not_or.mp h0
    have hnm' : n ≠ m := fun h ↦ hnm (by rw [h])
    have hnpos : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn0)
    by_cases hfar : 2 * n ≤ m ∨ 2 * m ≤ n
    · have hl : Real.log 2 ≤ |Real.log ((m : ℝ) / n)| :=
        truncatedPerron_error_noninteger_far hm0 hnpos (by exact_mod_cast hfar)
      have hle : ‖LSeries.term a (s + (c : ℂ)) n‖ / |Real.log ((m : ℝ) / n)| ≤
          ‖LSeries.term a (s + (c : ℂ)) n‖ / Real.log 2 :=
        div_le_div_of_nonneg_left ht hlog2 hl
      linarith
    · obtain ⟨hl1, hl2⟩ := not_or.mp hfar
      have hn2 : (n : ℝ) < 2 * m := by exact_mod_cast not_le.mp hl2
      have hm2 : (m : ℝ) < 2 * n := by exact_mod_cast not_le.mp hl1
      have hlogb := truncatedPerron_error_noninteger_log hm0 hnpos hn2
      have hdist : 0 < |(m : ℝ) - n| := abs_pos.mpr (sub_ne_zero.mpr (Ne.symm hnm))
      have h4 : (m : ℝ) ^ (s.re + c) / 4 ≤ (n : ℝ) ^ (s.re + c) := by
        have h1 : ((m : ℝ) / 2) ^ (s.re + c) ≤ (n : ℝ) ^ (s.re + c) :=
          Real.rpow_le_rpow (by positivity) (by linarith) (by linarith [hσ.1])
        have h2 : (2 : ℝ) ^ (s.re + c) ≤ 4 := by
          calc (2 : ℝ) ^ (s.re + c) ≤ (2 : ℝ) ^ (2 : ℝ) :=
                Real.rpow_le_rpow_of_exponent_le one_le_two hσ.2
            _ = 4 := by
                rw [Real.rpow_two]
                norm_num
        rw [Real.div_rpow hm0.le zero_le_two] at h1
        have h3 : 0 < (2 : ℝ) ^ (s.re + c) := by positivity
        exact (div_le_div_of_nonneg_left hQ.le h3 h2).trans h1
      have htK : ‖LSeries.term a (s + (c : ℂ)) n‖ ≤
          4 * (C₁ * ψ (2 * m)) / (m : ℝ) ^ (s.re + c) := by
        rw [LSeries.norm_term_eq, ite_eq_right hn0, hσre]
        have han : ‖a n‖ ≤ C₁ * ψ (2 * m) :=
          (hcoef n).trans (mul_le_mul_of_nonneg_left (hmono (by omega)) hC₁.le)
        calc ‖a n‖ / (n : ℝ) ^ (s.re + c)
            ≤ C₁ * ψ (2 * m) / ((m : ℝ) ^ (s.re + c) / 4) :=
              div_le_div₀ (mul_pos hC₁ hψ₂).le han (by positivity) h4
          _ = 4 * (C₁ * ψ (2 * m)) / (m : ℝ) ^ (s.re + c) := by
              field_simp
      have hmain : ‖LSeries.term a (s + (c : ℂ)) n‖ / |Real.log ((m : ℝ) / n)| ≤
          4 * (C₁ * ψ (2 * m)) / (m : ℝ) ^ (s.re + c) * (2 * m) / |(m : ℝ) - n| := by
        calc ‖LSeries.term a (s + (c : ℂ)) n‖ / |Real.log ((m : ℝ) / n)|
            ≤ 4 * (C₁ * ψ (2 * m)) / (m : ℝ) ^ (s.re + c) / (|(m : ℝ) - n| / (2 * m)) :=
              div_le_div₀ hK0 htK (by positivity) hlogb
          _ = _ := by
              field_simp
      rcases lt_or_gt_of_ne hnm' with hlt | hgt
      · rw [ite_eq_left (Finset.mem_Ico.mpr ⟨Nat.one_le_iff_ne_zero.mpr hn0, hlt⟩)]
        have e : ((m - n : ℕ) : ℝ) = |(m : ℝ) - n| := by
          rw [Nat.cast_sub hlt.le, abs_of_pos (sub_pos.mpr (Nat.cast_lt.mpr hlt))]
        rw [e]
        linarith
      · have hmem : n ∈ Finset.Ico (1 + m) (m + m) := Finset.mem_Ico.mpr ⟨by omega, by omega⟩
        rw [ite_eq_left hmem]
        have e : ((n - m : ℕ) : ℝ) = |(m : ℝ) - n| := by
          rw [Nat.cast_sub hgt.le, abs_sub_comm, abs_of_pos (sub_pos.mpr (Nat.cast_lt.mpr hgt))]
        rw [e]
        linarith

/-- Paper: Equation (B.7.1.8), p. 645, and the coefficient choice on p. 646.
The cutoff polynomial sums the twisted von Mangoldt coefficients, grouped by
the norm of the ideal, through the last integer norm at most `x`. -/
def heckeLogDerivPolynomial (χ : U[F]) (x : ℝ) (s : ℂ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, LSeries.term (heckeLogDerivCoefficient (ideleClassNormTwist χ 0)) s n

/-- Paper: Equation (B.7.1.8), p. 645. The polynomial grouped by norm equals
the sum over all nonzero integral ideals whose norms are at most the cutoff. -/
theorem heckeLogDerivPolynomial_eq_sum_ideals (χ : U[F]) (x : ℝ) (s : ℂ) :
    heckeLogDerivPolynomial χ x s =
      ∑ᶠ I : {I : Ideal (𝓞 F) // I ≠ ⊥ ∧ (I.absNorm : ℝ) ≤ x},
        heckeIdealVonMangoldt (ideleClassNormTwist χ 0) I.val / (I.val.absNorm : ℂ) ^ s := by
  classical
  let g : Ideal (𝓞 F) → ℂ := fun I ↦
    heckeIdealVonMangoldt (ideleClassNormTwist χ 0) I / (I.absNorm : ℂ) ^ s
  have hfin : {I : Ideal (𝓞 F) | I ≠ ⊥ ∧ (I.absNorm : ℝ) ≤ x}.Finite :=
    (Ring.HasFiniteQuotients.finite_absNorm_le (S := 𝓞 F) ⌊x⌋₊).subset
      fun I hI ↦ Nat.le_floor hI.2
  let T := hfin.toFinset
  have hfib (n : ℕ) (hn : n ∈ Finset.Icc 1 ⌊x⌋₊) :
      LSeries.term (heckeLogDerivCoefficient (ideleClassNormTwist χ 0)) s n =
        ∑ I ∈ T with I.absNorm = n, g I := by
    have hn0 : n ≠ 0 := Nat.one_le_iff_ne_zero.mp (Finset.mem_Icc.mp hn).1
    have hset : {I : Ideal (𝓞 F) | I ≠ ⊥ ∧ I.absNorm = n} =
        ↑(T.filter fun I ↦ I.absNorm = n) := by
      ext I
      simp only [Set.mem_ofPred_eq, Finset.coe_filter, T, Set.Finite.mem_toFinset]
      constructor
      · rintro ⟨h0, h1⟩
        refine ⟨⟨h0, ?_⟩, h1⟩
        rw [h1]
        exact (Nat.le_floor_iff' hn0).mp (Finset.mem_Icc.mp hn).2
      · rintro ⟨⟨h0, -⟩, h1⟩
        exact ⟨h0, h1⟩
    rw [LSeries.term_of_ne_zero hn0, heckeLogDerivCoefficient]
    change (∑ᶠ I : ↥{I : Ideal (𝓞 F) | I ≠ ⊥ ∧ I.absNorm = n},
      heckeIdealVonMangoldt (ideleClassNormTwist χ 0) I) / (n : ℂ) ^ s = _
    rw [hset, finsum_set_coe_eq_finsum_mem, finsum_mem_coe_finset, Finset.sum_div]
    refine Finset.sum_congr rfl fun I hI ↦ ?_
    change _ = heckeIdealVonMangoldt (ideleClassNormTwist χ 0) I / (I.absNorm : ℂ) ^ s
    rw [(Finset.mem_filter.mp hI).2]
  change ∑ n ∈ Finset.Icc 1 ⌊x⌋₊,
      LSeries.term (heckeLogDerivCoefficient (ideleClassNormTwist χ 0)) s n =
    ∑ᶠ I : ↥{I : Ideal (𝓞 F) | I ≠ ⊥ ∧ (I.absNorm : ℝ) ≤ x}, g I
  rw [finsum_set_coe_eq_finsum_mem, finsum_mem_eq_finite_toFinset_sum _ hfin,
    Finset.sum_congr rfl hfib]
  refine Finset.sum_fiberwise_of_maps_to (fun I hI ↦ ?_) _
  simp only [T, Set.Finite.mem_toFinset, Set.mem_ofPred_eq] at hI
  exact Finset.mem_Icc.mpr
    ⟨Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hI.1), Nat.le_floor hI.2⟩

/-- Paper: Theorem B.7.1.2(1), p. 645. The set `J_b` consists of the integer
cuts and the real cuts at distance at least `b` from the integers. -/
def perronCutoffSet (b : ℝ) : Set ℝ :=
  Set.range (Int.cast : ℤ → ℝ) ∪ {x : ℝ | b ≤ |x - (round x : ℝ)|}

/-- Paper: Theorem B.7.1.2(1), p. 645. For positive `b`, integer cuts are always
allowed and half-integer cuts are allowed precisely when `b ≤ 1/2`. -/
theorem perronCutoffSet_integer_half_integer {b : ℝ} (hb : 0 < b) (n : ℤ) :
    (n : ℝ) ∈ perronCutoffSet b ∧
      ((n : ℝ) + 1 / 2 ∈ perronCutoffSet b ↔ b ≤ 1 / 2) := by
  refine ⟨Or.inl ⟨n, rfl⟩, ?_⟩
  have hround : round ((n : ℝ) + 1 / 2) = n + 1 := by
    rw [round_eq, add_assoc, add_halves, Int.floor_intCast_add, Int.floor_one]
  have hnot : (n : ℝ) + 1 / 2 ∉ Set.range (Int.cast : ℤ → ℝ) := by
    rintro ⟨k, hk⟩
    have h : ((2 * (k - n) : ℤ) : ℝ) = 1 := by push_cast; linarith
    have h' : 2 * (k - n) = 1 := by exact_mod_cast h
    omega
  have habs : |(n : ℝ) + 1 / 2 - (round ((n : ℝ) + 1 / 2) : ℝ)| = 1 / 2 := by
    rw [hround, Int.cast_add, Int.cast_one, show (n : ℝ) + 1 / 2 - (n + 1) = -(1 / 2) by ring,
      abs_neg, abs_of_pos one_half_pos]
  change (n : ℝ) + 1 / 2 ∈ Set.range (Int.cast : ℤ → ℝ) ∨
    b ≤ |(n : ℝ) + 1 / 2 - (round ((n : ℝ) + 1 / 2) : ℝ)| ↔ _
  rw [habs]
  exact ⟨fun h ↦ h.resolve_left hnot, Or.inr⟩

/-- The twisted von Mangoldt weight of an ideal is bounded by the plain weight. -/
private theorem heckeLDP_weight_le (χ : U[F]) (I : Ideal (𝓞 F)) :
    ‖heckeIdealVonMangoldt (ideleClassNormTwist χ 0) I‖ ≤ idealVonMangoldt I := by
  classical
  have hΛ : 0 ≤ idealVonMangoldt I := by
    unfold idealVonMangoldt
    split_ifs
    · exact Real.log_natCast_nonneg _
    · exact le_rfl
  have hval : ‖heckeIdealValue (ideleClassNormTwist χ 0) I‖ ≤ 1 := by
    unfold heckeIdealValue
    split_ifs
    · simp
    · refine finprod_induction (fun z : ℂ ↦ ‖z‖ ≤ 1) (by simp)
        (fun x y hx hy ↦ (norm_mul_le x y).trans (by nlinarith [norm_nonneg x, norm_nonneg y]))
        fun v ↦ ?_
      rw [norm_pow]
      refine pow_le_one₀ (norm_nonneg _) ?_
      split_ifs
      · exact (norm_ideleClassNormTwist_zero_localValue χ v).le
      · simp
  rw [heckeIdealVonMangoldt, norm_mul, Complex.norm_real, Real.norm_of_nonneg hΛ]
  exact mul_le_of_le_one_left hΛ hval

/-- The trivial character twisted by exponent zero takes value one on every nonzero ideal. -/
private theorem heckeLDP_value_one {I : Ideal (𝓞 F)} (hI : I ≠ ⊥) :
    heckeIdealValue (ideleClassNormTwist (1 : U[F]) 0) I = 1 := by
  classical
  have hone : ∀ g : IdeleClassGroup (𝓞 F) F, ideleClassNormTwist (1 : U[F]) 0 g = 1 := by
    intro g
    change (1 : ℂ) * (((ideleClassNorm F g : NNReal) : ℝ) : ℂ) ^ (0 : ℂ) = 1
    simp
  have hres : ∀ v : HeightOneSpectrum (𝓞 F), ∀ x : v.adicCompletion F, x ≠ 0 →
      (ideleClassNormTwist (1 : U[F]) 0).restrict v x = 1 := fun v x hx ↦ by
    have hu : IsUnit x := isUnit_iff_ne_zero.mpr hx
    rw [← hu.unit_spec, HeckeCharacter.restrict_apply]
    simp [hone, hx]
  have hun : ∀ v : HeightOneSpectrum (𝓞 F),
      (ideleClassNormTwist (1 : U[F]) 0).IsUnramifiedAt v := fun v ↦
    HeckeCharacter.isUnramifiedAt_iff.mpr fun x ↦ hres v _ (by simp)
  have hloc : ∀ v : HeightOneSpectrum (𝓞 F),
      (ideleClassNormTwist (1 : U[F]) 0).localValue v = 1 := fun v ↦ by
    rw [HeckeCharacter.localValue]
    apply hres
    exact (Valued.v.exists_isUniformizer_of_isCyclic_of_nontrivial).choose_spec.ne_zero
  unfold heckeIdealValue
  rw [ite_eq_right hI]
  exact finprod_eq_one_of_forall_eq_one fun v ↦ by simp [hun v, hloc v]

/-- On the half-plane of absolute convergence, the norm-grouped twisted von Mangoldt
series sums to the negative logarithmic derivative of any matching continuation. -/
private theorem heckeLDP_hasSum (χ : U[F]) (L : ℂ → ℂ) (hL : MeromorphicNFOn L univ)
    (hSeries : ∀ s : halfPlane, L s = finiteHeckeL χ s) (s : halfPlane) :
    LSeriesHasSum (heckeLogDerivCoefficient (ideleClassNormTwist χ 0)) (s : ℂ)
      (-logDeriv L s) := by
  classical
  have hI : HasSum (fun I : {I : Ideal (𝓞 F) // I ≠ ⊥} ↦
      heckeIdealVonMangoldt (ideleClassNormTwist χ 0) I.val / (I.val.absNorm : ℂ) ^ (s : ℂ))
      (-logDeriv L s) := by
    have := (finiteHeckeL_logDeriv_hasSum_ideals χ L hL hSeries s).2.2.neg
    convert this using 1
    funext I
    ring
  let normIndex (I : {I : Ideal (𝓞 F) // I ≠ ⊥}) : ℕ := I.val.absNorm
  have hfib := hI.tsum_fiberwise normIndex
  refine hfib.congr_fun fun n ↦ ?_
  by_cases hn0 : n = 0
  · subst hn0
    haveI : IsEmpty (normIndex ⁻¹' ({0} : Set ℕ)) :=
      ⟨fun I ↦ I.val.property (Ideal.absNorm_eq_zero_iff.mp I.property)⟩
    rw [LSeries.term_zero]
    exact hasSum_empty.tsum_eq.symm
  · rw [LSeries.term_of_ne_zero hn0]
    symm
    let normFiber : Set (Ideal (𝓞 F)) := {I | I ≠ ⊥ ∧ I.absNorm = n}
    let e : (normIndex ⁻¹' ({n} : Set ℕ) : Set {I : Ideal (𝓞 F) // I ≠ ⊥}) ≃ normFiber :=
      { toFun := fun I ↦ ⟨I.val.val, I.val.property, I.property⟩
        invFun := fun I ↦ ⟨⟨I.val, I.property.1⟩, I.property.2⟩
        left_inv := fun _ ↦ rfl
        right_inv := fun _ ↦ rfl }
    have hnorm (I : normFiber) : I.val.absNorm = n := I.property.2
    have hfin : Finite normFiber :=
      ((Ring.HasFiniteQuotients.finite_absNorm_eq n).subset
        (show normFiber ⊆ {I | I.absNorm = n} from fun I hI ↦ hI.2)).to_subtype
    rw [← e.symm.tsum_eq]
    change (∑' I : normFiber,
      heckeIdealVonMangoldt (ideleClassNormTwist χ 0) I.val / (I.val.absNorm : ℂ) ^ (s : ℂ)) =
      heckeLogDerivCoefficient (ideleClassNormTwist χ 0) n / (n : ℂ) ^ (s : ℂ)
    simp_rw [hnorm, tsum_div_const, tsum_eq_finsum (Set.toFinite _)]
    rfl

/-- On the half-plane of absolute convergence the finite L-function of the trivial
character is the Dedekind zeta function. -/
private theorem heckeLDP_zeta_eq (s : halfPlane) :
    finiteHeckeL (1 : U[F]) s = dedekindZeta F s := by
  have h := completedHeckeL_one_eq_dedekindZeta (F := F) s
  rw [← heckeGammaFactor_one] at h
  change heckeGammaFactor (1 : U[F]) s * finiteHeckeL (1 : U[F]) s = _ at h
  have hs : 0 < (s : ℂ).re := zero_lt_one.trans s.property
  exact mul_left_cancel₀ (heckeGammaFactor_ne_zero_of_re_pos (1 : U[F]) hs) h

/-- The finite Euler factor of a pure imaginary norm twist is the trivial-character
factor at the shifted point. -/
private theorem heckeLDP_eulerFactor_shift (χ : U[F]) (t₀ : ℝ)
    (hχ : ideleClassNormTwist χ 0 = ideleClassNormTwist (1 : U[F]) (-Complex.I * t₀))
    (v : HeightOneSpectrum (𝓞 F)) (s : ℂ) :
    finiteHeckeEulerFactor χ v s =
      finiteHeckeEulerFactor (1 : U[F]) v (s - Complex.I * t₀) := by
  classical
  set a : ℂ := -Complex.I * t₀ with ha
  have hval (z : ℂ) (u : (v.adicCompletion F)ˣ) :
      (ideleClassNormTwist (1 : U[F]) z).restrict v u =
        (‖(u : v.adicCompletion F)‖ : ℂ) ^ z := by
    rw [HeckeCharacter.restrict, MulChar.ofUnitHom_coe]
    change 1 * (((ideleClassNorm F (IdeleClassGroup.ofAdicCompletion (𝓞 F) F v u) : NNReal) : ℝ) : ℂ) ^ z = _
    rw [one_mul, ideleClassNorm_ofAdicCompletion]
    rfl
  have hu (z : ℂ) : (ideleClassNormTwist (1 : U[F]) z).IsUnramifiedAt v := by
    apply HeckeCharacter.isUnramifiedAt_iff.mpr
    intro x
    let u := Units.map (v.adicCompletionIntegers F).subtype.toMonoidHom x
    change (ideleClassNormTwist (1 : U[F]) z).restrict v u = 1
    rw [hval z u, show ‖(u : v.adicCompletion F)‖ = 1 from ?_, Complex.ofReal_one,
      Complex.one_cpow]
    apply Valued.toNormedField.norm_eq_one_iff.mpr
    exact HeightOneSpectrum.adicCompletionIntegers.mem_units_iff_valued_eq_one.mp
      (show u ∈ (v.adicCompletionIntegers F).units from ⟨x.val.property, x.inv.property⟩)
  let val : Valuation (v.adicCompletion F) (WithZero (Multiplicative ℤ)) := Valued.v
  obtain ⟨π, hπ⟩ := val.exists_isUniformizer_of_isCyclic_of_nontrivial
  let u := Units.mk0 (π : v.adicCompletion F) hπ.ne_zero
  have hnorm : ‖(u : v.adicCompletion F)‖ = (v.asIdeal.absNorm : ℝ)⁻¹ :=
    norm_uniformizer_adicCompletion v _ hπ
  have hmain : finiteHeckeEulerFactor χ v s =
      finiteHeckeEulerFactor (1 : U[F]) v (s + a) := by
    rw [finiteHeckeEulerFactor, finiteHeckeEulerFactor, hχ, ite_eq_left (hu a),
      ite_eq_left (hu 0), (hu a).localValue_eq u hπ, (hu 0).localValue_eq u hπ, hval, hval,
      hnorm, Complex.cpow_zero, one_mul, Complex.ofReal_inv,
      Complex.inv_cpow_ofReal_nonneg (Nat.cast_nonneg _) a, ← Complex.cpow_neg,
      Complex.ofReal_natCast, ← Complex.cpow_add _ _
        (by exact_mod_cast ((zero_lt_one.trans (HeightOneSpectrum.one_lt_absNorm v))).ne'),
      neg_add, add_comm (-a)]
  convert hmain using 1
  rw [ha, neg_mul, sub_eq_add_neg]

/-- A pure imaginary norm twist of the trivial character shifts the Dedekind zeta
function on the half-plane of absolute convergence. -/
private theorem heckeLDP_finiteHeckeL_shift (χ : U[F]) (t₀ : ℝ)
    (hχ : ideleClassNormTwist χ 0 = ideleClassNormTwist (1 : U[F]) (-Complex.I * t₀))
    (s : halfPlane) : finiteHeckeL χ s = dedekindZeta F ((s : ℂ) - Complex.I * t₀) := by
  let w : halfPlane := ⟨(s : ℂ) - Complex.I * t₀, by
    have hre : ((s : ℂ) - Complex.I * t₀).re = (s : ℂ).re := by simp [Complex.sub_re]
    rw [Set.mem_preimage, Set.mem_Ioi, hre]
    exact s.property⟩
  have h := (finiteHeckeL_hasProd χ s).unique <|
    (finiteHeckeL_hasProd (1 : U[F]) w).congr_fun
      (fun v ↦ heckeLDP_eulerFactor_shift χ t₀ hχ v s)
  exact h.trans (heckeLDP_zeta_eq w)

/-- For a pure imaginary norm twist, the norm-grouped series sums to the negative
logarithmic derivative of the shifted Dedekind zeta continuation. -/
private theorem heckeLDP_normTwist_hasSum (χ : U[F]) (t₀ : ℝ)
    (hχ : ideleClassNormTwist χ 0 = ideleClassNormTwist (1 : U[F]) (-Complex.I * t₀))
    (Z : ℂ → ℂ) (hZ : MeromorphicNFOn Z univ)
    (hSeries : ∀ s : halfPlane, Z s = dedekindZeta F s) (s : halfPlane) :
    LSeriesHasSum (heckeLogDerivCoefficient (ideleClassNormTwist χ 0)) (s : ℂ)
      (-logDeriv Z ((s : ℂ) - Complex.I * t₀)) := by
  let L₀ : ℂ → ℂ := fun w ↦ Z (w - Complex.I * t₀)
  have hL₀ : MeromorphicNFOn L₀ univ := fun z _ ↦
    meromorphicNFAt_comp_sub_const_iff_meromorphicNFAt.mpr (hZ (mem_univ _))
  have hS₀ : ∀ s : halfPlane, L₀ s = finiteHeckeL χ s := fun s ↦ by
    have hs : 1 < ((s : ℂ) - Complex.I * t₀).re := by
      have hre : ((s : ℂ) - Complex.I * t₀).re = (s : ℂ).re := by simp [Complex.sub_re]
      rw [hre]
      exact s.property
    change Z ((s : ℂ) - Complex.I * t₀) = _
    rw [hSeries ⟨_, hs⟩, heckeLDP_finiteHeckeL_shift χ t₀ hχ s]
  have h := heckeLDP_hasSum χ L₀ hL₀ hS₀ s
  convert h using 1
  have han : AnalyticAt ℂ Z ((s : ℂ) - Complex.I * t₀) :=
    (finiteHeckeL_logDeriv_hasSum_ideals (1 : U[F]) Z hZ
      (fun w ↦ (hSeries w).trans (heckeLDP_zeta_eq w).symm) ⟨_, by
        have hre : ((s : ℂ) - Complex.I * t₀).re = (s : ℂ).re := by simp [Complex.sub_re]
        rw [Set.mem_preimage, Set.mem_Ioi, hre]
        exact s.property⟩).1
  have hcomp : L₀ = Z ∘ (· - Complex.I * t₀) := rfl
  rw [hcomp, logDeriv_comp (f := Z) (g := (· - Complex.I * t₀))]
  · simp
  · exact han.differentiableAt
  · fun_prop

/-- The norm of the twisted grouped coefficient is bounded by the plain grouped
von Mangoldt coefficient. -/
private theorem heckeLDP_coeff_norm_le (χ : U[F]) (n : ℕ) :
    ‖heckeLogDerivCoefficient (ideleClassNormTwist χ 0) n‖ ≤
      ∑ᶠ I : {I : Ideal (𝓞 F) // I ≠ ⊥ ∧ I.absNorm = n}, idealVonMangoldt I.val := by
  classical
  let S : Set (Ideal (𝓞 F)) := {I | I ≠ ⊥ ∧ I.absNorm = n}
  have hfin : S.Finite :=
    (Ring.HasFiniteQuotients.finite_absNorm_eq n).subset fun I hI ↦ hI.2
  change ‖∑ᶠ I : ↥S, heckeIdealVonMangoldt (ideleClassNormTwist χ 0) I.val‖ ≤
    ∑ᶠ I : ↥S, idealVonMangoldt I.val
  rw [finsum_set_coe_eq_finsum_mem, finsum_set_coe_eq_finsum_mem,
    finsum_mem_eq_finite_toFinset_sum _ hfin, finsum_mem_eq_finite_toFinset_sum _ hfin]
  calc ‖∑ I ∈ hfin.toFinset, heckeIdealVonMangoldt (ideleClassNormTwist χ 0) I‖
      ≤ ∑ I ∈ hfin.toFinset, ‖heckeIdealVonMangoldt (ideleClassNormTwist χ 0) I‖ :=
        norm_sum_le _ _
    _ ≤ ∑ I ∈ hfin.toFinset, idealVonMangoldt I :=
        Finset.sum_le_sum fun I _ ↦ heckeLDP_weight_le χ I

/-- The trivial-character grouped coefficient is the plain ideal von Mangoldt sum. -/
private theorem heckeLDP_coeff_trivial (n : ℕ) :
    heckeLogDerivCoefficient (ideleClassNormTwist (1 : U[F]) 0) n =
      (∑ᶠ I : {I : Ideal (𝓞 F) // I ≠ ⊥ ∧ I.absNorm = n}, idealVonMangoldt I.val : ℂ) := by
  unfold heckeLogDerivCoefficient
  refine finsum_congr fun I ↦ ?_
  rw [heckeIdealVonMangoldt, heckeLDP_value_one I.property.1, one_mul]

/-- The norm-grouped twisted von Mangoldt series is absolutely summable to the right
of the 1-line, since it sums to the logarithmic derivative of a matching continuation. -/
private theorem heckeLDP_summable (χ : U[F]) (s : ℂ) (hs : 1 < s.re) :
    LSeriesSummable (heckeLogDerivCoefficient (ideleClassNormTwist χ 0)) s := by
  obtain ⟨L, hL, hS⟩ := finiteHeckeL_exists_continuation χ
  exact (heckeLDP_hasSum χ L hL hS ⟨s, hs⟩).LSeriesSummable

/-- Near a point where it is in normal form, the logarithmic derivative of a meromorphic
function is at most a constant times the inverse distance to that point. -/
private theorem heckeLDP_logDeriv_local (Z : ℂ → ℂ) (p : ℂ) (hZ : MeromorphicNFAt Z p) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ᶠ z in 𝓝 p, z ≠ p → ‖logDeriv Z z‖ ≤ M / ‖z - p‖ := by
  rcases hZ with h0 | ⟨n, g, hg, hgp, hfg⟩
  · refine ⟨0, le_rfl, ?_⟩
    filter_upwards [logDeriv_congr_nhds h0] with z hz _
    rw [hz]
    simp [logDeriv_apply]
  · have hcont : ContinuousAt (fun z ↦ ‖logDeriv g z‖) p :=
      (hg.deriv.continuousAt.div hg.continuousAt hgp).norm
    have hbd : ∀ᶠ z in 𝓝 p, ‖logDeriv g z‖ < ‖logDeriv g p‖ + 1 :=
      hcont.eventually (gt_mem_nhds (lt_add_one _))
    refine ⟨|(n : ℝ)| + (‖logDeriv g p‖ + 1), by positivity, ?_⟩
    filter_upwards [logDeriv_congr_nhds hfg, hg.eventually_analyticAt,
      hg.continuousAt.eventually_ne hgp, hbd, Metric.ball_mem_nhds p one_pos]
      with z hz hga hgz hb hball hzp
    have hsub : z - p ≠ 0 := sub_ne_zero.mpr hzp
    have hd : DifferentiableAt ℂ (fun w : ℂ ↦ w - p) z := by fun_prop
    have h1 : logDeriv ((· - p) ^ n • g) z = n / (z - p) + logDeriv g z := by
      have hfun : ((· - p) ^ n • g : ℂ → ℂ) = (fun w : ℂ ↦ (w - p) ^ n) * g := by
        ext w
        simp
      rw [hfun, logDeriv_mul (f := fun w : ℂ ↦ (w - p) ^ n) (g := g) z (zpow_ne_zero n hsub)
        hgz (hd.zpow (Or.inl hsub)) hga.differentiableAt, logDeriv_fun_zpow hd n]
      congr 1
      simp [logDeriv_apply, div_eq_mul_inv]
    rw [hz, h1]
    have hdist : ‖z - p‖ < 1 := by simpa [dist_eq_norm] using hball
    have hpos : 0 < ‖z - p‖ := norm_pos_iff.mpr hsub
    have hn : ‖(n : ℂ) / (z - p)‖ = |(n : ℝ)| / ‖z - p‖ := by
      rw [norm_div, Complex.norm_intCast]
    have hg1 : ‖logDeriv g z‖ ≤ (‖logDeriv g p‖ + 1) / ‖z - p‖ := by
      rw [le_div_iff₀ hpos]
      nlinarith [norm_nonneg (logDeriv g z), norm_nonneg (logDeriv g p)]
    calc ‖(n : ℂ) / (z - p) + logDeriv g z‖
        ≤ ‖(n : ℂ) / (z - p)‖ + ‖logDeriv g z‖ := norm_add_le _ _
      _ ≤ |(n : ℝ)| / ‖z - p‖ + (‖logDeriv g p‖ + 1) / ‖z - p‖ := by rw [hn]; linarith
      _ = (|(n : ℝ)| + (‖logDeriv g p‖ + 1)) / ‖z - p‖ := by ring

/-- A logarithmic majorant for the twisted coefficients, with the absolute-sum
bound of order `(σ - 1)⁻¹` at the 1-line. -/
private theorem heckeLDP_majorant (χ : U[F]) :
    ∃ ψ : ℕ → ℝ, (∀ n, 0 < ψ n) ∧ Monotone ψ ∧
      (heckeLogDerivCoefficient (ideleClassNormTwist χ 0) =O[atTop] ψ) ∧
      ((fun σ : ℝ ↦ ∑' n : ℕ,
          ‖LSeries.term (heckeLogDerivCoefficient (ideleClassNormTwist χ 0)) (σ : ℂ) n‖)
        =O[𝓝[>] 1] (fun σ : ℝ ↦ (σ - 1)⁻¹)) := by
  obtain ⟨C, hC, hbound⟩ := heckeLogDerivCoefficient_bound (Module.finrank ℚ F)
  have hbF := hbound F rfl
  let ψ : ℕ → ℝ := fun n ↦ C * Real.log (n + 2) + 1
  have hψ : ∀ n, 0 < ψ n := fun n ↦ by
    dsimp [ψ]
    have : 0 ≤ Real.log (n + 2) :=
      Real.log_nonneg (by exact_mod_cast (show 1 ≤ n + 2 by omega))
    linarith [mul_nonneg hC.le this]
  have hmono : Monotone ψ := by
    intro a b hab
    dsimp [ψ]
    gcongr <;> linarith
  have hcoeff : heckeLogDerivCoefficient (ideleClassNormTwist χ 0) =O[atTop] ψ := by
    apply Asymptotics.IsBigO.of_bound 1
    filter_upwards [hbF, eventually_ge_atTop 2] with m hm hm2
    rw [one_mul, Real.norm_of_nonneg (hψ m).le]
    calc ‖heckeLogDerivCoefficient (ideleClassNormTwist χ 0) m‖
        ≤ C * Real.log m := hm χ
      _ ≤ C * Real.log (m + 2) :=
        mul_le_mul_of_nonneg_left (Real.log_le_log (by positivity) (by linarith)) hC.le
      _ ≤ ψ m := by dsimp [ψ]; linarith
  have habs : (fun σ : ℝ ↦ ∑' n : ℕ,
      ‖LSeries.term (heckeLogDerivCoefficient (ideleClassNormTwist χ 0)) (σ : ℂ) n‖)
      =O[𝓝[>] 1] (fun σ : ℝ ↦ (σ - 1)⁻¹) := by
    obtain ⟨Z₀, hZ₀, hS₀⟩ := finiteHeckeL_exists_continuation (1 : U[F])
    obtain ⟨M, hM, hlocal⟩ := heckeLDP_logDeriv_local Z₀ 1 (hZ₀ (mem_univ 1))
    apply Asymptotics.IsBigO.of_bound M
    obtain ⟨δ, hδ0, hδ⟩ := Metric.eventually_nhds_iff.mp hlocal
    filter_upwards [Ioo_mem_nhdsGT (show (1 : ℝ) < 1 + δ by linarith)] with σ hσ
    have hσ1 : 1 < σ := hσ.1
    have hdist : dist (σ : ℂ) 1 < δ := by
      rw [Complex.dist_eq]
      have hnorm : ‖(σ : ℂ) - 1‖ = σ - 1 := by
        have hsub : (σ : ℂ) - 1 = ((σ - 1 : ℝ) : ℂ) := by simp only [Complex.ofReal_sub, Complex.ofReal_one]
        rw [hsub, Complex.norm_real, Real.norm_of_nonneg (show 0 ≤ σ - 1 by linarith)]
      rw [hnorm]
      linarith [hσ.2]
    have hb := hδ hdist (by exact_mod_cast hσ1.ne')
    have hb' : ‖logDeriv Z₀ (σ : ℂ)‖ ≤ M / (σ - 1) := by
      have hnorm : ‖(σ : ℂ) - 1‖ = σ - 1 := by
        have hsub : (σ : ℂ) - 1 = ((σ - 1 : ℝ) : ℂ) := by simp only [Complex.ofReal_sub, Complex.ofReal_one]
        rw [hsub, Complex.norm_real, Real.norm_of_nonneg (show 0 ≤ σ - 1 by linarith)]
      rwa [hnorm] at hb
    let a₁ := heckeLogDerivCoefficient (ideleClassNormTwist (1 : U[F]) 0)
    have h₁ := heckeLDP_hasSum (1 : U[F]) Z₀ hZ₀ hS₀ ⟨σ, hσ1⟩
    have hempty : IsEmpty {I : Ideal (𝓞 F) // I ≠ ⊥ ∧ I.absNorm = 0} :=
      ⟨fun I ↦ I.property.1 (Ideal.absNorm_eq_zero_iff.mp I.property.2)⟩
    have hre (n : ℕ) : (LSeries.term a₁ (σ : ℂ) n).re =
        (∑ᶠ I : {I : Ideal (𝓞 F) // I ≠ ⊥ ∧ I.absNorm = n}, idealVonMangoldt I.val) /
          (n : ℝ) ^ σ := by
      by_cases hn : n = 0
      · subst hn
        simp only [LSeries.term]
        rw [finsum_eq_zero_of_forall_eq_zero fun I ↦ False.elim (hempty.false I)]
        simp
      · rw [LSeries.term_of_ne_zero hn]
        simp only [a₁, heckeLDP_coeff_trivial]
        have h1 : (∑ᶠ I : {I : Ideal (𝓞 F) // I ≠ ⊥ ∧ I.absNorm = n}, (idealVonMangoldt I.val : ℂ)) =
            ↑(∑ᶠ I : {I : Ideal (𝓞 F) // I ≠ ⊥ ∧ I.absNorm = n}, idealVonMangoldt I.val) := by
          have hfin : {I : Ideal (𝓞 F) | I ≠ ⊥ ∧ I.absNorm = n}.Finite :=
            (Ring.HasFiniteQuotients.finite_absNorm_eq n).subset
              (fun I (hI : I ≠ ⊥ ∧ I.absNorm = n) => hI.2)
          haveI : Fintype {I : Ideal (𝓞 F) // I ≠ ⊥ ∧ I.absNorm = n} := hfin.fintype
          exact (AddMonoidHom.map_finsum Complex.ofRealHom.toAddMonoidHom (Set.toFinite _)).symm
        rw [h1]
        have h2 : (↑n : ℂ) ^ (↑σ : ℂ) = ↑((n : ℝ) ^ σ) :=
          (Complex.ofReal_cpow (Nat.cast_nonneg _) σ).symm
        rw [h2, ← Complex.ofReal_div, Complex.ofReal_re]
    have hreal : HasSum (fun n ↦
        (∑ᶠ I : {I : Ideal (𝓞 F) // I ≠ ⊥ ∧ I.absNorm = n}, idealVonMangoldt I.val) /
          (n : ℝ) ^ σ) (-logDeriv Z₀ (σ : ℂ)).re := by
      convert Complex.hasSum_re h₁ using 1
      funext n
      exact (hre n).symm
    have hle : ∀ n, ‖LSeries.term (heckeLogDerivCoefficient (ideleClassNormTwist χ 0)) (σ : ℂ) n‖ ≤
        (∑ᶠ I : {I : Ideal (𝓞 F) // I ≠ ⊥ ∧ I.absNorm = n}, idealVonMangoldt I.val) /
          (n : ℝ) ^ σ := by
      intro n
      by_cases hn : n = 0
      · subst hn
        simp only [LSeries.term]
        rw [finsum_eq_zero_of_forall_eq_zero fun I ↦ False.elim (hempty.false I)]
        simp
      · rw [LSeries.norm_term_eq]
        simp only [hn, ite_false, Complex.ofReal_re]
        gcongr
        exact heckeLDP_coeff_norm_le χ n
    calc ‖(∑' n : ℕ, ‖LSeries.term (heckeLogDerivCoefficient (ideleClassNormTwist χ 0))
        (σ : ℂ) n‖)‖
        = ∑' n : ℕ, ‖LSeries.term (heckeLogDerivCoefficient (ideleClassNormTwist χ 0))
          (σ : ℂ) n‖ :=
          Real.norm_of_nonneg (tsum_nonneg fun n ↦ norm_nonneg _)
      _ ≤ ∑' n : ℕ, (∑ᶠ I : {I : Ideal (𝓞 F) // I ≠ ⊥ ∧ I.absNorm = n},
          idealVonMangoldt I.val) / (n : ℝ) ^ σ :=
          (summable_norm_iff.mpr (heckeLDP_summable χ (σ : ℂ) hσ1)).tsum_le_tsum hle
            hreal.summable
      _ = (-logDeriv Z₀ (σ : ℂ)).re := hreal.tsum_eq
      _ ≤ ‖logDeriv Z₀ (σ : ℂ)‖ := by simpa using Complex.re_le_norm (-logDeriv Z₀ (σ : ℂ))
      _ ≤ M / (σ - 1) := hb'
      _ = M * ‖(σ - 1)⁻¹‖ := by
          rw [Real.norm_of_nonneg (inv_nonneg.mpr (show 0 ≤ σ - 1 by linarith))]
          ring
  exact ⟨ψ, hψ, hmono, hcoeff, habs⟩

/-- A pure imaginary norm twist of the trivial character has exponent zero. -/
private theorem heckeLDP_twist_param_zero (t : ℝ)
    (ht : ideleClassNormTwist (1 : U[F]) 0 = ideleClassNormTwist (1 : U[F]) (-Complex.I * t)) :
    t = 0 := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, ⟨σ, hσ, hnorm⟩, _⟩ := ideleGroup_quotient.{_, 0} F
  have htw (z : ℂ) (g : IdeleClassGroup (𝓞 F) F) :
      ideleClassNormTwist (1 : U[F]) z g =
        (((ideleClassNorm F g : NNReal) : ℝ) : ℂ) ^ z := by
    change ((1 : U[F]) g : ℂ) * (((ideleClassNorm F g : NNReal) : ℝ) : ℂ) ^ z = _
    rw [PontryaginDual.one_apply]
    simp only [Circle.coe_one, one_mul]
  let c : ℝ≥0ˣ →ₜ* ℂ := (ideleClassNormTwist (1 : U[F]) (-Complex.I * t)).comp ⟨σ, hσ⟩
  have hc1 : ∀ u : ℝ≥0ˣ, c u = 1 := by
    intro u
    have h := DFunLike.congr_fun ht (σ u)
    rw [htw, htw] at h
    have := h.symm
    simp only [Complex.cpow_zero] at this
    change ideleClassNormTwist (1 : U[F]) (-Complex.I * t) (σ u) = 1
    rw [htw]
    exact this
  have hcval (u : ℝ≥0ˣ) : c u = (((u : ℝ≥0) : ℝ) : ℂ) ^ (-Complex.I * t) := by
    change ideleClassNormTwist (1 : U[F]) (-Complex.I * t) (σ u) = _
    rw [htw]
    congr 1
    exact_mod_cast hnorm u
  obtain ⟨z, ⟨hzre, hz⟩, huniq⟩ := existsUnique_unitaryComplexPower c
    (fun u ↦ by rw [hc1 u]; simp)
  have h1 : -Complex.I * t = z := huniq _ ⟨by simp, hcval⟩
  have h2 : (0 : ℂ) = z := huniq 0 ⟨by simp, fun u ↦ by rw [hc1 u]; simp⟩
  have : -Complex.I * t = 0 := by rw [h1, h2]
  simpa [Complex.ext_iff] using this

/-- A meromorphic normal-form continuation of the completed trivial-character L-function,
with the same meromorphic order as `Z` on the positive half-plane. -/
private theorem heckeLDP_completed (Z : ℂ → ℂ) (hZ : MeromorphicNFOn Z univ)
    (hSeries : ∀ s : halfPlane, Z s = dedekindZeta F s) :
    ∃ Λ : ℂ → ℂ, MeromorphicNFOn Λ univ ∧
      (∀ s : halfPlane, Λ s = completedHeckeL (1 : U[F]) s) ∧
      ∀ s : ℂ, 0 < s.re → meromorphicOrderAt Λ s = meromorphicOrderAt Z s := by
  have hΓ (s : ℂ) (hs : 0 < s.re) : AnalyticAt ℂ (heckeGammaFactor (1 : U[F])) s :=
    DifferentiableOn.analyticAt (s := Complex.re ⁻¹' Ioi 0)
      (fun w hw ↦ (differentiableAt_heckeGammaFactor_of_re_pos (1 : U[F]) hw).differentiableWithinAt)
      ((isOpen_Ioi.preimage Complex.continuous_re).mem_nhds hs)
  let M : ℂ → ℂ := fun w ↦ heckeGammaFactor (1 : U[F]) w * Z w
  have hM : MeromorphicOn M univ := fun x _ ↦
    (meromorphic_heckeGammaFactor (1 : U[F]) x).mul (hZ (mem_univ x)).meromorphicAt
  refine ⟨toMeromorphicNFOn M univ, meromorphicNFOn_toMeromorphicNFOn _ _, fun s ↦ ?_,
    fun s hs ↦ ?_⟩
  · have hs : 0 < (s : ℂ).re := zero_lt_one.trans s.property
    have hMan : AnalyticAt ℂ M s :=
      (hΓ s hs).mul (finiteHeckeL_logDeriv_hasSum_ideals (1 : U[F]) Z hZ
        (fun w ↦ (hSeries w).trans (heckeLDP_zeta_eq w).symm) s).1
    rw [toMeromorphicNFOn_eq_toMeromorphicNFAt hM (mem_univ _),
      toMeromorphicNFAt_eq_self.mpr hMan.meromorphicNFAt]
    have hZfin : Z s = finiteHeckeL (1 : U[F]) s := by
      rw [hSeries s, (heckeLDP_zeta_eq s).symm]
    simp [M, hZfin, completedHeckeL, finiteHeckeL]
  · rw [meromorphicOrderAt_toMeromorphicNFOn hM (mem_univ _)]
    exact meromorphicOrderAt_mul_of_ne_zero (hΓ s hs)
      (heckeGammaFactor_ne_zero_of_re_pos (1 : U[F]) hs)

/-- The Dedekind zeta continuation is analytic at every point of the positive
half-plane except one. -/
private theorem heckeLDP_analytic (Z : ℂ → ℂ) (hZ : MeromorphicNFOn Z univ)
    (hSeries : ∀ s : halfPlane, Z s = dedekindZeta F s) {z : ℂ} (hz : 0 < z.re)
    (hz1 : z ≠ 1) : AnalyticAt ℂ Z z := by
  obtain ⟨Λ, hΛ, hΛs, hord⟩ := heckeLDP_completed Z hZ hSeries
  obtain ⟨t, ⟨ht, hord0, hord1, han⟩, -⟩ :=
    completedHeckeL_continuation_simplePoles (1 : U[F]) Λ hΛ hΛs
    (by apply MonoidHom.ext; intro g; exact PontryaginDual.one_apply _)
  have ht0 : t = 0 := heckeLDP_twist_param_zero t ht
  subst ht0
  have hz0 : z ≠ 0 := fun h ↦ by rw [h, Complex.zero_re] at hz; exact lt_irrefl _ hz
  have hanΛ : AnalyticAt ℂ Λ z := han z (by simp [hz1, hz0])
  have hge : 0 ≤ meromorphicOrderAt Z z := by
    rw [← hord z hz]
    exact hanΛ.meromorphicOrderAt_nonneg
  exact (hZ (mem_univ z)).meromorphicOrderAt_nonneg_iff_analyticAt.mp hge

/-- The Dedekind zeta continuation has a simple pole at one. -/
private theorem heckeLDP_order_one (Z : ℂ → ℂ) (hZ : MeromorphicNFOn Z univ)
    (hSeries : ∀ s : halfPlane, Z s = dedekindZeta F s) :
    meromorphicOrderAt Z 1 = -1 := by
  obtain ⟨Λ, hΛ, hΛs, hord⟩ := heckeLDP_completed Z hZ hSeries
  obtain ⟨t, ⟨ht, hord0, hord1, han⟩, -⟩ :=
    completedHeckeL_continuation_simplePoles (1 : U[F]) Λ hΛ hΛs
    (by apply MonoidHom.ext; intro g; exact PontryaginDual.one_apply _)
  have ht0 : t = 0 := heckeLDP_twist_param_zero t ht
  subst ht0
  simp at hord1
  exact (hord 1 (by norm_num)).symm.trans hord1

/-- Near one, the logarithmic derivative is `-1/(z-1)` plus an analytic germ. -/
private theorem heckeLDP_principalPart (Z : ℂ → ℂ) (hZ : MeromorphicNFOn Z univ)
    (hSeries : ∀ s : halfPlane, Z s = dedekindZeta F s) :
    ∃ h : ℂ → ℂ, AnalyticAt ℂ h 1 ∧
      logDeriv Z =ᶠ[𝓝[≠] (1 : ℂ)] fun z ↦ -1 / (z - 1) + h z := by
  have horder := heckeLDP_order_one Z hZ hSeries
  rcases hZ (mem_univ 1) with h0 | ⟨n, g, hg, hgp, hfg⟩
  · have := meromorphicOrderAt_eq_top_iff.mpr (h0.filter_mono nhdsWithin_le_nhds)
    rw [this] at horder
    exact False.elim (WithTop.coe_ne_top horder.symm)
  · have hmer : MeromorphicAt Z 1 := by
      apply MeromorphicAt.congr _ (hfg.filter_mono nhdsWithin_le_nhds).symm
      fun_prop
    have hn : meromorphicOrderAt Z 1 = (n : WithTop ℤ) := by
      rw [meromorphicOrderAt_eq_int_iff hmer]
      exact ⟨g, hg, hgp, eventually_nhdsWithin_of_eventually_nhds hfg⟩
    rw [horder] at hn
    have hn' : n = -1 := by
      have := hn.symm
      change (n : WithTop ℤ) = (-1 : ℤ) at this
      exact_mod_cast this
    subst hn'
    refine ⟨logDeriv g, ?_, ?_⟩
    · have := hg.deriv.div hg hgp
      convert this using 1
      funext z
      exact (logDeriv_apply g z).symm
    · have h1 : logDeriv ((· - (1 : ℂ)) ^ (-1 : ℤ) • g) =ᶠ[𝓝[≠] 1]
          fun z ↦ -1 / (z - 1) + logDeriv g z := by
        filter_upwards [self_mem_nhdsWithin (a := (1 : ℂ)) (s := ({1}ᶜ : Set ℂ)),
          hg.eventually_analyticAt.filter_mono nhdsWithin_le_nhds,
          (hg.continuousAt.eventually_ne hgp).filter_mono nhdsWithin_le_nhds] with z hz hga hgz
        have hsub : z - 1 ≠ 0 := sub_ne_zero.mpr hz
        have hfun : ((· - (1 : ℂ)) ^ (-1 : ℤ) • g : ℂ → ℂ) =
            (fun w : ℂ ↦ (w - 1) ^ (-1 : ℤ)) * g := by ext w; simp
        have hd : deriv (fun w : ℂ ↦ w - 1) z = 1 :=
          ((hasDerivAt_id z).sub_const (1 : ℂ)).deriv
        have hzpow : (fun w : ℂ ↦ (w - 1) ^ (-1 : ℤ)) = (fun w : ℂ ↦ w - 1) ^ (-1 : ℤ) := by
          funext w; rfl
        have hdiff : DifferentiableAt ℂ (fun w : ℂ ↦ (w - 1) ^ (-1 : ℤ)) z :=
          DifferentiableAt.zpow (by fun_prop) (Or.inl hsub)
        rw [hfun, logDeriv_mul z (zpow_ne_zero (-1 : ℤ) hsub : (z - 1) ^ (-1 : ℤ) ≠ 0) hgz hdiff hga.differentiableAt]
        have hlog : logDeriv (fun w : ℂ ↦ (w - 1) ^ (-1 : ℤ)) z = -1 / (z - 1) := by
          have := logDeriv_fun_zpow (f := (fun w : ℂ ↦ w - 1))
            (by fun_prop : DifferentiableAt ℂ (fun w : ℂ ↦ w - 1) z) (-1 : ℤ)
          convert this using 1 <;> simp [logDeriv_apply, hd] <;> ring
        simp only [hlog]
      exact (logDeriv_congr_nhdsNE (hfg.filter_mono nhdsWithin_le_nhds)).trans h1

/-- A germ of the form `H z / (z - ρ)` with `H` analytic has residue `H ρ`. -/
private theorem heckeLDP_residue_div {f H : ℂ → ℂ} {ρ : ℂ} (hH : AnalyticAt ℂ H ρ)
    (hf : f =ᶠ[𝓝[≠] ρ] fun z ↦ H z / (z - ρ)) : complexResidue f ρ = H ρ := by
  obtain ⟨R₁, hR₁, hball⟩ := Metric.eventually_nhds_iff.mp (eventually_nhdsWithin_iff.mp hf)
  obtain ⟨R₂, hR₂, hHR⟩ := hH.exists_ball_analyticOnNhd
  let R := min R₁ R₂
  have hR : 0 < R := lt_min hR₁ hR₂
  have heq : (fun r : ℝ ↦ circleIntegral f ρ r / (2 * (Real.pi : ℂ) * Complex.I)) =ᶠ[𝓝[>] 0]
      (fun _ ↦ H ρ) := by
    filter_upwards [Ioo_mem_nhdsGT hR] with r hr
    have hsub : Metric.closedBall ρ r ⊆ Metric.ball ρ R₂ :=
      Metric.closedBall_subset_ball (hr.2.trans_le (min_le_right _ _))
    have hcirc : circleIntegral f ρ r = circleIntegral (fun z ↦ H z / (z - ρ)) ρ r := by
      apply circleIntegral.integral_congr hr.1.le
      intro z hz
      have hzρ : z ≠ ρ := by
        intro h
        have hdist : dist z ρ = r := by simpa [Metric.sphere] using hz
        rw [h, dist_self] at hdist
        linarith [hr.1]
      have hzdist : dist z ρ < R₁ :=
        (Metric.sphere_subset_closedBall hz).trans_lt (hr.2.trans_le (min_le_left _ _))
      have hfz := hball (y := z) hzdist
      exact hfz (Set.mem_compl_singleton_iff.mpr hzρ)
    have hint : circleIntegral (fun z ↦ H z / (z - ρ)) ρ r =
        2 * (Real.pi : ℂ) * Complex.I * H ρ := by
      have := Complex.circleIntegral_sub_inv_smul_of_differentiable_on_off_countable
        (f := H) Set.countable_empty (Metric.mem_ball_self hr.1)
        (fun z hz ↦ (hHR z (hsub hz)).continuousAt.continuousWithinAt)
        (fun z hz ↦ (hHR z (hsub (Metric.ball_subset_closedBall hz.1))).differentiableAt)
      simpa [div_eq_inv_mul] using this
    rw [hcirc, hint]
    field_simp
  exact (tendsto_const_nhds.congr' heq.symm).limUnder_eq

/-- `sqrt (log x)` tends to infinity. -/
private theorem heckeLDP_tendsto_sqrt_log :
    Tendsto (fun x : ℝ ↦ Real.sqrt (Real.log x)) atTop atTop :=
  Real.tendsto_sqrt_atTop.comp Real.tendsto_log_atTop

/-- Polynomial powers of `log x` decay against `exp (-b * sqrt (log x))`. -/
private theorem heckeLDP_tendsto_log_pow_exp_sqrt (n : ℕ) (b : ℝ) (hb : 0 < b) :
    Tendsto (fun x : ℝ ↦ (Real.log x) ^ n * Real.exp (-b * Real.sqrt (Real.log x)))
      atTop (𝓝 0) := by
  have hbase := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (2 * n : ℝ) b hb
  refine (hbase.comp heckeLDP_tendsto_sqrt_log).congr' ?_
  filter_upwards [eventually_ge_atTop 1] with x hx
  have hl : 0 ≤ Real.log x := Real.log_nonneg hx
  have hpow : (Real.log x) ^ n = (Real.sqrt (Real.log x)) ^ (2 * n : ℝ) := by
    have hs : (Real.sqrt (Real.log x)) ^ (2 : ℝ) = Real.log x := by
      rw [Real.rpow_two, Real.sq_sqrt hl]
    have := congrArg (fun t ↦ t ^ (n : ℝ)) hs
    rw [← Real.rpow_mul (Real.sqrt_nonneg _) 2 (n : ℝ), Real.rpow_natCast] at this
    have hcast : (2 : ℝ) * (n : ℝ) = (2 * n : ℝ) := by ring
    rw [hcast] at this
    exact this.symm
  rw [hpow]
  simp only [Function.comp_apply]
  try ring

/-- The logarithmic derivative of a function analytic and nonzero at a point is analytic. -/
private theorem heckeLDP_logDeriv_analytic {Z : ℂ → ℂ} {z : ℂ}
    (han : AnalyticAt ℂ Z z) (hne : Z z ≠ 0) : AnalyticAt ℂ (logDeriv Z) z := by
  have := han.deriv.div han hne
  convert this using 1
  funext w
  rfl

/-- The cutoff polynomial is entire in the evaluation point. -/
private theorem heckeLDP_poly_analytic (χ : U[F]) (x : ℝ) (s : ℂ) :
    AnalyticAt ℂ (heckeLogDerivPolynomial χ x) s := by
  unfold heckeLogDerivPolynomial
  apply Finset.analyticAt_fun_sum
  intro n hn
  have hn0 : n ≠ 0 := Nat.one_le_iff_ne_zero.mp (Finset.mem_Icc.mp hn).1
  have hterm : (fun s ↦ LSeries.term (heckeLogDerivCoefficient (ideleClassNormTwist χ 0)) s n) =
      (fun s ↦ heckeLogDerivCoefficient (ideleClassNormTwist χ 0) n / (n : ℂ) ^ s) := by
    funext s
    rw [LSeries.term_of_ne_zero hn0]
  rw [hterm]
  refine AnalyticAt.div analyticAt_const ?_ ?_
  · exact AnalyticAt.cpow analyticAt_const analyticAt_id
      (Complex.ofReal_mem_slitPlane.mpr (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn0)))
  · exact Complex.cpow_ne_zero_iff.mpr (Or.inl (Nat.cast_ne_zero.mpr hn0))

/-- Shifting the truncated Perron contour left across the 1-line picks up the kernel
residue at the evaluation point and the oscillatory pole term; the remaining edges
are the left and horizontal integrals. -/
private theorem heckeLDP_contour_shift (t₀ : ℝ) (Z : ℂ → ℂ) (hZ : MeromorphicNFOn Z univ)
    (hSeries : ∀ s : halfPlane, Z s = dedekindZeta F s)
    (s : ℂ) (hsre : s.re = 1) (hsp : s ≠ 1 + Complex.I * t₀)
    (x c T δ : ℝ) (hx : 1 < x) (hc : 0 < c) (hT : |s.im - t₀| < T)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1 / 2)
    (hzf : ∀ z : ℂ, 1 - δ ≤ z.re → |z.im - (s.im - t₀)| ≤ T → meromorphicOrderAt Z z ≤ 0) :
    truncatedPerronIntegral (fun w ↦ -logDeriv Z (w - Complex.I * t₀)) s x c T =
      -logDeriv Z (s - Complex.I * t₀) +
        (x : ℂ) ^ (1 + Complex.I * t₀ - s) / (1 + Complex.I * t₀ - s) +
        (Complex.I * ((∫ u in -δ..c,
            -logDeriv Z (s - Complex.I * t₀ + ⟨u, -T⟩) * (x : ℂ) ^ (⟨u, -T⟩ : ℂ) /
              (⟨u, -T⟩ : ℂ)) -
          (∫ u in -δ..c,
            -logDeriv Z (s - Complex.I * t₀ + ⟨u, T⟩) * (x : ℂ) ^ (⟨u, T⟩ : ℂ) /
              (⟨u, T⟩ : ℂ))) +
        (∫ t in -T..T,
          -logDeriv Z (s - Complex.I * t₀ + ⟨-δ, t⟩) * (x : ℂ) ^ (⟨-δ, t⟩ : ℂ) /
            (⟨-δ, t⟩ : ℂ))) / (2 * (Real.pi : ℂ)) := by
  let z₀ : ℂ := s - Complex.I * t₀
  have hz₀re : z₀.re = 1 := by simp [z₀, hsre]
  have hz₀im : z₀.im = s.im - t₀ := by simp [z₀]
  have hz₀ne : z₀ ≠ 1 := by
    intro h
    apply hsp
    simp [z₀] at h
    linear_combination h
  have hT0 : 0 < T := (abs_nonneg _).trans_lt hT
  let g : ℂ → ℂ := fun z ↦ -logDeriv Z z * (x : ℂ) ^ (z - z₀) / (z - z₀)
  have hcpow : AnalyticOnNhd ℂ (fun z : ℂ ↦ (x : ℂ) ^ (z - z₀)) univ := by
    intro z _
    exact AnalyticAt.cpow analyticAt_const
      (by fun_prop : AnalyticAt ℂ (fun w : ℂ ↦ w - z₀) z)
      (Complex.ofReal_mem_slitPlane.mpr (zero_lt_one.trans hx))
  have hgmero : MeromorphicOn g (Icc (1 - δ) (1 + c) ×ℂ Icc (z₀.im - T) (z₀.im + T)) := by
    intro z hz
    exact (((hZ.meromorphicOn.logDeriv) z (mem_univ _)).neg.mul
      ((hcpow z (mem_univ _)).meromorphicAt)).div
      ((by fun_prop : AnalyticAt ℂ (fun w : ℂ ↦ w - z₀) z).meromorphicAt)
  have hinside : ∀ ρ ∈ ({z₀, 1} : Finset ℂ),
      ρ ∈ Ioo (1 - δ) (1 + c) ×ℂ Ioo (z₀.im - T) (z₀.im + T) := by
    intro ρ hρ
    simp only [Finset.mem_insert, Finset.mem_singleton] at hρ
    rcases hρ with rfl | rfl
    · simp only [Complex.mem_reProdIm, hz₀re]
      constructor
      · constructor <;> linarith
      · constructor <;> linarith
    · simp only [Complex.mem_reProdIm, Complex.one_re, Complex.one_im]
      constructor
      · constructor <;> linarith
      · rw [abs_lt] at hT
        simp only [hz₀im]
        constructor <;> linarith

  have houtside : ∀ ρ ∈ Icc (1 - δ) (1 + c) ×ℂ Icc (z₀.im - T) (z₀.im + T),
      ρ ∉ ({z₀, 1} : Finset ℂ) → 0 ≤ meromorphicOrderAt g ρ := by
    intro ρ hρ hρS
    have hρ1 : ρ ≠ 1 := by
      intro h
      apply hρS
      simp [h]
    have hρ0 : ρ ≠ z₀ := by
      intro h
      apply hρS
      simp [h]
    have hre : 0 < ρ.re := by linarith [hρ.1.1]
    have hanZ : AnalyticAt ℂ Z ρ := heckeLDP_analytic Z hZ hSeries hre hρ1
    have hord : meromorphicOrderAt Z ρ ≤ 0 := by
      apply hzf ρ hρ.1.1
      rw [← hz₀im]
      exact abs_le.mpr ⟨by linarith [hρ.2.1], by linarith [hρ.2.2]⟩
    have hneZ : Z ρ ≠ 0 := by
      have h0 : 0 ≤ meromorphicOrderAt Z ρ := hanZ.meromorphicOrderAt_nonneg
      have heq : meromorphicOrderAt Z ρ = 0 := le_antisymm hord h0
      exact (hZ (mem_univ ρ)).meromorphicOrderAt_eq_zero_iff.mp heq
    have hanlog : AnalyticAt ℂ (logDeriv Z) ρ := by
      have := hanZ.deriv.div hanZ hneZ
      exact this
    have hang : AnalyticAt ℂ g ρ := by
      have hden : ρ - z₀ ≠ 0 := sub_ne_zero.mpr hρ0
      have := ((hanlog.neg).mul (hcpow ρ (mem_univ _))).div
        (by fun_prop : AnalyticAt ℂ (fun w : ℂ ↦ w - z₀) ρ) hden
      exact this
    exact hang.meromorphicOrderAt_nonneg
  have hres0 : complexResidue g z₀ = -logDeriv Z z₀ := by
    have hanZ : AnalyticAt ℂ Z z₀ :=
      heckeLDP_analytic Z hZ hSeries (by simp [hz₀re]) hz₀ne
    have hneZ : Z z₀ ≠ 0 := by
      have hord : meromorphicOrderAt Z z₀ ≤ 0 := by
        apply hzf z₀ (by linarith [hz₀re])
        simp [hz₀im]
        linarith
      have h0 : 0 ≤ meromorphicOrderAt Z z₀ := hanZ.meromorphicOrderAt_nonneg
      exact (hZ (mem_univ z₀)).meromorphicOrderAt_eq_zero_iff.mp
        (le_antisymm hord h0)
    have hanlog : AnalyticAt ℂ (logDeriv Z) z₀ := by
      have := hanZ.deriv.div hanZ hneZ
      exact this
    have hH : AnalyticAt ℂ (fun z ↦ -logDeriv Z z * (x : ℂ) ^ (z - z₀)) z₀ :=
      hanlog.neg.mul (hcpow z₀ (mem_univ _))
    have := heckeLDP_residue_div (f := g) (H := fun z ↦ -logDeriv Z z * (x : ℂ) ^ (z - z₀))
      hH (Filter.Eventually.of_forall fun z ↦ rfl)
    simpa [sub_self] using this
  have hres1 : complexResidue g 1 = (x : ℂ) ^ (1 - z₀) / (1 - z₀) := by
    obtain ⟨h, hh, hpp⟩ := heckeLDP_principalPart Z hZ hSeries
    have hK : AnalyticAt ℂ (fun z : ℂ ↦ (x : ℂ) ^ (z - z₀) / (z - z₀)) 1 :=
      (hcpow 1 (mem_univ _)).div
        (by fun_prop : AnalyticAt ℂ (fun w : ℂ ↦ w - z₀) 1) (sub_ne_zero.mpr hz₀ne.symm)
    have hH : AnalyticAt ℂ
        (fun z : ℂ ↦ ((x : ℂ) ^ (z - z₀) / (z - z₀)) * (1 - (z - 1) * h z)) 1 :=
      hK.mul (analyticAt_const.sub
        ((by fun_prop : AnalyticAt ℂ (fun w : ℂ ↦ w - (1 : ℂ)) 1).mul hh))
    have heq : g =ᶠ[𝓝[≠] (1 : ℂ)]
        fun z ↦ (((x : ℂ) ^ (z - z₀) / (z - z₀)) * (1 - (z - 1) * h z)) / (z - 1) := by
      filter_upwards [hpp, self_mem_nhdsWithin (a := (1 : ℂ)) (s := ({1}ᶜ : Set ℂ))] with z hz hz1
      have hsub : z - 1 ≠ 0 := sub_ne_zero.mpr hz1
      by_cases hzz : z = z₀
      · simp [g, hzz, hsub]
      · simp only [g, hz]
        field_simp [hsub, hzz]
        ring
    have := heckeLDP_residue_div hH heq
    convert this using 1
    simp only [sub_self, zero_mul, sub_zero, mul_one]
  have hrect := rectangleIntegral_eq_sum_complexResidue (g := g)
    (σ₁ := 1 - δ) (σ₂ := 1 + c) (t₁ := z₀.im - T) (t₂ := z₀.im + T)
    (S := {z₀, 1}) (by linarith) (by linarith) hgmero hinside houtside
  have hsum : ∑ ρ ∈ ({z₀, 1} : Finset ℂ), complexResidue g ρ =
      -logDeriv Z z₀ + (x : ℂ) ^ (1 - z₀) / (1 - z₀) := by
    rw [Finset.sum_pair hz₀ne, hres0, hres1]
  rw [hsum] at hrect
  -- Convert the four edges to the normalized coordinates.
  have hR : (∫ y in z₀.im - T..z₀.im + T, g ((1 + c : ℂ) + y * Complex.I)) =
      2 * (Real.pi : ℂ) * truncatedPerronIntegral (fun w ↦ -logDeriv Z (w - Complex.I * t₀))
        s x c T := by
    have hb : z₀.im - T = -T + z₀.im := by ring
    have hb' : z₀.im + T = T + z₀.im := by ring
    rw [hb, hb', ← intervalIntegral.integral_comp_add_right
      (fun y ↦ g ((1 + c : ℂ) + y * Complex.I)) z₀.im, truncatedPerronIntegral]
    field_simp
    refine intervalIntegral.integral_congr (fun t _ ↦ ?_)
    have hA : (1 : ℂ) + c + ((t + z₀.im : ℝ) : ℂ) * Complex.I = s + ⟨c, t⟩ - Complex.I * t₀ := by
      apply Complex.ext <;> simp [hz₀re, hz₀im, z₀, hsre] <;> ring
    have hE : (1 : ℂ) + c + ((t + z₀.im : ℝ) : ℂ) * Complex.I - z₀ = (⟨c, t⟩ : ℂ) := by
      apply Complex.ext <;> simp [hz₀re, hz₀im, z₀, hsre] <;> ring
    simp only [g]
    rw [hE, hA]
    ring
  have hL : (∫ y in z₀.im - T..z₀.im + T, g ((1 - δ : ℂ) + y * Complex.I)) =
      ∫ t in -T..T, g (z₀ + (⟨-δ, t⟩ : ℂ)) := by
    have hb : z₀.im - T = -T + z₀.im := by ring
    have hb' : z₀.im + T = T + z₀.im := by ring
    rw [hb, hb', ← intervalIntegral.integral_comp_add_right
      (fun y ↦ g ((1 - δ : ℂ) + y * Complex.I)) z₀.im]
    refine intervalIntegral.integral_congr (fun t _ ↦ ?_)
    exact congrArg g (by apply Complex.ext <;> simp [hz₀re, hz₀im] <;> ring)
  have hB : (∫ u in (1 - δ)..(1 + c), g ((u : ℂ) + (z₀.im - T) * Complex.I)) =
      ∫ v in -δ..c, g (z₀ + (⟨v, -T⟩ : ℂ)) := by
    have hb1 : (1 - δ : ℝ) = -δ + 1 := by ring
    have hb2 : (1 + c : ℝ) = c + 1 := by ring
    rw [hb1, hb2, ← intervalIntegral.integral_comp_add_right
      (fun u ↦ g ((u : ℂ) + (z₀.im - T) * Complex.I)) 1]
    refine intervalIntegral.integral_congr (fun v _ ↦ ?_)
    exact congrArg g (by apply Complex.ext <;> simp [hz₀re, hz₀im] <;> ring)
  have hTp : (∫ u in (1 - δ)..(1 + c), g ((u : ℂ) + (z₀.im + T) * Complex.I)) =
      ∫ v in -δ..c, g (z₀ + (⟨v, T⟩ : ℂ)) := by
    have hb1 : (1 - δ : ℝ) = -δ + 1 := by ring
    have hb2 : (1 + c : ℝ) = c + 1 := by ring
    rw [hb1, hb2, ← intervalIntegral.integral_comp_add_right
      (fun u ↦ g ((u : ℂ) + (z₀.im + T) * Complex.I)) 1]
    refine intervalIntegral.integral_congr (fun v _ ↦ ?_)
    exact congrArg g (by apply Complex.ext <;> simp [hz₀re, hz₀im] <;> ring)
  simp only at hrect
  have hc1 : ((1 + c : ℝ) : ℂ) = 1 + c := by push_cast; ring
  have hδ1 : ((1 - δ : ℝ) : ℂ) = 1 - δ := by push_cast; ring
  have him1 : ((z₀.im - T : ℝ) : ℂ) = z₀.im - T := by push_cast; ring
  have him2 : ((z₀.im + T : ℝ) : ℂ) = z₀.im + T := by push_cast; ring
  rw [hc1, hδ1, him1, him2] at hrect
  rw [hR, hL, hB, hTp] at hrect
  have hpi : (2 * (Real.pi : ℂ)) ≠ 0 := by simp [Real.pi_ne_zero]
  have hgoal : truncatedPerronIntegral (fun w ↦ -logDeriv Z (w - Complex.I * t₀)) s x c T =
      -logDeriv Z z₀ + (x : ℂ) ^ (1 - z₀) / (1 - z₀) +
        (Complex.I * ((∫ v in -δ..c, g (z₀ + (⟨v, -T⟩ : ℂ))) -
          (∫ v in -δ..c, g (z₀ + (⟨v, T⟩ : ℂ)))) +
        (∫ t in -T..T, g (z₀ + (⟨-δ, t⟩ : ℂ)))) / (2 * (Real.pi : ℂ)) := by
    apply mul_left_cancel₀ (show (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 by
      simp [Real.pi_ne_zero])
    rw [mul_add]
    have hrem : 2 * (Real.pi : ℂ) * Complex.I *
        ((Complex.I * ((∫ v in -δ..c, g (z₀ + (⟨v, -T⟩ : ℂ))) -
            (∫ v in -δ..c, g (z₀ + (⟨v, T⟩ : ℂ)))) +
          (∫ t in -T..T, g (z₀ + (⟨-δ, t⟩ : ℂ)))) / (2 * (Real.pi : ℂ))) =
        Complex.I * (Complex.I * ((∫ v in -δ..c, g (z₀ + (⟨v, -T⟩ : ℂ))) -
            (∫ v in -δ..c, g (z₀ + (⟨v, T⟩ : ℂ)))) +
          (∫ t in -T..T, g (z₀ + (⟨-δ, t⟩ : ℂ)))) := by field_simp
    rw [hrem]
    have h2 : 2 * (Real.pi : ℂ) * Complex.I *
        truncatedPerronIntegral (fun w ↦ -logDeriv Z (w - Complex.I * t₀)) s x c T =
        Complex.I * (2 * (Real.pi : ℂ) *
          truncatedPerronIntegral (fun w ↦ -logDeriv Z (w - Complex.I * t₀)) s x c T) := by ring
    rw [h2]
    have h3 : Complex.I * (2 * (Real.pi : ℂ) *
        truncatedPerronIntegral (fun w ↦ -logDeriv Z (w - Complex.I * t₀)) s x c T) =
        2 * (Real.pi : ℂ) * Complex.I * (-logDeriv Z z₀ + (x : ℂ) ^ (1 - z₀) / (1 - z₀)) -
        ((∫ v in -δ..c, g (z₀ + (⟨v, -T⟩ : ℂ))) - (∫ v in -δ..c, g (z₀ + (⟨v, T⟩ : ℂ)))) +
        Complex.I * (∫ t in -T..T, g (z₀ + (⟨-δ, t⟩ : ℂ))) := by
      have := congrArg (fun z ↦ z -
          ((∫ v in -δ..c, g (z₀ + (⟨v, -T⟩ : ℂ))) - (∫ v in -δ..c, g (z₀ + (⟨v, T⟩ : ℂ)))) +
          Complex.I * (∫ t in -T..T, g (z₀ + (⟨-δ, t⟩ : ℂ)))) hrect
      convert this using 1 <;> ring
    rw [h3]
    ring_nf
    simp only [Complex.I_sq]
    ring
  convert hgoal using 1 <;> simp [g, z₀, pow_two, Complex.I_mul_I] <;> ring

/-- On the half-plane of absolute convergence the finite L-function of the trivial
character is the Dedekind zeta function. -/
private theorem dedekindZeta_perron_left_bound_zeta {F : Type*} [Field F] [NumberField F]
    (s : halfPlane) : finiteHeckeL (1 : U[F]) s = dedekindZeta F s := by
  have h := completedHeckeL_one_eq_dedekindZeta (F := F) s
  rw [← heckeGammaFactor_one] at h
  change heckeGammaFactor (1 : U[F]) s * finiteHeckeL (1 : U[F]) s = _ at h
  have hs : 0 < (s : ℂ).re := zero_lt_one.trans s.property
  exact mul_left_cancel₀ (heckeGammaFactor_ne_zero_of_re_pos (1 : U[F]) hs) h

/-- The logarithmic width `A / log (B (t + 3))` is an admissible width for the
logarithmic-derivative estimate: positive and at most `1/2`, differentiable,
nonincreasing, with derivative tending to zero and reciprocal `O(log t)`. -/
private theorem dedekindZeta_perron_left_bound_width (A B : ℝ) (hA : 0 < A)
    (hB : 1 / 3 < B) (hwidth : A ≤ Real.log (B * 3) / 2) :
    MapsTo (fun t : ℝ ↦ A / Real.log (B * (t + 3))) (Ici 0) (Ioc 0 (1 / 2)) ∧
      DifferentiableOn ℝ (fun t : ℝ ↦ A / Real.log (B * (t + 3))) (Ici 0) ∧
      AntitoneOn (fun t : ℝ ↦ A / Real.log (B * (t + 3))) (Ici 0) ∧
      Tendsto (derivWithin (fun t : ℝ ↦ A / Real.log (B * (t + 3))) (Ici 0)) atTop (𝓝 0) ∧
      ((fun t : ℝ ↦ (A / Real.log (B * (t + 3)))⁻¹) =O[atTop] Real.log) := by
  have hB0 : 0 < B := by linarith
  have hl3 : 0 < Real.log (B * 3) := by linarith
  have hpos : ∀ t : ℝ, 0 ≤ t → 0 < B * (t + 3) := fun t ht ↦ by positivity
  have hmono : ∀ t : ℝ, 0 ≤ t → Real.log (B * 3) ≤ Real.log (B * (t + 3)) := fun t ht ↦
    Real.log_le_log (by positivity) (by nlinarith)
  have hg0 : ∀ t : ℝ, 0 ≤ t → 0 < Real.log (B * (t + 3)) := fun t ht ↦
    hl3.trans_le (hmono t ht)
  have hgd : ∀ t : ℝ, 0 ≤ t →
      HasDerivAt (fun t : ℝ ↦ Real.log (B * (t + 3))) (B / (B * (t + 3))) t := fun t ht ↦ by
    have h1 : HasDerivAt (fun t : ℝ ↦ B * (t + 3)) (B * 1) t :=
      ((hasDerivAt_id t).add_const 3).const_mul B
    rw [mul_one] at h1
    exact h1.log (hpos t ht).ne'
  have hηd : ∀ t : ℝ, 0 ≤ t → HasDerivAt (fun t : ℝ ↦ A / Real.log (B * (t + 3)))
      (A * (-(B / (B * (t + 3))) / Real.log (B * (t + 3)) ^ 2)) t := fun t ht ↦ by
    have := ((hgd t ht).inv (hg0 t ht).ne').const_mul A
    refine this.congr_of_eventuallyEq (Eventually.of_forall fun x ↦ ?_)
    simp [div_eq_mul_inv]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro t ht
    have ht : 0 ≤ t := ht
    refine ⟨div_pos hA (hg0 t ht), ?_⟩
    rw [div_le_iff₀ (hg0 t ht)]
    linarith [hmono t ht]
  · exact fun t ht ↦ (hηd t ht).differentiableAt.differentiableWithinAt
  · intro a ha b hb hab
    have ha : 0 ≤ a := ha
    exact div_le_div_of_nonneg_left hA.le (hg0 a ha)
      (Real.log_le_log (hpos a ha) (by nlinarith))
  · have hbound : ∀ᶠ t : ℝ in atTop,
        ‖derivWithin (fun t : ℝ ↦ A / Real.log (B * (t + 3))) (Ici 0) t‖ ≤
          A / Real.log (B * 3) ^ 2 / (t + 3) := by
      filter_upwards [eventually_gt_atTop 0] with t ht
      rw [derivWithin_of_mem_nhds (Ici_mem_nhds ht), (hηd t ht.le).deriv]
      have hBt : B / (B * (t + 3)) = 1 / (t + 3) := by field_simp
      have ht3 : 0 < t + 3 := by linarith
      have hgt := hg0 t ht.le
      have hsq : Real.log (B * 3) ^ 2 ≤ Real.log (B * (t + 3)) ^ 2 :=
        pow_le_pow_left₀ hl3.le (hmono t ht.le) 2
      have hval : A * (-(1 / (t + 3)) / Real.log (B * (t + 3)) ^ 2) =
          -(A / Real.log (B * (t + 3)) ^ 2 / (t + 3)) := by ring
      rw [hBt, hval, Real.norm_eq_abs, abs_neg, abs_of_nonneg (by positivity)]
      exact div_le_div_of_nonneg_right
        (div_le_div_of_nonneg_left hA.le (pow_pos hl3 2) hsq) ht3.le
    exact squeeze_zero_norm' hbound
      (tendsto_const_nhds.div_atTop (tendsto_atTop_add_const_right _ _ tendsto_id))
  · apply Asymptotics.IsBigO.of_bound (2 / A)
    filter_upwards [eventually_ge_atTop (max 3 (B + 3))] with t ht
    have ht3 : 3 ≤ t := (le_max_left _ _).trans ht
    have htB : B + 3 ≤ t := (le_max_right _ _).trans ht
    have hlogt : 0 < Real.log t := Real.log_pos (by linarith)
    have hgt0 := hg0 t (by linarith)
    rw [inv_div, Real.norm_of_nonneg (div_pos hgt0 hA).le, Real.norm_of_nonneg hlogt.le,
      div_le_iff₀ hA]
    have hlog : Real.log (B * (t + 3)) ≤ 2 * Real.log t := by
      rw [show (2 : ℝ) * Real.log t = Real.log (t ^ 2) by rw [Real.log_pow]; norm_num]
      apply Real.log_le_log (by positivity)
      nlinarith
    have hA' : 2 / A * Real.log t * A = 2 * Real.log t := by field_simp
    linarith

/-- In the narrowed logarithmic zero-free region the logarithmic derivative of the
Dedekind zeta continuation is bounded by a squared logarithm at large heights. -/
private theorem dedekindZeta_perron_left_bound_logDeriv {F : Type*} [Field F]
    [NumberField F] (Z : ℂ → ℂ) (hZ : MeromorphicNFOn Z univ)
    (hSeries : ∀ s : halfPlane, Z s = dedekindZeta F s)
    {A B α : ℝ} (hA : 0 < A) (hB : 1 / 3 < B) (hα : α ∈ Ioo 0 1)
    (hwidth : A ≤ Real.log (B * 3) / 2)
    (hdisc : ∀ z : ℂ, 0 < ‖z - 1‖ → ‖z - 1‖ < α → meromorphicOrderAt Z z ≤ 0)
    (hzero : ∀ z : ℂ, 1 - A / Real.log (B * (|z.im| + 3)) < z.re →
      meromorphicOrderAt Z z ≤ 0) :
    ∃ C T₁ : ℝ, 0 < C ∧ ∀ z : ℂ, T₁ ≤ |z.im| →
      1 - α * (A / Real.log (B * (|z.im| + 3))) ≤ z.re →
      ‖logDeriv Z z‖ ≤ C * (Real.log |z.im|) ^ 2 := by
  have hS1 : ∀ s : halfPlane, Z s = finiteHeckeL (1 : U[F]) s := fun s ↦
    (hSeries s).trans (dedekindZeta_perron_left_bound_zeta s).symm
  obtain ⟨C, hC, hmain⟩ := finiteHeckeL_logDeriv_isBigO_of_zeroFree (1 : U[F]) Z Z hZ hS1
    hZ hSeries α hα.1 hα.2 hdisc
  obtain ⟨hmaps, hdiff, hanti, hderiv, hO⟩ :=
    dedekindZeta_perron_left_bound_width A B hA hB hwidth
  obtain ⟨-, hbig⟩ := hmain (fun t : ℝ ↦ A / Real.log (B * (t + 3))) hmaps hdiff hanti hderiv
    hO hzero
  rw [Asymptotics.isBigOWith_iff, eventually_inf_principal, eventually_comap,
    eventually_atTop] at hbig
  obtain ⟨T₁, hT₁⟩ := hbig
  refine ⟨C, T₁, hC, fun z hz hre ↦ ?_⟩
  have h := hT₁ |z.im| hz z rfl hre
  rwa [Real.norm_of_nonneg (sq_nonneg _)] at h

/-- Near a point where it is in normal form, the logarithmic derivative of a meromorphic
function is at most a constant times the inverse distance to that point. -/
private theorem dedekindZeta_perron_left_bound_local (Z : ℂ → ℂ) (p : ℂ)
    (hZ : MeromorphicNFAt Z p) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ᶠ z in 𝓝 p, z ≠ p → ‖logDeriv Z z‖ ≤ M / ‖z - p‖ := by
  rcases hZ with h0 | ⟨n, g, hg, hgp, hfg⟩
  · refine ⟨0, le_rfl, ?_⟩
    filter_upwards [logDeriv_congr_nhds h0] with z hz _
    rw [hz]
    simp [logDeriv_apply]
  · have hcont : ContinuousAt (fun z ↦ ‖logDeriv g z‖) p :=
      (hg.deriv.continuousAt.div hg.continuousAt hgp).norm
    have hbd : ∀ᶠ z in 𝓝 p, ‖logDeriv g z‖ < ‖logDeriv g p‖ + 1 :=
      hcont.eventually (gt_mem_nhds (lt_add_one _))
    refine ⟨|(n : ℝ)| + (‖logDeriv g p‖ + 1), by positivity, ?_⟩
    filter_upwards [logDeriv_congr_nhds hfg, hg.eventually_analyticAt,
      hg.continuousAt.eventually_ne hgp, hbd, Metric.ball_mem_nhds p one_pos]
      with z hz hga hgz hb hball hzp
    have hsub : z - p ≠ 0 := sub_ne_zero.mpr hzp
    have hd : DifferentiableAt ℂ (fun w : ℂ ↦ w - p) z := by fun_prop
    have h1 : logDeriv ((· - p) ^ n • g) z = n / (z - p) + logDeriv g z := by
      have hfun : ((· - p) ^ n • g : ℂ → ℂ) = (fun w : ℂ ↦ (w - p) ^ n) * g := by
        ext w
        simp
      rw [hfun, logDeriv_mul (f := fun w : ℂ ↦ (w - p) ^ n) (g := g) z (zpow_ne_zero n hsub)
        hgz (hd.zpow (Or.inl hsub)) hga.differentiableAt, logDeriv_fun_zpow hd n]
      congr 1
      simp [logDeriv_apply, div_eq_mul_inv]
    rw [hz, h1]
    have hdist : ‖z - p‖ < 1 := by simpa [dist_eq_norm] using hball
    have hpos : 0 < ‖z - p‖ := norm_pos_iff.mpr hsub
    have hn : ‖(n : ℂ) / (z - p)‖ = |(n : ℝ)| / ‖z - p‖ := by
      rw [norm_div, Complex.norm_intCast]
    have hg1 : ‖logDeriv g z‖ ≤ (‖logDeriv g p‖ + 1) / ‖z - p‖ := by
      rw [le_div_iff₀ hpos]
      nlinarith [norm_nonneg (logDeriv g z), norm_nonneg (logDeriv g p)]
    calc ‖(n : ℂ) / (z - p) + logDeriv g z‖
        ≤ ‖(n : ℂ) / (z - p)‖ + ‖logDeriv g z‖ := norm_add_le _ _
      _ ≤ |(n : ℝ)| / ‖z - p‖ + (‖logDeriv g p‖ + 1) / ‖z - p‖ := by
          rw [hn]
          linarith
      _ = (|(n : ℝ)| + (‖logDeriv g p‖ + 1)) / ‖z - p‖ := by ring

/-- Close to a segment of the line `Re z = 1` and to its left, the logarithmic derivative
of a meromorphic function in normal form is at most a constant times `1 / (1 - Re z)`. -/
private theorem dedekindZeta_perron_left_bound_tube (Z : ℂ → ℂ) (hZ : MeromorphicNFOn Z univ)
    (T₁ : ℝ) :
    ∃ M δ₀ : ℝ, 0 ≤ M ∧ 0 < δ₀ ∧ ∀ z : ℂ, 1 - δ₀ < z.re → z.re < 1 → |z.im| ≤ T₁ →
      ‖logDeriv Z z‖ ≤ M / (1 - z.re) := by
  have hcont : Continuous fun t : ℝ ↦ (⟨1, t⟩ : ℂ) := by
    rw [show (fun t : ℝ ↦ (⟨1, t⟩ : ℂ)) = fun t : ℝ ↦ ((1 : ℝ) : ℂ) + (t : ℂ) * Complex.I from
      funext fun t ↦ Complex.mk_eq_add_mul_I 1 t]
    fun_prop
  have hK : IsCompact ((fun t : ℝ ↦ (⟨1, t⟩ : ℂ)) '' Icc (-T₁) T₁) := isCompact_Icc.image hcont
  have hP : ∃ M : ℝ, 0 ≤ M ∧ ∀ᶠ z in 𝓝ˢ ((fun t : ℝ ↦ (⟨1, t⟩ : ℂ)) '' Icc (-T₁) T₁),
      z.re < 1 → ‖logDeriv Z z‖ ≤ M / (1 - z.re) := by
    refine hK.induction_on (p := fun S ↦ ∃ M : ℝ, 0 ≤ M ∧ ∀ᶠ z in 𝓝ˢ S,
      z.re < 1 → ‖logDeriv Z z‖ ≤ M / (1 - z.re)) ?_ ?_ ?_ ?_
    · exact ⟨0, le_rfl, by simp⟩
    · rintro S S' hSS' ⟨M, hM, h⟩
      exact ⟨M, hM, h.filter_mono (nhdsSet_mono hSS')⟩
    · rintro S S' ⟨M, hM, h⟩ ⟨M', hM', h'⟩
      refine ⟨max M M', hM.trans (le_max_left _ _), ?_⟩
      rw [nhdsSet_union, eventually_sup]
      constructor
      · filter_upwards [h] with z hz hre
        exact (hz hre).trans (div_le_div_of_nonneg_right (le_max_left _ _) (by linarith))
      · filter_upwards [h'] with z hz hre
        exact (hz hre).trans (div_le_div_of_nonneg_right (le_max_right _ _) (by linarith))
    · rintro p ⟨t, -, rfl⟩
      obtain ⟨M, hM, h⟩ := dedekindZeta_perron_left_bound_local Z ⟨1, t⟩ (hZ (mem_univ _))
      obtain ⟨U, hUsub, hUopen, hpU⟩ := eventually_nhds_iff.mp h
      refine ⟨_ ∩ U, inter_mem_nhdsWithin _ (hUopen.mem_nhds hpU), M, hM, ?_⟩
      have hU : U ∈ 𝓝ˢ (((fun t : ℝ ↦ (⟨1, t⟩ : ℂ)) '' Icc (-T₁) T₁) ∩ U) :=
        hUopen.mem_nhdsSet.mpr inter_subset_right
      filter_upwards [hU] with z hz hre
      have hne : z ≠ ⟨1, t⟩ := fun h ↦ by
        rw [h] at hre
        exact lt_irrefl _ hre
      have hle : 1 - z.re ≤ ‖z - ⟨1, t⟩‖ := by
        have h1 := Complex.abs_re_le_norm (z - ⟨1, t⟩)
        rw [Complex.sub_re] at h1
        have h2 := neg_abs_le (z.re - 1)
        change -|z.re - 1| ≤ z.re - 1 at h2
        change |z.re - 1| ≤ _ at h1
        linarith
      exact (hUsub z hz hne).trans (div_le_div_of_nonneg_left hM (by linarith) hle)
  obtain ⟨M, hM, h⟩ := hP
  obtain ⟨U, hUopen, hKU, hUsub⟩ := mem_nhdsSet_iff_exists.mp h
  obtain ⟨δ₀, hδ₀, hthick⟩ := hK.exists_thickening_subset_open hUopen hKU
  refine ⟨M, δ₀, hM, hδ₀, fun z h1 h2 h3 ↦ ?_⟩
  refine hUsub (hthick ?_) h2
  rw [Metric.mem_thickening_iff]
  refine ⟨⟨1, z.im⟩, ⟨z.im, abs_le.mp h3, rfl⟩, ?_⟩
  rw [Complex.dist_of_im_eq (z := z) (w := ⟨1, z.im⟩) rfl, Real.dist_eq]
  change |z.re - 1| < δ₀
  rw [abs_of_neg (by linarith)]
  linarith

/-- The integral of `1 / √(δ² + y²)` over a symmetric interval is at most a logarithm. -/
private theorem dedekindZeta_perron_left_bound_integral {δ T : ℝ} (hδ : 0 < δ) (hT : 0 < T) :
    Continuous (fun y : ℝ ↦ 1 / √(δ ^ 2 + y ^ 2)) ∧
      ∫ y in -T..T, 1 / √(δ ^ 2 + y ^ 2) ≤ 2 * Real.log ((2 * T + δ) / δ) := by
  have hcont : Continuous fun y : ℝ ↦ 1 / √(δ ^ 2 + y ^ 2) := by
    refine continuous_const.div
      (Real.continuous_sqrt.comp (continuous_const.add (continuous_pow 2))) fun y ↦ ?_
    exact (Real.sqrt_pos.mpr (by positivity)).ne'
  refine ⟨hcont, ?_⟩
  have hG : ∀ y ∈ uIcc (-T) T, HasDerivAt (fun y : ℝ ↦ Real.log (y + √(δ ^ 2 + y ^ 2)))
      (1 / √(δ ^ 2 + y ^ 2)) y := by
    intro y _
    have hpos : 0 < δ ^ 2 + y ^ 2 := by positivity
    have hr : 0 < √(δ ^ 2 + y ^ 2) := Real.sqrt_pos.mpr hpos
    have habsy : |y| < √(δ ^ 2 + y ^ 2) := by
      rw [Real.lt_sqrt (abs_nonneg y), sq_abs]
      linarith [pow_pos hδ 2]
    have hyr : 0 < y + √(δ ^ 2 + y ^ 2) := by linarith [neg_abs_le y]
    have h1 : HasDerivAt (fun y : ℝ ↦ δ ^ 2 + y ^ 2) (2 * y) y := by
      simpa using (hasDerivAt_pow 2 y).const_add (δ ^ 2)
    have hs : HasDerivAt (fun y : ℝ ↦ √(δ ^ 2 + y ^ 2)) (y / √(δ ^ 2 + y ^ 2)) y := by
      have h := h1.rpow_const (p := 1 / 2) (Or.inl hpos.ne')
      have hfun : (fun y : ℝ ↦ √(δ ^ 2 + y ^ 2)) =
          fun y : ℝ ↦ (δ ^ 2 + y ^ 2) ^ (1 / 2 : ℝ) := funext fun y ↦ Real.sqrt_eq_rpow _
      rw [hfun]
      refine h.congr_deriv ?_
      rw [Real.sqrt_eq_rpow, Real.rpow_sub hpos, Real.rpow_one]
      obtain ⟨r, hrdef⟩ : ∃ r : ℝ, r = (δ ^ 2 + y ^ 2) ^ (1 / 2 : ℝ) := ⟨_, rfl⟩
      have hrpos : 0 < r := hrdef ▸ Real.rpow_pos_of_pos hpos _
      have hX : δ ^ 2 + y ^ 2 = r * r := by
        rw [hrdef, ← Real.rpow_add hpos]
        norm_num
      rw [← hrdef, hX]
      field_simp
    have h2 : HasDerivAt (fun y : ℝ ↦ Real.log (y + √(δ ^ 2 + y ^ 2)))
        ((1 + y / √(δ ^ 2 + y ^ 2)) / (y + √(δ ^ 2 + y ^ 2))) y :=
      ((hasDerivAt_id' y).add hs).log hyr.ne'
    refine h2.congr_deriv ?_
    have hr' := hr.ne'
    have hyr' := hyr.ne'
    rw [div_eq_div_iff hyr' hr']
    field_simp
    ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hG (hcont.intervalIntegrable _ _), neg_sq]
  have hr : √(δ ^ 2 + T ^ 2) ≤ T + δ :=
    Real.sqrt_le_iff.mpr ⟨by linarith, by nlinarith⟩
  have hrT : T < √(δ ^ 2 + T ^ 2) :=
    (Real.lt_sqrt hT.le).mpr (by linarith [pow_pos hδ 2])
  have hsq : √(δ ^ 2 + T ^ 2) ^ 2 = δ ^ 2 + T ^ 2 := Real.sq_sqrt (by positivity)
  have hlow : δ ^ 2 / (2 * T + δ) ≤ -T + √(δ ^ 2 + T ^ 2) := by
    rw [div_le_iff₀ (by linarith)]
    nlinarith [mul_le_mul_of_nonneg_left
      (show √(δ ^ 2 + T ^ 2) + T ≤ 2 * T + δ by linarith)
      (show 0 ≤ √(δ ^ 2 + T ^ 2) - T by linarith)]
  have h1 : Real.log (T + √(δ ^ 2 + T ^ 2)) ≤ Real.log (2 * T + δ) :=
    Real.log_le_log (by linarith) (by linarith)
  have h2 : Real.log (δ ^ 2 / (2 * T + δ)) ≤ Real.log (-T + √(δ ^ 2 + T ^ 2)) :=
    Real.log_le_log (div_pos (pow_pos hδ 2) (by linarith)) hlow
  rw [Real.log_div (pow_pos hδ 2).ne' (by linarith), Real.log_pow] at h2
  rw [Real.log_div (by linarith) hδ.ne']
  push_cast at h2
  linarith

/-- The scalar inequality behind the cubed logarithm: a bound of size
`M / δ + C₁ (log h)²` times the logarithmic length of the edge. -/
private theorem dedekindZeta_perron_left_bound_scalar {M C₁ K₁ δ T h : ℝ} (hM : 0 ≤ M)
    (hC₁ : 0 < C₁) (hK₁ : 0 < K₁) (hδ : 0 < δ) (hT : 0 < T) (hTh : T ≤ h)
    (hL1 : 1 ≤ Real.log h) (hinvδ : 1 / δ ≤ K₁ * Real.log h) :
    (M / δ + C₁ * (Real.log h) ^ 2) * (2 * Real.log ((2 * T + δ) / δ)) ≤
      2 * (Real.log (2 * K₁ + 1) + 2) * (M * K₁ + C₁) * (Real.log h) ^ 3 := by
  have hh0 : 0 < h := hT.trans_le hTh
  have hLh : Real.log h ≤ h := (Real.log_le_sub_one_of_pos hh0).trans (by linarith)
  have h1h : 1 ≤ h := hL1.trans hLh
  have hlogK : 0 ≤ Real.log (2 * K₁ + 1) := Real.log_nonneg (by linarith)
  have hratio : (2 * T + δ) / δ ≤ (2 * K₁ + 1) * h ^ 2 := by
    have h1 : (2 * T + δ) / δ = 2 * T * (1 / δ) + 1 := by
      field_simp
    have h2 : 2 * T * (1 / δ) ≤ 2 * h * (K₁ * h) :=
      mul_le_mul (by linarith) (hinvδ.trans (mul_le_mul_of_nonneg_left hLh hK₁.le))
        (by positivity) (by linarith)
    rw [h1]
    nlinarith [mul_le_mul h1h h1h zero_le_one hh0.le]
  have hlogratio : Real.log ((2 * T + δ) / δ) ≤
      (Real.log (2 * K₁ + 1) + 2) * Real.log h := by
    have h1 : Real.log ((2 * T + δ) / δ) ≤ Real.log ((2 * K₁ + 1) * h ^ 2) :=
      Real.log_le_log (div_pos (by linarith) hδ) hratio
    rw [Real.log_mul (by linarith) (pow_pos hh0 2).ne', Real.log_pow] at h1
    push_cast at h1
    nlinarith [mul_nonneg hlogK (sub_nonneg.mpr hL1)]
  have hbL : M / δ + C₁ * (Real.log h) ^ 2 ≤ (M * K₁ + C₁) * (Real.log h) ^ 2 := by
    have h1 : M / δ ≤ M * (K₁ * Real.log h) := by
      rw [div_eq_mul_one_div]
      exact mul_le_mul_of_nonneg_left hinvδ hM
    have h2 : Real.log h ≤ (Real.log h) ^ 2 := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left h2 (mul_nonneg hM hK₁.le)]
  have hb0 : 0 ≤ M / δ + C₁ * (Real.log h) ^ 2 :=
    add_nonneg (div_nonneg hM hδ.le) (mul_nonneg hC₁.le (sq_nonneg _))
  have hK2L : 0 ≤ 2 * ((Real.log (2 * K₁ + 1) + 2) * Real.log h) :=
    mul_nonneg zero_le_two (mul_nonneg (by linarith) (by linarith))
  calc (M / δ + C₁ * (Real.log h) ^ 2) * (2 * Real.log ((2 * T + δ) / δ))
      ≤ (M / δ + C₁ * (Real.log h) ^ 2) *
        (2 * ((Real.log (2 * K₁ + 1) + 2) * Real.log h)) :=
        mul_le_mul_of_nonneg_left (by linarith) hb0
    _ ≤ (M * K₁ + C₁) * (Real.log h) ^ 2 *
        (2 * ((Real.log (2 * K₁ + 1) + 2) * Real.log h)) :=
        mul_le_mul_of_nonneg_right hbL hK2L
    _ = 2 * (Real.log (2 * K₁ + 1) + 2) * (M * K₁ + C₁) * (Real.log h) ^ 3 := by ring

-- TODO(paper-gap): The proof of (B.7.1.12) bounds the raw logarithmic derivative
-- on a region containing its pole. Subtract the principal part before using
-- compactness, and use the maximum absolute shifted height on the rectangle.

/-- Paper: Equation (B.7.1.12), p. 647. The integral along the left edge is
bounded by the cutoff to the power `-δ` times a cubed logarithm.
Deviation: The width `δ` uses the maximum absolute shifted height. The
estimate allows the unregularized logarithmic derivative to contribute a
term of order `1 / δ` near its pole. The punctured disc is the hypothesis
on `α` in Theorem B.6.1.3. Both constants may depend on the chosen width. -/
theorem dedekindZeta_perron_left_bound (Z : ℂ → ℂ) (hZ : MeromorphicNFOn Z univ)
    (hSeries : ∀ s : halfPlane, Z s = dedekindZeta F s)
    {A B α : ℝ} (hA : 0 < A) (hB : 1 / 3 < B) (hα : α ∈ Ioo 0 1)
    (hwidth : A ≤ Real.log (B * 3) / 2)
    (hdisc : ∀ z : ℂ, 0 < ‖z - 1‖ → ‖z - 1‖ < α → meromorphicOrderAt Z z ≤ 0)
    (hzero : ∀ z : ℂ, 1 - A / Real.log (B * (|z.im| + 3)) < z.re →
      meromorphicOrderAt Z z ≤ 0) :
    ∃ C T₀ : ℝ, 0 < C ∧ 2 ≤ T₀ ∧ ∀ (s : ℂ) (t₀ x T : ℝ),
      s ∈ oneLine → 1 ≤ x → T₀ + |s.im - t₀| ≤ T →
      let height := T + |s.im - t₀| + 3
      let δ := α * A / Real.log (B * height)
      ‖∫ y in -T..T, logDeriv Z (s - Complex.I * t₀ + ⟨-δ, y⟩) *
        (x : ℂ) ^ (⟨-δ, y⟩ : ℂ) / (⟨-δ, y⟩ : ℂ)‖ ≤
        C * x ^ (-δ) * (Real.log height) ^ 3 := by
  obtain ⟨C₁, T₁, hC₁, hbound⟩ := dedekindZeta_perron_left_bound_logDeriv Z hZ hSeries
    hA hB hα hwidth hdisc hzero
  obtain ⟨M, δ₀, hM, hδ₀, htube⟩ := dedekindZeta_perron_left_bound_tube Z hZ (max T₁ 1)
  have hB0 : 0 < B := by linarith
  have hαA : 0 < α * A := mul_pos hα.1 hA
  obtain ⟨K₁, hK₁⟩ : ∃ K₁ : ℝ, K₁ = (|Real.log B| + 1) / (α * A) := ⟨_, rfl⟩
  have hK₁pos : 0 < K₁ := by
    rw [hK₁]
    exact div_pos (by linarith [abs_nonneg (Real.log B)]) hαA
  have hlogK : 0 ≤ Real.log (2 * K₁ + 1) := Real.log_nonneg (by linarith)
  have hMK : 0 < M * K₁ + C₁ := by linarith [mul_nonneg hM hK₁pos.le]
  refine ⟨2 * (Real.log (2 * K₁ + 1) + 2) * (M * K₁ + C₁),
    max 2 (max (Real.exp 1) (Real.exp (α * A / δ₀) / B)),
    mul_pos (mul_pos two_pos (by linarith)) hMK, le_max_left _ _, ?_⟩
  intro s t₀ x T hs hx hT height δ
  have hh : height = T + |s.im - t₀| + 3 := rfl
  have hδ : δ = α * A / Real.log (B * height) := rfl
  clear_value δ height
  have hs1 : s.re = 1 := hs
  have hx0 : 0 < x := zero_lt_one.trans_le hx
  have hD : 0 ≤ |s.im - t₀| := abs_nonneg _
  have hT2 : 2 ≤ T := by
    linarith [le_max_left 2 (max (Real.exp 1) (Real.exp (α * A / δ₀) / B))]
  have hTe : Real.exp 1 ≤ T := by
    linarith [le_max_right 2 (max (Real.exp 1) (Real.exp (α * A / δ₀) / B)),
      le_max_left (Real.exp 1) (Real.exp (α * A / δ₀) / B)]
  have hTB : Real.exp (α * A / δ₀) / B ≤ T := by
    linarith [le_max_right 2 (max (Real.exp 1) (Real.exp (α * A / δ₀) / B)),
      le_max_right (Real.exp 1) (Real.exp (α * A / δ₀) / B)]
  have hT0 : 0 < T := by linarith
  have hh0 : 0 < height := by linarith
  have hL1 : 1 ≤ Real.log height := by
    rw [Real.le_log_iff_exp_le hh0]
    linarith
  have hl3 : 0 < Real.log (B * 3) := Real.log_pos (by linarith)
  have hlogBh : Real.log (B * 3) ≤ Real.log (B * height) :=
    Real.log_le_log (by positivity) (mul_le_mul_of_nonneg_left (by linarith) hB0.le)
  have hlogBh0 : 0 < Real.log (B * height) := by linarith
  have hδpos : 0 < δ := hδ ▸ div_pos hαA hlogBh0
  have hδlt : δ < δ₀ := by
    have h0 : B * height = T * B + B * (|s.im - t₀| + 3) := by
      rw [hh]
      ring
    have h1 : Real.exp (α * A / δ₀) < B * height := by
      have h2 := (div_le_iff₀ hB0).mp hTB
      have h3 : 0 < B * (|s.im - t₀| + 3) := mul_pos hB0 (by linarith)
      linarith
    have h2 : α * A / δ₀ < Real.log (B * height) :=
      (Real.lt_log_iff_exp_lt (mul_pos hB0 hh0)).mpr h1
    rw [div_lt_iff₀ hδ₀] at h2
    rw [hδ, div_lt_iff₀ hlogBh0]
    linarith
  have hinvδ : 1 / δ ≤ K₁ * Real.log height := by
    have h1 : 1 / δ = Real.log (B * height) / (α * A) := by
      rw [hδ, one_div_div]
    have h2 : Real.log (B * height) ≤ (|Real.log B| + 1) * Real.log height := by
      rw [Real.log_mul hB0.ne' hh0.ne']
      nlinarith [le_abs_self (Real.log B), mul_nonneg (abs_nonneg (Real.log B))
        (sub_nonneg.mpr hL1)]
    rw [h1, hK₁, div_mul_eq_mul_div]
    exact div_le_div_of_nonneg_right h2 hαA.le
  have hxδ : 0 ≤ x ^ (-δ) := (Real.rpow_pos_of_pos hx0 _).le
  have hpt : ∀ y : ℝ, y ∈ Ioc (-T) T →
      ‖logDeriv Z (s - Complex.I * t₀ + ⟨-δ, y⟩) * (x : ℂ) ^ (⟨-δ, y⟩ : ℂ) /
        (⟨-δ, y⟩ : ℂ)‖ ≤
        (M / δ + C₁ * (Real.log height) ^ 2) * x ^ (-δ) * (1 / √(δ ^ 2 + y ^ 2)) := by
    intro y hy
    have hre : (s - Complex.I * t₀ + ⟨-δ, y⟩ : ℂ).re = 1 - δ := by
      simp [hs1, sub_eq_add_neg]
    have him : (s - Complex.I * t₀ + ⟨-δ, y⟩ : ℂ).im = s.im - t₀ + y := by
      simp
    have habs : |s.im - t₀ + y| ≤ T + |s.im - t₀| := by
      have h1 := abs_add_le (s.im - t₀) y
      have h2 : |y| ≤ T := abs_le.mpr ⟨hy.1.le, hy.2⟩
      linarith
    have hb : ‖logDeriv Z (s - Complex.I * t₀ + ⟨-δ, y⟩)‖ ≤
        M / δ + C₁ * (Real.log height) ^ 2 := by
      have hMδ : 0 ≤ M / δ := div_nonneg hM hδpos.le
      have hCL : 0 ≤ C₁ * (Real.log height) ^ 2 := mul_nonneg hC₁.le (sq_nonneg _)
      rcases le_or_gt (max T₁ 1) |s.im - t₀ + y| with hbig | hsmall
      · have h1 : (1 : ℝ) ≤ |s.im - t₀ + y| := (le_max_right _ _).trans hbig
        have hlogle : Real.log (B * (|s.im - t₀ + y| + 3)) ≤ Real.log (B * height) :=
          Real.log_le_log (by positivity)
            (mul_le_mul_of_nonneg_left (by linarith) hB0.le)
        have hlogpos : 0 < Real.log (B * (|s.im - t₀ + y| + 3)) :=
          hl3.trans_le (Real.log_le_log (by positivity)
            (mul_le_mul_of_nonneg_left (by linarith) hB0.le))
        have hδle : δ ≤ α * (A / Real.log (B * (|s.im - t₀ + y| + 3))) := by
          rw [hδ, ← mul_div_assoc]
          exact div_le_div_of_nonneg_left hαA.le hlogpos hlogle
        have h := hbound (s - Complex.I * t₀ + ⟨-δ, y⟩)
          (by rw [him]; exact (le_max_left _ _).trans hbig) (by rw [hre, him]; linarith)
        rw [him] at h
        have hℓ0 : 0 ≤ Real.log |s.im - t₀ + y| := Real.log_nonneg h1
        have hℓle : Real.log |s.im - t₀ + y| ≤ Real.log height :=
          Real.log_le_log (by linarith) (by linarith)
        have hsq : (Real.log |s.im - t₀ + y|) ^ 2 ≤ (Real.log height) ^ 2 :=
          pow_le_pow_left₀ hℓ0 hℓle 2
        calc ‖logDeriv Z (s - Complex.I * t₀ + ⟨-δ, y⟩)‖
            ≤ C₁ * (Real.log |s.im - t₀ + y|) ^ 2 := h
          _ ≤ C₁ * (Real.log height) ^ 2 := mul_le_mul_of_nonneg_left hsq hC₁.le
          _ ≤ M / δ + C₁ * (Real.log height) ^ 2 := le_add_of_nonneg_left hMδ
      · have h := htube (s - Complex.I * t₀ + ⟨-δ, y⟩) (by rw [hre]; linarith)
          (by rw [hre]; linarith) (by rw [him]; exact hsmall.le)
        rw [hre, sub_sub_cancel] at h
        exact h.trans (le_add_of_nonneg_right hCL)
    have hn : ‖(⟨-δ, y⟩ : ℂ)‖ = √(δ ^ 2 + y ^ 2) := by
      rw [Complex.norm_eq_sqrt_sq_add_sq]
      change √((-δ) ^ 2 + y ^ 2) = _
      rw [neg_sq]
    rw [norm_div, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx0,
      show (⟨-δ, y⟩ : ℂ).re = -δ from rfl, hn, div_eq_mul_one_div]
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hb hxδ)
      (one_div_nonneg.mpr (Real.sqrt_nonneg _))
  obtain ⟨hcont, hI⟩ := dedekindZeta_perron_left_bound_integral hδpos hT0
  have hb0 : 0 ≤ (M / δ + C₁ * (Real.log height) ^ 2) * x ^ (-δ) :=
    mul_nonneg (add_nonneg (div_nonneg hM hδpos.le) (mul_nonneg hC₁.le (sq_nonneg _))) hxδ
  have hle : ‖∫ y in -T..T, logDeriv Z (s - Complex.I * t₀ + ⟨-δ, y⟩) *
      (x : ℂ) ^ (⟨-δ, y⟩ : ℂ) / (⟨-δ, y⟩ : ℂ)‖ ≤
      ∫ y in -T..T,
        (M / δ + C₁ * (Real.log height) ^ 2) * x ^ (-δ) * (1 / √(δ ^ 2 + y ^ 2)) :=
    intervalIntegral.norm_integral_le_of_norm_le (by linarith : -T ≤ T)
      (Eventually.of_forall hpt) ((continuous_const.mul hcont).intervalIntegrable _ _)
  rw [intervalIntegral.integral_const_mul] at hle
  have hscalar := dedekindZeta_perron_left_bound_scalar hM hC₁ hK₁pos hδpos hT0
    (show T ≤ height by linarith) hL1 hinvδ
  calc ‖∫ y in -T..T, logDeriv Z (s - Complex.I * t₀ + ⟨-δ, y⟩) *
        (x : ℂ) ^ (⟨-δ, y⟩ : ℂ) / (⟨-δ, y⟩ : ℂ)‖
      ≤ (M / δ + C₁ * (Real.log height) ^ 2) * x ^ (-δ) *
        ∫ y in -T..T, 1 / √(δ ^ 2 + y ^ 2) := hle
    _ ≤ (M / δ + C₁ * (Real.log height) ^ 2) * x ^ (-δ) *
        (2 * Real.log ((2 * T + δ) / δ)) := mul_le_mul_of_nonneg_left hI hb0
    _ = (M / δ + C₁ * (Real.log height) ^ 2) * (2 * Real.log ((2 * T + δ) / δ)) *
        x ^ (-δ) := by ring
    _ ≤ 2 * (Real.log (2 * K₁ + 1) + 2) * (M * K₁ + C₁) * (Real.log height) ^ 3 *
        x ^ (-δ) := mul_le_mul_of_nonneg_right hscalar hxδ
    _ = 2 * (Real.log (2 * K₁ + 1) + 2) * (M * K₁ + C₁) * x ^ (-δ) *
        (Real.log height) ^ 3 := by ring

/-- Paper: Equations (B.7.1.13)–(B.7.1.14), p. 647. On either horizontal
edge the squared logarithm of its shifted height controls the integral.
Deviation: Each edge uses its own absolute shifted height. The contour
width uses the maximum of both heights, and the estimate starts at a
sufficiently large height for the logarithmic-derivative estimate of §B.6.
The punctured disc is its hypothesis on `α`. Both constants may depend on the width. -/
theorem dedekindZeta_perron_horizontal_bound (Z : ℂ → ℂ) (hZ : MeromorphicNFOn Z univ)
    (hSeries : ∀ s : halfPlane, Z s = dedekindZeta F s)
    {A B α : ℝ} (hA : 0 < A) (hB : 1 / 3 < B) (hα : α ∈ Ioo 0 1)
    (hwidth : A ≤ Real.log (B * 3) / 2)
    (hdisc : ∀ z : ℂ, 0 < ‖z - 1‖ → ‖z - 1‖ < α → meromorphicOrderAt Z z ≤ 0)
    (hzero : ∀ z : ℂ, 1 - A / Real.log (B * (|z.im| + 3)) < z.re →
      meromorphicOrderAt Z z ≤ 0) :
    ∃ C T₀ : ℝ, 0 < C ∧ 2 ≤ T₀ ∧ ∀ (s : ℂ) (t₀ x c T y : ℝ),
      s ∈ oneLine → 1 < x → 0 < c → T₀ + |s.im - t₀| ≤ T → (y = -T ∨ y = T) →
      let δ := α * A / Real.log (B * (T + |s.im - t₀| + 3))
      ‖∫ u in -δ..c, logDeriv Z (s - Complex.I * t₀ + ⟨u, y⟩) *
        (x : ℂ) ^ (⟨u, y⟩ : ℂ) / (⟨u, y⟩ : ℂ)‖ ≤
        C * x ^ c * (Real.log (|s.im - t₀ + y| + 3)) ^ 2 / (T * Real.log x) := by
  obtain ⟨C, T₁, hC, hbound⟩ := dedekindZeta_perron_left_bound_logDeriv Z hZ hSeries
    hA hB hα hwidth hdisc hzero
  refine ⟨C, max 2 T₁, hC, le_max_left _ _, ?_⟩
  intro s t₀ x c T y hs hx hc hT hy δ
  have hs1 : s.re = 1 := hs
  have hx0 : 0 < x := zero_lt_one.trans hx
  have hlogx : 0 < Real.log x := Real.log_pos hx
  have hD : 0 ≤ |s.im - t₀| := abs_nonneg _
  have hT2 : 2 + |s.im - t₀| ≤ T := (add_le_add_left (le_max_left 2 T₁) _).trans hT
  have hTT₁ : T₁ + |s.im - t₀| ≤ T := (add_le_add_left (le_max_right 2 T₁) _).trans hT
  have hT0 : 0 < T := by linarith
  have hyT : |y| = T := by
    rcases hy with rfl | rfl
    · rw [abs_neg, abs_of_pos hT0]
    · exact abs_of_pos hT0
  have hlo : T - |s.im - t₀| ≤ |s.im - t₀ + y| := by
    have h1 := abs_sub_abs_le_abs_sub y (-(s.im - t₀))
    rw [abs_neg, sub_neg_eq_add, hyT, add_comm y] at h1
    exact h1
  have hhi : |s.im - t₀ + y| ≤ T + |s.im - t₀| := by
    have h1 := abs_add_le (s.im - t₀) y
    rw [hyT] at h1
    linarith
  have hB0 : 0 < B := by linarith
  have hl3 : 0 < Real.log (B * 3) := Real.log_pos (by linarith)
  have hlogh : Real.log (B * 3) ≤ Real.log (B * (|s.im - t₀ + y| + 3)) :=
    Real.log_le_log (by positivity) (by nlinarith [abs_nonneg (s.im - t₀ + y)])
  have hlogle : Real.log (B * (|s.im - t₀ + y| + 3)) ≤
      Real.log (B * (T + |s.im - t₀| + 3)) :=
    Real.log_le_log (by positivity) (by nlinarith)
  have hδpos : 0 < δ := div_pos (mul_pos hα.1 hA) (by linarith)
  have hδle : δ ≤ α * (A / Real.log (B * (|s.im - t₀ + y| + 3))) := by
    rw [← mul_div_assoc]
    exact div_le_div_of_nonneg_left (mul_pos hα.1 hA).le (by linarith) hlogle
  have hℓ0 : 0 ≤ Real.log |s.im - t₀ + y| := Real.log_nonneg (by linarith)
  have hℓle : Real.log |s.im - t₀ + y| ≤ Real.log (|s.im - t₀ + y| + 3) :=
    Real.log_le_log (by linarith) (by linarith)
  have hpt : ∀ u : ℝ, u ∈ Ioc (-δ) c →
      ‖logDeriv Z (s - Complex.I * t₀ + ⟨u, y⟩) * (x : ℂ) ^ (⟨u, y⟩ : ℂ) / (⟨u, y⟩ : ℂ)‖ ≤
        C * (Real.log |s.im - t₀ + y|) ^ 2 / T * x ^ u := by
    intro u hu
    have hre : (s - Complex.I * t₀ + ⟨u, y⟩ : ℂ).re = 1 + u := by
      simp [hs1]
    have him : (s - Complex.I * t₀ + ⟨u, y⟩ : ℂ).im = s.im - t₀ + y := by
      simp
    have hb := hbound (s - Complex.I * t₀ + ⟨u, y⟩) (by rw [him]; linarith)
      (by rw [hre, him]; linarith [hu.1])
    rw [him] at hb
    have hn : T ≤ ‖(⟨u, y⟩ : ℂ)‖ := by
      have := Complex.abs_im_le_norm (⟨u, y⟩ : ℂ)
      rwa [show (⟨u, y⟩ : ℂ).im = y from rfl, hyT] at this
    rw [norm_div, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx0,
      show (⟨u, y⟩ : ℂ).re = u from rfl, mul_div_right_comm]
    have hxu : 0 ≤ x ^ u := (Real.rpow_pos_of_pos hx0 u).le
    refine mul_le_mul_of_nonneg_right ?_ hxu
    exact div_le_div₀ (mul_nonneg hC.le (sq_nonneg _)) hb hT0 hn
  have hderiv : ∀ u ∈ uIcc (-δ) c, HasDerivAt
      (fun u : ℝ ↦ C * (Real.log |s.im - t₀ + y|) ^ 2 / T * (x ^ u / Real.log x))
      (C * (Real.log |s.im - t₀ + y|) ^ 2 / T * x ^ u) u := by
    intro u _
    have h1 := (Real.hasStrictDerivAt_const_rpow hx0 u).hasDerivAt.div_const (Real.log x)
    rw [mul_div_cancel_right₀ _ hlogx.ne'] at h1
    exact h1.const_mul _
  have hcont : Continuous fun u : ℝ ↦ C * (Real.log |s.im - t₀ + y|) ^ 2 / T * x ^ u :=
    continuous_const.mul (Real.continuous_const_rpow hx0.ne')
  have hint := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
    (hcont.intervalIntegrable _ _)
  have hle : ‖∫ u in -δ..c, logDeriv Z (s - Complex.I * t₀ + ⟨u, y⟩) *
      (x : ℂ) ^ (⟨u, y⟩ : ℂ) / (⟨u, y⟩ : ℂ)‖ ≤
      ∫ u in -δ..c, C * (Real.log |s.im - t₀ + y|) ^ 2 / T * x ^ u :=
    intervalIntegral.norm_integral_le_of_norm_le (by linarith : -δ ≤ c)
      (Eventually.of_forall hpt) (hcont.intervalIntegrable (-δ) c)
  rw [hint] at hle
  refine hle.trans ?_
  have hxδ : 0 ≤ x ^ (-δ) := (Real.rpow_pos_of_pos hx0 _).le
  have hxc : 0 ≤ x ^ c := (Real.rpow_pos_of_pos hx0 _).le
  have hK : 0 ≤ C * (Real.log |s.im - t₀ + y|) ^ 2 / T :=
    div_nonneg (mul_nonneg hC.le (sq_nonneg _)) hT0.le
  have hsq : (Real.log |s.im - t₀ + y|) ^ 2 ≤ (Real.log (|s.im - t₀ + y| + 3)) ^ 2 :=
    pow_le_pow_left₀ hℓ0 hℓle 2
  calc C * (Real.log |s.im - t₀ + y|) ^ 2 / T * (x ^ c / Real.log x) -
        C * (Real.log |s.im - t₀ + y|) ^ 2 / T * (x ^ (-δ) / Real.log x)
      ≤ C * (Real.log |s.im - t₀ + y|) ^ 2 / T * (x ^ c / Real.log x) :=
        sub_le_self _ (mul_nonneg hK (div_nonneg hxδ hlogx.le))
    _ = C * x ^ c * (Real.log |s.im - t₀ + y|) ^ 2 / (T * Real.log x) := by
        field_simp
    _ ≤ C * x ^ c * (Real.log (|s.im - t₀ + y| + 3)) ^ 2 / (T * Real.log x) :=
        div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left hsq (mul_nonneg hC.le hxc)) (mul_pos hT0 hlogx).le

/-- An explicit logarithmic majorant for the twisted von Mangoldt coefficients,
with the growth of the majorant itself exposed. -/
private theorem heckeLDP_majorant_explicit (χ : U[F]) :
    ∃ ψ : ℕ → ℝ, (∀ n, 0 < ψ n) ∧ Monotone ψ ∧
      (heckeLogDerivCoefficient (ideleClassNormTwist χ 0) =O[atTop] ψ) ∧
      ((fun σ : ℝ ↦ ∑' n : ℕ,
          ‖LSeries.term (heckeLogDerivCoefficient (ideleClassNormTwist χ 0)) (σ : ℂ) n‖)
        =O[𝓝[>] 1] (fun σ : ℝ ↦ (σ - 1)⁻¹)) ∧
      ∃ K : ℝ, 0 ≤ K ∧ ∀ n, ψ n ≤ K * (Real.log ((n : ℝ) + 2) + 1) := by
  obtain ⟨_, _, _, _, habs⟩ := heckeLDP_majorant χ
  obtain ⟨C, hC, hbound⟩ := heckeLogDerivCoefficient_bound (Module.finrank ℚ F)
  have hbF := hbound F rfl
  let ψ : ℕ → ℝ := fun n ↦ C * Real.log (n + 2) + 1
  have hψ : ∀ n, 0 < ψ n := fun n ↦ by
    dsimp [ψ]
    have : 0 ≤ Real.log (n + 2) :=
      Real.log_nonneg (by exact_mod_cast (show 1 ≤ n + 2 by omega))
    linarith [mul_nonneg hC.le this]
  have hmono : Monotone ψ := by
    intro a b hab
    dsimp [ψ]
    gcongr <;> linarith
  have hcoeff : heckeLogDerivCoefficient (ideleClassNormTwist χ 0) =O[atTop] ψ := by
    apply Asymptotics.IsBigO.of_bound 1
    filter_upwards [hbF, eventually_ge_atTop 2] with m hm hm2
    rw [one_mul, Real.norm_of_nonneg (hψ m).le]
    calc ‖heckeLogDerivCoefficient (ideleClassNormTwist χ 0) m‖
        ≤ C * Real.log m := hm χ
      _ ≤ C * Real.log (m + 2) :=
        mul_le_mul_of_nonneg_left (Real.log_le_log (by positivity) (by linarith)) hC.le
      _ ≤ ψ m := by dsimp [ψ]; linarith
  refine ⟨ψ, hψ, hmono, hcoeff, habs, max C 1, by positivity, fun n ↦ ?_⟩
  dsimp only [ψ]
  have hl : 0 ≤ Real.log ((n : ℝ) + 2) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ n + 2 by omega))
  have h1 : C * Real.log ((n : ℝ) + 2) ≤ max C 1 * Real.log ((n : ℝ) + 2) :=
    mul_le_mul_of_nonneg_right (le_max_left _ _) hl
  have h2 : (1 : ℝ) ≤ max C 1 := le_max_right _ _
  linarith

/-- The cutoff polynomial is the half-weighted Perron sum plus the half-endpoint
correction at an integer cutoff. -/
private theorem heckeLDP_poly_half (χ : U[F]) (x : ℝ) (hx : 1 ≤ x) (s : ℂ) :
    heckeLogDerivPolynomial χ x s -
        (if (⌊x⌋₊ : ℝ) = x then
          LSeries.term (heckeLogDerivCoefficient (ideleClassNormTwist χ 0)) s ⌊x⌋₊ / 2
         else 0) =
      perronHalfWeightedSum (heckeLogDerivCoefficient (ideleClassNormTwist χ 0)) s x := by
  classical
  let a := heckeLogDerivCoefficient (ideleClassNormTwist χ 0)
  simp only [heckeLogDerivPolynomial, perronHalfWeightedSum, a]
  have hkey : (if (⌊x⌋₊ : ℝ) = x then LSeries.term a s ⌊x⌋₊ / 2 else 0) =
      ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, if (n : ℝ) = x then LSeries.term a s n / 2 else 0 := by
    by_cases hxint : (⌊x⌋₊ : ℝ) = x
    · simp only [hxint, ite_true]
      have hmem : ⌊x⌋₊ ∈ Finset.Icc 1 ⌊x⌋₊ := by
        refine Finset.mem_Icc.mpr ⟨?_, le_rfl⟩
        have : 1 ≤ (⌊x⌋₊ : ℝ) := by rw [hxint]; exact hx
        exact_mod_cast this
      have hcast : (∑ n ∈ Finset.Icc 1 ⌊x⌋₊,
          if (n : ℝ) = x then LSeries.term a s n / 2 else 0) =
          ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, if n = ⌊x⌋₊ then LSeries.term a s n / 2 else 0 := by
        apply Finset.sum_congr rfl; intro n _
        have hcond : ((n : ℝ) = x) = (n = ⌊x⌋₊) := by
          apply propext; constructor
          · intro h; exact_mod_cast (by linarith [hxint] : (n : ℝ) = (⌊x⌋₊ : ℝ))
          · intro h; rw [h]; exact hxint
        simp [hcond]
      rw [hcast]
      simp [hmem]
    · simp only [hxint, ite_false]
      symm
      apply Finset.sum_eq_zero; intro n hn
      have hnx : (n : ℝ) ≠ x := by
        intro h; apply hxint
        have hn' := Finset.mem_Icc.mp hn
        have hle : (n : ℝ) ≤ ⌊x⌋₊ := by exact_mod_cast hn'.2
        have hfl : (⌊x⌋₊ : ℝ) ≤ x := Nat.floor_le (by linarith)
        linarith
      simp [hnx]
  rw [hkey, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun n hn ↦ ?_
  by_cases hnx : (n : ℝ) = x
  · simp [hnx]; ring
  · simp [hnx]

/-- On the 1-line the truncated Perron integral of the coefficient L-series agrees
with the truncated Perron integral of the shifted negative logarithmic derivative. -/
private theorem heckeLDP_perron_congr (χ : U[F]) (t₀ : ℝ)
    (hχ : ideleClassNormTwist χ 0 = ideleClassNormTwist (1 : U[F]) (-Complex.I * t₀))
    (Z : ℂ → ℂ) (hZ : MeromorphicNFOn Z univ)
    (hSeries : ∀ s : halfPlane, Z s = dedekindZeta F s)
    (s : ℂ) (x c T : ℝ) (hs : s.re = 1) (hc : 0 < c) :
    truncatedPerronIntegral
        (LSeries (heckeLogDerivCoefficient (ideleClassNormTwist χ 0))) s x c T =
      truncatedPerronIntegral (fun w ↦ -logDeriv Z (w - Complex.I * t₀)) s x c T := by
  have hLS (w : ℂ) (hw : 1 < w.re) :
      LSeries (heckeLogDerivCoefficient (ideleClassNormTwist χ 0)) w =
        -logDeriv Z (w - Complex.I * t₀) :=
    (heckeLDP_normTwist_hasSum χ t₀ hχ Z hZ hSeries ⟨w, hw⟩).LSeries_eq
  simp only [truncatedPerronIntegral]
  congr 1
  refine intervalIntegral.integral_congr fun t _ ↦ ?_
  have hw : 1 < (s + (⟨c, t⟩ : ℂ)).re := by simp [hs, Complex.add_re]; linarith
  rw [hLS _ hw]

/-- Zero-free region parameters for `Z` in the shape required by the Perron
left-edge and horizontal-edge bounds: a width `A`, a scale `B > 1/3`, and a
puncture radius `α` around the pole. -/
private theorem heckeLDP_zf_params (Z : ℂ → ℂ) (hZ : MeromorphicNFOn Z univ)
    (hSeries : ∀ s : halfPlane, Z s = dedekindZeta F s) :
    ∃ A B α : ℝ, 0 < A ∧ 1 / 3 < B ∧ α ∈ Ioo (0 : ℝ) 1 ∧
      A ≤ Real.log (B * 3) / 2 ∧
      (∀ z : ℂ, 1 - A / Real.log (B * (|z.im| + 3)) ≤ z.re → meromorphicOrderAt Z z ≤ 0) ∧
      (∀ z : ℂ, 0 < ‖z - 1‖ → ‖z - 1‖ < α → meromorphicOrderAt Z z ≤ 0) := by
  obtain ⟨A₀, hA₀, hF⟩ := finiteHeckeL_zeroFreeRegion
  obtain ⟨B₀, hB₀, hzf₀⟩ := hF F (1 : U[F])
  have hzfZ : ∀ z : ℂ,
      1 - A₀ / ((Module.finrank ℚ F : ℝ) ^ 4 * Real.log (B₀ * (|z.im| + 3))) ≤ z.re →
      meromorphicOrderAt Z z ≤ 0 :=
    fun z hz ↦ hzf₀ Z hZ (fun s ↦ (hSeries s).trans (heckeLDP_zeta_eq s).symm) z hz
  set B := max B₀ 1 with hBdef
  have hB13 : 1 / 3 < B := by linarith [le_max_left B₀ 1]
  have hB1 : 1 ≤ B := le_max_right _ _
  have hB0 : 0 < B := by linarith
  have hl3 : 0 < Real.log (B * 3) := Real.log_pos (by nlinarith)
  set d := (Module.finrank ℚ F : ℝ) with hddef
  have hd0 : 0 < d := Nat.cast_pos.mpr Module.finrank_pos
  set A := min (A₀ / d ^ 4) (Real.log (B * 3) / 2) with hAdef
  have hA : 0 < A := lt_min (div_pos hA₀ (pow_pos hd0 4)) (by linarith)
  have hAle : A ≤ A₀ / d ^ 4 := min_le_left _ _
  have hAw : A ≤ Real.log (B * 3) / 2 := min_le_right _ _
  have hzero : ∀ z : ℂ, 1 - A / Real.log (B * (|z.im| + 3)) ≤ z.re →
      meromorphicOrderAt Z z ≤ 0 := by
    intro z hz
    apply hzfZ
    have hlB : 0 < Real.log (B * (|z.im| + 3)) :=
      Real.log_pos (by nlinarith [abs_nonneg z.im])
    have hlog : Real.log (B₀ * (|z.im| + 3)) ≤ Real.log (B * (|z.im| + 3)) :=
      Real.log_le_log (by nlinarith [abs_nonneg z.im])
        (mul_le_mul_of_nonneg_right (le_max_left B₀ 1) (by linarith [abs_nonneg z.im]))
    have hkey : A / Real.log (B * (|z.im| + 3)) ≤
        A₀ / (d ^ 4 * Real.log (B₀ * (|z.im| + 3))) := by
      calc A / Real.log (B * (|z.im| + 3))
          ≤ (A₀ / d ^ 4) / Real.log (B * (|z.im| + 3)) :=
            div_le_div_of_nonneg_right hAle hlB.le
        _ = A₀ / (d ^ 4 * Real.log (B * (|z.im| + 3))) := by ring
        _ ≤ A₀ / (d ^ 4 * Real.log (B₀ * (|z.im| + 3))) :=
            div_le_div_of_nonneg_left hA₀.le
              (mul_pos (pow_pos hd0 4) (Real.log_pos (by nlinarith [abs_nonneg z.im])))
              (mul_le_mul_of_nonneg_left hlog (pow_nonneg hd0.le 4))
    linarith
  set α := min (1 / 2) (A / (2 * Real.log (B * (7 / 2)))) with hαdef
  have hl72 : 0 < Real.log (B * (7 / 2)) := Real.log_pos (by nlinarith)
  have hα0 : 0 < α := lt_min (by norm_num) (div_pos hA (by positivity))
  have hα1 : α < 1 := by
    linarith [min_le_left (1 / 2 : ℝ) (A / (2 * Real.log (B * (7 / 2))))]
  have hαhalf : α ≤ 1 / 2 := min_le_left _ _
  have hdisc : ∀ z : ℂ, 0 < ‖z - 1‖ → ‖z - 1‖ < α → meromorphicOrderAt Z z ≤ 0 := by
    intro z hz0 hz
    have him : |z.im| < α := by
      have := Complex.abs_im_le_norm (z - 1)
      have him' : (z - 1).im = z.im := by simp
      rw [him'] at this
      linarith
    have hre : 1 - α < z.re := by
      have := Complex.abs_re_le_norm (z - 1)
      have hre' : (z - 1).re = z.re - 1 := by simp
      rw [hre'] at this
      have := abs_lt.mp (lt_of_le_of_lt this hz)
      linarith
    apply hzero
    have hlz : 0 < Real.log (B * (|z.im| + 3)) :=
      Real.log_pos (by nlinarith [abs_nonneg z.im])
    have hlog : Real.log (B * (|z.im| + 3)) ≤ Real.log (B * (7 / 2)) :=
      Real.log_le_log (by positivity) (by nlinarith)
    have hkey : α ≤ A / Real.log (B * (|z.im| + 3)) := by
      calc α ≤ A / (2 * Real.log (B * (7 / 2))) := min_le_right _ _
        _ ≤ A / Real.log (B * (|z.im| + 3)) :=
            div_le_div_of_nonneg_left hA.le hlz (by linarith)
    linarith
  exact ⟨A, B, α, hA, hB13, ⟨hα0, hα1⟩, hAw, hzero, hdisc⟩

set_option maxHeartbeats 800000

/-- Paper: Theorem B.7.1.2(1), Equation (B.7.1.8), p. 645. For the character
`|·|^(-it₀)`, the cutoff polynomial on the 1-line is the negative shifted
Dedekind zeta logarithmic derivative plus the oscillatory pole term and an
analytic remainder. The remainder tends uniformly to zero on compact subsets
away from the pole along `J_b`. -/
theorem heckeLogDerivPolynomial_normTwist (χ : U[F]) (t₀ : ℝ)
    (hχ : ideleClassNormTwist χ 0 = ideleClassNormTwist (1 : U[F]) (-Complex.I * t₀))
    (Z : ℂ → ℂ) (hZ : MeromorphicNFOn Z univ)
    (hSeries : ∀ s : halfPlane, Z s = dedekindZeta F s)
    (K : Set ℂ) (hK : IsCompact K) (hKline : K ⊆ oneLine)
    (hpole : (1 + Complex.I * t₀ : ℂ) ∉ K) {b : ℝ} (hb : 0 < b) :
    ∃ error : ℝ → ℂ → ℂ,
      (∀ x > 1, AnalyticOnNhd ℂ (error x) oneLine ∧
        ∀ s ∈ oneLine, s ≠ 1 + Complex.I * t₀ →
          heckeLogDerivPolynomial χ x s = -logDeriv Z (s - Complex.I * t₀) +
            (x : ℂ) ^ (1 + Complex.I * t₀ - s) / (1 + Complex.I * t₀ - s) + error x s) ∧
      TendstoUniformlyOn error (fun _ ↦ 0) (atTop ⊓ 𝓟 (perronCutoffSet b)) K := by
  classical
  set s₀ : ℂ := 1 + Complex.I * t₀ with hs₀def
  let a := heckeLogDerivCoefficient (ideleClassNormTwist χ 0)
  -- zero-free region for Z (via the trivial character)
  obtain ⟨A₀, hA₀, hF⟩ := finiteHeckeL_zeroFreeRegion
  obtain ⟨B₀, hB₀, hzf₀⟩ := hF F (1 : U[F])
  have hzfZ : ∀ z : ℂ,
      1 - A₀ / ((Module.finrank ℚ F : ℝ) ^ 4 * Real.log (B₀ * (|z.im| + 3))) ≤ z.re →
      meromorphicOrderAt Z z ≤ 0 :=
    fun z hz ↦ hzf₀ Z hZ (fun s ↦ (hSeries s).trans (heckeLDP_zeta_eq s).symm) z hz
  have hneZ : ∀ s : ℂ, s.re = 1 → s ≠ s₀ → Z (s - Complex.I * t₀) ≠ 0 := by
    intro s hsre hsp
    have hne : s - Complex.I * t₀ ≠ 1 := by
      intro h; apply hsp; rw [hs₀def]; linear_combination h
    have hre : (s - Complex.I * t₀).re = 1 := by
      simp only [Complex.sub_re, Complex.mul_re, Complex.I_re, Complex.I_im,
        Complex.ofReal_re, Complex.ofReal_im, hsre]; ring
    have hanZ : AnalyticAt ℂ Z (s - Complex.I * t₀) :=
      heckeLDP_analytic Z hZ hSeries (by rw [hre]; norm_num) hne
    have hord : meromorphicOrderAt Z (s - Complex.I * t₀) ≤ 0 := by
      apply hzfZ
      have hnonneg : 0 ≤ A₀ / ((Module.finrank ℚ F : ℝ) ^ 4 *
          Real.log (B₀ * (|(s - Complex.I * t₀).im| + 3))) := by
        apply div_nonneg hA₀.le
        apply mul_nonneg (pow_nonneg (Nat.cast_nonneg _) _)
        apply Real.log_nonneg
        have h3 : (3 : ℝ) ≤ |(s - Complex.I * t₀).im| + 3 := by
          linarith [abs_nonneg ((s - Complex.I * t₀).im)]
        nlinarith
      linarith
    exact (hZ (mem_univ _)).meromorphicOrderAt_eq_zero_iff.mp
      (le_antisymm hord hanZ.meromorphicOrderAt_nonneg)
  obtain ⟨h, hh, hpp⟩ := heckeLDP_principalPart Z hZ hSeries
  let naive : ℝ → ℂ → ℂ := fun x s ↦
    heckeLogDerivPolynomial χ x s + logDeriv Z (s - Complex.I * t₀) -
      (x : ℂ) ^ (s₀ - s) / (s₀ - s)
  let error : ℝ → ℂ → ℂ := fun x ↦ Function.update (naive x) s₀
    (heckeLogDerivPolynomial χ x s₀ + h (s₀ - Complex.I * t₀) +
      deriv (fun w : ℂ ↦ (x : ℂ) ^ (-(w - s₀))) s₀)
  refine ⟨error, ?_, ?_⟩
  · intro x hx
    refine ⟨?_, ?_⟩
    · intro s hs
      have hsre : s.re = 1 := hs
      by_cases hsp : s = s₀
      · subst hsp
        let f : ℂ → ℂ := fun w ↦ (x : ℂ) ^ (-(w - s₀))
        have hf : AnalyticAt ℂ f s₀ :=
          AnalyticAt.cpow analyticAt_const (by fun_prop)
            (Complex.ofReal_mem_slitPlane.mpr (zero_lt_one.trans hx))
        have hh' : AnalyticAt ℂ h (s₀ - Complex.I * t₀) := by
          have : s₀ - Complex.I * t₀ = 1 := by rw [hs₀def]; ring
          rw [this]; exact hh
        have hg : AnalyticAt ℂ (fun s ↦ heckeLogDerivPolynomial χ x s +
            h (s - Complex.I * t₀) + dslope f s₀ s) s₀ :=
          ((heckeLDP_poly_analytic χ x s₀).add
            (hh'.comp (f := fun s : ℂ ↦ s - Complex.I * t₀) (by fun_prop))).add (hf.dslope s₀)
        have heq : error x =ᶠ[𝓝 s₀] (fun s ↦ heckeLogDerivPolynomial χ x s +
            h (s - Complex.I * t₀) + dslope f s₀ s) := by
          obtain ⟨R, hR, hball⟩ := Metric.eventually_nhds_iff.mp
            (eventually_nhdsWithin_iff.mp hpp)
          filter_upwards [Metric.ball_mem_nhds s₀ hR] with s hs
          by_cases hseq : s = s₀
          · subst hseq
            simp only [error, Function.update_self, f, dslope_same]
          · have hne' : s - Complex.I * t₀ ≠ 1 := by
              intro h'; apply hseq; rw [hs₀def]; linear_combination h'
            have hdist : dist (s - Complex.I * t₀) 1 < R := by
              rw [Complex.dist_eq,
                show (s - Complex.I * (t₀ : ℂ) - 1 : ℂ) = s - s₀ by rw [hs₀def]; ring,
                ← Complex.dist_eq]
              exact hs
            have hpp' := hball hdist (by simpa using hne')
            have hden : s₀ - s = -(s - s₀) := by ring
            have hsub : s - Complex.I * (t₀ : ℂ) - 1 = s - s₀ := by rw [hs₀def]; ring
            simp only [error, Function.update_of_ne hseq, naive]
            rw [hpp']
            simp only [f, dslope, slope, vsub_eq_sub, Function.update_of_ne hseq]
            rw [hsub, hden]
            simp (config := {failIfUnchanged := false}) only
              [sub_self, neg_zero, Complex.cpow_zero]
            rw [div_neg_eq_neg_div]
            ring_nf
        exact hg.congr heq.symm
      · have hne : s - Complex.I * t₀ ≠ 1 := by
          intro h'; apply hsp; rw [hs₀def]; linear_combination h'
        have hanZ : AnalyticAt ℂ Z (s - Complex.I * t₀) :=
          heckeLDP_analytic Z hZ hSeries (by
            simp only [Complex.sub_re, Complex.mul_re, Complex.I_re, Complex.I_im,
              Complex.ofReal_re, Complex.ofReal_im, hsre, mul_zero, zero_mul, sub_zero];
            norm_num) hne
        have hlog : AnalyticAt ℂ (fun s ↦ logDeriv Z (s - Complex.I * t₀)) s :=
          (heckeLDP_logDeriv_analytic hanZ (hneZ s hsre hsp)).comp
            (f := fun s : ℂ ↦ s - Complex.I * t₀) (by fun_prop)
        have hpoleterm : AnalyticAt ℂ (fun s ↦ (x : ℂ) ^ (s₀ - s) / (s₀ - s)) s := by
          refine AnalyticAt.div ?_ (by fun_prop) ?_
          · exact AnalyticAt.cpow analyticAt_const (by fun_prop)
              (Complex.ofReal_mem_slitPlane.mpr (zero_lt_one.trans hx))
          · intro h'; apply hsp; linear_combination -h'
        have hna : AnalyticAt ℂ (naive x) s :=
          ((heckeLDP_poly_analytic χ x s).add hlog).sub hpoleterm
        exact hna.congr (by
          filter_upwards [isOpen_ne.mem_nhds hsp] with s' hs'
          simp [error, Function.update_of_ne hs'])
    · intro s hs hsp
      simp only [error, Function.update_of_ne hsp, naive]
      ring
  · by_cases hKne : K.Nonempty
    · obtain ⟨ψ, hψ, hmono, hcoeff, habs, Kψ, hKψ, hψle⟩ := heckeLDP_majorant_explicit χ
      obtain ⟨Cf, hCf, hcoef⟩ := truncatedPerron_error_noninteger_coeff a ψ hψ hcoeff
      have ha : ∀ s : ℂ, 1 < s.re → LSeriesSummable a s := fun s hs ↦ heckeLDP_summable χ s hs
      have habs' : (fun σ : ℝ ↦ ∑' n : ℕ, ‖LSeries.term a (σ : ℂ) n‖) =O[𝓝[>] 1]
          (fun σ : ℝ ↦ ((σ - 1) ^ (1 : ℝ))⁻¹) := by
        simpa [a, Real.rpow_one] using habs
      obtain ⟨CN, hCN, hN⟩ := truncatedPerron_error_noninteger a ψ hψ hmono 1 (by norm_num)
        ha hcoeff habs'
      obtain ⟨CI, hCI, hI⟩ := truncatedPerron_error_integer a ψ hψ hmono 1 (by norm_num)
        ha hcoeff habs'
      obtain ⟨A, B, α, hA, hB, hα, hAw, hzero, hdisc⟩ := heckeLDP_zf_params Z hZ hSeries
      obtain ⟨CL, T₀L, hCL, hT₀L, hleft⟩ := dedekindZeta_perron_left_bound Z hZ hSeries
        hA hB hα hAw hdisc (fun z hz ↦ hzero z hz.le)
      obtain ⟨CH, T₀H, hCH, hT₀H, hhoriz⟩ := dedekindZeta_perron_horizontal_bound Z hZ hSeries
        hA hB hα hAw hdisc (fun z hz ↦ hzero z hz.le)
      set T₀ := max T₀L T₀H with hT₀def
      have hT₀2 : 2 ≤ T₀ := by linarith [le_max_left T₀L T₀H, hT₀L]
      have hT₀L' : T₀L ≤ T₀ := by rw [hT₀def]; exact le_max_left _ _
      have hT₀H' : T₀H ≤ T₀ := by rw [hT₀def]; exact le_max_right _ _
      have hcont : ContinuousOn (fun s : ℂ ↦ |s.im - t₀|) K :=
        (by fun_prop : Continuous fun s : ℂ ↦ |s.im - t₀|).continuousOn
      obtain ⟨sM, hsM, hMmax⟩ := hK.exists_isMaxOn hKne hcont
      set M := |sM.im - t₀| with hMdef
      have hM : ∀ s ∈ K, |s.im - t₀| ≤ M := fun s hs ↦ hMmax hs
      have hM0 : 0 ≤ M := abs_nonneg _
      set K₂ := Kψ * (2 + Real.log 4) with hK₂def
      have hK₂0 : 0 ≤ K₂ :=
        mul_nonneg hKψ (by linarith [Real.log_pos (show (1 : ℝ) < 4 by norm_num)])
      set D₁ := max CN CI * (Real.exp 1 + K₂ + K₂ / b) with hD₁def
      set D₂ := Cf * K₂ with hD₂def
      set D₃ := 4 * Real.exp 1 * CH / Real.pi with hD₃def
      set D₄ := 4 * CL / Real.pi with hD₄def
      set b₁ := α * A / 2 with hb₁def
      have hb₁ : 0 < b₁ := div_pos (mul_pos hα.1 hA) two_pos
      let G : ℝ → ℝ := fun x ↦
        D₁ * ((Real.log x) ^ 2 * Real.exp (-Real.sqrt (Real.log x))) +
        D₂ * (Real.log x / x) +
        D₃ * Real.exp (-Real.sqrt (Real.log x)) +
        D₄ * ((Real.log x) ^ 2 * Real.exp (-b₁ * Real.sqrt (Real.log x)))
      have hG : Tendsto G atTop (𝓝 0) := by
        have h1 := heckeLDP_tendsto_log_pow_exp_sqrt 2 1 one_pos
        have h3 := heckeLDP_tendsto_log_pow_exp_sqrt 0 1 one_pos
        have h4 := heckeLDP_tendsto_log_pow_exp_sqrt 2 b₁ hb₁
        have h2 : Tendsto (fun x : ℝ ↦ Real.log x / x) atTop (𝓝 0) := by
          have hle : ∀ᶠ x : ℝ in atTop, Real.log x / x ≤ 2 * x ^ (-(1 / 2 : ℝ)) := by
            filter_upwards [eventually_ge_atTop 1] with x hx
            have hx0 : 0 < x := by linarith
            have hlog : Real.log x ≤ 2 * Real.sqrt x := by
              have hl := Real.log_le_sub_one_of_pos (Real.sqrt_pos.mpr hx0)
              have h2 : Real.log x = 2 * Real.log (Real.sqrt x) := by
                rw [Real.log_sqrt (by linarith : 0 ≤ x)]; ring
              linarith [Real.sqrt_nonneg x]
            have hdiv : Real.log x / x ≤ 2 * Real.sqrt x / x :=
              div_le_div_of_nonneg_right hlog hx0.le
            have heq : 2 * Real.sqrt x / x = 2 * x ^ (-(1 / 2 : ℝ)) := by
              have h1 : 2 * Real.sqrt x / x = 2 / Real.sqrt x := by
                rw [div_eq_div_iff hx0.ne' (Real.sqrt_ne_zero'.mpr hx0), mul_assoc,
                  Real.mul_self_sqrt (by linarith : 0 ≤ x)]
              rw [h1, Real.rpow_neg (by linarith : 0 ≤ x), Real.sqrt_eq_rpow]
              ring
            linarith
          have hu : Tendsto (fun x : ℝ ↦ 2 * x ^ (-(1 / 2 : ℝ))) atTop (𝓝 0) := by
            have := (tendsto_rpow_neg_atTop (show (0 : ℝ) < 1 / 2 by norm_num)).const_mul 2
            simpa using this
          refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hu ?_ hle
          filter_upwards [eventually_ge_atTop 1] with x hx
          exact div_nonneg (Real.log_nonneg hx) (by linarith)
        have t1 : Tendsto (fun x : ℝ ↦
            D₁ * ((Real.log x) ^ 2 * Real.exp (-Real.sqrt (Real.log x)))) atTop (𝓝 0) := by
          simpa using h1.const_mul D₁
        have t2 : Tendsto (fun x : ℝ ↦ D₂ * (Real.log x / x)) atTop (𝓝 0) := by
          simpa using h2.const_mul D₂
        have t3 : Tendsto (fun x : ℝ ↦
            D₃ * Real.exp (-Real.sqrt (Real.log x))) atTop (𝓝 0) := by
          simpa using h3.const_mul D₃
        have t4 : Tendsto (fun x : ℝ ↦
            D₄ * ((Real.log x) ^ 2 * Real.exp (-b₁ * Real.sqrt (Real.log x)))) atTop (𝓝 0) := by
          simpa using h4.const_mul D₄
        dsimp only [G]
        simpa using ((t1.add t2).add t3).add t4
      have hbound : ∀ᶠ x in atTop ⊓ 𝓟 (perronCutoffSet b), ∀ s ∈ K, ‖error x s‖ ≤ G x := by
        rw [Filter.eventually_inf_principal]
        have hev1 : ∀ᶠ x : ℝ in atTop, max 2 (max b (Real.exp 1)) ≤ x := eventually_ge_atTop _
        have hev2 : ∀ᶠ x : ℝ in atTop,
            max (Real.log (T₀ + M))
              (max (Real.log (2 * B)) (max (Real.log (M + 3)) (max (Real.log 2) 1))) ≤
              Real.sqrt (Real.log x) :=
          heckeLDP_tendsto_sqrt_log.eventually (eventually_ge_atTop _)
        filter_upwards [hev1, hev2] with x hx1 hx2 hxmem
        intro s hs
        have hsre : s.re = 1 := hKline hs
        have hsp : s ≠ s₀ := fun h ↦ hpole (h ▸ hs)
        have him : |s.im - t₀| ≤ M := hM s hs
        have hx2' : 2 ≤ x := (le_max_left _ _).trans hx1
        have hxb : b ≤ x :=
          (le_max_left _ _).trans ((le_max_right _ _).trans hx1)
        have hxexp : Real.exp 1 ≤ x :=
          (le_max_right _ _).trans ((le_max_right _ _).trans hx1)
        have hx1' : 1 < x := by linarith
        have hx0 : 0 < x := by linarith
        have hlog : 0 < Real.log x := Real.log_pos hx1'
        have hlog1 : 1 ≤ Real.log x := by
          have := Real.log_le_log (Real.exp_pos 1) hxexp
          rwa [Real.log_exp] at this
        have hx2a : Real.log (T₀ + M) ≤ Real.sqrt (Real.log x) := (le_max_left _ _).trans hx2
        have hx2b : Real.log (2 * B) ≤ Real.sqrt (Real.log x) :=
          (le_max_left _ _).trans ((le_max_right _ _).trans hx2)
        have hx2c : Real.log (M + 3) ≤ Real.sqrt (Real.log x) :=
          (le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hx2))
        have hx2d : Real.log 2 ≤ Real.sqrt (Real.log x) :=
          (le_max_left _ _).trans ((le_max_right _ _).trans
            ((le_max_right _ _).trans ((le_max_right _ _).trans hx2)))
        have hx2e : 1 ≤ Real.sqrt (Real.log x) :=
          (le_max_right _ _).trans ((le_max_right _ _).trans
            ((le_max_right _ _).trans ((le_max_right _ _).trans hx2)))
        set c := 1 / Real.log x with hcdef
        set T := Real.exp (Real.sqrt (Real.log x)) with hTdef
        have hc0 : 0 < c := one_div_pos.mpr hlog
        have hc1 : c ≤ 1 := by rw [hcdef, div_le_iff₀ hlog, one_mul]; exact hlog1
        have hσ : s.re + c ∈ Ioc 1 2 := by rw [hsre]; exact ⟨by linarith, by linarith⟩
        have hs0 : 0 < Real.sqrt (Real.log x) := Real.sqrt_pos.mpr hlog
        have hT1 : 1 ≤ T := by rw [hTdef]; exact Real.one_le_exp (Real.sqrt_nonneg _)
        have hT0' : 0 < T := by linarith
        have hTinv : 1 / T = Real.exp (-Real.sqrt (Real.log x)) := by
          rw [hTdef, Real.exp_neg, one_div]
        have hTbig : T₀ + M ≤ T := by
          have h2 : Real.exp (Real.log (T₀ + M)) ≤ Real.exp (Real.sqrt (Real.log x)) :=
            Real.exp_le_exp.mpr hx2a
          rw [Real.exp_log (show 0 < T₀ + M by linarith)] at h2
          rw [hTdef]; exact h2
        have hTB : 2 * B ≤ T := by
          have h2 : Real.exp (Real.log (2 * B)) ≤ Real.exp (Real.sqrt (Real.log x)) :=
            Real.exp_le_exp.mpr hx2b
          rw [Real.exp_log (show 0 < 2 * B by linarith)] at h2
          rw [hTdef]; exact h2
        have hTM3 : M + 3 ≤ T := by
          have h2 : Real.exp (Real.log (M + 3)) ≤ Real.exp (Real.sqrt (Real.log x)) :=
            Real.exp_le_exp.mpr hx2c
          rw [Real.exp_log (show 0 < M + 3 by linarith)] at h2
          rw [hTdef]; exact h2
        have hT2 : 2 ≤ T := by
          have h2 : Real.exp (Real.log 2) ≤ Real.exp (Real.sqrt (Real.log x)) :=
            Real.exp_le_exp.mpr hx2d
          rw [Real.exp_log two_pos] at h2
          rw [hTdef]; exact h2
        have hsT : |s.im - t₀| < T := by linarith [hTbig, hT₀2]
        set δ := α * A / Real.log (B * (T + |s.im - t₀| + 3)) with hδdef
        set δm := α * A / Real.log (B * (T + M + 3)) with hδmdef
        have hB3 : (1 : ℝ) < B * 3 := by linarith
        have hB0' : 0 < B := by linarith
        have hlδ : 0 < Real.log (B * (T + |s.im - t₀| + 3)) :=
          Real.log_pos (by
            have : B * 3 ≤ B * (T + |s.im - t₀| + 3) :=
              mul_le_mul_of_nonneg_left (by linarith [abs_nonneg (s.im - t₀), hT1]) hB0'.le
            linarith)
        have hlδm : 0 < Real.log (B * (T + M + 3)) :=
          Real.log_pos (by
            have : B * 3 ≤ B * (T + M + 3) :=
              mul_le_mul_of_nonneg_left (by linarith [hM0, hT1]) hB0'.le
            linarith)
        have hδ0 : 0 < δ := by rw [hδdef]; exact div_pos (mul_pos hα.1 hA) hlδ
        have hδm0 : 0 < δm := by rw [hδmdef]; exact div_pos (mul_pos hα.1 hA) hlδm
        have hδ1 : δ ≤ 1 / 2 := by
          rw [hδdef]
          have h1 : α * A / Real.log (B * (T + |s.im - t₀| + 3)) ≤ α * A / Real.log (B * 3) :=
            div_le_div_of_nonneg_left (mul_pos hα.1 hA).le (Real.log_pos hB3)
              (Real.log_le_log (by linarith)
                (mul_le_mul_of_nonneg_left (by linarith [abs_nonneg (s.im - t₀), hT1]) hB0'.le))
          have h2 : α * A / Real.log (B * 3) ≤ α * (1 / 2) := by
            have hA' : A / Real.log (B * 3) ≤ 1 / 2 := by
              rw [div_le_iff₀ (Real.log_pos hB3)]
              linarith [hAw]
            calc α * A / Real.log (B * 3) = α * (A / Real.log (B * 3)) := by ring
              _ ≤ α * (1 / 2) := mul_le_mul_of_nonneg_left hA' hα.1.le
          linarith [hα.2]
        have hδmδ : δm ≤ δ := by
          rw [hδdef, hδmdef]
          exact div_le_div_of_nonneg_left (mul_pos hα.1 hA).le hlδ
            (Real.log_le_log (by positivity)
              (mul_le_mul_of_nonneg_left (by linarith) hB0'.le))
        have hzf : ∀ z : ℂ, 1 - δ ≤ z.re → |z.im - (s.im - t₀)| ≤ T →
            meromorphicOrderAt Z z ≤ 0 := by
          intro z hz1 hz2
          apply hzero
          have himz : |z.im| ≤ T + |s.im - t₀| := by
            have := abs_sub_abs_le_abs_sub z.im (s.im - t₀)
            linarith
          have hlz : 0 < Real.log (B * (|z.im| + 3)) :=
            Real.log_pos (by
              have : B * 3 ≤ B * (|z.im| + 3) :=
                mul_le_mul_of_nonneg_left (by linarith [abs_nonneg z.im]) hB0'.le
              linarith)
          have hlog : Real.log (B * (|z.im| + 3)) ≤ Real.log (B * (T + |s.im - t₀| + 3)) :=
            Real.log_le_log (by positivity)
              (mul_le_mul_of_nonneg_left (by linarith) hB0'.le)
          have h1 : δ ≤ A / Real.log (B * (T + |s.im - t₀| + 3)) := by
            rw [hδdef]
            have : α * A / Real.log (B * (T + |s.im - t₀| + 3)) =
                α * (A / Real.log (B * (T + |s.im - t₀| + 3))) := by ring
            rw [this]
            exact mul_le_of_le_one_left (div_nonneg hA.le hlδ.le) hα.2.le
          have h2 : A / Real.log (B * (T + |s.im - t₀| + 3)) ≤ A / Real.log (B * (|z.im| + 3)) :=
            div_le_div_of_nonneg_left hA.le hlz hlog
          linarith
        have hsp' : s ≠ 1 + Complex.I * t₀ := by rw [← hs₀def]; exact hsp
        have hshift := heckeLDP_contour_shift t₀ Z hZ hSeries s hsre hsp' x c T δ
          hx1' hc0 hsT hδ0 hδ1 hzf
        rw [← hs₀def] at hshift
        have h1' : heckeLogDerivPolynomial χ x s =
            perronHalfWeightedSum a s x +
              (if (⌊x⌋₊ : ℝ) = x then LSeries.term a s ⌊x⌋₊ / 2 else 0) := by
          have := heckeLDP_poly_half χ x hx1'.le s
          simp only [a]
          linear_combination this
        have h2' := heckeLDP_perron_congr χ t₀ hχ Z hZ hSeries s x c T hsre hc0
        let Btm : ℂ := ∫ u in -δ..c,
          -logDeriv Z (s - Complex.I * t₀ + ⟨u, -T⟩) * (x : ℂ) ^ (⟨u, -T⟩ : ℂ) / (⟨u, -T⟩ : ℂ)
        let Top : ℂ := ∫ u in -δ..c,
          -logDeriv Z (s - Complex.I * t₀ + ⟨u, T⟩) * (x : ℂ) ^ (⟨u, T⟩ : ℂ) / (⟨u, T⟩ : ℂ)
        let Lft : ℂ := ∫ t in -T..T,
          -logDeriv Z (s - Complex.I * t₀ + ⟨-δ, t⟩) * (x : ℂ) ^ (⟨-δ, t⟩ : ℂ) / (⟨-δ, t⟩ : ℂ)
        have hdecomp : naive x s =
            (perronHalfWeightedSum a s x - truncatedPerronIntegral (LSeries a) s x c T) +
            (if (⌊x⌋₊ : ℝ) = x then LSeries.term a s ⌊x⌋₊ / 2 else 0) +
            (Complex.I * (Btm - Top) + Lft) / (2 * (Real.pi : ℂ)) := by
          simp only [naive, Btm, Top, Lft]
          rw [h1', h2', hshift]
          ring
        have hxc : x ^ c = Real.exp 1 := by
          rw [hcdef, Real.rpow_def_of_pos hx0, mul_one_div, div_self hlog.ne']
        have hψbound : ∀ n : ℕ, (n : ℝ) ≤ 2 * x → ψ n ≤ K₂ * Real.log x := by
          intro n hn
          have hlog : Real.log ((n : ℝ) + 2) ≤ Real.log 4 + Real.log x := by
            have h1 : Real.log ((n : ℝ) + 2) ≤ Real.log (2 * x + 2) :=
              Real.log_le_log (by positivity) (by linarith)
            have h2 : Real.log (2 * x + 2) ≤ Real.log (4 * x) :=
              Real.log_le_log (by positivity) (by linarith)
            have h3 : Real.log (4 * x) = Real.log 4 + Real.log x :=
              Real.log_mul (by norm_num) hx0.ne'
            linarith
          have hstep : Kψ * (Real.log ((n : ℝ) + 2) + 1) ≤ K₂ * Real.log x := by
            rw [hK₂def]
            have hinner : Real.log ((n : ℝ) + 2) + 1 ≤ (2 + Real.log 4) * Real.log x := by
              have hmul : 0 ≤ Real.log 4 * (Real.log x - 1) :=
                mul_nonneg (Real.log_pos (show (1 : ℝ) < 4 by norm_num)).le
                  (sub_nonneg.mpr hlog1)
              linarith
            have := mul_le_mul_of_nonneg_left hinner hKψ
            convert this using 1 <;> ring
          linarith [hψle n]
        have hE1 : ‖perronHalfWeightedSum a s x - truncatedPerronIntegral (LSeries a) s x c T‖ ≤
            D₁ * ((Real.log x) ^ 2 * Real.exp (-Real.sqrt (Real.log x))) := by
          have hkey : ‖perronHalfWeightedSum a s x -
              truncatedPerronIntegral (LSeries a) s x c T‖ ≤
              max CN CI * (Real.exp 1 * Real.log x + K₂ * Real.log x * Real.log x +
                K₂ / b * Real.log x) / T := by
            by_cases hxint : x ∈ Set.range (Int.cast : ℤ → ℝ)
            · obtain ⟨z, hz⟩ := hxint
              have hz0 : 0 ≤ z := by exact_mod_cast (by linarith : (0 : ℝ) ≤ z)
              have hm0 : 0 < z.toNat := by
                have hzpos : (0 : ℤ) < z := by exact_mod_cast (by linarith : (0 : ℝ) < z)
                rw [← Int.toNat_of_nonneg hz0] at hzpos
                exact_mod_cast hzpos
              have hcast : ((z.toNat : ℕ) : ℝ) = x := by
                rw [← hz]
                exact_mod_cast Int.toNat_of_nonneg hz0
              have hbI := hI s z.toNat c T hm0 hc0 hT1 hσ
              rw [hcast] at hbI
              have hp1 : (s.re + c - 1) ^ (1 : ℝ) = c := by
                rw [hsre, Real.rpow_one]; ring
              have hp2 : x ^ (1 - s.re) = 1 := by rw [hsre, sub_self, Real.rpow_zero]
              have hp3 : x ^ (-s.re) = 1 / x := by
                rw [hsre, Real.rpow_neg_one, one_div]
              simp only [hp1, hp2, hp3, mul_one] at hbI
              have hψ2m : ψ (2 * z.toNat) ≤ K₂ * Real.log x := by
                apply hψbound
                have : ((2 * z.toNat : ℕ) : ℝ) = 2 * ((z.toNat : ℕ) : ℝ) := by push_cast; ring
                linarith
              have hψm : ψ z.toNat ≤ K₂ * Real.log x :=
                hψbound z.toNat (by linarith)
              have hL : 0 ≤ Real.log x := Real.log_nonneg (by linarith)
              have hterm1 : x ^ c / (T * c) = Real.exp 1 * Real.log x / T := by
                rw [hxc, hcdef]; field_simp [hT0'.ne', hlog.ne']
              rw [hterm1] at hbI
              have hmid : ψ (2 * z.toNat) * Real.log x / T ≤
                  K₂ * Real.log x * Real.log x / T :=
                div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hψ2m hL) hT0'.le
              have hterm3 : ψ z.toNat * c * (1 / x) / T ≤
                  K₂ / b * Real.log x / T := by
                have hcz : c * (1 / x) ≤ 1 / b := by
                  calc c * (1 / x) ≤ 1 * (1 / x) :=
                        mul_le_mul_of_nonneg_right hc1 (one_div_nonneg.mpr (by linarith))
                    _ = 1 / x := one_mul _
                    _ ≤ 1 / b := one_div_le_one_div_of_le hb (by linarith)
                have hψL : ψ z.toNat * (c * (1 / x)) ≤
                    K₂ * Real.log x * (1 / b) :=
                  mul_le_mul hψm hcz (mul_nonneg hc0.le (one_div_nonneg.mpr (by linarith)))
                    (mul_nonneg hK₂0 hL)
                have e1 : ψ z.toNat * c * (1 / x) / T =
                    ψ z.toNat * (c * (1 / x)) / T := by ring
                have e2 : K₂ / b * Real.log x / T =
                    K₂ * Real.log x * (1 / b) / T := by ring
                rw [e1, e2]
                exact div_le_div_of_nonneg_right hψL hT0'.le
              calc ‖perronHalfWeightedSum a s x - truncatedPerronIntegral (LSeries a) s x c T‖
                  ≤ CI * (Real.exp 1 * Real.log x / T +
                      ψ (2 * z.toNat) * Real.log x / T +
                      ψ z.toNat * c * (1 / x) / T) := hbI
                _ ≤ CI * (Real.exp 1 * Real.log x / T +
                      K₂ * Real.log x * Real.log x / T +
                      K₂ / b * Real.log x / T) :=
                    mul_le_mul_of_nonneg_left
                      (add_le_add (add_le_add le_rfl hmid) hterm3) hCI.le
                _ = CI * (Real.exp 1 * Real.log x +
                      K₂ * Real.log x * Real.log x +
                      K₂ / b * Real.log x) / T := by ring
                _ ≤ max CN CI * (Real.exp 1 * Real.log x +
                      K₂ * Real.log x * Real.log x +
                      K₂ / b * Real.log x) / T :=
                    div_le_div_of_nonneg_right
                      (mul_le_mul_of_nonneg_right (le_max_right CN CI)
                        (add_nonneg (add_nonneg (mul_nonneg (Real.exp_pos 1).le hL)
                          (mul_nonneg (mul_nonneg hK₂0 hL) hL))
                          (mul_nonneg (div_nonneg hK₂0 hb.le) hL))) hT0'.le

            · set N := (round x).toNat with hNdef
              have hround : 0 ≤ round x := by
                rw [round_eq]
                exact Int.floor_nonneg.mpr (by linarith)
              have hNcast : (N : ℝ) = round x := by
                exact_mod_cast Int.toNat_of_nonneg hround
              have hNdist : |x - (N : ℝ)| ≤ 1 / 2 := by rw [hNcast]; exact abs_sub_round x
              have hNb : b ≤ |x - (N : ℝ)| := by
                have := hxmem.resolve_left hxint
                rwa [hNcast]
              have hbN := hN s x c T N hx0 hc0 hT1 hσ hxint hNdist
              have hp1 : (s.re + c - 1) ^ (1 : ℝ) = c := by
                rw [hsre, Real.rpow_one]; ring
              have hp2 : x ^ (1 - s.re) = 1 := by rw [hsre, sub_self, Real.rpow_zero]
              have hp3 : |Real.log x| = Real.log x := abs_of_pos hlog
              simp only [hp1, hp2, hp3, mul_one] at hbN
              have hψ2x : ψ ⌊2 * x⌋₊ ≤ K₂ * Real.log x :=
                hψbound ⌊2 * x⌋₊ (Nat.floor_le (by positivity))
              have hψN : ψ N ≤ K₂ * Real.log x := by
                apply hψbound
                have := abs_le.mp hNdist
                linarith
              have hthird : ψ N / (T * |x - (N : ℝ)|) ≤ K₂ / b * Real.log x / T := by
                have h1 : ψ N / (T * |x - (N : ℝ)|) ≤ ψ N / (T * b) :=
                  div_le_div_of_nonneg_left (hψ N).le (mul_pos hT0' hb)
                    (mul_le_mul_of_nonneg_left hNb hT0'.le)
                have h2 : ψ N / (T * b) ≤ K₂ * Real.log x / (T * b) :=
                  div_le_div_of_nonneg_right hψN (mul_pos hT0' hb).le
                have h3 : K₂ * Real.log x / (T * b) = K₂ / b * Real.log x / T := by ring
                linarith
              have hterm1 : x ^ c / (T * c) = Real.exp 1 * Real.log x / T := by
                rw [hxc, hcdef]; field_simp [hT0'.ne', hlog.ne']
              rw [hterm1] at hbN
              have hmid : ψ ⌊2 * x⌋₊ * Real.log x / T ≤
                  K₂ * Real.log x * Real.log x / T :=
                div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hψ2x hlog.le) hT0'.le
              calc ‖perronHalfWeightedSum a s x - truncatedPerronIntegral (LSeries a) s x c T‖
                  ≤ CN * (Real.exp 1 * Real.log x / T +
                      ψ ⌊2 * x⌋₊ * Real.log x / T + ψ N / (T * |x - (N : ℝ)|)) := hbN
                _ ≤ CN * (Real.exp 1 * Real.log x / T +
                      K₂ * Real.log x * Real.log x / T + K₂ / b * Real.log x / T) :=
                    mul_le_mul_of_nonneg_left
                      (add_le_add (add_le_add le_rfl hmid) hthird) hCN.le
                _ = CN * (Real.exp 1 * Real.log x + K₂ * Real.log x * Real.log x +
                      K₂ / b * Real.log x) / T := by ring
                _ ≤ max CN CI * (Real.exp 1 * Real.log x + K₂ * Real.log x * Real.log x +
                      K₂ / b * Real.log x) / T :=
                    div_le_div_of_nonneg_right
                      (mul_le_mul_of_nonneg_right (le_max_left CN CI)
                        (add_nonneg (add_nonneg (mul_nonneg (Real.exp_pos 1).le hlog.le)
                          (mul_nonneg (mul_nonneg hK₂0 hlog.le) hlog.le))
                          (mul_nonneg (div_nonneg hK₂0 hb.le) hlog.le))) hT0'.le
          have hL2 : Real.log x ≤ (Real.log x) ^ 2 := by
            have h1 := mul_le_mul_of_nonneg_right hlog1 hlog.le
            have h2 : (Real.log x) ^ 2 = Real.log x * Real.log x := by ring
            linarith
          have h1 : Real.exp 1 * Real.log x ≤ Real.exp 1 * (Real.log x) ^ 2 :=
            mul_le_mul_of_nonneg_left hL2 (Real.exp_pos 1).le
          have h2 : K₂ / b * Real.log x ≤ K₂ / b * (Real.log x) ^ 2 :=
            mul_le_mul_of_nonneg_left hL2 (div_nonneg hK₂0 hb.le)
          have h3 : K₂ * Real.log x * Real.log x = K₂ * (Real.log x) ^ 2 := by ring
          have hsum : Real.exp 1 * Real.log x + K₂ * Real.log x * Real.log x +
              K₂ / b * Real.log x ≤ (Real.exp 1 + K₂ + K₂ / b) * (Real.log x) ^ 2 := by
            linarith
          refine hkey.trans ?_
          calc max CN CI * (Real.exp 1 * Real.log x + K₂ * Real.log x * Real.log x +
                K₂ / b * Real.log x) / T
              ≤ max CN CI * ((Real.exp 1 + K₂ + K₂ / b) * (Real.log x) ^ 2) / T :=
                div_le_div_of_nonneg_right
                  (mul_le_mul_of_nonneg_left hsum (le_trans hCN.le (le_max_left CN CI))) hT0'.le
            _ = D₁ * ((Real.log x) ^ 2 * (1 / T)) := by rw [hD₁def]; ring
            _ = D₁ * ((Real.log x) ^ 2 * Real.exp (-Real.sqrt (Real.log x))) := by
                rw [hTinv]
        have hE2 : ‖(if (⌊x⌋₊ : ℝ) = x then LSeries.term a s ⌊x⌋₊ / 2 else 0)‖ ≤
            D₂ * (Real.log x / x) := by
          split_ifs with hxeq
          · have hfl1 : 1 ≤ ⌊x⌋₊ := by
              apply Nat.le_floor
              norm_num
              linarith
            have hfl0 : ⌊x⌋₊ ≠ 0 := Nat.one_le_iff_ne_zero.mp hfl1
            have hnorm : ‖LSeries.term a s ⌊x⌋₊ / 2‖ = ‖a ⌊x⌋₊‖ / ((⌊x⌋₊ : ℝ) * 2) := by
              have h2 : ‖(2 : ℂ)‖ = (2 : ℝ) := by
                rw [show (2 : ℂ) = ((2 : ℝ) : ℂ) by push_cast; ring, Complex.norm_real]
                norm_num
              rw [norm_div, LSeries.norm_term_eq, ite_eq_right hfl0, hsre, Real.rpow_one, h2]
              ring
            rw [hnorm]
            have h1 : ‖a ⌊x⌋₊‖ ≤ Cf * ψ ⌊x⌋₊ := hcoef ⌊x⌋₊
            have h2 : ψ ⌊x⌋₊ ≤ K₂ * Real.log x := by
              apply hψbound
              have := Nat.floor_le (by linarith : 0 ≤ x)
              linarith
            have hflx : x ≤ (⌊x⌋₊ : ℝ) * 2 := by
              have := Nat.lt_floor_add_one x
              linarith
            calc ‖a ⌊x⌋₊‖ / ((⌊x⌋₊ : ℝ) * 2)
                ≤ Cf * ψ ⌊x⌋₊ / ((⌊x⌋₊ : ℝ) * 2) :=
                  div_le_div_of_nonneg_right h1
                    (mul_pos (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hfl0)) two_pos).le
              _ ≤ Cf * (K₂ * Real.log x) / ((⌊x⌋₊ : ℝ) * 2) :=
                  div_le_div_of_nonneg_right
                    (mul_le_mul_of_nonneg_left h2 hCf.le)
                    (mul_pos (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hfl0)) two_pos).le
              _ ≤ Cf * (K₂ * Real.log x) / x :=
                  div_le_div_of_nonneg_left (mul_nonneg hCf.le (mul_nonneg hK₂0 hlog.le))
                    hx0 hflx
              _ = D₂ * (Real.log x / x) := by rw [hD₂def]; ring
          · simp only [norm_zero]
            rw [hD₂def]
            exact mul_nonneg (mul_nonneg hCf.le hK₂0) (div_nonneg hlog.le hx0.le)
        have hlogT : Real.log (T + M + 3) ≤ 2 * Real.sqrt (Real.log x) := by
          have h1 : Real.log (T + M + 3) ≤ Real.log (2 * T) :=
            Real.log_le_log (by linarith) (by linarith)
          have h2 : Real.log (2 * T) = Real.log 2 + Real.sqrt (Real.log x) := by
            rw [Real.log_mul two_ne_zero hT0'.ne', hTdef, Real.log_exp]
          linarith
        have hlogB : Real.log (B * (T + M + 3)) ≤ 2 * Real.sqrt (Real.log x) := by
          have hBT : B * (T + M + 3) ≤ T * T := by
            have h1 : T + M + 3 ≤ 2 * T := by linarith
            have h2 : B * (T + M + 3) ≤ B * (2 * T) :=
              mul_le_mul_of_nonneg_left h1 (by linarith)
            have h3 : B * (2 * T) ≤ T * T := by
              have : B * (2 * T) = (2 * B) * T := by ring
              rw [this]
              exact mul_le_mul_of_nonneg_right hTB hT0'.le
            linarith
          have h1 : Real.log (B * (T + M + 3)) ≤ Real.log (T * T) :=
            Real.log_le_log (by positivity) hBT
          have h2 : Real.log (T * T) = 2 * Real.sqrt (Real.log x) := by
            rw [Real.log_mul hT0'.ne' hT0'.ne', hTdef, Real.log_exp]; ring
          linarith
        have hsq : (Real.log (T + M + 3)) ^ 2 ≤ 4 * Real.log x := by
          have h1 := pow_le_pow_left₀
            (Real.log_nonneg (by linarith : (1 : ℝ) ≤ T + M + 3)) hlogT 2
          have h2 : (2 * Real.sqrt (Real.log x)) ^ 2 = 4 * Real.log x := by
            rw [mul_pow, Real.sq_sqrt hlog.le]; ring
          linarith
        have hsqrt : Real.sqrt (Real.log x) ≤ Real.log x := by
          have hmul : 0 ≤ Real.sqrt (Real.log x) * (Real.sqrt (Real.log x) - 1) :=
            mul_nonneg (Real.sqrt_nonneg _) (sub_nonneg.mpr hx2e)
          linarith [Real.mul_self_sqrt hlog.le]
        have hcube : (Real.log (T + M + 3)) ^ 3 ≤ 8 * (Real.log x) ^ 2 := by
          have h1 := pow_le_pow_left₀
            (Real.log_nonneg (by linarith : (1 : ℝ) ≤ T + M + 3)) hlogT 3
          have h2 : (2 * Real.sqrt (Real.log x)) ^ 3 =
              8 * (Real.log x * Real.sqrt (Real.log x)) := by
            have : (Real.sqrt (Real.log x)) ^ 3 = Real.log x * Real.sqrt (Real.log x) := by
              rw [pow_succ, Real.sq_sqrt hlog.le]
            rw [mul_pow, this]; ring
          have h3 : Real.log x * Real.sqrt (Real.log x) ≤ Real.log x * Real.log x :=
            mul_le_mul_of_nonneg_left hsqrt hlog.le
          have h4 : Real.log x * Real.log x = (Real.log x) ^ 2 := by ring
          nlinarith
        have hBtm : ‖Btm‖ ≤ 4 * Real.exp 1 * CH * Real.exp (-Real.sqrt (Real.log x)) := by
          have hb := hhoriz s t₀ x c T (-T) (hKline hs) hx1' hc0
            (by linarith [hTbig, him, hT₀H']) (Or.inl rfl)
          simp only at hb
          rw [← hδdef] at hb
          have hneg : Btm = -(∫ u in -δ..c,
              logDeriv Z (s - Complex.I * t₀ + ⟨u, -T⟩) *
                (x : ℂ) ^ (⟨u, -T⟩ : ℂ) / (⟨u, -T⟩ : ℂ)) := by
            dsimp only [Btm]
            rw [← intervalIntegral.integral_neg]
            congr 1; funext u; ring
          rw [hneg, norm_neg]
          have hlogle : Real.log (|s.im - t₀ + -T| + 3) ≤ Real.log (T + M + 3) :=
            Real.log_le_log (by positivity) (by
              have := abs_add_le (s.im - t₀) (-T)
              simp only [abs_neg, abs_of_pos hT0'] at this
              linarith)
          have hsq' : (Real.log (|s.im - t₀ + -T| + 3)) ^ 2 ≤ 4 * Real.log x := by
            have := pow_le_pow_left₀
              (Real.log_nonneg (by linarith [abs_nonneg (s.im - t₀ + -T)])) hlogle 2
            linarith
          calc ‖∫ u in -δ..c, logDeriv Z (s - Complex.I * t₀ + ⟨u, -T⟩) *
                (x : ℂ) ^ (⟨u, -T⟩ : ℂ) / (⟨u, -T⟩ : ℂ)‖
              ≤ CH * x ^ c * (Real.log (|s.im - t₀ + -T| + 3)) ^ 2 / (T * Real.log x) := hb
            _ ≤ CH * Real.exp 1 * (4 * Real.log x) / (T * Real.log x) := by
                rw [hxc]
                exact div_le_div_of_nonneg_right
                  (mul_le_mul_of_nonneg_left hsq'
                    (mul_nonneg hCH.le (Real.exp_pos 1).le)) (mul_pos hT0' hlog).le
            _ = 4 * Real.exp 1 * CH * Real.exp (-Real.sqrt (Real.log x)) := by
                rw [← hTinv]; field_simp [hT0'.ne', hlog.ne']; try ring
        have hTop : ‖Top‖ ≤ 4 * Real.exp 1 * CH * Real.exp (-Real.sqrt (Real.log x)) := by
          have hb := hhoriz s t₀ x c T T (hKline hs) hx1' hc0
            (by linarith [hTbig, him, hT₀H']) (Or.inr rfl)
          simp only at hb
          rw [← hδdef] at hb
          have hneg : Top = -(∫ u in -δ..c,
              logDeriv Z (s - Complex.I * t₀ + ⟨u, T⟩) *
                (x : ℂ) ^ (⟨u, T⟩ : ℂ) / (⟨u, T⟩ : ℂ)) := by
            dsimp only [Top]
            rw [← intervalIntegral.integral_neg]
            congr 1; funext u; ring
          rw [hneg, norm_neg]
          have hlogle : Real.log (|s.im - t₀ + T| + 3) ≤ Real.log (T + M + 3) :=
            Real.log_le_log (by positivity) (by
              have := abs_add_le (s.im - t₀) T
              simp only [abs_of_pos hT0'] at this
              linarith)
          have hsq' : (Real.log (|s.im - t₀ + T| + 3)) ^ 2 ≤ 4 * Real.log x := by
            have := pow_le_pow_left₀
              (Real.log_nonneg (by linarith [abs_nonneg (s.im - t₀ + T)])) hlogle 2
            linarith
          calc ‖∫ u in -δ..c, logDeriv Z (s - Complex.I * t₀ + ⟨u, T⟩) *
                (x : ℂ) ^ (⟨u, T⟩ : ℂ) / (⟨u, T⟩ : ℂ)‖
              ≤ CH * x ^ c * (Real.log (|s.im - t₀ + T| + 3)) ^ 2 / (T * Real.log x) := hb
            _ ≤ CH * Real.exp 1 * (4 * Real.log x) / (T * Real.log x) := by
                rw [hxc]
                exact div_le_div_of_nonneg_right
                  (mul_le_mul_of_nonneg_left hsq'
                    (mul_nonneg hCH.le (Real.exp_pos 1).le)) (mul_pos hT0' hlog).le
            _ = 4 * Real.exp 1 * CH * Real.exp (-Real.sqrt (Real.log x)) := by
                rw [← hTinv]; field_simp [hT0'.ne', hlog.ne']; try ring
        have hLft : ‖Lft‖ ≤
            8 * CL * ((Real.log x) ^ 2 * Real.exp (-b₁ * Real.sqrt (Real.log x))) := by
          have hb := hleft s t₀ x T (hKline hs) hx1'.le (by linarith [hTbig, him, hT₀L'])
          simp only at hb
          rw [← hδdef] at hb
          have hneg : Lft = -(∫ t in -T..T,
              logDeriv Z (s - Complex.I * t₀ + ⟨-δ, t⟩) *
                (x : ℂ) ^ (⟨-δ, t⟩ : ℂ) / (⟨-δ, t⟩ : ℂ)) := by
            dsimp only [Lft]
            rw [← intervalIntegral.integral_neg]
            congr 1; funext t; ring
          rw [hneg, norm_neg]
          have hδle : x ^ (-δ) ≤ x ^ (-δm) :=
            Real.rpow_le_rpow_of_exponent_le hx1'.le (neg_le_neg hδmδ)
          have hlogcube : (Real.log (T + |s.im - t₀| + 3)) ^ 3 ≤ 8 * (Real.log x) ^ 2 := by
            have := pow_le_pow_left₀
              (Real.log_nonneg
                (by linarith [abs_nonneg (s.im - t₀)] : (1 : ℝ) ≤ T + |s.im - t₀| + 3))
              (Real.log_le_log
                (by linarith [abs_nonneg (s.im - t₀)] : 0 < T + |s.im - t₀| + 3)
                (by linarith : T + |s.im - t₀| + 3 ≤ T + M + 3)) 3
            linarith
          have hxδm : x ^ (-δm) ≤ Real.exp (-b₁ * Real.sqrt (Real.log x)) := by
            have hδmge : b₁ / Real.sqrt (Real.log x) ≤ δm := by
              rw [hδmdef, hb₁def]
              have e1 : α * A / 2 / Real.sqrt (Real.log x) =
                  α * A / (2 * Real.sqrt (Real.log x)) := by ring
              rw [e1]
              exact div_le_div_of_nonneg_left (mul_pos hα.1 hA).le hlδm hlogB
            have hmono := Real.rpow_le_rpow_of_exponent_le hx1'.le (neg_le_neg hδmge)
            have heq : x ^ (-(b₁ / Real.sqrt (Real.log x))) =
                Real.exp (-b₁ * Real.sqrt (Real.log x)) := by
              rw [Real.rpow_def_of_pos hx0]
              congr 1
              have hsq : Real.log x * (b₁ / Real.sqrt (Real.log x)) =
                  b₁ * Real.sqrt (Real.log x) := by
                rw [← mul_div_assoc, div_eq_iff hs0.ne', mul_comm (Real.log x) b₁,
                  mul_assoc, Real.mul_self_sqrt hlog.le]
              linarith
            linarith
          calc ‖∫ t in -T..T, logDeriv Z (s - Complex.I * t₀ + ⟨-δ, t⟩) *
                (x : ℂ) ^ (⟨-δ, t⟩ : ℂ) / (⟨-δ, t⟩ : ℂ)‖
              ≤ CL * x ^ (-δ) * (Real.log (T + |s.im - t₀| + 3)) ^ 3 := hb
            _ = CL * (x ^ (-δ) * (Real.log (T + |s.im - t₀| + 3)) ^ 3) := by ring
            _ ≤ CL * (x ^ (-δm) * (8 * (Real.log x) ^ 2)) :=
                mul_le_mul_of_nonneg_left
                  (mul_le_mul hδle hlogcube
                    (pow_nonneg (Real.log_nonneg
                      (by linarith [abs_nonneg (s.im - t₀)] :
                        (1 : ℝ) ≤ T + |s.im - t₀| + 3)) 3)
                    (Real.rpow_pos_of_pos hx0 _).le) hCL.le
            _ ≤ CL * (Real.exp (-b₁ * Real.sqrt (Real.log x)) * (8 * (Real.log x) ^ 2)) :=
                mul_le_mul_of_nonneg_left
                  (mul_le_mul_of_nonneg_right hxδm (by positivity)) hCL.le
            _ = 8 * CL * ((Real.log x) ^ 2 * Real.exp (-b₁ * Real.sqrt (Real.log x))) := by
                ring
        have hE3 : ‖(Complex.I * (Btm - Top) + Lft) / (2 * (Real.pi : ℂ))‖ ≤
            D₃ * Real.exp (-Real.sqrt (Real.log x)) +
            D₄ * ((Real.log x) ^ 2 * Real.exp (-b₁ * Real.sqrt (Real.log x))) := by
          have hπ : ‖(2 * (Real.pi : ℂ))‖ = 2 * Real.pi := by
            rw [show (2 * (Real.pi : ℂ)) = ((2 * Real.pi : ℝ) : ℂ) by push_cast; ring,
              Complex.norm_real, Real.norm_of_nonneg (mul_pos two_pos Real.pi_pos).le]
          have hnorm : ‖(Complex.I * (Btm - Top) + Lft) / (2 * (Real.pi : ℂ))‖ ≤
              (‖Btm‖ + ‖Top‖ + ‖Lft‖) / (2 * Real.pi) := by
            rw [norm_div, hπ]
            refine div_le_div_of_nonneg_right ?_ (mul_pos two_pos Real.pi_pos).le
            calc ‖Complex.I * (Btm - Top) + Lft‖
                ≤ ‖Complex.I * (Btm - Top)‖ + ‖Lft‖ := norm_add_le _ _
              _ = ‖Btm - Top‖ + ‖Lft‖ := by rw [norm_mul, Complex.norm_I, one_mul]
              _ ≤ ‖Btm‖ + ‖Top‖ + ‖Lft‖ := by linarith [norm_sub_le Btm Top]
          calc ‖(Complex.I * (Btm - Top) + Lft) / (2 * (Real.pi : ℂ))‖
              ≤ (‖Btm‖ + ‖Top‖ + ‖Lft‖) / (2 * Real.pi) := hnorm
            _ ≤ (4 * Real.exp 1 * CH * Real.exp (-Real.sqrt (Real.log x)) +
                  4 * Real.exp 1 * CH * Real.exp (-Real.sqrt (Real.log x)) +
                  8 * CL * ((Real.log x) ^ 2 *
                    Real.exp (-b₁ * Real.sqrt (Real.log x)))) / (2 * Real.pi) :=
                div_le_div_of_nonneg_right
                  (add_le_add (add_le_add hBtm hTop) hLft) (mul_pos two_pos Real.pi_pos).le
            _ = D₃ * Real.exp (-Real.sqrt (Real.log x)) +
                D₄ * ((Real.log x) ^ 2 * Real.exp (-b₁ * Real.sqrt (Real.log x))) := by
                rw [hD₃def, hD₄def]
                field_simp [Real.pi_ne_zero]
                try ring
        calc ‖error x s‖ = ‖naive x s‖ := by
              simp only [error, Function.update_of_ne hsp]
          _ = ‖(perronHalfWeightedSum a s x - truncatedPerronIntegral (LSeries a) s x c T) +
              (if (⌊x⌋₊ : ℝ) = x then LSeries.term a s ⌊x⌋₊ / 2 else 0) +
              (Complex.I * (Btm - Top) + Lft) / (2 * (Real.pi : ℂ))‖ := by
              rw [hdecomp]
          _ ≤ ‖perronHalfWeightedSum a s x - truncatedPerronIntegral (LSeries a) s x c T‖ +
              ‖(if (⌊x⌋₊ : ℝ) = x then LSeries.term a s ⌊x⌋₊ / 2 else 0)‖ +
              ‖(Complex.I * (Btm - Top) + Lft) / (2 * (Real.pi : ℂ))‖ := by
              have hn1 := norm_add_le
                ((perronHalfWeightedSum a s x - truncatedPerronIntegral (LSeries a) s x c T) +
                  (if (⌊x⌋₊ : ℝ) = x then LSeries.term a s ⌊x⌋₊ / 2 else 0))
                ((Complex.I * (Btm - Top) + Lft) / (2 * (Real.pi : ℂ)))
              have hn2 := norm_add_le
                (perronHalfWeightedSum a s x - truncatedPerronIntegral (LSeries a) s x c T)
                (if (⌊x⌋₊ : ℝ) = x then LSeries.term a s ⌊x⌋₊ / 2 else 0)
              linarith
          _ ≤ G x := by
              dsimp only [G]
              linarith
      rw [TendstoUniformlyOn]
      intro u hu
      obtain ⟨ε, hε, hεu⟩ := Metric.uniformity_basis_dist.mem_iff.mp hu
      have hεv : ∀ᶠ x in atTop, G x < ε := by
        have := Metric.tendsto_nhds.mp hG ε hε
        filter_upwards [this] with x hx
        rw [Real.dist_eq, sub_zero] at hx
        exact lt_of_le_of_lt (le_abs_self (G x)) hx
      have hεv' : ∀ᶠ x in atTop ⊓ 𝓟 (perronCutoffSet b), G x < ε := by
        rw [Filter.eventually_inf_principal]
        filter_upwards [hεv] with x hx _
        exact hx
      filter_upwards [hbound, hεv'] with x hb hGε
      intro s hs
      apply hεu
      show dist (0 : ℂ) (error x s) < ε
      rw [dist_comm, dist_zero_right]
      exact (hb s hs).trans_lt hGε
    · rw [Set.not_nonempty_iff_eq_empty] at hKne
      rw [hKne]
      exact tendstoUniformlyOn_empty
/-- Paper: Theorem B.7.1.2(1), Equation (B.7.1.9), p. 645. At the pole
ordinate, the cutoff polynomial differs from the logarithm of the cutoff by
a bounded quantity as the real cutoff tends to infinity.
Deviation: The implied constant is for the fixed number field. The double-pole
residue on p. 648 involves the field's Euler–Kronecker constant. -/
theorem heckeLogDerivPolynomial_at_pole (χ : U[F]) (t₀ : ℝ)
    (hχ : ideleClassNormTwist χ 0 = ideleClassNormTwist (1 : U[F]) (-Complex.I * t₀)) :
    (fun x : ℝ ↦ heckeLogDerivPolynomial χ x (1 + Complex.I * t₀) - (Real.log x : ℂ))
      =O[atTop] (fun _ ↦ (1 : ℝ)) := by
  sorry

/-- Paper: Theorem B.7.1.2(2), Equation (B.7.1.10), p. 646. For a character
nontrivial on the norm-one subgroup, the cutoff polynomial on the 1-line is the
negative logarithmic derivative plus an analytic remainder that tends uniformly
to zero on compact subsets along `J_b`.
Deviation: The positive parameter `b` occurring in part (1) is made explicit. -/
theorem heckeLogDerivPolynomial_of_nontrivial_on_normOne (χ : U[F])
    (hχ : χ.toMonoidHom.comp (ideleClassNorm F).ker.subtype ≠ 1)
    (L : ℂ → ℂ) (hL : MeromorphicNFOn L univ) (hSeries : ∀ s : halfPlane, L s = finiteHeckeL χ s)
    (K : Set ℂ) (hK : IsCompact K) (hKline : K ⊆ oneLine) {b : ℝ} (hb : 0 < b) :
    ∃ error : ℝ → ℂ → ℂ,
      (∀ x > 1, AnalyticOnNhd ℂ (error x) oneLine ∧
        ∀ s ∈ oneLine, heckeLogDerivPolynomial χ x s = -logDeriv L s + error x s) ∧
      TendstoUniformlyOn error (fun _ ↦ 0) (atTop ⊓ 𝓟 (perronCutoffSet b)) K := by
  sorry

/-- Paper: Equation (B.7.1.11), p. 646. Perron's estimate for the full Hecke
cutoff includes a correction for the remaining half of the last coefficient
at an integer cutoff.
Deviation: Adds the half-endpoint correction. For `c ≥ 1` the absence of
a norm-one coefficient gives exponential decay to the right. The initial contour lies
strictly to the right of the pole, so the estimate also holds at the pole ordinate. -/
theorem heckeLogDerivPolynomial_perron_error (χ : U[F]) (t₀ : ℝ)
    (hχ : ideleClassNormTwist χ 0 = ideleClassNormTwist (1 : U[F]) (-Complex.I * t₀))
    (Z : ℂ → ℂ) (hZ : MeromorphicNFOn Z univ)
    (hSeries : ∀ s : halfPlane, Z s = dedekindZeta F s) :
    ∃ C : ℝ, 0 < C ∧ ∀ (s : ℂ) (x c T : ℝ), s ∈ oneLine → 1 < x → 0 < c → 1 ≤ T →
      ‖heckeLogDerivPolynomial χ x s -
        truncatedPerronIntegral (fun w ↦ -logDeriv Z (w - Complex.I * t₀)) s x c T -
        (if (⌊x⌋₊ : ℝ) = x then
          LSeries.term (heckeLogDerivCoefficient (ideleClassNormTwist χ 0)) s ⌊x⌋₊ / 2
         else 0)‖ ≤
        C * (x ^ c / (T * c) + (Real.log x) ^ 2 / T +
          (if (⌊x⌋₊ : ℝ) = x then c * Real.log x / (T * x)
           else Real.log x / (T * |x - (round x : ℝ)|))) := by
  classical
  let a := heckeLogDerivCoefficient (ideleClassNormTwist χ 0)
  obtain ⟨ψ, hψ, hmono, hcoeff, habs⟩ := heckeLDP_majorant χ
  have ha : ∀ s : ℂ, 1 < s.re → LSeriesSummable a s := fun s hs ↦ heckeLDP_summable χ s hs
  have habs' : (fun σ : ℝ ↦ ∑' n : ℕ, ‖LSeries.term a (σ : ℂ) n‖) =O[𝓝[>] 1]
      (fun σ : ℝ ↦ ((σ - 1) ^ (1 : ℝ))⁻¹) := by
    simpa [a, Real.rpow_one] using habs
  obtain ⟨CN, hCN, hN⟩ := truncatedPerron_error_noninteger a ψ hψ hmono 1 (by norm_num)
    ha hcoeff habs'
  obtain ⟨CI, hCI, hI⟩ := truncatedPerron_error_integer a ψ hψ hmono 1 (by norm_num)
    ha hcoeff habs'
  have hhalf (x : ℝ) (hx : 1 ≤ x) (s : ℂ) : heckeLogDerivPolynomial χ x s -
      (if (⌊x⌋₊ : ℝ) = x then LSeries.term a s ⌊x⌋₊ / 2 else 0) =
      perronHalfWeightedSum a s x := by
    simp only [heckeLogDerivPolynomial, perronHalfWeightedSum, a]
    have hkey : (if (⌊x⌋₊ : ℝ) = x then LSeries.term a s ⌊x⌋₊ / 2 else 0) =
        ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, if (n : ℝ) = x then LSeries.term a s n / 2 else 0 := by
      by_cases hxint : (⌊x⌋₊ : ℝ) = x
      · simp only [hxint, ite_true]
        have hmem : ⌊x⌋₊ ∈ Finset.Icc 1 ⌊x⌋₊ := by
          refine Finset.mem_Icc.mpr ⟨?_, le_rfl⟩
          have : 1 ≤ (⌊x⌋₊ : ℝ) := by rw [hxint]; exact hx
          exact_mod_cast this
        have hcast : (∑ n ∈ Finset.Icc 1 ⌊x⌋₊,
            if (n : ℝ) = x then LSeries.term a s n / 2 else 0) =
            ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, if n = ⌊x⌋₊ then LSeries.term a s n / 2 else 0 := by
          apply Finset.sum_congr rfl; intro n _
          have hcond : ((n : ℝ) = x) = (n = ⌊x⌋₊) := by
            apply propext; constructor
            · intro h; exact_mod_cast (by linarith [hxint] : (n : ℝ) = (⌊x⌋₊ : ℝ))
            · intro h; rw [h]; exact hxint
          simp [hcond]
        rw [hcast]
        simp [hmem]
      · simp only [hxint, ite_false]
        symm
        apply Finset.sum_eq_zero; intro n hn
        have hnx : (n : ℝ) ≠ x := by
          intro h; apply hxint
          have hn' := Finset.mem_Icc.mp hn
          have hle : (n : ℝ) ≤ ⌊x⌋₊ := by exact_mod_cast hn'.2
          have hfl : (⌊x⌋₊ : ℝ) ≤ x := Nat.floor_le (by linarith)
          linarith
        simp [hnx]
    rw [hkey, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun n hn ↦ ?_
    by_cases hnx : (n : ℝ) = x
    · simp [hnx]; ring
    · simp [hnx]
  have hLS (w : ℂ) (hw : 1 < w.re) : LSeries a w = -logDeriv Z (w - Complex.I * t₀) :=
    (heckeLDP_normTwist_hasSum χ t₀ hχ Z hZ hSeries ⟨w, hw⟩).LSeries_eq
  have hPerron (s : ℂ) (x c T : ℝ) (hs : s.re = 1) (hc : 0 < c) :
      truncatedPerronIntegral (LSeries a) s x c T =
        truncatedPerronIntegral (fun w ↦ -logDeriv Z (w - Complex.I * t₀)) s x c T := by
    simp only [truncatedPerronIntegral]
    congr 1
    refine intervalIntegral.integral_congr fun t _ ↦ ?_
    have hw : 1 < (s + (⟨c, t⟩ : ℂ)).re := by
      simp [hs, Complex.add_re]; linarith
    rw [hLS _ hw]
  sorry


-- TODO(paper-gap): The uniform limit away from the pole does not justify taking
-- the limit at the pole in (B.7.1.9). The contour there has a double pole.

end RiemannMasullo
