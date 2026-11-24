module

public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.Analysis.Meromorphic.Order
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Complex
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Data.Finset.NatDivisors
public import Mathlib.Data.Set.Card
public import Mathlib.Topology.JacobsonSpace
public import Mathlib.Topology.Algebra.InfiniteSum.Defs
public import Mathlib.Topology.Algebra.InfiniteSum.Real

/-!
# §§14.2–14.3: Global function fields and higher rank

Masullo, pp. 534–536. The Euler product (14.2.0.1) uses every closed point of
the smooth projective curve, including those above infinity for a map to the
projective line.
-/

@[expose] public section

namespace RiemannMasullo

open AlgebraicGeometry CategoryTheory

universe u

variable {k : Type u} [Field k] [Finite k] {X : Scheme.{u}}

/-- Paper: (14.2.0.1), p. 534. The local factor at a closed point, in the
complex parameter on the covering plane. -/
noncomputable def curveZetaEulerFactor (x : closedPoints X) (s : ℂ) : ℂ :=
  (1 - (Nat.card (X.residueField x.val) : ℂ) ^ (-s))⁻¹

/-- Paper: (14.2.0.1), p. 534. The zeta Euler product of a smooth projective
geometrically connected curve over a finite field multiplies the reciprocal
factors determined by the sizes of the residue fields of its closed points.
Deviation: The product is defined on `Re(s) > 1`, its half-plane of absolute
convergence. A smooth proper curve over a field is projective. -/
noncomputable def curveZetaEulerProduct (f : X ⟶ Spec (.of k))
    [SmoothOfRelativeDimension 1 f] [IsProper f] [GeometricallyConnected f]
    (s : {s : ℂ // 1 < s.re}) : ℂ :=
  ∏' x : closedPoints X, curveZetaEulerFactor x s.val

/-- Paper: (14.2.0.1), p. 534. On `Re(s) > 1` the finite products over closed
points converge to the zeta Euler product.
Deviation: `HasProd` asserts convergence of the product in the display. -/
theorem hasProd_curveZetaEulerProduct (f : X ⟶ Spec (.of k))
    [SmoothOfRelativeDimension 1 f] [IsProper f] [GeometricallyConnected f]
    (s : {s : ℂ // 1 < s.re}) :
    HasProd (fun x : closedPoints X ↦ curveZetaEulerFactor x s.val)
      (curveZetaEulerProduct f s) := by sorry

/-- Paper: §14.2, p. 534. For a finite set of closed points every local
factor has a simple pole at each integral multiple of the imaginary period.
The product has pole order equal to the number of places. -/
theorem curveZetaEulerFactor_prod_order (f : X ⟶ Spec (.of k))
    [SmoothOfRelativeDimension 1 f] [IsProper f] [GeometricallyConnected f]
    (S : Finset (closedPoints X)) (n : ℤ) :
    meromorphicOrderAt (fun s : ℂ ↦ ∏ x ∈ S, curveZetaEulerFactor x s)
      (2 * Real.pi * Complex.I * n / Real.log (Nat.card k)) = -(S.card : ℤ) := by sorry

-- TODO(paper-gap): Page 534 does not construct the function-field Sobolev
-- quotient or show that the trace approximation requires one Mellin test to
-- cancel all finite-stage poles. Under T = q^(-s) these lifts give one point.

/-- Paper: §14.2, last paragraph, p. 534. For each degree there are finitely
many closed points whose residue field has that degree over the base field.
Deviation: Page 534 says that the factors repeat "infinitely many times". The
number at each fixed degree is finite, and p. 535 estimates it; it grows as the
degree tends to infinity. -/
theorem curveZeta_closedPointsOfDegree_finite (f : X ⟶ Spec (.of k))
    [SmoothOfRelativeDimension 1 f] [IsProper f] [GeometricallyConnected f] (m : ℕ) :
    {x : X | x ∈ closedPoints X ∧
      Nat.card (X.residueField x) = Nat.card k ^ m}.Finite := by sorry

/-- Paper: §14.2, p. 535. The number of closed points of degree m over k. -/
noncomputable def curveZetaClosedPointCount (f : X ⟶ Spec (.of k))
    [SmoothOfRelativeDimension 1 f] [IsProper f] [GeometricallyConnected f] (m : ℕ) : ℕ :=
  {x : X | x ∈ closedPoints X ∧
    Nat.card (X.residueField x) = Nat.card k ^ m}.ncard

/-- Paper: §14.2, p. 535. A closed point of degree d contributes d rational
points over an extension of degree m exactly when d divides m.
Deviation: Uses the exact counting identity behind the printed upper bound. -/
theorem curveZeta_extensionPointCount (f : X ⟶ Spec (.of k))
    [SmoothOfRelativeDimension 1 f] [IsProper f] [GeometricallyConnected f]
    (K : Type u) [Field K] [Algebra k K] [Finite K] :
    Nat.card {p : Spec (.of K) ⟶ X // p ≫ f = Spec.map (CommRingCat.ofHom (algebraMap k K))} =
      ∑ d ∈ (Module.finrank k K).divisors, d * curveZetaClosedPointCount f d := by sorry

/-- Paper: §14.2, p. 535. The number of degree-m closed points is
q^m/m with error O(q^(m/2)/m) as m tends to infinity.
Deviation: The Big-O constant here is for the given curve. The paper also
specifies uniformity in the curve through its genus. -/
theorem curveZeta_closedPointsOfDegree_asymptotic (f : X ⟶ Spec (.of k))
    [SmoothOfRelativeDimension 1 f] [IsProper f] [GeometricallyConnected f] :
    let q : ℝ := Nat.card k
    (fun m : ℕ ↦ (curveZetaClosedPointCount f m : ℝ) - q ^ m / m) =O[Filter.atTop]
      (fun m : ℕ ↦ Real.sqrt (q ^ m) / m) := by sorry

/-- The base field of a curve over a finite field has at least two elements. -/
private lemma two_le_card_baseField : 2 ≤ Nat.card k := by
  haveI : Fintype k := Fintype.ofFinite k
  rw [Nat.card_eq_fintype_card]
  exact Fintype.one_lt_card

/-- A closed point of a curve over a finite field has a finite residue field: its cardinality is
`(Nat.card k) ^ m` for some `m ≥ 1`. -/
private theorem residueField_card_eq_pow_of_closed (f : X ⟶ Spec (.of k))
    [SmoothOfRelativeDimension 1 f] {x : X} (hx : x ∈ closedPoints X) :
    ∃ m : ℕ, 1 ≤ m ∧ Nat.card (X.residueField x) = Nat.card k ^ m := by
  haveI : Smooth f := SmoothOfRelativeDimension.smooth (f := f) (n := 1)
  haveI : LocallyOfFiniteType f := inferInstance
  haveI : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace f
  have hclosed : IsClosed ({x} : Set X) := hx
  have h1 : LocallyOfFiniteType (X.fromSpecResidueField x) :=
    (isClosed_singleton_iff_locallyOfFiniteType (X := X)).mp hclosed
  have h2 : LocallyOfFiniteType (X.fromSpecResidueField x ≫ f) := inferInstance
  obtain ⟨φ, hφ⟩ := Spec.homEquiv.symm.surjective (X.fromSpecResidueField x ≫ f)
  have h2' : LocallyOfFiniteType (Spec.homEquiv.symm φ) := hφ ▸ h2
  have h3 : RingHom.FiniteType φ.hom := HasRingHomProperty.Spec_iff.mp h2'
  algebraize [φ.hom]
  haveI : Algebra.FiniteType k (X.residueField x) := h3
  haveI : Module.Finite k (X.residueField x) :=
    finite_of_finite_type_of_isJacobsonRing k (X.residueField x)
  haveI : Finite (X.residueField x) := Module.finite_of_finite k (M := X.residueField x)
  have hcard : Nat.card (X.residueField x) = Nat.card k ^ Module.finrank k (X.residueField x) :=
    Module.natCard_eq_pow_finrank (K := k) (V := X.residueField x)
  refine ⟨Module.finrank k (X.residueField x), ?_, hcard⟩
  haveI : Fintype k := Fintype.ofFinite k
  haveI : Fintype (X.residueField x) := Fintype.ofFinite _
  have hq : 2 ≤ Nat.card k := two_le_card_baseField
  have hc : 2 ≤ Nat.card (X.residueField x) := by
    rw [Nat.card_eq_fintype_card]; exact Fintype.one_lt_card
  by_contra hlt
  have h0 : Module.finrank k (X.residueField x) = 0 := by omega
  rw [h0, pow_zero] at hcard
  omega

/-- The residue field of a closed point of a curve over a finite field has at least two
elements. -/
private lemma two_le_card_residueField (f : X ⟶ Spec (.of k))
    [SmoothOfRelativeDimension 1 f] (x : closedPoints X) :
    2 ≤ Nat.card (X.residueField x.val) := by
  obtain ⟨m, hm, hcard⟩ := residueField_card_eq_pow_of_closed f x.2
  rw [hcard]
  have h1 : 1 ≤ Nat.card k := by
    have := two_le_card_baseField (k := k)
    omega
  have h2 : m ≠ 0 := by omega
  calc 2 ≤ Nat.card k := two_le_card_baseField
    _ ≤ Nat.card k ^ m := le_self_pow h1 h2

/-- The reciprocal local factor minus `1` is bounded by twice the `-σ`-th power of the size of
the residue field, where `σ = Re s > 1`. -/
private lemma norm_curveZetaEulerFactor_sub_one_le (c : ℕ) (hc : 2 ≤ c) {s : ℂ} (hs : 1 < s.re) :
    ‖(1 - (c : ℂ) ^ (-s))⁻¹ - 1‖ ≤ 2 * (c : ℝ) ^ (-s.re) := by
  have hc0 : (0 : ℕ) < c := by omega
  set u : ℂ := (c : ℂ) ^ (-s) with hu
  have hunorm : ‖u‖ = (c : ℝ) ^ (-s.re) := Complex.norm_natCast_cpow_of_pos hc0 _
  have hsmall : ‖u‖ ≤ 1 / 2 := by
    have hstep1 : (c : ℝ) ^ (-s.re) ≤ (2 : ℝ) ^ (-s.re) :=
      Real.rpow_le_rpow_of_nonpos (by norm_num) (by exact_mod_cast hc) (by linarith)
    have hstep2 : (2 : ℝ) ^ (-s.re) ≤ (2 : ℝ) ^ (-1 : ℝ) := by
      rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), Real.rpow_neg_one]
      have h2 : (2 : ℝ) ≤ (2 : ℝ) ^ s.re :=
        Real.self_le_rpow_of_one_le (by norm_num) (le_of_lt hs)
      exact (inv_le_inv₀ (by positivity) (by norm_num)).mpr h2
    rw [hunorm]
    calc (c : ℝ) ^ (-s.re) ≤ (2 : ℝ) ^ (-s.re) := hstep1
      _ ≤ (2 : ℝ) ^ (-1 : ℝ) := hstep2
      _ = 1 / 2 := by norm_num
  have hden : (1 / 2 : ℝ) ≤ ‖(1 : ℂ) - u‖ := by
    have h := norm_sub_norm_le (1 : ℂ) u
    rw [norm_one] at h
    linarith
  have hden0 : (1 : ℂ) - u ≠ 0 := by
    intro h
    rw [h, norm_zero] at hden
    linarith
  have hinv : ‖((1 : ℂ) - u)⁻¹‖ ≤ 2 := by
    rw [norm_inv]
    simpa using inv_anti₀ (by norm_num : (0 : ℝ) < 1 / 2) hden
  have hfac : (1 - u)⁻¹ - 1 = u * (1 - u)⁻¹ := by
    have h : (1 : ℂ) - u ≠ 0 := hden0
    calc (1 - u)⁻¹ - 1 = (1 - u)⁻¹ - (1 - u) * (1 - u)⁻¹ := by rw [mul_inv_cancel₀ h]
      _ = (1 - u)⁻¹ * (1 - (1 - u)) := by ring
      _ = u * (1 - u)⁻¹ := by ring
  have hgoal : ‖(1 - (c : ℂ) ^ (-s))⁻¹ - 1‖ = ‖(1 - u)⁻¹ - 1‖ := by rw [← hu]
  rw [hgoal, hfac, norm_mul]
  calc ‖u‖ * ‖(1 - u)⁻¹‖ ≤ (c : ℝ) ^ (-s.re) * 2 :=
        mul_le_mul hunorm.le hinv (norm_nonneg _) (Real.rpow_nonneg (by positivity) _)
    _ = 2 * (c : ℝ) ^ (-s.re) := by ring

/-- The number of closed points whose residue field has `(Nat.card k) ^ m` elements, counted in
the subtype of closed points. -/
private lemma ncard_setOf_residueField_card_eq (f : X ⟶ Spec (.of k))
    [SmoothOfRelativeDimension 1 f] [IsProper f] [GeometricallyConnected f] (m : ℕ) :
    {x : closedPoints X | Nat.card (X.residueField x.val) = Nat.card k ^ m}.ncard =
      curveZetaClosedPointCount f m := by
  rw [curveZetaClosedPointCount]
  have h : Subtype.val '' {x : closedPoints X | Nat.card (X.residueField x.val) = Nat.card k ^ m} =
      {x : X | x ∈ closedPoints X ∧ Nat.card (X.residueField x) = Nat.card k ^ m} := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y.2, hy⟩
    · rintro ⟨hx, hpx⟩
      exact ⟨⟨x, hx⟩, hpx, rfl⟩
  rw [← h, Set.ncard_image_of_injective _ Subtype.val_injective]

/-- For each degree there are only finitely many closed points of that degree. -/
private lemma finite_setOf_residueField_card_eq (f : X ⟶ Spec (.of k))
    [SmoothOfRelativeDimension 1 f] [IsProper f] [GeometricallyConnected f] (m : ℕ) :
    {x : closedPoints X | Nat.card (X.residueField x.val) = Nat.card k ^ m}.Finite := by
  have h : Subtype.val '' {x : closedPoints X | Nat.card (X.residueField x.val) = Nat.card k ^ m} =
      {x : X | x ∈ closedPoints X ∧ Nat.card (X.residueField x) = Nat.card k ^ m} := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y.2, hy⟩
    · rintro ⟨hx, hpx⟩
      exact ⟨⟨x, hx⟩, hpx, rfl⟩
  exact Set.Finite.of_finite_image (h ▸ curveZeta_closedPointsOfDegree_finite f m)
    Subtype.val_injective.injOn

/-- The number of closed points of degree `m` grows at most like `(Nat.card k) ^ m`. -/
private lemma closedPointCount_le_mul_pow (f : X ⟶ Spec (.of k))
    [SmoothOfRelativeDimension 1 f] [IsProper f] [GeometricallyConnected f] :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ m : ℕ,
      (curveZetaClosedPointCount f m : ℝ) ≤ C * (Nat.card k : ℝ) ^ m := by
  classical
  have hbig : (fun m : ℕ => (curveZetaClosedPointCount f m : ℝ) - (Nat.card k : ℝ) ^ m / m)
      =O[Filter.atTop] (fun m : ℕ => Real.sqrt ((Nat.card k : ℝ) ^ m) / m) := by
    simpa using curveZeta_closedPointsOfDegree_asymptotic f
  obtain ⟨c₀, hc₀⟩ := hbig.bound
  set c : ℝ := max c₀ 0 with hcdef
  have hc0 : 0 ≤ c := le_max_right _ _
  have hc : ∀ᶠ (x : ℕ) in Filter.atTop,
      ‖(curveZetaClosedPointCount f x : ℝ) - (Nat.card k : ℝ) ^ x / x‖ ≤
        c * ‖Real.sqrt ((Nat.card k : ℝ) ^ x) / x‖ :=
    hc₀.mono fun x hx =>
      le_trans hx (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 hc
  have hq1 : (1 : ℝ) < (Nat.card k : ℝ) := by
    have h := two_le_card_baseField (k := k)
    have h' : (1 : ℕ) < Nat.card k := by omega
    exact_mod_cast h'
  have hN₁ : 1 ≤ max N 1 := le_max_right N 1
  refine ⟨max (∑ m ∈ Finset.range (max N 1), (curveZetaClosedPointCount f m : ℝ)) (1 + c), ?_, ?_⟩
  · positivity
  · intro m
    rcases lt_or_ge m (max N 1) with hm | hm
    · have hsum : (curveZetaClosedPointCount f m : ℝ) ≤
          ∑ m ∈ Finset.range (max N 1), (curveZetaClosedPointCount f m : ℝ) :=
        Finset.single_le_sum (f := fun m => (curveZetaClosedPointCount f m : ℝ))
          (fun i _ => by positivity) (Finset.mem_range.2 hm)
      have hpow : (1 : ℝ) ≤ (Nat.card k : ℝ) ^ m := one_le_pow₀ hq1.le
      calc (curveZetaClosedPointCount f m : ℝ)
          ≤ max (∑ m ∈ Finset.range (max N 1), (curveZetaClosedPointCount f m : ℝ)) (1 + c) :=
            le_trans hsum (le_max_left _ _)
        _ = max (∑ m ∈ Finset.range (max N 1), (curveZetaClosedPointCount f m : ℝ)) (1 + c) * 1 :=
            (mul_one _).symm
        _ ≤ max (∑ m ∈ Finset.range (max N 1), (curveZetaClosedPointCount f m : ℝ)) (1 + c) *
              (Nat.card k : ℝ) ^ m :=
            mul_le_mul_of_nonneg_left hpow (by positivity)
    · have hm1 : 1 ≤ m := le_trans hN₁ hm
      have hmpos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm1
      have hbound := hN m (le_trans (le_max_left N 1) hm)
      have hqm : (0 : ℝ) < (Nat.card k : ℝ) ^ m := pow_pos (by linarith) m
      have hsqrt : Real.sqrt ((Nat.card k : ℝ) ^ m) ≤ (Nat.card k : ℝ) ^ m := by
        rw [Real.sqrt_le_self_iff]
        exact Or.inr (one_le_pow₀ hq1.le)
      have hquot : (Nat.card k : ℝ) ^ m / (m : ℝ) ≤ (Nat.card k : ℝ) ^ m := by
        rw [div_le_iff₀ hmpos]
        calc (Nat.card k : ℝ) ^ m = (Nat.card k : ℝ) ^ m * 1 := (mul_one _).symm
          _ ≤ (Nat.card k : ℝ) ^ m * (m : ℝ) :=
              mul_le_mul_of_nonneg_left (by exact_mod_cast hm1) hqm.le
      have hquotSqrt : Real.sqrt ((Nat.card k : ℝ) ^ m) / (m : ℝ) ≤ (Nat.card k : ℝ) ^ m := by
        have h2 : Real.sqrt ((Nat.card k : ℝ) ^ m) / (m : ℝ) ≤
            (Nat.card k : ℝ) ^ m / (m : ℝ) :=
          (div_le_div_iff_of_pos_right hmpos).mpr hsqrt
        linarith
      have hmain : (curveZetaClosedPointCount f m : ℝ) - (Nat.card k : ℝ) ^ m / m ≤
          c * (Nat.card k : ℝ) ^ m := by
        calc (curveZetaClosedPointCount f m : ℝ) - (Nat.card k : ℝ) ^ m / m
            ≤ ‖(curveZetaClosedPointCount f m : ℝ) - (Nat.card k : ℝ) ^ m / m‖ := le_abs_self _
          _ ≤ c * ‖Real.sqrt ((Nat.card k : ℝ) ^ m) / (m : ℝ)‖ := hbound
          _ = c * (Real.sqrt ((Nat.card k : ℝ) ^ m) / (m : ℝ)) := by
              rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
          _ ≤ c * (Nat.card k : ℝ) ^ m := mul_le_mul_of_nonneg_left hquotSqrt hc0
      calc (curveZetaClosedPointCount f m : ℝ)
          ≤ (Nat.card k : ℝ) ^ m / m + c * (Nat.card k : ℝ) ^ m := by linarith
        _ ≤ (Nat.card k : ℝ) ^ m + c * (Nat.card k : ℝ) ^ m := by
            linarith [hquot]
        _ = (1 + c) * (Nat.card k : ℝ) ^ m := by ring
        _ ≤ max (∑ m ∈ Finset.range (max N 1), (curveZetaClosedPointCount f m : ℝ)) (1 + c) *
              (Nat.card k : ℝ) ^ m := by
            exact mul_le_mul_of_nonneg_right (le_max_right _ _) hqm.le

/-- Paper: (14.2.0.1), p. 534. The product converges absolutely on its
half-plane of definition. -/
theorem summable_curveZetaEulerFactor_sub_one (f : X ⟶ Spec (.of k))
    [SmoothOfRelativeDimension 1 f] [IsProper f] [GeometricallyConnected f]
    (s : {s : ℂ // 1 < s.re}) :
    Summable (fun x : closedPoints X ↦ ‖curveZetaEulerFactor x s.val - 1‖) := by
  classical
  obtain ⟨C, hC0, hC⟩ := closedPointCount_le_mul_pow f
  have hq1 : (1 : ℝ) < (Nat.card k : ℝ) := by
    have h : (1 : ℕ) < Nat.card k := by
      have := two_le_card_baseField (k := k)
      omega
    exact_mod_cast h
  have hq0 : (0 : ℝ) < (Nat.card k : ℝ) := by linarith
  have hσ1 : 1 < s.val.re := s.2
  set r : ℝ := (Nat.card k : ℝ) ^ (1 - s.val.re) with hr
  have hr0 : 0 ≤ r := by rw [hr]; positivity
  have hr1 : r < 1 := by
    rw [hr, Real.rpow_lt_one_iff_of_pos hq0]
    exact Or.inl ⟨hq1, by linarith⟩
  let deg : closedPoints X → ℕ :=
    fun x => Classical.choose (residueField_card_eq_pow_of_closed f x.2)
  have hdeg : ∀ x : closedPoints X, Nat.card (X.residueField x.val) = Nat.card k ^ deg x :=
    fun x => (Classical.choose_spec (residueField_card_eq_pow_of_closed f x.2)).2
  refine summable_of_sum_le (f := fun x : closedPoints X => ‖curveZetaEulerFactor x s.val - 1‖)
    (fun _ => norm_nonneg _) (c := 2 * C * (1 - r)⁻¹) ?_
  intro T
  have step1 : ∑ x ∈ T, ‖curveZetaEulerFactor x s.val - 1‖
      ≤ ∑ x ∈ T, 2 * ((Nat.card k : ℝ) ^ deg x) ^ (-s.val.re) := by
    refine Finset.sum_le_sum fun x _ => ?_
    have h2 := two_le_card_residueField f x
    refine le_trans (norm_curveZetaEulerFactor_sub_one_le (Nat.card (X.residueField x.val)) h2 hσ1) ?_
    have hcast : (Nat.card (X.residueField x.val) : ℝ) = (Nat.card k : ℝ) ^ deg x := by
      rw [hdeg x, Nat.cast_pow]
    rw [hcast]
  have step2 : ∑ x ∈ T, 2 * ((Nat.card k : ℝ) ^ deg x) ^ (-s.val.re)
      = ∑ m ∈ T.image deg,
          ((T.filter fun x => deg x = m).card : ℝ) * (2 * ((Nat.card k : ℝ) ^ m) ^ (-s.val.re)) := by
    rw [← Finset.sum_fiberwise_of_maps_to' (s := T) (g := deg) (t := T.image deg)
      (fun x hx => Finset.mem_image_of_mem deg hx)
      (f := fun m : ℕ => 2 * ((Nat.card k : ℝ) ^ m) ^ (-s.val.re))]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [Finset.sum_const, nsmul_eq_mul]
  have step3 : ∑ m ∈ T.image deg,
        ((T.filter fun x => deg x = m).card : ℝ) * (2 * ((Nat.card k : ℝ) ^ m) ^ (-s.val.re))
      ≤ ∑ m ∈ T.image deg,
          (C * (Nat.card k : ℝ) ^ m) * (2 * ((Nat.card k : ℝ) ^ m) ^ (-s.val.re)) := by
    refine Finset.sum_le_sum fun m _ => ?_
    have hcard : ((T.filter fun x => deg x = m).card : ℝ) ≤ (curveZetaClosedPointCount f m : ℝ) := by
      have hfin := finite_setOf_residueField_card_eq f m
      have hsub : (↑(T.filter fun x => deg x = m) : Set (closedPoints X)) ⊆
          {x : closedPoints X | Nat.card (X.residueField x.val) = Nat.card k ^ m} := by
        intro x hx
        simp only [Finset.coe_filter, Set.mem_ofPred_eq] at hx ⊢
        rw [hdeg x, hx.2]
      have h1 : (↑(T.filter fun x => deg x = m) : Set (closedPoints X)).ncard ≤
          {x : closedPoints X | Nat.card (X.residueField x.val) = Nat.card k ^ m}.ncard :=
        Set.ncard_le_ncard hsub hfin
      rw [ncard_setOf_residueField_card_eq f m, Set.ncard_coe_finset] at h1
      exact_mod_cast h1
    have hle := hC m
    have hpos : (0 : ℝ) ≤ 2 * ((Nat.card k : ℝ) ^ m) ^ (-s.val.re) := by positivity
    calc ((T.filter fun x => deg x = m).card : ℝ) * (2 * ((Nat.card k : ℝ) ^ m) ^ (-s.val.re))
        ≤ (curveZetaClosedPointCount f m : ℝ) * (2 * ((Nat.card k : ℝ) ^ m) ^ (-s.val.re)) :=
          mul_le_mul_of_nonneg_right hcard hpos
      _ ≤ (C * (Nat.card k : ℝ) ^ m) * (2 * ((Nat.card k : ℝ) ^ m) ^ (-s.val.re)) :=
          mul_le_mul_of_nonneg_right hle hpos
  have hcombine : ∀ m : ℕ,
      ((Nat.card k : ℝ) ^ m) * (((Nat.card k : ℝ) ^ m) ^ (-s.val.re)) = r ^ m := by
    intro m
    rw [hr]
    calc ((Nat.card k : ℝ) ^ m) * (((Nat.card k : ℝ) ^ m) ^ (-s.val.re))
        = ((Nat.card k : ℝ) ^ (m : ℝ)) * (((Nat.card k : ℝ) ^ (m : ℝ)) ^ (-s.val.re)) := by
          rw [Real.rpow_natCast]
      _ = ((Nat.card k : ℝ) ^ (m : ℝ)) * ((Nat.card k : ℝ) ^ ((m : ℝ) * (-s.val.re))) := by
          rw [Real.rpow_mul hq0.le]
      _ = ((Nat.card k : ℝ) ^ ((m : ℝ) + (m : ℝ) * (-s.val.re))) := by
          rw [Real.rpow_add hq0]
      _ = ((Nat.card k : ℝ) ^ ((1 - s.val.re) * (m : ℝ))) := by
          congr 1
          ring
      _ = (((Nat.card k : ℝ) ^ (1 - s.val.re)) ^ (m : ℝ)) := by
          rw [Real.rpow_mul hq0.le]
      _ = (((Nat.card k : ℝ) ^ (1 - s.val.re)) ^ m) := by
          rw [Real.rpow_natCast]
  have step4 : ∑ m ∈ T.image deg,
        (C * (Nat.card k : ℝ) ^ m) * (2 * ((Nat.card k : ℝ) ^ m) ^ (-s.val.re))
      = ∑ m ∈ T.image deg, (2 * C) * r ^ m := by
    refine Finset.sum_congr rfl fun m _ => ?_
    calc (C * (Nat.card k : ℝ) ^ m) * (2 * ((Nat.card k : ℝ) ^ m) ^ (-s.val.re))
        = 2 * C * (((Nat.card k : ℝ) ^ m) * (((Nat.card k : ℝ) ^ m) ^ (-s.val.re))) := by ring
      _ = 2 * C * r ^ m := by rw [hcombine m]
  have step5 : ∑ m ∈ T.image deg, (2 * C) * r ^ m ≤ 2 * C * (1 - r)⁻¹ := by
    have hsummable : Summable (fun m : ℕ => r ^ m) := summable_geometric_of_lt_one hr0 hr1
    have htsum : (∑' m : ℕ, r ^ m) = (1 - r)⁻¹ := tsum_geometric_of_lt_one hr0 hr1
    have hle : ∑ m ∈ T.image deg, r ^ m ≤ (1 - r)⁻¹ := by
      rw [← htsum]
      exact hsummable.sum_le_tsum _ (fun m _ => by positivity)
    calc ∑ m ∈ T.image deg, (2 * C) * r ^ m = (2 * C) * ∑ m ∈ T.image deg, r ^ m := by
          rw [Finset.mul_sum]
      _ ≤ (2 * C) * (1 - r)⁻¹ := mul_le_mul_of_nonneg_left hle (by positivity)
  calc ∑ x ∈ T, ‖curveZetaEulerFactor x s.val - 1‖
      ≤ ∑ x ∈ T, 2 * ((Nat.card k : ℝ) ^ deg x) ^ (-s.val.re) := step1
    _ = ∑ m ∈ T.image deg,
          ((T.filter fun x => deg x = m).card : ℝ) * (2 * ((Nat.card k : ℝ) ^ m) ^ (-s.val.re)) :=
        step2
    _ ≤ ∑ m ∈ T.image deg,
          (C * (Nat.card k : ℝ) ^ m) * (2 * ((Nat.card k : ℝ) ^ m) ^ (-s.val.re)) := step3
    _ = ∑ m ∈ T.image deg, (2 * C) * r ^ m := step4
    _ ≤ 2 * C * (1 - r)⁻¹ := step5


/-- Paper: §14.2, p. 535. The Weil point-count estimate with genus g gives
an error constant depending only on g in the closed-point count.
Deviation: Uses the numerical Weil hypothesis and the closed-point expression
for the extension-field counts. The displayed constant is an explicit bound. -/
theorem curveZeta_closedPointsOfDegree_bound_of_weil (f : X ⟶ Spec (.of k))
    [SmoothOfRelativeDimension 1 f] [IsProper f] [GeometricallyConnected f] (g : ℕ) :
    let q : ℝ := Nat.card k
    let N (r : ℕ) : ℝ := ∑ d ∈ r.divisors, (d : ℝ) * curveZetaClosedPointCount f d
    (∀ r : ℕ, 0 < r → |N r - (q ^ r + 1)| ≤ 2 * g * Real.sqrt (q ^ r)) →
    ∀ m : ℕ, 0 < m → |(curveZetaClosedPointCount f m : ℝ) - q ^ m / m| ≤
      (5 + 6 * (g : ℝ)) * Real.sqrt (q ^ m) / m := by sorry

-- TODO(paper-gap): The comparison on p. 535 refers to the missing Theorem
-- 13.3.1.2. Equation (5.3.1.5) supplies a finite-place principal-value
-- operator. The function-field completion, convergence in the topology of
-- uniform convergence on bounded sets, and trace identity are unspecified.

-- TODO(paper-gap): The gonality equality on p. 535 fails for the Hermitian
-- quartic y³ + y = x⁴ over 𝔽₉. Its genus is three and projection to x has
-- degree three. It is maximal and its sole Frobenius eigenvalue has
-- multiplicity six. For g ≥ 2 the general bound gon_k(X) ≤ g + 1 < 2g
-- follows by Riemann–Roch at a rational point. For g = 1 the strict
-- inequality also fails, since gon_k(E) = 2 = 2g. The printed equality
-- and strict inequality need curve-genus and gonality interfaces.

-- TODO(paper-gap): The supersingular example on p. 536 needs a choice of
-- curve with equal Frobenius eigenvalues. Over 𝔽₉, y² = x³ − x has numerator
-- (1 + 3T)². The supersingular curve y² = x³ + (1 + i)x with i² = −1 has
-- numerator 1 + 9T² and gives simple zeros for the quadratic cover's L-function.

-- TODO(paper-gap): §14.3, p. 536 gives n[F : ℚ] as a proposed multiplicity
-- bound for generic zeros. Page 533 identifies these as non-central zeros.
-- A unitary imaginary norm twist translates the zeros in the s-plane.
-- The higher-rank centering convention and argument need to be supplied
-- before stating the bound (ERRATA R24 and M43).

end RiemannMasullo
