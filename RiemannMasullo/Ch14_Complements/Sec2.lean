module

public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.Analysis.Meromorphic.Order
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Complex
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Data.Finset.NatDivisors
public import Mathlib.Data.Set.Card
public import Mathlib.FieldTheory.Finite.GaloisField
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

/-- The order of `exp w - 1` at a point where `exp w = 1` is `1`. -/
private lemma meromorphicOrderAt_exp_sub_one (w : ℂ) (hw : Complex.exp w = 1) :
    meromorphicOrderAt (fun s : ℂ => Complex.exp s - 1) w = 1 := by
  have hcomp := meromorphicOrderAt_comp_of_deriv_ne_zero (𝕜 := ℂ) (f := fun x : ℂ => x)
    (g := fun s : ℂ => Complex.exp s - 1) (x := w)
    (analyticAt_cexp.sub analyticAt_const) (by simp [Complex.deriv_exp, hw])
  simp only [Function.comp_def] at hcomp
  rw [hcomp, show Complex.exp w - 1 = 0 from by rw [hw]; ring]
  exact meromorphicOrderAt_id (𝕜 := ℂ)

/-- The order of `1 - exp w` at a point where `exp w = 1` is `1`. -/
private lemma meromorphicOrderAt_one_sub_exp (w : ℂ) (hw : Complex.exp w = 1) :
    meromorphicOrderAt (fun s : ℂ => 1 - Complex.exp s) w = 1 := by
  have h := meromorphicOrderAt_exp_sub_one w hw
  have hneg : meromorphicOrderAt (fun s : ℂ => -(Complex.exp s - 1)) w = 1 := by
    rw [← meromorphicOrderAt_fun_neg (f := fun s : ℂ => Complex.exp s - 1) (x := w)]
    exact h
  rw [show (fun s : ℂ => 1 - Complex.exp s) = fun s : ℂ => -(Complex.exp s - 1) from by
    funext s; ring]
  exact hneg

/-- The reciprocal local factor `(1 - exp w)⁻¹` has a simple pole at `w`. -/
private lemma meromorphicOrderAt_one_sub_exp_inv (w : ℂ) (hw : Complex.exp w = 1) :
    meromorphicOrderAt (fun s : ℂ => (1 - Complex.exp s)⁻¹) w = -1 := by
  have h := meromorphicOrderAt_one_sub_exp w hw
  have hfun : (fun s : ℂ => (1 - Complex.exp s)⁻¹) = (fun s : ℂ => 1 - Complex.exp s)⁻¹ := rfl
  rw [hfun, meromorphicOrderAt_inv, h]

/-- Composing with the affine substitution `s ↦ -(s * L)` (`L ≠ 0`) transports the pole. -/
private lemma meromorphicOrderAt_one_sub_exp_inv_affine (L : ℝ) (hL : L ≠ 0) (z : ℂ)
    (hz : Complex.exp (-(z * (L : ℂ))) = 1) :
    meromorphicOrderAt (fun s : ℂ => (1 - Complex.exp (-(s * (L : ℂ))))⁻¹) z = -1 := by
  have h := meromorphicOrderAt_comp_of_deriv_ne_zero (𝕜 := ℂ)
    (f := fun s : ℂ => (1 - Complex.exp s)⁻¹) (g := fun s : ℂ => -(s * (L : ℂ))) (x := z)
    (by fun_prop) (by simp [hL])
  simp only [Function.comp_def] at h
  rw [h]
  exact meromorphicOrderAt_one_sub_exp_inv _ hz

/-- The complex power of a positive natural number, written through the exponential. -/
private lemma natCast_cpow_eq_exp (c : ℕ) (hc : c ≠ 0) (z : ℂ) :
    (c : ℂ) ^ (-z) = Complex.exp (-(z * (Real.log c : ℂ))) := by
  have hc0 : (c : ℂ) ≠ 0 := by simpa using hc
  rw [Complex.cpow_def_of_ne_zero hc0, Complex.natCast_log]
  ring_nf

/-- A single local factor `(1 - c ^ (-s))⁻¹` with `c ≥ 2` has a simple pole at every `z`
where `c ^ (-z) = 1`. -/
private lemma meromorphicOrderAt_cpow_factor (c : ℕ) (hc : 2 ≤ c) (z : ℂ)
    (hz : (c : ℂ) ^ (-z) = 1) :
    meromorphicOrderAt (fun s : ℂ => (1 - (c : ℂ) ^ (-s))⁻¹) z = -1 := by
  have hc0 : c ≠ 0 := by omega
  have hL : Real.log c ≠ 0 := by
    have h1 : (1 : ℝ) < c := by exact_mod_cast hc
    exact ne_of_gt (Real.log_pos h1)
  have hz' : Complex.exp (-(z * (Real.log c : ℂ))) = 1 := by
    rw [← natCast_cpow_eq_exp c hc0 z]
    exact hz
  have hfun : (fun s : ℂ => (1 - (c : ℂ) ^ (-s))⁻¹) =
      fun s : ℂ => (1 - Complex.exp (-(s * (Real.log c : ℂ))))⁻¹ := by
    funext s
    rw [natCast_cpow_eq_exp c hc0 s]
  rw [hfun]
  exact meromorphicOrderAt_one_sub_exp_inv_affine _ hL z hz'

/-- The residue field of a closed point of a curve over a finite field is a finite extension
of the base field, so its cardinality is a positive power of `Nat.card k`. -/
private theorem closedPoint_residueField_card_pow (f : X ⟶ Spec (.of k))
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
  have hq : 2 ≤ Nat.card k := by
    rw [Nat.card_eq_fintype_card]; exact Fintype.one_lt_card
  have hc : 2 ≤ Nat.card (X.residueField x) := by
    rw [Nat.card_eq_fintype_card]; exact Fintype.one_lt_card
  by_contra hlt
  have h0 : Module.finrank k (X.residueField x) = 0 := by omega
  rw [h0, pow_zero] at hcard
  omega
/-- Paper: §14.2, p. 534. For a finite set of closed points every local
factor has a simple pole at each integral multiple of the imaginary period.
The product has pole order equal to the number of places. -/
theorem curveZetaEulerFactor_prod_order (f : X ⟶ Spec (.of k))
    [SmoothOfRelativeDimension 1 f] [IsProper f] [GeometricallyConnected f]
    (S : Finset (closedPoints X)) (n : ℤ) :
    meromorphicOrderAt (fun s : ℂ ↦ ∏ x ∈ S, curveZetaEulerFactor x s)
      (2 * Real.pi * Complex.I * n / Real.log (Nat.card k)) = -(S.card : ℤ) := by
  have hq : 2 ≤ Nat.card k := by
    haveI : Fintype k := Fintype.ofFinite k
    rw [Nat.card_eq_fintype_card]
    exact Fintype.one_lt_card
  have hlogk : Real.log (Nat.card k) ≠ 0 := by
    have h1 : (1 : ℝ) < Nat.card k := by exact_mod_cast hq
    exact ne_of_gt (Real.log_pos h1)
  set s0 : ℂ := 2 * Real.pi * Complex.I * n / Real.log (Nat.card k) with hs0
  have hkey : ∀ x ∈ S, meromorphicOrderAt (curveZetaEulerFactor x) s0 = -1 := by
    intro x _
    obtain ⟨m, hm1, hm⟩ := closedPoint_residueField_card_pow f x.2
    have hc2 : 2 ≤ Nat.card (X.residueField x.val) := by
      rw [hm]
      exact le_trans hq (le_self_pow (by omega) (by omega))
    have hval : (Nat.card (X.residueField x.val) : ℂ) ^ (-s0) = 1 := by
      have hc0 : Nat.card (X.residueField x.val) ≠ 0 := by omega
      have hlogc : Real.log (Nat.card (X.residueField x.val)) =
          (m : ℝ) * Real.log (Nat.card k) := by
        rw [hm, Nat.cast_pow, Real.log_pow]
      rw [natCast_cpow_eq_exp _ hc0, hlogc, hs0]
      push_cast
      have hlk : Complex.log ((Nat.card k : ℕ) : ℂ) ≠ 0 := by
        rw [← Complex.natCast_log]
        exact_mod_cast hlogk
      have harg : -((2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) / Complex.log ((Nat.card k : ℕ) : ℂ)) *
            ((m : ℂ) * Complex.log ((Nat.card k : ℕ) : ℂ))) =
          ((-(n * (m : ℤ)) : ℤ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
        field_simp
        push_cast
        ring
      rw [harg]
      simpa using Complex.exp_int_mul_two_pi_mul_I (-(n * (m : ℤ)))
    exact meromorphicOrderAt_cpow_factor _ hc2 s0 hval
  rw [meromorphicOrderAt_fun_prod fun x hx =>
    meromorphicAt_of_meromorphicOrderAt_ne_zero (by rw [hkey x hx]; norm_num)]
  rw [Finset.sum_congr rfl hkey, Finset.sum_const]
  norm_num

-- TODO(paper-gap): Page 534 does not construct the function-field Sobolev
-- quotient or show that the trace approximation requires one Mellin test to
-- cancel all finite-stage poles. Under T = q^(-s) these lifts give one point.

/-- A finitely generated algebra over a finite ring has finitely many ring homs into a
finite field. -/
private theorem finite_ringHom_of_adjoin {R A K : Type u} [CommSemiring R] [Finite R]
    [CommRing A] [Algebra R A] [Field K] [Finite K]
    (s : Finset A) (hs : Algebra.adjoin R (s : Set A) = ⊤) : Finite (A →+* K) := by
  refine Finite.of_injective
    (fun φ : A →+* K => (fun r : R => φ (algebraMap R A r), fun a : s => φ a)) ?_
  intro φ ψ h
  simp only [Prod.mk.injEq, funext_iff] at h
  obtain ⟨h1, h2⟩ := h
  have key : ∀ a, a ∈ Algebra.adjoin R (s : Set A) → φ a = ψ a := by
    intro a ha
    refine Algebra.adjoin_induction (p := fun a _ => φ a = ψ a) ?_ ?_ ?_ ?_ ha
    · intro x hx
      exact h2 ⟨x, hx⟩
    · intro r
      exact h1 r
    · intro x y _ _ ihx ihy
      rw [map_add, map_add, ihx, ihy]
    · intro x y _ _ ihx ihy
      rw [map_mul, map_mul, ihx, ihy]
  exact RingHom.ext fun a => key a (hs ▸ Algebra.mem_top)

/-- Morphisms from the spectrum of a finite field into an affine open of a scheme locally of
finite type over a finite field are finite in number. -/
private theorem finite_spec_hom_affineOpen (f : X ⟶ Spec (.of k)) [LocallyOfFiniteType f]
    (K : Type u) [Field K] [Finite K] (U : X.Opens) (hU : IsAffineOpen U) :
    Finite (Spec (.of K) ⟶ ↑U) := by
  have hle : U ≤ f ⁻¹ᵁ (⊤ : (Spec (.of k)).Opens) := by simp
  let g : Γ(Spec (.of k), ⊤) →+* Γ(X, U) := (Scheme.Hom.appLE f ⊤ U hle).hom
  have hg : g.FiniteType :=
    LocallyOfFiniteType.finiteType_appLE f (isAffineOpen_top _) hU hle
  haveI : Finite Γ(Spec (.of k), ⊤) :=
    Finite.of_injective
      ((Scheme.ΓSpecIso (.of k)).commRingCatIsoToRingEquiv : Γ(Spec (.of k), ⊤) → k)
      (Scheme.ΓSpecIso (.of k)).commRingCatIsoToRingEquiv.injective
  have hAfin : Finite (Γ(X, U) →+* K) := by
    letI := g.toAlgebra
    obtain ⟨s, hs⟩ := hg.out
    exact finite_ringHom_of_adjoin s hs
  have h1 : Finite (Spec (.of K) ⟶ Spec (Γ(X, U))) := by
    have h2 : Finite (CommRingCat.of (Γ(X, U)) ⟶ CommRingCat.of K) :=
      Finite.of_injective (fun f => f.hom) (fun f g' h => CommRingCat.Hom.ext h)
    exact Finite.of_injective (fun φ => Spec.homEquiv φ) Spec.homEquiv.injective
  exact Finite.of_injective (fun φ : Spec (.of K) ⟶ ↑U => φ ≫ hU.isoSpec.hom)
    (fun φ ψ h => by
      have := congrArg (fun t => t ≫ hU.isoSpec.inv) h
      simpa [Category.assoc] using this)

/-- A scheme locally of finite type and quasi-compact over a finite field has finitely many
points with values in any fixed finite field. -/
private theorem finite_spec_hom (f : X ⟶ Spec (.of k)) [LocallyOfFiniteType f] [QuasiCompact f]
    (K : Type u) [Field K] [Finite K] : Finite (Spec (.of K) ⟶ X) := by
  classical
  haveI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  have hpick : ∀ x : X, ∃ U : X.affineOpens, x ∈ (U : X.Opens) := by
    intro x
    obtain ⟨_, ⟨U, hU, rfl⟩, hx, -⟩ :=
      X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
    exact ⟨⟨U, hU⟩, hx⟩
  choose U hU using hpick
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (s := Set.univ)
    (U := fun x : X => (U x : Set X)) (fun x => (U x : X.Opens).isOpen)
    (fun y _ => Set.mem_iUnion.mpr ⟨y, hU y⟩)
  have hcover : ∀ y : X, ∃ x : X, x ∈ t ∧ y ∈ (U x : X.Opens) := by
    intro y
    have h := ht (Set.mem_univ y)
    simpa using h
  haveI hpiece : ∀ x : X, Finite (Spec (.of K) ⟶ ↑(U x : X.Opens)) :=
    fun x => finite_spec_hom_affineOpen f K (U x : X.Opens) (U x).2
  let pt : Spec (.of K) := IsLocalRing.closedPoint K
  haveI : Unique ↥(Spec (.of K)) := inferInstance
  have key : ∀ h : Spec (.of K) ⟶ X,
      ∃ (i : t) (h' : Spec (.of K) ⟶ ↑(U (i : X) : X.Opens)),
        h' ≫ (U (i : X) : X.Opens).ι = h := by
    intro h
    obtain ⟨x, hx, hmem⟩ := hcover (h pt)
    have hrange : Set.range ⇑h ⊆ Set.range ⇑(U x : X.Opens).ι := by
      rw [Scheme.Opens.range_ι]
      intro y hy
      obtain ⟨z, rfl⟩ := hy
      rw [Subsingleton.elim z pt]
      exact hmem
    exact ⟨⟨x, hx⟩, IsOpenImmersion.lift (U x : X.Opens).ι h hrange,
      IsOpenImmersion.lift_fac (U x : X.Opens).ι h hrange⟩
  let F : (Spec (.of K) ⟶ X) → Σ i : t, (Spec (.of K) ⟶ ↑(U (i : X) : X.Opens)) :=
    fun h => ⟨(key h).choose, (key h).choose_spec.choose⟩
  have Ffac : ∀ h, (F h).2 ≫ (U ((F h).1 : X) : X.Opens).ι = h :=
    fun h => (key h).choose_spec.choose_spec
  refine Finite.of_injective F ?_
  intro a b hab
  have h1 := Ffac a
  have h2 := Ffac b
  rw [hab] at h1
  exact h1.symm.trans h2

/-- Paper: §14.2, last paragraph, p. 534. For each degree there are finitely
many closed points whose residue field has that degree over the base field.
Deviation: Page 534 says that the factors repeat "infinitely many times". The
number at each fixed degree is finite, and p. 535 estimates it; it grows as the
degree tends to infinity. -/
theorem curveZeta_closedPointsOfDegree_finite (f : X ⟶ Spec (.of k))
    [SmoothOfRelativeDimension 1 f] [IsProper f] [GeometricallyConnected f] (m : ℕ) :
    {x : X | x ∈ closedPoints X ∧
      Nat.card (X.residueField x) = Nat.card k ^ m}.Finite := by
  classical
  have hq : 2 ≤ Nat.card k := by
    haveI : Fintype k := Fintype.ofFinite k
    rw [Nat.card_eq_fintype_card]
    exact Fintype.one_lt_card
  rcases m with _ | m
  · have hempty : {x : X | x ∈ closedPoints X ∧
        Nat.card (X.residueField x) = Nat.card k ^ 0} = ∅ := by
      ext x
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_and]
      intro hx hc
      obtain ⟨n, hn, hncard⟩ := closedPoint_residueField_card_pow f hx
      have h2 : 2 ≤ Nat.card (X.residueField x) := by
        rw [hncard]
        exact le_trans hq (le_self_pow (by omega) (by omega))
      rw [pow_zero] at hc
      omega
    rw [hempty]
    exact Set.finite_empty
  · set S : Set X := {x : X | x ∈ closedPoints X ∧
      Nat.card (X.residueField x) = Nat.card k ^ (m + 1)} with hSdef
    rcases S.eq_empty_or_nonempty with hempty | ⟨x₀, hx₀⟩
    · rw [hempty]
      exact Set.finite_empty
    · rw [hSdef] at hx₀
      obtain ⟨hx₀cl, hx₀card⟩ := hx₀
      have hK0 : Nat.card (X.residueField x₀) ≠ 0 := by
        rw [hx₀card]
        exact pow_ne_zero _ (Nat.card_ne_zero.mpr ⟨⟨0⟩, inferInstance⟩)
      haveI : Finite (X.residueField x₀) := (Nat.card_ne_zero.mp hK0).2
      haveI : Fintype (X.residueField x₀) := Fintype.ofFinite _
      haveI : QuasiCompact f := inferInstance
      haveI : Finite (Spec (.of (↥(X.residueField x₀))) ⟶ X) :=
        finite_spec_hom f (↥(X.residueField x₀))
      let pt : ↥(Spec (.of (↥(X.residueField x₀)))) := default
      have hsub : S ⊆ Set.range (fun h : Spec (.of (↥(X.residueField x₀))) ⟶ X => h pt) := by
        intro x hx
        rw [hSdef] at hx
        obtain ⟨hxcl, hxcard⟩ := hx
        have hx0 : Nat.card (X.residueField x) ≠ 0 := by
          rw [hxcard]
          exact pow_ne_zero _ (Nat.card_ne_zero.mpr ⟨⟨0⟩, inferInstance⟩)
        haveI : Finite (X.residueField x) := (Nat.card_ne_zero.mp hx0).2
        haveI : Fintype (X.residueField x) := Fintype.ofFinite _
        have hcard : Fintype.card (X.residueField x) =
            Fintype.card (X.residueField x₀) := by
          have h1 : Fintype.card (X.residueField x) = Nat.card (X.residueField x) :=
            (Nat.card_eq_fintype_card).symm
          have h2 : Fintype.card (X.residueField x₀) = Nat.card (X.residueField x₀) :=
            (Nat.card_eq_fintype_card).symm
          rw [h1, h2, hxcard, hx₀card]
        let e : (X.residueField x) ≃+* (X.residueField x₀) :=
          FiniteField.ringEquivOfCardEq hcard
        let h : Spec (.of (↥(X.residueField x₀))) ⟶ X :=
          Spec.map (CommRingCat.ofHom e.toRingHom) ≫ X.fromSpecResidueField x
        refine ⟨h, ?_⟩
        show (Spec.map (CommRingCat.ofHom e.toRingHom) ≫ X.fromSpecResidueField x) pt = x
        exact Scheme.fromSpecResidueField_apply x _
      exact Set.Finite.subset (Set.finite_range _) hsub

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
