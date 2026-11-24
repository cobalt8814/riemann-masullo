module

public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.Analysis.Meromorphic.Order
public import Mathlib.Analysis.SpecialFunctions.Pow.Complex
public import Mathlib.Data.Finset.NatDivisors
public import Mathlib.Data.Set.Card
public import Mathlib.FieldTheory.Finite.GaloisField
public import Mathlib.Topology.JacobsonSpace
public import Mathlib.Topology.Algebra.InfiniteSum.Defs

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

/-- Paper: (14.2.0.1), p. 534. The product converges absolutely on its
half-plane of definition. -/
theorem summable_curveZetaEulerFactor_sub_one (f : X ⟶ Spec (.of k))
    [SmoothOfRelativeDimension 1 f] [IsProper f] [GeometricallyConnected f]
    (s : {s : ℂ // 1 < s.re}) :
    Summable (fun x : closedPoints X ↦ ‖curveZetaEulerFactor x s.val - 1‖) := by sorry

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

/-- The structure ring map `k →+* κ(x)` at a point of a curve over `k`: the ring map of the
morphism `Spec κ(x) ⟶ Spec k` induced by `X.fromSpecResidueField x ≫ f`. -/
private noncomputable def curveZetaStructMap (f : X ⟶ Spec (.of k)) (x : X) :
    k →+* ↥(X.residueField x) :=
  (Spec.preimage (X.fromSpecResidueField x ≫ f)).hom

omit [Finite k] in
private lemma curveZetaStructMap_spec (f : X ⟶ Spec (.of k)) (x : X) :
    Spec.map (CommRingCat.ofHom (curveZetaStructMap f x)) =
      X.fromSpecResidueField x ≫ f := by
  rw [curveZetaStructMap, CommRingCat.ofHom_hom]
  exact Spec.map_preimage _

/-- A morphism `Spec K ⟶ Spec κ(x)` composed with the structure map of `x` is a morphism over
`k` exactly when the corresponding ring map is a morphism of `k`-algebras. -/
private lemma curveZeta_structMap_comp_iff {K : Type u} [Field K] [Algebra k K]
    (f : X ⟶ Spec (.of k)) (x : X) (ψ : ↥(X.residueField x) →+* K) :
    Spec.map (CommRingCat.ofHom ψ) ≫ X.fromSpecResidueField x ≫ f =
        Spec.map (CommRingCat.ofHom (algebraMap k K)) ↔
      ψ.comp (curveZetaStructMap f x) = algebraMap k K := by
  have hspec := curveZetaStructMap_spec f x
  constructor
  · intro h
    rw [← hspec, ← Spec.map_comp] at h
    have h2 := congrArg CommRingCat.Hom.hom (Spec.map_inj.mp h)
    simpa [RingHom.comp_apply] using h2
  · intro h
    rw [← hspec, ← Spec.map_comp, ← CommRingCat.ofHom_comp, h]

/-- A point of a curve over `k` whose residue field maps into a finite field is a closed point. -/
private lemma curveZeta_isClosed_of_residueFieldMap {K : Type u} [Field K] [Algebra k K]
    [Finite K] (f : X ⟶ Spec (.of k)) [SmoothOfRelativeDimension 1 f] [IsProper f] (x : X)
    (ψ : ↥(X.residueField x) →+* K) (hψ : ψ.comp (curveZetaStructMap f x) = algebraMap k K) :
    IsClosed ({x} : Set X) := by
  classical
  haveI : Module.Finite k K := Module.Finite.of_finite
  haveI : Unique ↥(Spec (.of K)) := inferInstance
  let pt : ↥(Spec (.of K)) := default
  have hof : CommRingCat.ofHom (curveZetaStructMap f x) ≫ CommRingCat.ofHom ψ =
      CommRingCat.ofHom (algebraMap k K) := by
    rw [← CommRingCat.ofHom_comp, hψ]
  obtain ⟨p, hp⟩ : ∃ p : Spec (.of K) ⟶ X,
      p = Spec.map (CommRingCat.ofHom ψ) ≫ X.fromSpecResidueField x := ⟨_, rfl⟩
  have hpcomp : p ≫ f = Spec.map (CommRingCat.ofHom (algebraMap k K)) := by
    rw [hp, Category.assoc, ← curveZetaStructMap_spec f x, ← Spec.map_comp, hof]
  haveI : IsFinite (Spec.map (CommRingCat.ofHom (algebraMap k K))) := by
    rw [IsFinite.SpecMap_iff]
    simpa using RingHom.finite_algebraMap.mpr (inferInstance : Module.Finite k K)
  haveI : IsProper (p ≫ f) := hpcomp ▸ inferInstance
  haveI : IsProper p := IsProper.of_comp p f
  have hcl : IsClosedMap ⇑p := Scheme.Hom.isClosedMap p
  have hsub : Set.range ⇑p ⊆ {x} := by
    rintro y ⟨s, rfl⟩
    rw [hp, Scheme.Hom.comp_apply]
    exact Scheme.fromSpecResidueField_apply x _
  have hxmem : x ∈ Set.range ⇑p :=
    ⟨pt, by
      rw [hp, Scheme.Hom.comp_apply]
      exact Scheme.fromSpecResidueField_apply x _⟩
  rw [← show Set.range ⇑p = {x} from
    Set.Subset.antisymm hsub (Set.singleton_subset_iff.mpr hxmem)]
  exact hcl.isClosed_range

/-- The residue field of a closed point of a curve over `k` is finite over `k` for the structure
map of the point. -/
private lemma curveZeta_moduleFinite_residueField (f : X ⟶ Spec (.of k))
    [SmoothOfRelativeDimension 1 f] {x : X} (hx : IsClosed ({x} : Set X)) :
    letI := (curveZetaStructMap f x).toAlgebra
    Module.Finite k ↥(X.residueField x) := by
  haveI : Smooth f := SmoothOfRelativeDimension.smooth (f := f) (n := 1)
  haveI : LocallyOfFiniteType f := inferInstance
  haveI : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace f
  have h1 : LocallyOfFiniteType (X.fromSpecResidueField x) :=
    (isClosed_singleton_iff_locallyOfFiniteType (X := X)).mp hx
  have h2 : LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (curveZetaStructMap f x))) :=
    (curveZetaStructMap_spec f x) ▸ inferInstance
  have hft : RingHom.FiniteType (curveZetaStructMap f x) :=
    (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).mp h2
  letI := (curveZetaStructMap f x).toAlgebra
  have h3 : Algebra.FiniteType k ↥(X.residueField x) := hft
  exact finite_of_finite_type_of_isJacobsonRing k _

/-- The ring maps from the residue field of a point into `K` that are compatible with its
structure map, regarded as `k`-algebra maps for the structure map itself. -/
private noncomputable def curveZeta_ringHomEquivAlgHom {K : Type u} [Field K] [Algebra k K]
    (f : X ⟶ Spec (.of k)) (x : X) :
    letI := (curveZetaStructMap f x).toAlgebra
    {ψ : ↥(X.residueField x) →+* K // ψ.comp (curveZetaStructMap f x) = algebraMap k K} ≃
      (↥(X.residueField x) →ₐ[k] K) :=
  letI := (curveZetaStructMap f x).toAlgebra
  { toFun := fun ψ =>
      { toFun := ψ.1
        map_one' := map_one ψ.1
        map_mul' := map_mul ψ.1
        map_zero' := map_zero ψ.1
        map_add' := map_add ψ.1
        commutes' := fun r => RingHom.congr_fun ψ.2 r }
    invFun := fun φ => ⟨φ.toRingHom, RingHom.ext fun r => φ.commutes r⟩
    left_inv := fun ψ => Subtype.ext (RingHom.ext fun r => rfl)
    right_inv := fun φ => AlgHom.ext fun r => rfl }

/-- The number of `k`-algebra maps from the residue field of a closed point of degree `d` into a
finite extension of degree divisible by `d` is `d`, and it is `0` otherwise. -/
private lemma curveZeta_natCard_residueFieldMap {K : Type u} [Field K] [Algebra k K] [Finite K]
    (f : X ⟶ Spec (.of k)) (x : X) (d : ℕ)
    (hnd : Nat.card (X.residueField x) = Nat.card k ^ d)
    (hfin : letI := (curveZetaStructMap f x).toAlgebra
      Module.Finite k ↥(X.residueField x)) :
    Nat.card {ψ : ↥(X.residueField x) →+* K //
        ψ.comp (curveZetaStructMap f x) = algebraMap k K} =
      if d ∣ Module.finrank k K then d else 0 := by
  classical
  letI := (curveZetaStructMap f x).toAlgebra
  haveI : Module.Finite k ↥(X.residueField x) := hfin
  have hq : 2 ≤ Nat.card k := by
    have : Fintype k := Fintype.ofFinite k
    rw [Nat.card_eq_fintype_card]
    exact Fintype.one_lt_card
  have hpow : Nat.card ↥(X.residueField x) =
      Nat.card k ^ Module.finrank k ↥(X.residueField x) := Module.natCard_eq_pow_finrank
  have hfl : Module.finrank k ↥(X.residueField x) = d := by
    refine Nat.pow_right_injective hq ?_
    show Nat.card k ^ Module.finrank k ↥(X.residueField x) = Nat.card k ^ d
    rw [← hpow, hnd]
  rw [Nat.card_congr (curveZeta_ringHomEquivAlgHom f x)]
  by_cases h : d ∣ Module.finrank k K
  · have h' : Module.finrank k ↥(X.residueField x) ∣ Module.finrank k K := hfl ▸ h
    rw [if_pos h, ← hfl]
    exact FiniteField.natCard_algHom_of_finrank_dvd h'
  · rw [if_neg h]
    have hempty : IsEmpty (↥(X.residueField x) →ₐ[k] K) := ⟨fun φ => by
      have hd := FiniteField.nonempty_algHom_iff_finrank_dvd.mp ⟨φ⟩
      rw [hfl] at hd
      exact h hd⟩
    exact Nat.card_eq_zero.mpr (Or.inl hempty)

/-- A closed point of degree `d` contributes `d` points over an extension whose degree is a
multiple of `d`. -/
private lemma curveZeta_natCard_fiberOfClosed {K : Type u} [Field K] [Algebra k K] [Finite K]
    (f : X ⟶ Spec (.of k)) [SmoothOfRelativeDimension 1 f] (x : X) (d : ℕ)
    (hx : x ∈ closedPoints X) (hnd : Nat.card (X.residueField x) = Nat.card k ^ d)
    (hdvd : d ∣ Module.finrank k K) :
    Nat.card {ψ : ↥(X.residueField x) →+* K //
        ψ.comp (curveZetaStructMap f x) = algebraMap k K} = d := by
  letI := (curveZetaStructMap f x).toAlgebra
  haveI : Module.Finite k ↥(X.residueField x) :=
    curveZeta_moduleFinite_residueField f (by simpa [closedPoints] using hx)
  rw [curveZeta_natCard_residueFieldMap f x d hnd ‹_›, if_pos hdvd]

/-- A point of the curve whose residue field admits a map into `K` that is compatible with the
structure map has degree dividing the degree of `K`. -/
private lemma curveZeta_dvd_finrank_of_fiber {K : Type u} [Field K] [Algebra k K] [Finite K]
    (f : X ⟶ Spec (.of k)) (x : X)
    (ψ : ↥(X.residueField x) →+* K) (hψ : ψ.comp (curveZetaStructMap f x) = algebraMap k K) :
    letI := (curveZetaStructMap f x).toAlgebra
    Module.finrank k ↥(X.residueField x) ∣ Module.finrank k K := by
  letI := (curveZetaStructMap f x).toAlgebra
  exact FiniteField.nonempty_algHom_iff_finrank_dvd.mp
    ⟨{ toFun := ψ
       map_one' := map_one ψ
       map_mul' := map_mul ψ
       map_zero' := map_zero ψ
       map_add' := map_add ψ
       commutes' := fun r => RingHom.congr_fun hψ r }⟩

/-- A sigma type whose fibers carry a predicate is the subtype of the sigma type on which the
predicate holds. -/
private noncomputable def curveZeta_sigmaSubtypeEquiv {α : Type u} (β : α → Type u)
    (q : (a : α) → β a → Prop) :
    ((a : α) × {b : β a // q a b}) ≃ {x : (a : α) × β a // q x.1 x.2} where
  toFun a := ⟨⟨a.1, a.2.1⟩, a.2.2⟩
  invFun x := ⟨x.1.1, x.1.2, x.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The residue-field fiber of a `k`-morphism, in terms of ring maps rather than of morphisms of
commutative rings. -/
private noncomputable def curveZeta_fiberEquiv {K : Type u} [Field K] [Algebra k K]
    (f : X ⟶ Spec (.of k)) (x : X) :
    {φ : X.residueField x ⟶ ↧K //
        Spec.map φ ≫ X.fromSpecResidueField x ≫ f =
          Spec.map (CommRingCat.ofHom (algebraMap k K))} ≃
      {ψ : ↥(X.residueField x) →+* K //
        ψ.comp (curveZetaStructMap f x) = algebraMap k K} where
  toFun φ := ⟨φ.1.hom, (curveZeta_structMap_comp_iff f x φ.1.hom).mp (by
    rw [CommRingCat.ofHom_hom]
    exact φ.2)⟩
  invFun ψ := ⟨CommRingCat.ofHom ψ.1, (curveZeta_structMap_comp_iff f x ψ.1).mpr ψ.2⟩
  left_inv φ := Subtype.ext (CommRingCat.ofHom_hom φ.1)
  right_inv ψ := Subtype.ext rfl

/-- `k`-morphisms from `Spec K` to a curve are pairs of a point of the curve and a compatible
morphism from its residue field into `K`. -/
private noncomputable def curveZeta_overEquiv {K : Type u} [Field K] [Algebra k K]
    (f : X ⟶ Spec (.of k)) :
    {p : Spec (.of K) ⟶ X // p ≫ f = Spec.map (CommRingCat.ofHom (algebraMap k K))} ≃
      (x : X) × {φ : X.residueField x ⟶ ↧K //
        Spec.map φ ≫ X.fromSpecResidueField x ≫ f =
          Spec.map (CommRingCat.ofHom (algebraMap k K))} :=
  ((Scheme.SpecToEquivOfField K X).subtypeEquiv (p := fun p =>
      p ≫ f = Spec.map (CommRingCat.ofHom (algebraMap k K)))
    (q := fun b : (x : ↥X) × (X.residueField x ⟶ ↧K) =>
      Spec.map b.2 ≫ X.fromSpecResidueField b.1 ≫ f =
        Spec.map (CommRingCat.ofHom (algebraMap k K))) (fun p => by
      have hfac : Spec.map ((Scheme.SpecToEquivOfField K X) p).2 ≫
          X.fromSpecResidueField ((Scheme.SpecToEquivOfField K X) p).1 = p :=
        Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField K X p
      constructor
      · intro h
        rw [← Category.assoc, hfac]
        exact h
      · intro h
        rw [← Category.assoc, hfac] at h
        exact h)).trans
    (curveZeta_sigmaSubtypeEquiv (fun x => (X.residueField x ⟶ ↧K))
      (fun x φ => Spec.map φ ≫ X.fromSpecResidueField x ≫ f =
        Spec.map (CommRingCat.ofHom (algebraMap k K)))).symm

/-- Paper: §14.2, p. 535. A closed point of degree d contributes d rational
points over an extension of degree m exactly when d divides m.
Deviation: Uses the exact counting identity behind the printed upper bound. -/
theorem curveZeta_extensionPointCount (f : X ⟶ Spec (.of k))
    [SmoothOfRelativeDimension 1 f] [IsProper f] [GeometricallyConnected f]
    (K : Type u) [Field K] [Algebra k K] [Finite K] :
    Nat.card {p : Spec (.of K) ⟶ X // p ≫ f = Spec.map (CommRingCat.ofHom (algebraMap k K))} =
      ∑ d ∈ (Module.finrank k K).divisors, d * curveZetaClosedPointCount f d := by
  classical
  have hq : 2 ≤ Nat.card k := by
    have : Fintype k := Fintype.ofFinite k
    rw [Nat.card_eq_fintype_card]
    exact Fintype.one_lt_card
  haveI : Module.Finite k K := Module.Finite.of_finite
  have hm : Module.finrank k K ≠ 0 := by
    intro h0
    have hcard : Nat.card K = Nat.card k ^ Module.finrank k K :=
      Module.natCard_eq_pow_finrank
    rw [h0, pow_zero] at hcard
    have : 2 ≤ Nat.card K := by
      have hK : Fintype K := Fintype.ofFinite K
      rw [Nat.card_eq_fintype_card]
      exact Fintype.one_lt_card
    omega
  set T : ℕ → Set X := fun d => {x : X | x ∈ closedPoints X ∧
    Nat.card (X.residueField x) = Nat.card k ^ d} with hT
  have hTfin : ∀ d, (T d).Finite := fun d => curveZeta_closedPointsOfDegree_finite f d
  set S : Set X := ⋃ d ∈ (Module.finrank k K).divisors, T d with hS
  set Y : X → Type u := fun x => {φ : X.residueField x ⟶ ↧K //
    Spec.map φ ≫ X.fromSpecResidueField x ≫ f =
      Spec.map (CommRingCat.ofHom (algebraMap k K))} with hY
  have hmem : ∀ x : X, Y x → x ∈ S := by
    intro x y
    have hy : y.1.hom.comp (curveZetaStructMap f x) = algebraMap k K :=
      (curveZeta_structMap_comp_iff f x y.1.hom).mp (by
        rw [CommRingCat.ofHom_hom]
        exact y.2)
    have hcl : IsClosed ({x} : Set X) :=
      curveZeta_isClosed_of_residueFieldMap f x y.1.hom hy
    letI := (curveZetaStructMap f x).toAlgebra
    haveI : Module.Finite k ↥(X.residueField x) := curveZeta_moduleFinite_residueField f hcl
    have hpow : Nat.card (X.residueField x) =
        Nat.card k ^ Module.finrank k ↥(X.residueField x) := Module.natCard_eq_pow_finrank
    have hdvd : Module.finrank k ↥(X.residueField x) ∣ Module.finrank k K :=
      curveZeta_dvd_finrank_of_fiber f x y.1.hom hy
    rw [hS]
    exact Set.mem_iUnion₂.mpr
      ⟨_, Nat.mem_divisors.mpr ⟨hdvd, hm⟩, hcl, hpow⟩
  have hYfin : ∀ x ∈ S, Finite (Y x) := by
    intro x hx
    rw [hS] at hx
    obtain ⟨d, -, hxT⟩ := Set.mem_iUnion₂.mp hx
    obtain ⟨hxcl, -⟩ := hxT
    have hcl : IsClosed ({x} : Set X) := hxcl
    letI := (curveZetaStructMap f x).toAlgebra
    haveI : Module.Finite k ↥(X.residueField x) := curveZeta_moduleFinite_residueField f hcl
    haveI : Finite ↥(X.residueField x) := Module.finite_of_finite k
    haveI : Finite (↥(X.residueField x) →+* K) :=
      Finite.of_injective (fun f : ↥(X.residueField x) →+* K => (f : ↥(X.residueField x) → K))
        DFunLike.coe_injective
    haveI : Finite (X.residueField x ⟶ ↧K) :=
      Finite.of_injective (fun φ : X.residueField x ⟶ ↧K => φ.hom)
        (fun a b hab => CommRingCat.hom_ext hab)
    exact Finite.of_injective (fun y : Y x => y.1) (fun a b hab =>
      Subtype.ext (by simpa using hab))
  have hstep1 : Nat.card
      {p : Spec (.of K) ⟶ X // p ≫ f = Spec.map (CommRingCat.ofHom (algebraMap k K))} =
      Nat.card ((x : X) × Y x) := Nat.card_congr (curveZeta_overEquiv f)
  have hSfin : S.Finite := by
    rw [hS]
    exact (Finset.finite_toSet _).biUnion (fun d _ => hTfin d)
  have hstep2 : Nat.card ((x : X) × Y x) = ∑ x ∈ hSfin.toFinset, Nat.card (Y x) := by
    haveI : Fintype ↥S := hSfin.fintype
    haveI : ∀ a : ↥S, Finite (Y a.1) := fun a => hYfin a.1 a.2
    have e : ((x : X) × Y x) ≃ ((a : ↥S) × Y a.1) :=
      { toFun := fun a => ⟨⟨a.1, hmem a.1 a.2⟩, a.2⟩
        invFun := fun a => ⟨a.1.1, a.2⟩
        left_inv := fun a => rfl
        right_inv := fun a => by
          obtain ⟨⟨x, hx⟩, y⟩ := a
          rfl }
    rw [Nat.card_congr e, Nat.card_sigma,
      Finset.sum_subtype hSfin.toFinset (fun x => ⟨fun hx =>
        (Set.Finite.mem_toFinset hSfin).mp hx, fun hx =>
        (Set.Finite.mem_toFinset hSfin).mpr hx⟩) (fun x => Nat.card (Y x))]
  have hstep3 : ∑ x ∈ hSfin.toFinset, Nat.card (Y x) =
      ∑ d ∈ (Module.finrank k K).divisors, d * curveZetaClosedPointCount f d := by
    have hSU : hSfin.toFinset =
        (Module.finrank k K).divisors.biUnion (fun d => (hTfin d).toFinset) := by
      ext x
      rw [Set.Finite.mem_toFinset hSfin, Finset.mem_biUnion]
      constructor
      · intro hx
        rw [hS] at hx
        obtain ⟨d, hd, hxT⟩ := Set.mem_iUnion₂.mp hx
        exact ⟨d, Finset.mem_coe.mp hd, (Set.Finite.mem_toFinset (hTfin d)).mpr hxT⟩
      · rintro ⟨d, hd, hxT⟩
        rw [hS]
        exact Set.mem_iUnion₂.mpr
          ⟨d, Finset.mem_coe.mpr hd, (Set.Finite.mem_toFinset (hTfin d)).mp hxT⟩
    have hdisj : Set.PairwiseDisjoint ((Module.finrank k K).divisors : Set ℕ)
        (fun d => (hTfin d).toFinset) := by
      intro d hd d' hd' hne
      refine Finset.disjoint_left.mpr (fun x hx hx' => ?_)
      have h1 : x ∈ T d := (Set.Finite.mem_toFinset (hTfin d)).mp hx
      have h2 : x ∈ T d' := (Set.Finite.mem_toFinset (hTfin d')).mp hx'
      obtain ⟨-, hc1⟩ := h1
      obtain ⟨-, hc2⟩ := h2
      refine hne (Nat.pow_right_injective hq ?_)
      show Nat.card k ^ d = Nat.card k ^ d'
      rw [← hc1, ← hc2]
    rw [hSU, Finset.sum_biUnion hdisj]
    refine Finset.sum_congr rfl (fun d hd => ?_)
    have hterm : ∀ x ∈ (hTfin d).toFinset, Nat.card (Y x) = d := by
      intro x hx
      have hxT : x ∈ T d := (Set.Finite.mem_toFinset (hTfin d)).mp hx
      obtain ⟨hxcl, hxq⟩ := hxT
      rw [Nat.card_congr (curveZeta_fiberEquiv f x)]
      exact curveZeta_natCard_fiberOfClosed f x d hxcl hxq
        (Nat.mem_divisors.mp hd).1
    rw [Finset.sum_congr rfl hterm, Finset.sum_const, smul_eq_mul, mul_comm]
    congr 1
    rw [← Set.ncard_eq_toFinset_card (T d) (hTfin d)]
    rfl
  rw [hstep1, hstep2, hstep3]

/-- Paper: §14.2, p. 535. The number of degree-m closed points is
q^m/m with error O(q^(m/2)/m) as m tends to infinity.
Deviation: The Big-O constant here is for the given curve. The paper also
specifies uniformity in the curve through its genus. -/
theorem curveZeta_closedPointsOfDegree_asymptotic (f : X ⟶ Spec (.of k))
    [SmoothOfRelativeDimension 1 f] [IsProper f] [GeometricallyConnected f] :
    let q : ℝ := Nat.card k
    (fun m : ℕ ↦ (curveZetaClosedPointCount f m : ℝ) - q ^ m / m) =O[Filter.atTop]
      (fun m : ℕ ↦ Real.sqrt (q ^ m) / m) := by sorry

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
