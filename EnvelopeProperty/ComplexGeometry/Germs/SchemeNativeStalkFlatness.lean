import EnvelopeProperty.ComplexGeometry.Germs.SchemeNativeHolomorphicGerm
import EnvelopeProperty.ComplexGeometry.Germs.SchemeCoordinateEtale
import EnvelopeProperty.ComplexGeometry.AnalyticGeometry.PolynomialPointAnalyticMap
import Mathlib.RingTheory.Unramified.Finite
import Mathlib.RingTheory.RingHom.FaithfullyFlat

/-!
# Faithful flatness of the same original smooth-scheme native stalk map

Flatness of the actual polynomial composite is transported along the existing
etale coordinates, then localized and passed through the original stalk and
native germ equivalences. No global integrality assumption is used.
-/

set_option autoImplicit false

noncomputable section

namespace HolomorphicGerms

open CategoryTheory AlgebraicGeometry Algebra ComplexSchemes Filter
open ComplexGeometry.Pluripotential ComplexGeometry.AnalyticGeometry
open HironakaHolomorphicJetMonomialSpan HironakaRelativeNormalIdeal

private def germDimensionEquiv {a b : ℕ} (h : a = b) :
    HolGerm (ComplexModel a) ≃+* HolGerm (ComplexModel b) := by
  subst b
  exact RingEquiv.refl _

private theorem germDimensionEquiv_const {a b : ℕ} (h : a = b) (c : ℂ) :
    germDimensionEquiv h (HolGerm.constHom c) = HolGerm.constHom c := by
  subst b
  rfl

private theorem germDimensionEquiv_coordinate {a b : ℕ} (h : a = b) (i : Fin a) :
    germDimensionEquiv h (coordinateGerm i) = coordinateGerm (Fin.cast h i) := by
  subst b
  rfl

/-- The shared actual polynomial germ map in the same normalized coordinate dimension. -/
def schemeTranslatedPolynomialGerm {n : ℕ} (x : Fin n → ℂ) :
    MvPolynomial (Fin n) ℂ →+* HolGerm (ComplexModel n) :=
  (germDimensionEquiv (Nat.zero_add n)).toRingHom.comp
    (PolynomialPointAnalyticMap.polynomialGermMap x).toRingHom

private theorem schemeTranslatedPolynomialGerm_X {n : ℕ} (x : Fin n → ℂ) (i : Fin n) :
    schemeTranslatedPolynomialGerm x (MvPolynomial.X i) =
      coordinateGerm i + HolGerm.constHom (x i) := by
  change germDimensionEquiv (Nat.zero_add n)
    (PolynomialPointAnalyticMap.polynomialGermMap x (MvPolynomial.X i)) = _
  rw [PolynomialPointAnalyticMap.polynomialGermMap_X, map_add,
    germDimensionEquiv_const, normalCoordinate, germDimensionEquiv_coordinate]
  congr 2
  apply Fin.ext
  simp

variable {X : Scheme} (f : X ⟶ Spec (.of ℂ)) (n : ℕ)
  [SmoothOfRelativeDimension n f] (p : SchemeComplexPoint f)

local instance flatSchemeAffineAlgebra : Algebra ℂ (SchemeCoordinateAffineRing f n p) :=
  affinePointFieldAlgebra ((standardSmoothComplexAffineChart f n p).val.map ≫ f)

/-- The original polynomial composite is exactly the shared actual translated map. -/
theorem schemeCoordinatePolynomialGerm_eq_translated :
    (schemeCoordinateModelGermEquiv n).toRingHom.comp (schemeCoordinatePolynomialGerm f n p) =
      schemeTranslatedPolynomialGerm (fun i => standardSmoothComplexAlgebraPoint f n p
        (standardSmoothComplexChartFreeGenerator f n p i)) := by
  apply MvPolynomial.ringHom_ext
  · intro c
    change schemeCoordinateModelGermEquiv n
      (schemeCoordinateRegularGerm f n p
        ((schemeCoordinatePolynomialMap f n p) (MvPolynomial.C c))) = _
    rw [schemeCoordinatePolynomialMap, MvPolynomial.aeval_C,
      schemeCoordinateRegularGerm_scalar, schemeCoordinateModelGermEquiv_const]
    change HolGerm.constHom c = germDimensionEquiv (Nat.zero_add n)
      (PolynomialPointAnalyticMap.polynomialGermMap _ (MvPolynomial.C c))
    have hc : PolynomialPointAnalyticMap.polynomialGermMap
        (fun i => standardSmoothComplexAlgebraPoint f n p
          (standardSmoothComplexChartFreeGenerator f n p i)) (MvPolynomial.C c) =
        HolGerm.constHom c :=
      (PolynomialPointAnalyticMap.polynomialGermMap _).commutes c
    rw [hc, germDimensionEquiv_const]
  · intro i
    change schemeCoordinateModelGermEquiv n
      (schemeCoordinateRegularGerm f n p
        ((schemeCoordinatePolynomialMap f n p) (MvPolynomial.X i))) = _
    rw [schemeCoordinatePolynomialMap, MvPolynomial.aeval_X, schemeTranslatedPolynomialGerm_X]
    have h := congrArg (schemeCoordinateModelGermEquiv n)
      (schemeCoordinateCenteredFreeGenerator_germ f n p i)
    rw [schemeCoordinateCenteredFreeGenerator, map_sub, schemeCoordinateRegularGerm_scalar,
      map_sub, schemeCoordinateModelGermEquiv_const,
      schemeCoordinateModelGermEquiv_coordinate] at h
    exact sub_eq_iff_eq_add.mp h

/-- Flatness of the existing original polynomial-coordinate composite. -/
theorem schemeCoordinatePolynomialGerm_flat :
    (schemeCoordinatePolynomialGerm f n p).Flat := by
  apply (RingHom.Flat.comp_iff_of_bijective_left
    (schemeCoordinateModelGermEquiv n).bijective).mp
  change ((schemeCoordinateModelGermEquiv n).toRingHom.comp
    (schemeCoordinatePolynomialGerm f n p)).Flat
  rw [schemeCoordinatePolynomialGerm_eq_translated]
  exact (PolynomialPointAnalyticMap.polynomialGermMap_flat _).comp
    (RingHom.Flat.of_bijective (germDimensionEquiv (Nat.zero_add n)).bijective)

/-- The existing etale coordinates upgrade polynomial flatness to affine flatness. -/
theorem schemeCoordinateRegularGerm_flat :
    (schemeCoordinateRegularGerm f n p).Flat := by
  let B := MvPolynomial (Fin n) ℂ
  let A := SchemeCoordinateAffineRing f n p
  let H := HolGerm (Fin n → ℂ)
  let : Algebra B A := (schemeCoordinatePolynomialMap f n p).toRingHom.toAlgebra
  let : Algebra A H := (schemeCoordinateRegularGerm f n p).toAlgebra
  let : Algebra B H := (schemeCoordinatePolynomialGerm f n p).toAlgebra
  let : IsScalarTower B A H := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let : Algebra.Etale B A :=
    RingHom.etale_algebraMap.mp (schemeCoordinatePolynomialMap_etale f n p)
  let : Module.Flat B H := schemeCoordinatePolynomialGerm_flat f n p
  change Module.Flat A H
  exact Algebra.FormallyUnramified.flat_of_restrictScalars B A H

/-- Flatness of the original local map with its original denominator action. -/
theorem schemeCoordinateLocalRegularGerm_flat :
    (schemeCoordinateLocalRegularGerm f n p).Flat := by
  let A := SchemeCoordinateAffineRing f n p
  let L := SchemeCoordinateLocalRing f n p
  let H := HolGerm (Fin n → ℂ)
  let : Algebra A H := (schemeCoordinateRegularGerm f n p).toAlgebra
  let : Algebra L H := (schemeCoordinateLocalRegularGerm f n p).toAlgebra
  let : IsScalarTower A L H := IsScalarTower.of_algebraMap_eq fun a =>
    (schemeCoordinateLocalRegularGerm_algebraMap f n p a).symm
  let : Module.Flat A H := schemeCoordinateRegularGerm_flat f n p
  change Module.Flat L H
  exact (Module.flat_iff_of_isLocalization L (schemeCoordinatePointIdeal f n p).primeCompl H).mpr
    inferInstance

/-- Localness and flatness prove faithful flatness without global integrality. -/
theorem schemeCoordinateLocalRegularGerm_faithfullyFlat :
    (schemeCoordinateLocalRegularGerm f n p).FaithfullyFlat := by
  let : Algebra (SchemeCoordinateLocalRing f n p) (HolGerm (Fin n → ℂ)) :=
    (schemeCoordinateLocalRegularGerm f n p).toAlgebra
  let : Module.Flat (SchemeCoordinateLocalRing f n p) (HolGerm (Fin n → ℂ)) :=
    schemeCoordinateLocalRegularGerm_flat f n p
  let : IsLocalHom (algebraMap (SchemeCoordinateLocalRing f n p) (HolGerm (Fin n → ℂ))) :=
    schemeCoordinateLocalRegularGerm_isLocalHom f n p
  exact Module.FaithfullyFlat.of_flat_of_isLocalHom

/-- Flatness starts at the same original scheme stalk, not a replacement local ring. -/
theorem schemeCoordinateStalkRegularGerm_flat :
    (schemeCoordinateStalkRegularGerm f n p).Flat :=
  (RingHom.Flat.of_bijective (schemeCoordinateStalkEquiv f n p).symm.bijective).comp
    (schemeCoordinateLocalRegularGerm_flat f n p)

variable [IsSeparated f] [QuasiCompact f]

local instance flatNativeSchemePointTopology : TopologicalSpace (SchemeComplexPoint f) :=
  schemeAnalyticPointTopology f

local instance flatNativeSchemePointCharts : ChartedSpace (ComplexModel n) (SchemeComplexPoint f) :=
  schemeAnalyticComplexChartedSpace f n

local instance flatNativeSchemePointManifold : IsComplexManifold n (SchemeComplexPoint f) :=
  schemeAnalyticComplex_isComplexManifold f n

/-- Flatness of the existing map to the whole original native holomorphic stalk. -/
theorem schemeNativeStalkGerm_flat : (schemeNativeStalkGerm f n p).Flat :=
  (schemeCoordinateStalkRegularGerm_flat f n p).comp
    (RingHom.Flat.of_bijective (schemeNativeCoordinateGermEquiv f n p).bijective)

/-- The same original native map is faithfully flat, without an integrality assumption. -/
theorem schemeNativeStalkGerm_faithfullyFlat :
    (schemeNativeStalkGerm f n p).FaithfullyFlat := by
  let : Algebra (X.presheaf.stalk (schemeComplexPointImage f p))
      (NativeHolGerm n (SchemeComplexPoint f) p) := (schemeNativeStalkGerm f n p).toAlgebra
  let : Module.Flat (X.presheaf.stalk (schemeComplexPointImage f p))
      (NativeHolGerm n (SchemeComplexPoint f) p) := schemeNativeStalkGerm_flat f n p
  let : IsLocalHom (algebraMap (X.presheaf.stalk (schemeComplexPointImage f p))
      (NativeHolGerm n (SchemeComplexPoint f) p)) := schemeNativeStalkGerm_isLocalHom f n p
  exact Module.FaithfullyFlat.of_flat_of_isLocalHom

/-- Faithful flatness detects whole original stalk ideal membership. -/
theorem mem_ideal_iff_schemeNativeStalkGerm
    (I : Ideal (X.presheaf.stalk (schemeComplexPointImage f p)))
    (a : X.presheaf.stalk (schemeComplexPointImage f p)) :
    a ∈ I ↔ schemeNativeStalkGerm f n p a ∈ I.map (schemeNativeStalkGerm f n p) := by
  let : Algebra (X.presheaf.stalk (schemeComplexPointImage f p))
      (NativeHolGerm n (SchemeComplexPoint f) p) := (schemeNativeStalkGerm f n p).toAlgebra
  let : Module.FaithfullyFlat (X.presheaf.stalk (schemeComplexPointImage f p))
      (NativeHolGerm n (SchemeComplexPoint f) p) := schemeNativeStalkGerm_faithfullyFlat f n p
  exact Iff.symm (SetLike.ext_iff.mp (Ideal.comap_map_eq_self_of_faithfullyFlat
    (B := NativeHolGerm n (SchemeComplexPoint f) p) I) a)

/-- Containment reflection for arbitrary whole original scheme stalk ideals. -/
theorem ideal_le_iff_schemeNativeStalkGerm
    (I J : Ideal (X.presheaf.stalk (schemeComplexPointImage f p))) :
    I ≤ J ↔ I.map (schemeNativeStalkGerm f n p) ≤ J.map (schemeNativeStalkGerm f n p) := by
  refine ⟨Ideal.map_mono, ?_⟩
  intro h a ha
  exact (mem_ideal_iff_schemeNativeStalkGerm f n p J a).mpr
    (h (Ideal.mem_map_of_mem (schemeNativeStalkGerm f n p) ha))

/-- Actual product containment reflects along the same original native stalk map. -/
theorem ideal_le_mul_iff_schemeNativeStalkGerm
    (I J K : Ideal (X.presheaf.stalk (schemeComplexPointImage f p))) :
    I ≤ J * K ↔ I.map (schemeNativeStalkGerm f n p) ≤
      J.map (schemeNativeStalkGerm f n p) * K.map (schemeNativeStalkGerm f n p) := by
  simpa only [Ideal.map_mul] using ideal_le_iff_schemeNativeStalkGerm f n p I (J * K)

end HolomorphicGerms
