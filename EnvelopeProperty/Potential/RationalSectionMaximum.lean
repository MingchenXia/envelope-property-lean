import EnvelopeProperty.Berkovich.SchemeRationalScalarLifts
import EnvelopeProperty.FiniteTypeFieldPoint
import Mathlib.AlgebraicGeometry.Morphisms.Separated

/-! # Genuine rational sections, closed native supports and exact scalar restriction -/

open scoped NNReal Classical Topology
open CategoryTheory AlgebraicGeometry
noncomputable section
universe u

namespace EnvelopeProperty

/-- Actual finite field points and algebraic closedness construct an original
rational section without any supplied rational-point data. -/
theorem exists_rational_section_of_finiteType_nonempty
    {K : Type u} [Field K] [IsAlgClosed K] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of K)) [LocallyOfFiniteType f] [Nonempty X] :
    ∃ s : Spec (CommRingCat.of K) ⟶ X, s ≫ f = 𝟙 _ := by
  obtain ⟨L, hL, aL, hfin, p, _, hp⟩ := FiniteTypePoint.exists_finite_field_point f
  let : Field L := hL
  let : Algebra K L := aL
  let : Module.Finite K L := hfin
  let : Algebra.IsIntegral K L := Algebra.IsIntegral.of_finite K L
  let e : K ≃ₐ[K] L := AlgEquiv.ofBijective (IsScalarTower.toAlgHom K K L)
    (IsAlgClosed.algebraMap_bijective_of_isIntegral (k := K) (K := L))
  let s := Spec.map (CommRingCat.ofHom e.symm.toRingHom) ≫ p
  refine ⟨s, ?_⟩
  change Spec.map (CommRingCat.ofHom e.symm.toRingHom) ≫ p ≫ f = _
  rw [hp, ← Spec.map_comp]
  have hcoe : e.symm.toRingHom.comp (algebraMap K L) = RingHom.id K := by
    ext a
    exact e.symm.commutes a
  change Spec.map (CommRingCat.ofHom (e.symm.toRingHom.comp (algebraMap K L))) = _
  rw [hcoe]
  exact Spec.map_id _

end EnvelopeProperty

namespace EnvelopeProperty.Berkovich.RelativeSchemeValuedPoint

variable {K : Type u} [CommRing K] (v : Valuation K ℝ≥0) {X : Scheme.{u}}
  (f : X ⟶ Spec (CommRingCat.of K))

/-- The genuine original norm point of an actual rational section. -/
def sectionNativePoint (s : Spec (CommRingCat.of K) ⟶ X) (hs : s ≫ f = 𝟙 _) :
    RelativeSchemeValuedPoint v f :=
  ⟨SchemeValuedPoint.map s (SchemeValuedPoint.basePoint v), by
    change SchemeValuedPoint.map f (SchemeValuedPoint.map s (SchemeValuedPoint.basePoint v)) =
      SchemeValuedPoint.basePoint v
    rw [← SchemeValuedPoint.map_comp, hs, SchemeValuedPoint.map_id]⟩

/-- Separatedness derives actual closedness of a rational section's native support. -/
theorem isClosed_support_sectionNativePoint [IsSeparated f]
    (s : Spec (CommRingCat.of K) ⟶ X) (hs : s ≫ f = 𝟙 _)
    [T1Space (Spec (CommRingCat.of K))] :
    IsClosed ({(sectionNativePoint v f s hs).1.point} : Set X) := by
  have : IsClosedImmersion (s ≫ f) := by rw [hs]; infer_instance
  have : IsClosedImmersion s := IsClosedImmersion.of_comp s f
  change IsClosed ({s (SchemeValuedPoint.basePoint v).point} : Set X)
  simpa only [Set.image_singleton] using
    s.isClosedEmbedding.isClosedMap _
      (isClosed_singleton : IsClosed ({(SchemeValuedPoint.basePoint v).point} : Set (Spec (CommRingCat.of K))))

end EnvelopeProperty.Berkovich.RelativeSchemeValuedPoint

namespace EnvelopeProperty.Berkovich.SchemeScalarBaseChange

variable {F E : Type u} [NormedField F] [IsUltrametricDist F]
  [NormedField E] [IsUltrametricDist E] [NormedAlgebra F E]
  {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of F))

/-- The actual scalar-changed rational section returns the entire original
section native point under the genuine scalar restriction. -/
theorem nativeMap_sectionNativePoint
    (s : Spec (CommRingCat.of F) ⟶ X) (hs : s ≫ f = 𝟙 _) :
    nativeMap (fun c => nnnorm_algebraMap' E c) f
      (RelativeSchemeValuedPoint.sectionNativePoint (NormedField.valuation (K := E))
        (structureMap (S := E) f) (fcScalarChangeRationalSection (E := E) f s hs)
        (fcScalarChangeRationalSection_structure (E := E) f s hs)) =
      RelativeSchemeValuedPoint.sectionNativePoint (NormedField.valuation (K := F)) f s hs := by
  apply Subtype.ext
  exact fcScalarChangeRationalSection_nativeProjection (E := E) f s hs

omit [NormedField E] [IsUltrametricDist E] [NormedAlgebra F E] in
/-- The genuinely constructed rational lift of every original point has
closed support over its actual complete algebraically closed extension. -/
theorem isClosed_support_fcRationalScalarLift [IsSeparated f]
    (x : RelativeSchemeValuedPoint (NormedField.valuation (K := F)) f) :
    IsClosed ({(fcRationalScalarLift f x).1.point} : Set (model (S := fcRationalLiftField f x) f)) := by
  have h := RelativeSchemeValuedPoint.isClosed_support_sectionNativePoint
    (NormedField.valuation (K := fcRationalLiftField f x))
    (structureMap (S := fcRationalLiftField f x) f)
    (fcRationalLiftSection f x) (fcRationalLiftSection_structure f x)
  exact h

end EnvelopeProperty.Berkovich.SchemeScalarBaseChange
