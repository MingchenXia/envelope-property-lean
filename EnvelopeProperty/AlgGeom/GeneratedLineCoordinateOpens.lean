import EnvelopeProperty.AlgGeom.GeneratedLineProjectiveMap
import EnvelopeProperty.AlgGeom.FiniteProjectivePort.FiniteProjectiveAffineCharts
import EnvelopeProperty.AlgGeom.SchemeGeneratorFrameNeighborhoods

/-! # SAME original generator coefficient opens under the genuine whole projective map -/
noncomputable section
open AlgebraicGeometry CategoryTheory MvPolynomial
open Scheme.Modules
open Alterations.Geometry.ProjectiveIdeal
universe u
namespace EnvelopeProperty.GeneratedLineCoordinateOpens
open GeneratedLineProjectiveAffineMap GeneratedLineProjectiveMap GeneratedLineLocalCoefficients
open SchemeGeneratedLineCoefficients SchemeGeneratorFrameNeighborhoods
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {R : Type u} [CommRing R] {X : Scheme.{u}} {L : X.Modules}

private instance framedAffineIsAffine (U : X.AffineZariskiSite) : IsAffine U.1.toScheme := U.2

private instance pullbackIndexFintype {Y : Scheme.{u}} (f : Y ⟶ X)
    (G : L.GeneratingSections) [Fintype G.I] :
    Fintype (ClosedProjectiveGlobalGeneration.pullback_generatingSections f G).I :=
  (inferInstance : Fintype G.I)

/-- The whole actual original affine map retains its literal original coefficient basic opens. -/
theorem affineMap_preimage_coordinate [IsAffine X] (p : X ⟶ Spec (.of R))
    (G : L.GeneratingSections) [Fintype G.I] (e : L ≅ unitObj X)
    (i : Fin (Fintype.card G.I + 1)) :
    affineMap p G e ⁻¹ᵁ coordinateOpen (R := R) i =
      X.basicOpen (paddedCoefficients (coefficient G e) i) := by
  let a := paddedCoefficients (coefficient G e)
  let ha := span_paddedCoefficients_eq_top _ (span_coefficients_eq_top G e)
  have h : Alterations.Geometry.FiniteProjective.affineTupleMap
      (baseCoefficients p) a ha ⁻¹ᵁ coordinateOpen (R := R) i = PrimeSpectrum.basicOpen (a i) :=
    Alterations.Geometry.FiniteProjective.affineTupleMap_preimage_coordinate _ a ha i
  exact (Scheme.Hom.comp_preimage X.isoSpec.hom
    (Alterations.Geometry.FiniteProjective.affineTupleMap (baseCoefficients p) a ha)
    (coordinateOpen (R := R) i)).trans
    ((congrArg (fun V => X.isoSpec.hom ⁻¹ᵁ V) h).trans
      (Scheme.map_PrimeSpectrum_basicOpen_of_affine X (a i)))

/-- ANY actual original affine frame retains the exact coordinate inverse opens of SAME whole map. -/
theorem projectiveMap_preimage_on_frame (p : X ⟶ Spec (.of R)) (hL : IsInvertible L)
    (G : L.GeneratingSections) [Fintype G.I] (U : X.AffineZariskiSite)
    (e : (Scheme.Modules.pullback U.1.ι).obj L ≅ unitObj U.1.toScheme)
    (i : Fin (Fintype.card G.I + 1)) :
    U.1.ι ⁻¹ᵁ (projectiveMap p hL G ⁻¹ᵁ coordinateOpen (R := R) i) =
      U.1.toScheme.basicOpen (paddedCoefficients (localCoefficient G U.1 e) i) := by
  rw [← Scheme.Hom.comp_preimage, projectiveMap_on_frame]
  exact affineMap_preimage_coordinate (U.1.ι ≫ p)
    (ClosedProjectiveGlobalGeneration.pullback_generatingSections U.1.ι G) e i

/-- The SAME whole original projective map actually maps each canonical generator-frame
affine open into that SAME original generator coordinate chart. -/
theorem projectiveMap_generator_chart (p : X ⟶ Spec (.of R)) (hL : IsInvertible L)
    (G : L.GeneratingSections) [Fintype G.I] (U : X.AffineZariskiSite) (i : G.I)
    (hi : IsIso (SchemeLineSectionEvaluation.pullbackSectionHom U.1.ι
      (SchemeGeneratingSectionsUnit.generatorHom G i))) :
    U.1 ≤ projectiveMap p hL G ⁻¹ᵁ
      coordinateOpen (R := R) ((Fintype.equivFin G.I) i).succ := by
  have h := projectiveMap_preimage_on_frame p hL G U (generatorFrame G U.1 i hi)
    ((Fintype.equivFin G.I) i).succ
  have hc : paddedCoefficients (localCoefficient G U.1 (generatorFrame G U.1 i hi))
      ((Fintype.equivFin G.I) i).succ = 1 := by
    simpa only [paddedCoefficients, Fin.cases_succ, Equiv.symm_apply_apply] using
      localCoefficient_generatorFrame G U.1 i hi
  rw [hc, Scheme.basicOpen_one] at h
  intro x hx
  have ht : (⟨x, hx⟩ : U.1.toScheme) ∈
      U.1.ι ⁻¹ᵁ (projectiveMap p hL G ⁻¹ᵁ
        coordinateOpen (R := R) ((Fintype.equivFin G.I) i).succ) := by
    rw [h]
    trivial
  exact ht

end EnvelopeProperty.GeneratedLineCoordinateOpens
