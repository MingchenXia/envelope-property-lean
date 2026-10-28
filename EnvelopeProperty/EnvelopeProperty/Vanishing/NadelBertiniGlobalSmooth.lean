import EnvelopeProperty.Vanishing.NadelBertiniRestrictionSmooth
import EnvelopeProperty.Vanishing.NadelBertiniRestrictionCover
/-! # Smoothness of the actual entire original global projective incidence -/
noncomputable section
open AlgebraicGeometry CategoryTheory Opposite
open Scheme.Modules
universe u
namespace EnvelopeProperty.Vanishing.NadelBertiniGlobalSmooth
open NadelBertiniUniversal NadelBertiniRestrictionSmooth NadelBertiniRestrictionCover
  NadelBertiniProjectiveFrames SchemeLineSectionEvaluation
variable {R : Type u} [CommRing R] {m : ℕ} {X : Scheme.{u}}

theorem toSource_smooth_of_cover (p : X ⟶ Spec (.of R)) (L : X.Modules) (hL : IsInvertible L)
    (s : Fin (m + 1) → Γ(L, ⊤)) {T : Type*} (W : T → X.affineOpens)
    (hW : ⨆ t, (W t).1 = ⊤)
    (e : ∀ t, (Scheme.Modules.pullback (W t).1.ι).obj L ≅ unitObj (W t).1.toScheme)
    (pivot : T → Fin (m + 1))
    (hpivot : ∀ t, (show Γ((W t).1.toScheme, ⊤) from
      (e t).hom.app ⊤ (affinePullbackUnitTop (W t).1.ι L (s (pivot t)))) = 1) :
    Smooth (toSource p L hL s) := by
  let f := FlatGlobalSections.firstProjection (S := parameterRing R m) p
  let I := incidenceIdeal p L hL s
  have hV : ⨆ t, f ⁻¹ᵁ (W t).1 = ⊤ := by rw [← f.preimage_iSup, hW, Scheme.Hom.preimage_top]
  let C := restrictionCover I (fun t => f ⁻¹ᵁ (W t).1) hV
  let : IsZariskiLocalAtSource @Smooth.{u} :=
    HasRingHomProperty.instIsZariskiLocalAtSource (P := @Smooth.{u}) (Q := @RingHom.Smooth)
  apply IsZariskiLocalAtSource.of_openCover (P := @Smooth.{u}) (f := toSource p L hL s) C
  intro t
  change Smooth (restrictionMap I (f ⁻¹ᵁ (W t).1) ≫ I.subschemeι ≫ f)
  rw [restrictionMap_toSource]
  have : Smooth ((I.comap (f ⁻¹ᵁ (W t).1).ι).subschemeι ≫ f ∣_ (W t).1) :=
    restricted_toSource_smooth p L hL (W t) (e t) s (pivot t) (hpivot t)
  rw [← Category.assoc]
  infer_instance

theorem projectiveToSource_smooth (j : X ⟶ DeJongAlterations.projectiveSpace R m)
    [IsClosedImmersion j] : Smooth (projectiveToSource j) := by
  let W : Fin (m + 1) → X.affineOpens := fun a => ⟨sourceOpen j a, sourceOpen_affine j a⟩
  have hW : ⨆ a, (W a).1 = ⊤ := by
    change ⨆ a, j ⁻¹ᵁ MvPolynomial.coordinateOpen (R := R) a = ⊤
    exact j.iSup_preimage_eq_top (MvPolynomial.iSup_coordinateOpen_eq_top (R := R))
  have hpivot : ∀ a, (show Γ((W a).1.toScheme, ⊤) from
      (coordinateFrame j a).hom.app ⊤ (affinePullbackUnitTop (W a).1.ι (projectiveLine j) (projectiveSections j a))) = 1 := by
    intro a
    change (coordinateFrame j a).hom.app ⊤
      (affinePullbackUnitTop (sourceOpen j a).ι (projectiveLine j) (sectionAtOne (sectionHom j a))) = _
    rw [pullback_sectionAtOne]
    exact congrArg sectionAtOne (coordinateFrame_section j a)
  exact toSource_smooth_of_cover (j ≫ DeJongAlterations.projectiveSpaceStructure R m)
    (projectiveLine j) ((MvPolynomial.coordinateHyperplaneTwist_isInvertible (R := R) (0 : Fin (m + 1)) 1).pullback j)
    (projectiveSections j) W hW (coordinateFrame j) id hpivot

theorem projectiveTotal_smooth (j : X ⟶ DeJongAlterations.projectiveSpace R m)
    [IsClosedImmersion j] [Smooth (j ≫ DeJongAlterations.projectiveSpaceStructure R m)] :
    Smooth (projectiveToSource j ≫ j ≫ DeJongAlterations.projectiveSpaceStructure R m) := by
  have := projectiveToSource_smooth j
  infer_instance
end EnvelopeProperty.Vanishing.NadelBertiniGlobalSmooth
