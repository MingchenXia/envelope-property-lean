import EnvelopeProperty.AlgGeom.Canonical.ValuativeCanonicalDifferential
import EnvelopeProperty.AlgGeom.SchemeInvertibleHomSectionIsomorphism
import EnvelopeProperty.Char0.CanonicalDifferentialSection

/-! # The SAME original canonical Hom-section is a unit along actual original local lifts -/
noncomputable section
open AlgebraicGeometry CategoryTheory
namespace EnvelopeProperty.Char0.RoundedCanonicalModule
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {k R V : Type u} [Field k] [CommRing R] [CommRing V] [IsLocalRing V] [Algebra R V]
    {Y : Scheme.{u}}

/-- The SAME actual relative canonical differential SECTION becomes a true entire
unit isomorphism along EVERY original source-localization lift. Original geometric
smoothness/localization derives all inverses and actual Hom-section pullback comparisons. -/
theorem pullback_differentialSection_isIso_of_source_localization
    (f : Spec (.of R) ⟶ Spec (.of k)) (g : Y ⟶ Spec (.of R)) (n : ℕ)
    [SmoothOfRelativeDimension n f] [SmoothOfRelativeDimension n (g ≫ f)]
    (S : Submonoid R) [IsLocalization S V] (l : Spec (.of V) ⟶ Y)
    (hl : l ≫ g = Spec.map (CommRingCat.ofHom (algebraMap R V)))
    (bR : let := CanonicalGeometry.affineChartAlgebra f ⊤
      Module.Basis (Fin n) Γ(Spec (.of R), ⊤)
        (KaehlerDifferential k Γ(Spec (.of R), ⊤))) :
    IsIso ((Scheme.Modules.pullbackUnitIso l).inv ≫
      (Scheme.Modules.pullback l).map (differentialSection f g n)) := by
  let : IsIso ((Scheme.Modules.pullback l).map
      (CanonicalGeometry.exteriorCotangentSheafPullbackMap f g n)) :=
    CanonicalGeometry.pullback_exteriorDifferential_isIso_of_source_localization n f g S l hl bR
  let : IsIso ((Scheme.Modules.pullback l).map (differentialSection f g n)) :=
    SchemeInvertibleHomSection.isIso_pullback_equiv_of_isIso_pullback l
      ((Scheme.Modules.pullback g).obj (CanonicalGeometry.canonicalLineSheaf f n))
      ((CanonicalGeometry.canonicalLineSheaf_isInvertible f n).pullback g)
      (CanonicalGeometry.canonicalLineSheaf (g ≫ f) n)
      (CanonicalGeometry.exteriorCotangentSheafPullbackMap f g n)
  infer_instance

end EnvelopeProperty.Char0.RoundedCanonicalModule
