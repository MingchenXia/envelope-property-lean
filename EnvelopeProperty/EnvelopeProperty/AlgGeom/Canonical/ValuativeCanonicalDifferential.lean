import EnvelopeProperty.AlgGeom.Canonical.AffineFormallyEtaleDifferential
import EnvelopeProperty.AlgGeom.Canonical.ExteriorPullbackComposition
import EnvelopeProperty.AlgGeom.LocalLineMapCancellation
import EnvelopeProperty.AlgGeom.SpecFormallyEtaleSections

/-! # The SAME entire canonical differential becomes an isomorphism along original local lifts -/
noncomputable section
open AlgebraicGeometry CategoryTheory Opposite
namespace EnvelopeProperty.CanonicalGeometry
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {k : Type u} [Field k] {X Y : Scheme.{u}} [IsAffine X]
    (f : X ⟶ Spec (.of k)) (g : Y ⟶ X) (n : ℕ)
    [SmoothOfRelativeDimension n f] [SmoothOfRelativeDimension n (g ≫ f)]

/-- Genuine formal etaleness of the ORIGINAL local composite derives that the SAME
ENTIRE pulled-back original canonical differential is an actual isomorphism. -/
theorem pullback_exteriorDifferential_isIso_of_formallyEtale_composite
    {V : Type u} [CommRing V] [IsLocalRing V] (l : Spec (.of V) ⟶ Y)
    (bX : let := affineChartAlgebra f ⊤
      Module.Basis (Fin n) Γ(X, ⊤) (KaehlerDifferential k Γ(X, ⊤)))
    (he : (l ≫ g).appTop.hom.FormallyEtale) :
    IsIso ((Scheme.Modules.pullback l).map (exteriorCotangentSheafPullbackMap f g n)) := by
  let δ := exteriorCotangentSheafPullbackMap f (l ≫ g) n
  let : IsIso δ := exteriorCotangentSheafPullbackMap_isIso_of_formallyEtale f (l ≫ g) n bX he
  let a := (Scheme.Modules.pullback l).map (exteriorCotangentSheafPullbackMap f g n)
  let b := exteriorCotangentSheafPullbackMap (g ≫ f) l n ≫
    eqToHom (congrArg (fun q => exteriorCotangentSheaf q n) (Category.assoc l g f).symm)
  have hc : (Scheme.Modules.pullbackComp l g).inv.app (exteriorCotangentSheaf f n) ≫
      (a ≫ b) = δ := by
    simpa only [a, b, δ, Category.assoc] using
      (exteriorCotangentSheafPullbackMap_comp f g l n).symm
  let : IsIso (a ≫ b) := IsIso.of_isIso_fac_left hc
  have hX := canonicalLineSheaf_isInvertible f n
  have hY := canonicalLineSheaf_isInvertible (g ≫ f) n
  have hP : Scheme.Modules.IsInvertible (exteriorCotangentSheaf ((l ≫ g) ≫ f) n) :=
    (hX.pullback (l ≫ g)).of_iso (asIso δ).symm
  exact LocalLineMapCancellation.isIso_of_composite_on_localSpec
    ((hX.pullback g).pullback l) (hY.pullback l) hP a b

variable {R : Type u} [CommRing R]

/-- For EVERY actual lift over an ORIGINAL source localization, BOTH the actual native
coefficient-square formal etaleness and SAME full differential unitness are derived. -/
theorem pullback_exteriorDifferential_isIso_of_source_localization
    {V : Type u} [CommRing V] [IsLocalRing V] [Algebra R V]
    (fR : Spec (.of R) ⟶ Spec (.of k)) (gR : Y ⟶ Spec (.of R))
    [SmoothOfRelativeDimension n fR] [SmoothOfRelativeDimension n (gR ≫ fR)]
    (S : Submonoid R) [IsLocalization S V] (l : Spec (.of V) ⟶ Y)
    (hl : l ≫ gR = Spec.map (CommRingCat.ofHom (algebraMap R V)))
    (bR : let := affineChartAlgebra fR ⊤
      Module.Basis (Fin n) Γ(Spec (.of R), ⊤)
        (KaehlerDifferential k Γ(Spec (.of R), ⊤))) :
    IsIso ((Scheme.Modules.pullback l).map (exteriorCotangentSheafPullbackMap fR gR n)) := by
  apply pullback_exteriorDifferential_isIso_of_formallyEtale_composite fR gR n l bR
  rw [hl]
  let : Algebra.FormallyEtale R V := Algebra.FormallyEtale.of_isLocalization S
  apply spec_appTop_formallyEtale
  exact (RingHom.formallyEtale_algebraMap).mpr inferInstance

end EnvelopeProperty.CanonicalGeometry
