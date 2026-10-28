import EnvelopeProperty.AlgGeom.TildeExactness

/-! # Native homology of the SAME entire affine quasicoherent complex -/
noncomputable section
namespace EnvelopeProperty.AffineQuasicoherentComplexHomology
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u
variable (R : CommRingCat.{u})

private instance gammaAdditive : (moduleSpecΓFunctor (R := R)).Additive where
  map_add := by intro M N α β; rfl

/-- ACTUAL original module global-section image of the SAME native complex. -/
def sectionComplex (K : CochainComplex (Spec R).Modules ℕ) :
    CochainComplex (ModuleCat R) ℕ :=
  ((moduleSpecΓFunctor (R := R)).mapHomologicalComplex (ComplexShape.up ℕ)).obj K

/-- The ENTIRE original counit isomorphism of actual native complexes. -/
def complexIso (K : CochainComplex (Spec R).Modules ℕ)
    [∀ q, (K.X q).IsQuasicoherent] :
    TildeExactness.associatedComplex R (sectionComplex R K) ≅ K := by
  refine HomologicalComplex.Hom.isoOfComponents
    (fun q => by
      let : (K.X q).IsQuasicoherent := (inferInstance : ∀ j, (K.X j).IsQuasicoherent) q
      let η := (Scheme.Modules.fromTildeΓNatTrans (R := R)).app (K.X q)
      have hη : IsIso η :=
        (AlgebraicGeometry.isQuasicoherent_iff_isIso_fromTildeΓ (K.X q)).mp inferInstance
      exact @asIso _ _ _ _ η hη) ?_
  intro i j _
  exact ((Scheme.Modules.fromTildeΓNatTrans (R := R)).naturality (K.d i j)).symm

/-- Genuine actual native homology, retaining BOTH SAME original complexes and full counit. -/
def homologyIso (K : CochainComplex (Spec R).Modules ℕ)
    [∀ q, (K.X q).IsQuasicoherent] (q : ℕ) :
    AlgebraicGeometry.tilde ((sectionComplex R K).homology q) ≅ K.homology q :=
  (TildeExactness.homologyIso R (sectionComplex R K) q).symm ≪≫
    (HomologicalComplex.homologyFunctor (Spec R).Modules (ComplexShape.up ℕ) q).mapIso
      (complexIso R K)

/-- Original term quasicoherence DERIVES quasicoherence of the SAME native homology sheaf. -/
theorem homology_isQuasicoherent (K : CochainComplex (Spec R).Modules ℕ)
    [∀ q, (K.X q).IsQuasicoherent] (q : ℕ) : (K.homology q).IsQuasicoherent :=
  (Scheme.Modules.isQuasicoherent (Spec R)).prop_of_iso (homologyIso R K q) inferInstance

end EnvelopeProperty.AffineQuasicoherentComplexHomology
