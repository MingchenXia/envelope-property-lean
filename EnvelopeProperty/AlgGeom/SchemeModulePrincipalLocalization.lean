import EnvelopeProperty.AlgGeom.AffineOpenGlobalParameterLocalization
import EnvelopeProperty.AlgGeom.SheafCechTermLocalization
import EnvelopeProperty.AlgGeom.SchemeModuleCechLocalizationCriterion
import ModularCurves.ForMathlib.FiniteAffineOpenCover

/-! # Whole original quasicoherent sections localize at a global base parameter -/
open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
noncomputable section
universe u
namespace EnvelopeProperty.SchemeModulePrincipalLocalization

private theorem originalRestrictionLocalizationCongr
    {T : TopCat.{u}} {A : Type u} [CommRing A]
    (P : (Opens T)ᵒᵖ ⥤ ModuleCat.{u} A) (r : A)
    {U U' V V' : Opens T} (hU : U = U') (hV : V = V')
    (h : V ≤ U) (h' : V' ≤ U')
    (hl : IsLocalizedModule.Away r (P.map (homOfLE h).op).hom) :
    IsLocalizedModule.Away r (P.map (homOfLE h').op).hom := by
  subst U'
  subst V'
  exact hl

variable {X B : Scheme.{u}} (π : X ⟶ B) (M : X.Modules) [M.IsQuasicoherent]

/-- Every SAME affine tuple restriction at the original principal open is
localization for its original global base coefficient action. -/
theorem factorRestriction_isLocalizedModule [X.IsSeparated]
    {ι : Type u} (U : ι → X.Opens) (hU : ∀ i, IsAffineOpen (U i))
    (r : Γ(B, ⊤)) (n : ℕ) (i : Fin (n + 1) → ι) :
    IsLocalizedModule.Away r
      (SheafCechTermLocalization.factorRestriction
        (Scheme.Modules.baseModuleTopSheaf π M) U
        (le_top : π ⁻¹ᵁ B.basicOpen r ≤ ⊤) n i) := by
  let C : X.Opens := ∏ᶜ fun k : Fin (n + 1) => U (i k)
  have hh := AffineOpenGlobalParameterLocalization.restriction_isLocalizedModule π M
    ⟨C, IsAffineOpen.cechIntersection U hU n i⟩ r
  exact originalRestrictionLocalizationCongr (Scheme.Modules.baseModulePresheaf π M) r
    (top_inf_eq C).symm (inf_comm C (π ⁻¹ᵁ B.basicOpen r))
    inf_le_left (inf_le_inf_right C le_top) hh


/-- Quasicompactness, separatedness and actual quasi-coherence DERIVE the
whole original section restriction localization, with no H0 certificate. -/
theorem restriction_isLocalizedModule [CompactSpace X] [X.IsSeparated]
    (r : Γ(B, ⊤)) :
    IsLocalizedModule.Away r
      ((Scheme.Modules.baseModulePresheaf π M).map
        (homOfLE (le_top : π ⁻¹ᵁ B.basicOpen r ≤ ⊤)).op).hom := by
  obtain ⟨ι, hι, U, hcover, hU⟩ := X.exists_finite_affine_openCover
  let : Finite ι := hι
  let : ∀ (n : ℕ) (i : Fin (n + 1) → ι), IsLocalizedModule.Away r
      (SheafCechTermLocalization.factorRestriction
        (Scheme.Modules.baseModuleTopSheaf π M) U
        (le_top : π ⁻¹ᵁ B.basicOpen r ≤ ⊤) n i) :=
    fun n i => factorRestriction_isLocalizedModule π M U hU r n i
  let : IsLocalizedModule.Away r
      (SheafCechKernelRestrictions.termRestriction
        (Scheme.Modules.baseModuleTopSheaf π M) U
        (le_top : π ⁻¹ᵁ B.basicOpen r ≤ ⊤) 0).hom :=
    SheafCechTermLocalization.termRestriction_isLocalizedModule
      (Scheme.Modules.baseModuleTopSheaf π M) U le_top 0 (Submonoid.powers r)
  let : IsLocalizedModule.Away r
      (SheafCechKernelRestrictions.termRestriction
        (Scheme.Modules.baseModuleTopSheaf π M) U
        (le_top : π ⁻¹ᵁ B.basicOpen r ≤ ⊤) 1).hom :=
    SheafCechTermLocalization.termRestriction_isLocalizedModule
      (Scheme.Modules.baseModuleTopSheaf π M) U le_top 1 (Submonoid.powers r)
  exact SchemeModuleCechLocalizationCriterion.sectionRestriction_isLocalizedModule
    π M U hcover le_top (Submonoid.powers r)

end EnvelopeProperty.SchemeModulePrincipalLocalization
