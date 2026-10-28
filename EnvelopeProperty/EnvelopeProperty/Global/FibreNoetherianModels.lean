import EnvelopeProperty.Global.FibreCoefficientField
import EnvelopeProperty.ReesIntegral
import EnvelopeProperty.ReesBirational

/-!
# Actual Noetherian complete local models of original Rees fibres

The original field-valued fibre is the whole order-one maximal-ideal fibre
of a constructed complete flat local model. Its Noetherianity is derived
from the genuine coefficient section, in every characteristic. Actual
proper normal birational geometry identifies the whole total coefficient
ring. Closed-fibre connectedness still requires formal-H0 algebraization.
-/

open CategoryTheory AlgebraicGeometry Limits
noncomputable section
universe u

namespace EnvelopeProperty.FibreNoetherianModels

variable {F A K : Type u} [Field F] [CommRing A] [Field K]
    [Algebra F A] [Algebra F K] [Algebra.FiniteType F A]
    (w : A →ₐ[F] K) {X : Scheme.{u}} (f : X ⟶ Spec (.of A))

/-- Every original field fibre has its constructed NOETHERIAN complete flat local model,
retaining the WHOLE original scheme projection. -/
theorem exists_presentation :
    ∃ (B : Type u) (_ : CommRing B) (_ : Algebra A B) (_ : IsNoetherianRing B)
      (_ : IsLocalRing B), Module.Flat A B ∧
      IsAdicComplete (IsLocalRing.maximalIdeal B) B ∧
      ∃ γ : B →+* K, Function.Surjective γ ∧
        RingHom.ker γ = IsLocalRing.maximalIdeal B ∧
        γ.comp (algebraMap A B) = w.toRingHom ∧
        ∃ e : InfinitesimalSchemes.model (IsLocalRing.maximalIdeal B)
            (FlatGlobalSections.structureMap (S := B) f) 1 ≅
              pullback f (Spec.map (CommRingCat.ofHom w.toRingHom)),
          e.hom ≫ pullback.fst _ _ =
            InfinitesimalSchemes.projection (IsLocalRing.maximalIdeal B)
              (FlatGlobalSections.structureMap (S := B) f) 1 ≫
                FlatGlobalSections.firstProjection (S := B) f := by
  obtain ⟨B, hRing, hAlg, hNoeth, hLocal, hFlat, hComplete, γ, hγs, hγk, hγw⟩ :=
    FibreCoefficientField.exists_noetherian_completed_flat_local_lift w
  exact ⟨B, hRing, hAlg, hNoeth, hLocal, hFlat, hComplete, γ, hγs, hγk, hγw,
    FibreCompletedLocal.closedFibreIso w.toRingHom γ hγs hγk hγw f,
    FibreCompletedLocal.closedFibreIso_projection w.toRingHom γ hγs hγk hγw f⟩

variable [IsDomain A] [IsIntegrallyClosed A]

/-- Genuine normal proper-birational geometry yields the SAME proper connected total model
with its ENTIRE true local coefficient ring and actual original closed fibre. -/
theorem exists_birational_presentation [IsReduced X] [IsProper f]
    (h : Scheme.BirationalOver f (𝟙 (Spec (.of A)))) :
    ∃ (B : Type u) (_ : CommRing B) (_ : Algebra A B) (_ : IsNoetherianRing B)
      (_ : IsLocalRing B), Module.Flat A B ∧
      IsAdicComplete (IsLocalRing.maximalIdeal B) B ∧
      IsProper (FlatGlobalSections.structureMap (S := B) f) ∧
      Function.Bijective (ProperBirationalSections.coefficientMap
        (FlatGlobalSections.structureMap (S := B) f)) ∧
      ConnectedSpace (FlatGlobalSections.baseChange (S := B) f) ∧
      ∃ γ : B →+* K, Function.Surjective γ ∧
        RingHom.ker γ = IsLocalRing.maximalIdeal B ∧
        γ.comp (algebraMap A B) = w.toRingHom ∧
        ∃ e : InfinitesimalSchemes.model (IsLocalRing.maximalIdeal B)
            (FlatGlobalSections.structureMap (S := B) f) 1 ≅
              pullback f (Spec.map (CommRingCat.ofHom w.toRingHom)),
          e.hom ≫ pullback.fst _ _ =
            InfinitesimalSchemes.projection (IsLocalRing.maximalIdeal B)
              (FlatGlobalSections.structureMap (S := B) f) 1 ≫
                FlatGlobalSections.firstProjection (S := B) f := by
  obtain ⟨B, hRing, hAlg, hNoeth, hLocal, hFlat, hComplete, γ, hγs, hγk, hγw, e, he⟩ :=
    exists_presentation w f
  let : Module.Flat A B := hFlat
  exact ⟨B, hRing, hAlg, hNoeth, hLocal, hFlat, hComplete, inferInstance,
    FcProperBirationalFlatSections.coefficientMap_flat_bijective f h,
    FcProperBirationalFlatSections.connectedSpace_flatBaseChange f h,
    γ, hγs, hγk, hγw, e, he⟩

/-- For the SAME actual finite-generator Rees quotient, all geometric premises are DERIVED
from the genuine nonzero original generator and normal domain base. -/
theorem exists_rees_presentation {ι : Type u} [Finite ι] (g : ι → A)
    (j : ι) (hj : g j ≠ 0) :
    ∃ (B : Type u) (_ : CommRing B) (_ : Algebra A B) (_ : IsNoetherianRing B)
      (_ : IsLocalRing B), Module.Flat A B ∧
      IsAdicComplete (IsLocalRing.maximalIdeal B) B ∧
      IsProper (FlatGlobalSections.structureMap (S := B) (ReesPresentation.projection g)) ∧
      Function.Bijective (ProperBirationalSections.coefficientMap
        (FlatGlobalSections.structureMap (S := B) (ReesPresentation.projection g))) ∧
      ConnectedSpace (FlatGlobalSections.baseChange (S := B) (ReesPresentation.projection g)) ∧
      ∃ γ : B →+* K, Function.Surjective γ ∧
        RingHom.ker γ = IsLocalRing.maximalIdeal B ∧
        γ.comp (algebraMap A B) = w.toRingHom ∧
        ∃ e : InfinitesimalSchemes.model (IsLocalRing.maximalIdeal B)
            (FlatGlobalSections.structureMap (S := B) (ReesPresentation.projection g)) 1 ≅
              pullback (ReesPresentation.projection g) (Spec.map (CommRingCat.ofHom w.toRingHom)),
          e.hom ≫ pullback.fst _ _ =
            InfinitesimalSchemes.projection (IsLocalRing.maximalIdeal B)
              (FlatGlobalSections.structureMap (S := B) (ReesPresentation.projection g)) 1 ≫
                FlatGlobalSections.firstProjection (S := B) (ReesPresentation.projection g) := by
  let : IsReduced (ReesPresentation.Scheme g) := ReesPresentation.scheme_isReduced g
  let : IsProper (ReesPresentation.projection g) := ReesPresentation.projection_isProper g
  exact exists_birational_presentation w (ReesPresentation.projection g)
    (ReesPresentation.birationalOver_projection g j (mem_nonZeroDivisors_iff_ne_zero.mpr hj))

end EnvelopeProperty.FibreNoetherianModels
