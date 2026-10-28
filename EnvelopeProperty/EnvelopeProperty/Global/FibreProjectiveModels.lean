import EnvelopeProperty.Global.FibreNoetherianModels
import EnvelopeProperty.Projective.FactorizationBaseChange

/-! # Actual projective complete-local presentations of every original field-valued fibre -/

open CategoryTheory AlgebraicGeometry Limits
noncomputable section
universe u
namespace EnvelopeProperty.FibreProjectiveModels

variable {F A K : Type u} [Field F] [CommRing A] [Field K]
    [Algebra F A] [Algebra F K] [Algebra.FiniteType F A]
    [IsDomain A] [IsIntegrallyClosed A]
    (w : A →ₐ[F] K) {X : Scheme.{u}} (f : X ⟶ Spec (.of A)) [IsReduced X]

/-- The SAME actual field-valued fibre has a genuinely constructed complete
flat local model with a DERIVED projective factorization and actual whole
coefficient bijection. No normality of the completion or fibre is assumed. -/
theorem exists_birational_presentation (hf : IsProjectiveFactorization f)
    (h : Scheme.BirationalOver f (𝟙 (Spec (.of A)))) :
    ∃ (B : Type u) (_ : CommRing B) (_ : Algebra A B) (_ : IsNoetherianRing B)
      (_ : IsLocalRing B), Module.Flat A B ∧
      IsAdicComplete (IsLocalRing.maximalIdeal B) B ∧
      IsProjectiveFactorization (FlatGlobalSections.structureMap (S := B) f) ∧
      Function.Bijective (ProperBirationalSections.coefficientMap
        (FlatGlobalSections.structureMap (S := B) f)) ∧
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
  let : IsProper f := hf.isProper
  obtain ⟨B, hRing, hAlg, hNoeth, hLocal, hFlat, hComplete, _, hBij, _,
      γ, hγs, hγk, hγw, e, he⟩ :=
    FibreNoetherianModels.exists_birational_presentation w f h
  exact ⟨B, hRing, hAlg, hNoeth, hLocal, hFlat, hComplete,
    ProjectiveFactorizationBaseChange.baseChange f hf, hBij, γ, hγs, hγk, hγw, e, he⟩

end EnvelopeProperty.FibreProjectiveModels
