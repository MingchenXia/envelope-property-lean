import EnvelopeProperty.AlgGeom.IdealModulePullbackGlobalGeneration
import EnvelopeProperty.Local.PLIdealNormalizedPolarization

/-! # Actual globally generated ideal polarizations of the SAME normal PL model -/
open CategoryTheory CategoryTheory.MonoidalCategory AlgebraicGeometry Opposite Limits
open scoped Classical Polynomial NNReal ENNReal
noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace EnvelopeProperty.ProjSubvariety
open ProjBerk Berkovich Berkovich.RelativeSchemeValuedPoint IntegralSchemeNormalization
attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local instance] Scheme.Modules.monoidalCategory
variable {k : Type u} [Field k] {M : ℕ} (X : ProjSubvariety k M)

/-- The SAME original product's genuine closed embedding into actual original
polynomial projective space over the SAME original k[t]. -/
def nativeProductPolynomialInclusion : X.NativeProductModel ⟶ NativeProjectiveScheme k[X] M :=
  X.nativeProductInclusion ≫ (nativePolynomialLineProductIso k M).inv

/-- EVERY sufficiently large actual polynomial polarization of the SAME
original normalized Cartier ideal line is genuinely globally generated.
Its actual invertibility, finite generators and evaluation epimorphism are
all derived on the SAME original normalization, with no positivity certificate. -/
theorem normalizedSimultaneousIdeal_exists_eventual_generatingSections
    (I J : X.NativeProductModel.IdealSheafData)
    (hfin : ∀ w : X.an,
      modelIdealLog I gaussModelCoefficient_le_one (X.nativeProductGaussPoint w) ≠ ⊥ ∧
      modelIdealLog J gaussModelCoefficient_le_one (X.nativeProductGaussPoint w) ≠ ⊥)
    (j : Fin (M+1)) :
    ∃ N : ℕ, ∀ d : ℕ, N ≤ d →
      let L := Scheme.Modules.tensorObj
        (((I.comap (X.simultaneousIdealBlowupProjection I J)).comap
          (X.normalizedSimultaneousIdealBlowupProjection I J hfin)).toModules)
        ((Scheme.Modules.pullback
          ((X.normalizedSimultaneousIdealBlowupProjection I J hfin ≫
            X.simultaneousIdealBlowupProjection I J) ≫ X.nativeProductPolynomialInclusion)).obj
              (MvPolynomial.coordinateHyperplaneTwist (R := k[X]) j (d : ℤ)))
      Scheme.Modules.IsInvertible L ∧ ∃ G : L.GeneratingSections, G.IsFiniteType := by
  let : IsIntegral (X.simultaneousIdealBlowup I J) :=
    X.simultaneousIdealBlowup_isIntegral_of_finiteLogs I J X.triv (hfin X.triv).1 (hfin X.triv).2
  let μ := X.simultaneousIdealBlowupProjection I J
  let ν := X.normalizedSimultaneousIdealBlowupProjection I J hfin
  let i := X.nativeProductPolynomialInclusion
  let : IsClosedImmersion i := by dsimp [i, nativeProductPolynomialInclusion]; infer_instance
  obtain ⟨N, hN⟩ := IdealModulePullbackGlobalGeneration.exists_eventual_generatingSections
    i I (ν ≫ μ) j
  refine ⟨N, ?_⟩
  intro d hd
  obtain ⟨G, hG⟩ := hN d hd
  let : G.IsFiniteType := hG
  let B := (Scheme.Modules.pullback ((ν ≫ μ) ≫ i)).obj
    (MvPolynomial.coordinateHyperplaneTwist (R := k[X]) j (d : ℤ))
  let A := ((I.comap μ).comap ν).toModules
  let e : (I.comap (ν ≫ μ)).toModules ⊗ B ≅ Scheme.Modules.tensorObj A B :=
    ((Scheme.IdealSheafData.toModulesEqualityIso _ _ (I.comap_comp ν μ)) ⊗ᵢ Iso.refl _) ≪≫
      ModularCurves.monoidalTensorObjIso A B
  have hA : Scheme.Modules.IsInvertible A :=
    (cartier_comap _ (X.simultaneousIdealBlowup_isInvertible I J).1).isInvertibleModule_toModules
  have hB : Scheme.Modules.IsInvertible B :=
    (MvPolynomial.coordinateHyperplaneTwist_isInvertible j (d : ℤ)).pullback _
  refine ⟨hA.tensorObj hB, ?_⟩
  exact ⟨G.ofEpi e.hom, inferInstance⟩

end EnvelopeProperty.ProjSubvariety
