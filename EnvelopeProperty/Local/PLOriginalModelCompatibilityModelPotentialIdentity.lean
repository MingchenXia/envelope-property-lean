import EnvelopeProperty.Local.PLOriginalModelCompatibilityTwistedRatioPotential
import EnvelopeProperty.Local.PLOriginalModelCompatibilityTestConfiguration
import EnvelopeProperty.Local.PLOriginalModelCompatibilityNativeRatioSection
import EnvelopeProperty.Local.PLNormalizedOriginalProjection
import EnvelopeProperty.Projective.SubvarietyHomogeneousSectionNorms

/-! # The model potential of the normalized PL test configuration

For the normalized simultaneous PL model `C` of `X × 𝔸¹` (the test configuration
`normalizedSimultaneousNativeTestConfiguration` of
`Local/PLOriginalModelCompatibilityTestConfiguration`), and the twisted ratio line
`M = π^*O(n) ⊗ I ⊗ J^∨` with its action and fibre-one comparisons from the same file, the
native model potential `pot_M` (the potential of the finite Fubini–Study constructions,
`TestConfiguration.gaussNativeModelPotential`) satisfies, at every point `x` of `X^an`,

* `pot_M(x) = ratioWeight(z_x)`, where `z_x` is the total Gauss point of `C` over `x` (a
  relative scheme-valued point of the normalized blow-up over the Gauss norm of `k[t]`) and
  `ratioWeight` is the production `normalizedSimultaneousRatioWeightAt`
  (`normalizedSimultaneousNativeModelPotential_eq_ratioWeight`);
* consequently, if `r φ(baseRestriction y) = ratioWeight(y) + c` at every point `y` of the
  normalized blow-up (the identity produced by
  `NumericalOriginalCentralNef.exists_prescribedClass_originalCentralNef`), then
  `pot_M(h(w)) = r φ(w) - c` for every `w : X.an`, where `h = nativeAnalyticHomeomorph`
  (`normalizedSimultaneousNativeModelPotential_eq_convex`).

This is the comparison of the model metric of the PL model with the PL function in FHX,
proof of Lemma 5.5 (the identity `φ = φ_{(𝒳, ℒ)}` of BJ22 §2 for the model attached to a PL
function); the general computation is
`TestConfiguration.gaussNativeModelPotential_twistedRatio`.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
open Scheme.Modules
open scoped Classical Polynomial LaurentPolynomial NNReal ENNReal CategoryTheory.MonObj
noncomputable section
universe u

namespace EnvelopeProperty.ProjSubvariety
open ProjBerk Berkovich Berkovich.RelativeSchemeValuedPoint NativeTestConfiguration
open NativeTestConfiguration.TestConfiguration
open PLOriginalModelCompatibility.TwistedRatioCalculus
open PLOriginalModelCompatibility.RatioSectionTransport
open SchemeLineSectionEvaluation
attribute [local instance] MvPolynomial.gradedAlgebra

variable {k : Type u} [Field k] {M : ℕ} (X : ProjSubvariety k M)
variable (I J : HomogeneousIdeal (ProjectiveGrading k[X] M))
variable (hI : ∀ (S : Type u) [CommRing S] (f : k →+* S) (a : Sˣ),
  (I.toIdeal.map (MvPolynomial.map (Polynomial.mapRingHom f))).map
    (MvPolynomial.map (parameterScaleHom (a : S))) =
      I.toIdeal.map (MvPolynomial.map (Polynomial.mapRingHom f)))
variable (hJ : ∀ (S : Type u) [CommRing S] (f : k →+* S) (a : Sˣ),
  (J.toIdeal.map (MvPolynomial.map (Polynomial.mapRingHom f))).map
    (MvPolynomial.map (parameterScaleHom (a : S))) =
      J.toIdeal.map (MvPolynomial.map (Polynomial.mapRingHom f)))
variable (hfin : ∀ w : X.an,
  modelIdealLog (X.nativeProductIdeal I) gaussModelCoefficient_le_one
    (X.nativeProductGaussPoint w) ≠ ⊥ ∧
  modelIdealLog (X.nativeProductIdeal J) gaussModelCoefficient_le_one
    (X.nativeProductGaussPoint w) ≠ ⊥)
variable (A B : ℕ) (hA : MvPolynomial.C (Polynomial.X ^ A) ∈ I.toIdeal)
  (hB : MvPolynomial.C (Polynomial.X ^ B) ∈ J.toIdeal) (hX : X.IsProjNormal)

private local instance modelPotentialAmbientProper :
    IsProper (ProjBerk.nativeStructureMap (R := k) (n := M)) := ProjBerk.nativeStructureMap_isProper
private local instance modelPotentialNativeProper : IsProper X.nativeStructure := by
  change IsProper (X.nativeInclusion ≫ ProjBerk.nativeStructureMap)
  infer_instance

private local instance modelPotentialTestConfigurationProper {Y : Over (Spec (.of k))}
    (C : NativeTestConfiguration.TestConfiguration k Y) : IsProper C.projection :=
  C.projection_isProper

private local instance modelPotentialNormalizedProper :
    IsProper (X.normalizedSimultaneousIdealBlowupStructure (X.nativeProductIdeal I)
      (X.nativeProductIdeal J) hfin) :=
  X.normalizedSimultaneousIdealBlowupStructure_isProper _ _ hfin

private theorem ratioWeight_firstNorm_ne_zero
    (y : RelativeSchemeValuedPoint (gaussValuation (1 : Valuation k ℝ≥0) gaussRadius)
      (X.normalizedSimultaneousIdealBlowupStructure
        (X.nativeProductIdeal I) (X.nativeProductIdeal J) hfin))
    (hnI : modelIdealLog (X.nativeProductIdeal I) gaussModelCoefficient_le_one
      (X.normalizedSimultaneousProductPointAt (X.nativeProductIdeal I)
        (X.nativeProductIdeal J) hfin y) ≠ ⊥) :
    modelIdealNorm (((X.nativeProductIdeal I).comap (X.simultaneousIdealBlowupProjection
      (X.nativeProductIdeal I) (X.nativeProductIdeal J))).comap
        (X.normalizedSimultaneousIdealBlowupProjection
          (X.nativeProductIdeal I) (X.nativeProductIdeal J) hfin))
      gaussModelCoefficient_le_one y ≠ 0 := by
  intro hz
  apply hnI
  rw [← X.modelIdealLog_normalizedSimultaneous_comap (X.nativeProductIdeal I)
      (X.nativeProductIdeal J) hfin (X.nativeProductIdeal I) y,
    modelIdealLog, hz, ENNReal.log_zero]

/-- A homogeneous section of the projective twist which does not vanish at a prescribed
analytic point. -/
private theorem exists_twistSection_ne_zero (j : Fin (M + 1)) (n : ℕ) (w : X.an) :
    ∃ s : unitObj X.NativeScheme ⟶ X.nativeTwistLineSheaf j n,
      modelLineNorm Valuation.one_apply_le_one (X.nativeAnalyticHomeomorph w)
        ((MvPolynomial.coordinateHyperplanePoleSheafPower_isInvertible (R := k) j n).pullback
          X.nativeInclusion)
        (fibreSection (X.nativeAnalyticHomeomorph w) s) ≠ 0 := by
  obtain ⟨i, hi⟩ := ProjBerk.exists_val_X_eq_one w.1
  refine ⟨pullbackSectionHom X.nativeInclusion (ProjectiveHomogeneousSections.sectionHom j n
    (MvPolynomial.X i ^ n) (MvPolynomial.isHomogeneous_X_pow i n)), ?_⟩
  have h := X.homogeneousSectionNorm_eq_val j n (MvPolynomial.X i ^ n)
    (MvPolynomial.isHomogeneous_X_pow i n) w
  change X.homogeneousSectionNorm j n (MvPolynomial.X i ^ n)
    (MvPolynomial.isHomogeneous_X_pow i n) w ≠ 0
  rw [h, map_pow, hi, one_pow]
  exact one_ne_zero

/-- The original twist comparison of the normalized PL test configuration is the comparison of
the invariant original projection. -/
theorem normalizedSimultaneousOriginalTwistNativeGmComparison_eq (j : Fin (M + 1)) (n : ℕ)
    (hinv :
      (X.normalizedSimultaneousNativeTestConfiguration I J hI hJ hfin A B hA hB hX).lineActionMap ≫
          (X.normalizedSimultaneousOriginalProjection (X.nativeProductIdeal I)
            (X.nativeProductIdeal J) hfin) =
        (X.normalizedSimultaneousNativeTestConfiguration
            I J hI hJ hfin A B hA hB hX).lineProjectionMap ≫
          (X.normalizedSimultaneousOriginalProjection (X.nativeProductIdeal I)
            (X.nativeProductIdeal J) hfin)) :
    X.normalizedSimultaneousOriginalTwistNativeGmComparison I J hI hJ hfin j n =
      (Scheme.Modules.pullbackComp
          (X.normalizedSimultaneousNativeTestConfiguration
            I J hI hJ hfin A B hA hB hX).lineActionMap
          (X.normalizedSimultaneousOriginalProjection (X.nativeProductIdeal I)
            (X.nativeProductIdeal J) hfin)).app (X.nativeTwistLineSheaf j n) ≪≫
        (Scheme.Modules.pullbackCongr hinv).app (X.nativeTwistLineSheaf j n) ≪≫
        ((Scheme.Modules.pullbackComp
          (X.normalizedSimultaneousNativeTestConfiguration
            I J hI hJ hfin A B hA hB hX).lineProjectionMap
          (X.normalizedSimultaneousOriginalProjection (X.nativeProductIdeal I)
            (X.nativeProductIdeal J) hfin)).app (X.nativeTwistLineSheaf j n)).symm :=
  rfl

/-- The fibre-one comparison of the twisted ratio line of the normalized PL test configuration
is the tensor of the canonical identification of the twist and the trivialisation of the ratio
line on fibre one. -/
theorem normalizedSimultaneousNativeTestConfigurationFibreOneLineIso_eq (j : Fin (M + 1))
    (n : ℕ) :
    X.normalizedSimultaneousNativeTestConfigurationFibreOneLineIso I J hI hJ hfin A B hA hB hX j n =
      (Scheme.Modules.canonicalTensorPullbackIso
          (X.normalizedSimultaneousNativeTestConfiguration
            I J hI hJ hfin A B hA hB hX).fibreOneInclusion.left
          ((Scheme.Modules.pullback (X.normalizedSimultaneousOriginalProjection
            (X.nativeProductIdeal I) (X.nativeProductIdeal J) hfin)).obj
              (X.nativeTwistLineSheaf j n))
          ((((X.nativeProductIdeal I).comap (X.simultaneousIdealBlowupProjection
            (X.nativeProductIdeal I) (X.nativeProductIdeal J))).comap
              (X.normalizedSimultaneousIdealBlowupProjection (X.nativeProductIdeal I)
                (X.nativeProductIdeal J) hfin)).ratioModule
            (((X.nativeProductIdeal J).comap (X.simultaneousIdealBlowupProjection
              (X.nativeProductIdeal I) (X.nativeProductIdeal J))).comap
                (X.normalizedSimultaneousIdealBlowupProjection (X.nativeProductIdeal I)
                  (X.nativeProductIdeal J) hfin))) ≪≫
        tensorObjCongr (Iso.refl _) (X.normalizedSimultaneousRatioFibreOneIso I J A B hA hB hfin) ≪≫
          tensorObjUnitIso _ ≪≫
        (Scheme.Modules.pullbackComp
          (X.normalizedSimultaneousNativeTestConfiguration
            I J hI hJ hfin A B hA hB hX).fibreOneInclusion.left
          (X.normalizedSimultaneousOriginalProjection (X.nativeProductIdeal I)
            (X.nativeProductIdeal J) hfin)).app (X.nativeTwistLineSheaf j n)) ≪≫
      (Scheme.Modules.pullbackCongr
        ((X.normalizedSimultaneousFibreOneNativeIso_hom I J A B hA hB hfin hX).symm :
          (X.normalizedSimultaneousNativeTestConfiguration
              I J hI hJ hfin A B hA hB hX).fibreOneInclusion.left ≫
            (X.normalizedSimultaneousOriginalProjection (X.nativeProductIdeal I)
              (X.nativeProductIdeal J) hfin) =
          (X.normalizedSimultaneousNativeTestConfiguration
            I J hI hJ hfin A B hA hB hX).fibreOneIso.hom.left)).app (X.nativeTwistLineSheaf j n) :=
  rfl

/-- The canonical Cartier group comparison of the ratio line of the normalized PL test
configuration fixes the canonical ratio section along the noncentral action lift. -/
theorem normalizedSimultaneousRatioNativeGmLinearization_canonicalSection
    [IsIso ((((X.nativeProductIdeal I).comap (X.simultaneousIdealBlowupProjection
        (X.nativeProductIdeal I) (X.nativeProductIdeal J))).comap
          (X.normalizedSimultaneousIdealBlowupProjection (X.nativeProductIdeal I)
            (X.nativeProductIdeal J) hfin)).pullbackModuleInclusion
      ((X.normalizedSimultaneousNativeTestConfiguration
          I J hI hJ hfin A B hA hB hX).unitOpenActionLift.left ≫
        (X.normalizedSimultaneousNativeTestConfiguration
          I J hI hJ hfin A B hA hB hX).lineActionMap))]
    [IsIso ((((X.nativeProductIdeal I).comap (X.simultaneousIdealBlowupProjection
        (X.nativeProductIdeal I) (X.nativeProductIdeal J))).comap
          (X.normalizedSimultaneousIdealBlowupProjection (X.nativeProductIdeal I)
            (X.nativeProductIdeal J) hfin)).pullbackModuleInclusion
      ((X.normalizedSimultaneousNativeTestConfiguration
          I J hI hJ hfin A B hA hB hX).unitOpenActionLift.left ≫
        (X.normalizedSimultaneousNativeTestConfiguration
          I J hI hJ hfin A B hA hB hX).lineProjectionMap))] :
    canonicalPulledRatioSection
        (((X.nativeProductIdeal I).comap (X.simultaneousIdealBlowupProjection
          (X.nativeProductIdeal I) (X.nativeProductIdeal J))).comap
            (X.normalizedSimultaneousIdealBlowupProjection (X.nativeProductIdeal I)
              (X.nativeProductIdeal J) hfin))
        (((X.nativeProductIdeal J).comap (X.simultaneousIdealBlowupProjection
          (X.nativeProductIdeal I) (X.nativeProductIdeal J))).comap
            (X.normalizedSimultaneousIdealBlowupProjection (X.nativeProductIdeal I)
              (X.nativeProductIdeal J) hfin))
        (X.normalizedSimultaneousNativeCartierFactors_isInvertible I J hfin).2
        ((X.normalizedSimultaneousNativeTestConfiguration
            I J hI hJ hfin A B hA hB hX).unitOpenActionLift.left ≫
          (X.normalizedSimultaneousNativeTestConfiguration
            I J hI hJ hfin A B hA hB hX).lineActionMap) ≫
      (pullbackIsoAlong
        (X.normalizedSimultaneousNativeTestConfiguration I J hI hJ hfin A B hA hB hX).lineActionMap
        (X.normalizedSimultaneousNativeTestConfiguration
          I J hI hJ hfin A B hA hB hX).lineProjectionMap
        (X.normalizedSimultaneousRatioNativeGmLinearization I J hI hJ hfin)
        (X.normalizedSimultaneousNativeTestConfiguration
          I J hI hJ hfin A B hA hB hX).unitOpenActionLift.left).hom =
    canonicalPulledRatioSection
        (((X.nativeProductIdeal I).comap (X.simultaneousIdealBlowupProjection
          (X.nativeProductIdeal I) (X.nativeProductIdeal J))).comap
            (X.normalizedSimultaneousIdealBlowupProjection (X.nativeProductIdeal I)
              (X.nativeProductIdeal J) hfin))
        (((X.nativeProductIdeal J).comap (X.simultaneousIdealBlowupProjection
          (X.nativeProductIdeal I) (X.nativeProductIdeal J))).comap
            (X.normalizedSimultaneousIdealBlowupProjection (X.nativeProductIdeal I)
              (X.nativeProductIdeal J) hfin))
        (X.normalizedSimultaneousNativeCartierFactors_isInvertible I J hfin).2
        ((X.normalizedSimultaneousNativeTestConfiguration
            I J hI hJ hfin A B hA hB hX).unitOpenActionLift.left ≫
          (X.normalizedSimultaneousNativeTestConfiguration
            I J hI hJ hfin A B hA hB hX).lineProjectionMap) := by
  let := X.normalizedSimultaneousNativeGmModObj I J hI hJ hfin
  exact @cartierRatioGroupLinearization_canonicalSection k _ (nativeMultiplicativeGroup k)
    (totalOver k (X.normalizedSimultaneousIdealBlowupStructure (X.nativeProductIdeal I)
      (X.nativeProductIdeal J) hfin)) _ _
    (((X.nativeProductIdeal I).comap (X.simultaneousIdealBlowupProjection
      (X.nativeProductIdeal I) (X.nativeProductIdeal J))).comap
        (X.normalizedSimultaneousIdealBlowupProjection (X.nativeProductIdeal I)
          (X.nativeProductIdeal J) hfin))
    (((X.nativeProductIdeal J).comap (X.simultaneousIdealBlowupProjection
      (X.nativeProductIdeal I) (X.nativeProductIdeal J))).comap
        (X.normalizedSimultaneousIdealBlowupProjection (X.nativeProductIdeal I)
          (X.nativeProductIdeal J) hfin))
    (X.normalizedSimultaneousNativeCartierFactors_isInvertible I J hfin).1
    (X.normalizedSimultaneousNativeCartierFactors_isInvertible I J hfin).2
    (X.normalizedSimultaneousNativeCartierFactor_invariant I J hI hJ I
      (hI k[T;T⁻¹] LaurentPolynomial.C (parameterLaurentUnit k)) hfin)
    (X.normalizedSimultaneousNativeCartierFactor_invariant I J hI hJ J
      (hJ k[T;T⁻¹] LaurentPolynomial.C (parameterLaurentUnit k)) hfin)
    _ (X.normalizedSimultaneousNativeTestConfiguration
      I J hI hJ hfin A B hA hB hX).unitOpenActionLift.left ‹_› ‹_›

/-- **The model potential of the normalized PL test configuration is the ratio weight.**
For the normalized simultaneous PL test configuration and its twisted ratio line with the
action and fibre-one comparisons of `PLOriginalModelCompatibilityTestConfiguration`, the
native model potential at the Fubini–Study radius equals, at every point `x`, the ratio weight
`log|I| - log|J|` of the total Gauss point over `x`. -/
theorem normalizedSimultaneousNativeModelPotential_eq_ratioWeight (j : Fin (M + 1)) (n : ℕ)
    (x : RelativeSchemeValuedPoint (1 : Valuation k ℝ≥0) X.nativeStructure)
    (hnI : modelIdealLog (X.nativeProductIdeal I) gaussModelCoefficient_le_one
      (X.normalizedSimultaneousProductPointAt (X.nativeProductIdeal I) (X.nativeProductIdeal J) hfin
        (RelativeSchemeValuedPoint.map
          (X.normalizedSimultaneousNativeTestConfiguration
              I J hI hJ hfin A B hA hB hX).productTotalMap
          rfl ((X.normalizedSimultaneousNativeTestConfiguration
              I J hI hJ hfin A B hA hB hX).productGaussSource
            x weightedFSRadius weightedFSRadius_properties.1))) ≠ ⊥) :
    let C := X.normalizedSimultaneousNativeTestConfiguration I J hI hJ hfin A B hA hB hX
    ((C.gaussNativeModelPotential
        (X.normalizedSimultaneousTwistedRatioLine (X.nativeProductIdeal I) (X.nativeProductIdeal J)
          hfin j n)
        (X.normalizedSimultaneousTwistedRatioLine_isInvertible (X.nativeProductIdeal I)
          (X.nativeProductIdeal J) hfin j n)
        (X.nativeTwistLineSheaf j n)
        (X.normalizedSimultaneousNativeTestConfigurationLineComparison
            I J hI hJ hfin A B hA hB hX j n)
        (X.normalizedSimultaneousNativeTestConfigurationFibreOneLineIso
            I J hI hJ hfin A B hA hB hX j n)
        (X.nativeTwistLineSheaf_isInvertible j n) weightedFSRadius weightedFSRadius_properties.1
        weightedFSRadius_properties.2.1 x : ℝ) : EReal) =
      X.normalizedSimultaneousRatioWeightAt (X.nativeProductIdeal I) (X.nativeProductIdeal J) hfin
        (RelativeSchemeValuedPoint.map C.productTotalMap rfl
          (C.productGaussSource x weightedFSRadius weightedFSRadius_properties.1)) hnI := by
  intro C
  let bμ := X.simultaneousIdealBlowupProjection (X.nativeProductIdeal I) (X.nativeProductIdeal J)
  let ν := X.normalizedSimultaneousIdealBlowupProjection
    (X.nativeProductIdeal I) (X.nativeProductIdeal J) hfin
  let K := ((X.nativeProductIdeal I).comap bμ).comap ν
  let L' := ((X.nativeProductIdeal J).comap bμ).comap ν
  let π := X.normalizedSimultaneousOriginalProjection
    (X.nativeProductIdeal I) (X.nativeProductIdeal J) hfin
  have hKL := X.normalizedSimultaneousNativeCartierFactors_isInvertible I J hfin
  have hU := X.normalizedSimultaneousNoncentralOpen_off_nativeCartierFactors I J hfin A B hA hB
  -- the structural laws of the comparisons of the test configuration
  have hπw : C.unitOpenOriginalProjection.left = C.unitOpenInclusion.left ≫ π :=
    X.normalizedSimultaneousNativeTestConfiguration_originalProjection I J hI hJ hfin A B hA hB hX
  have hπbase : π ≫ (Over.mk X.nativeStructure).hom =
      C.projection ≫ Spec.map (CommRingCat.ofHom (Polynomial.C : k →+* Polynomial k)) :=
    X.normalizedSimultaneousOriginalProjection_over_base (X.nativeProductIdeal I)
      (X.nativeProductIdeal J) hfin
  have hπ₁ : C.fibreOneInclusion.left ≫ π = C.fibreOneIso.hom.left :=
    (X.normalizedSimultaneousFibreOneNativeIso_hom I J A B hA hB hfin hX).symm
  have hinv : C.lineActionMap ≫ π = C.lineProjectionMap ≫ π :=
    X.normalizedSimultaneousNativeOriginalProjection_invariant I J hI hJ hfin
  have hα := canonicalTensorPullbackIso_comparison_tensor_law C.lineActionMap C.lineProjectionMap
    ((Scheme.Modules.pullback π).obj (X.nativeTwistLineSheaf j n)) (K.ratioModule L')
    (X.normalizedSimultaneousOriginalTwistNativeGmComparison I J hI hJ hfin j n)
    (X.normalizedSimultaneousRatioNativeGmLinearization I J hI hJ hfin)
  have hαT : ∀ s : unitObj X.NativeScheme ⟶ X.nativeTwistLineSheaf j n,
      pullbackSectionHom C.lineActionMap (pullbackSectionHom π s) ≫
          (X.normalizedSimultaneousOriginalTwistNativeGmComparison I J hI hJ hfin j n).hom =
        pullbackSectionHom C.lineProjectionMap (pullbackSectionHom π s) :=
    C.twistedRatio_twistLaw_of_iso π (X.nativeTwistLineSheaf j n) hinv _
      (X.normalizedSimultaneousOriginalTwistNativeGmComparison_eq I J hI hJ hfin A B hA hB hX j n
        hinv)
  have hαR : ∀ [IsIso (K.pullbackModuleInclusion (C.unitOpenActionLift.left ≫ C.lineActionMap))]
      [IsIso (K.pullbackModuleInclusion (C.unitOpenActionLift.left ≫ C.lineProjectionMap))],
      canonicalPulledRatioSection K L' hKL.2 (C.unitOpenActionLift.left ≫ C.lineActionMap) ≫
        (pullbackIsoAlong C.lineActionMap C.lineProjectionMap
          (X.normalizedSimultaneousRatioNativeGmLinearization I J hI hJ hfin)
          C.unitOpenActionLift.left).hom =
      canonicalPulledRatioSection K L' hKL.2 (C.unitOpenActionLift.left ≫ C.lineProjectionMap) := by
    intro _ _
    exact X.normalizedSimultaneousRatioNativeGmLinearization_canonicalSection I J hI hJ hfin A B
      hA hB hX
  have he₁ := C.twistedRatio_fibreOneLaw_of_iso π (X.nativeTwistLineSheaf j n) K L' hπ₁
    (X.normalizedSimultaneousRatioFibreOneIso I J A B hA hB hfin) _
    (X.normalizedSimultaneousNativeTestConfigurationFibreOneLineIso_eq I J hI hJ hfin A B hA hB
      hX j n)
  -- a twist section not vanishing at `x`
  obtain ⟨s, hs⟩ := X.exists_twistSection_ne_zero j n (X.nativeAnalyticHomeomorph.symm x)
  rw [X.nativeAnalyticHomeomorph.apply_symm_apply] at hs
  -- the general computation
  have hfac := C.gaussNativeNormFactor_twistedRatio π (X.nativeTwistLineSheaf j n) K L' hKL.2
    hπw hπbase hπ₁ (X.nativeTwistLineSheaf_isInvertible j n)
    (X.normalizedSimultaneousRatioLine_isInvertible (X.nativeProductIdeal I)
      (X.nativeProductIdeal J) hfin)
    (X.normalizedSimultaneousTwistedRatioLine_isInvertible (X.nativeProductIdeal I)
      (X.nativeProductIdeal J) hfin j n) hU.1 hU.2
    (X.normalizedSimultaneousNativeTestConfigurationLineComparison I J hI hJ hfin A B hA hB hX j n)
    (X.normalizedSimultaneousOriginalTwistNativeGmComparison I J hI hJ hfin j n)
    (X.normalizedSimultaneousRatioNativeGmLinearization I J hI hJ hfin) hα hαT @hαR
    (X.normalizedSimultaneousRatioFibreOneIso I J A B hA hB hfin)
    (X.normalizedSimultaneousNativeTestConfigurationFibreOneLineIso I J hI hJ hfin A B hA hB hX j n)
    he₁ weightedFSRadius weightedFSRadius_properties.1 weightedFSRadius_properties.2.1 x s hs
  -- the fibre of the canonical ratio section is the canonical generic ratio section
  have hzU := C.twistedRatio_productGauss_mem_unitOpen x weightedFSRadius
    weightedFSRadius_properties.1
  have hzI : IsIso (K.pullbackModuleInclusion (C.total.fromSpecResidueField (C.productTotalMap
      (C.productGaussSource x weightedFSRadius weightedFSRadius_properties.1).1.point))) :=
    C.twistedRatio_residue_inclusion_isIso K hU.1 x weightedFSRadius
      weightedFSRadius_properties.1
  have hsec : sectionAtOne (canonicalPulledRatioSection K L' hKL.2
      (C.total.fromSpecResidueField (C.productTotalMap
        (C.productGaussSource x weightedFSRadius weightedFSRadius_properties.1).1.point))) =
      X.normalizedSimultaneousRatioSectionAt (X.nativeProductIdeal I) (X.nativeProductIdeal J) hfin
        (RelativeSchemeValuedPoint.map C.productTotalMap rfl
          (C.productGaussSource x weightedFSRadius weightedFSRadius_properties.1)) hnI :=
    (congrArg sectionAtOne (canonicalPulledRatioSection_eq_sectionViaFactor_localSection K L' hKL.2
      C.unitOpen hU.1 (SchemeSupportLineFrames.supportGenericFactor _ C.unitOpen hzU) _
      (SchemeSupportLineFrames.supportGenericFactor_comp _ C.unitOpen hzU))).trans
      (@CartierRatioLocalRealization.native_eq _ K L' hKL.2 C.unitOpen hU.1 _ _ _ C.projection
        C.projection_isProper gaussModelCoefficient_le_one
        (RelativeSchemeValuedPoint.map C.productTotalMap rfl
          (C.productGaussSource x weightedFSRadius weightedFSRadius_properties.1)) hKL.1
        (SchemeSupportLineFrames.supportGenericFactor _ C.unitOpen hzU)
        (SchemeSupportLineFrames.supportGenericFactor_comp _ C.unitOpen hzU)
        (X.ratioWeight_firstNorm_ne_zero I J hfin _ hnI))
  have hpos := C.gaussNativeNormFactor_pos
    (X.normalizedSimultaneousTwistedRatioLine (X.nativeProductIdeal I) (X.nativeProductIdeal J)
      hfin j n)
    (X.normalizedSimultaneousTwistedRatioLine_isInvertible (X.nativeProductIdeal I)
      (X.nativeProductIdeal J) hfin j n)
    (X.nativeTwistLineSheaf j n)
    (X.normalizedSimultaneousNativeTestConfigurationLineComparison I J hI hJ hfin A B hA hB hX j n)
    (X.normalizedSimultaneousNativeTestConfigurationFibreOneLineIso I J hI hJ hfin A B hA hB hX j n)
    (X.nativeTwistLineSheaf_isInvertible j n) weightedFSRadius weightedFSRadius_properties.1
    weightedFSRadius_properties.2.1 x
  have hN : C.gaussNativeNormFactor
        (X.normalizedSimultaneousTwistedRatioLine (X.nativeProductIdeal I)
          (X.nativeProductIdeal J) hfin j n)
        (X.normalizedSimultaneousTwistedRatioLine_isInvertible (X.nativeProductIdeal I)
          (X.nativeProductIdeal J) hfin j n)
        (X.nativeTwistLineSheaf j n)
        (X.normalizedSimultaneousNativeTestConfigurationLineComparison
            I J hI hJ hfin A B hA hB hX j n)
        (X.normalizedSimultaneousNativeTestConfigurationFibreOneLineIso I J hI hJ hfin A B hA hB
          hX j n)
        (X.nativeTwistLineSheaf_isInvertible j n) weightedFSRadius weightedFSRadius_properties.1
        weightedFSRadius_properties.2.1 x =
      modelLineNorm (Spectrum.trivialGaussValuation_le_one k weightedFSRadius
          weightedFSRadius_properties.2.1)
        (RelativeSchemeValuedPoint.map C.productTotalMap rfl
          (C.productGaussSource x weightedFSRadius weightedFSRadius_properties.1))
        (X.normalizedSimultaneousRatioLine_isInvertible (X.nativeProductIdeal I)
          (X.nativeProductIdeal J) hfin)
        (sectionAtOne (canonicalPulledRatioSection K L' hKL.2
          (C.total.fromSpecResidueField (C.productTotalMap
            (C.productGaussSource x weightedFSRadius weightedFSRadius_properties.1).1.point)))) :=
    hfac
  have hw : X.normalizedSimultaneousRatioWeightAt (X.nativeProductIdeal I)
      (X.nativeProductIdeal J) hfin (RelativeSchemeValuedPoint.map C.productTotalMap rfl
        (C.productGaussSource x weightedFSRadius weightedFSRadius_properties.1)) hnI =
      -ENNReal.log ((modelLineNorm (Spectrum.trivialGaussValuation_le_one k weightedFSRadius
          weightedFSRadius_properties.2.1)
        (RelativeSchemeValuedPoint.map C.productTotalMap rfl
          (C.productGaussSource x weightedFSRadius weightedFSRadius_properties.1))
        (X.normalizedSimultaneousRatioLine_isInvertible (X.nativeProductIdeal I)
          (X.nativeProductIdeal J) hfin)
        (sectionAtOne (canonicalPulledRatioSection K L' hKL.2
          (C.total.fromSpecResidueField (C.productTotalMap
            (C.productGaussSource x weightedFSRadius weightedFSRadius_properties.1).1.point)))) :
          ℝ≥0) : ℝ≥0∞) := by
    unfold normalizedSimultaneousRatioWeightAt
    rw [← hsec]
    try rfl
  rw [hN] at hpos
  unfold gaussNativeModelPotential
  rw [hw, hN, ENNReal.log_of_nnreal hpos.ne', EReal.coe_neg]

/-- **The model potential of the normalized PL test configuration is the convex function.**
If the PL function `φ` satisfies `r φ(baseRestriction y) = ratioWeight(y) + c` at every point
of the normalized blow-up (as produced by
`NumericalOriginalCentralNef.exists_prescribedClass_originalCentralNef`), then the native
model potential of the twisted ratio line satisfies `pot(h(w)) = r φ(w) - c` at every
`w : X.an`, where `h` is `nativeAnalyticHomeomorph`. -/
theorem normalizedSimultaneousNativeModelPotential_eq_convex (j : Fin (M + 1)) (n : ℕ)
    {φ : X.an → ℝ} {r : ℕ} {c : ℤ}
    (hnI : ∀ y : RelativeSchemeValuedPoint (gaussValuation (1 : Valuation k ℝ≥0) gaussRadius)
        (X.normalizedSimultaneousIdealBlowupStructure
          (X.nativeProductIdeal I) (X.nativeProductIdeal J) hfin),
      modelIdealLog (X.nativeProductIdeal I) gaussModelCoefficient_le_one
        (X.normalizedSimultaneousProductPointAt (X.nativeProductIdeal I)
          (X.nativeProductIdeal J) hfin y) ≠ ⊥)
    (hφ : ∀ y : RelativeSchemeValuedPoint (gaussValuation (1 : Valuation k ℝ≥0) gaussRadius)
        (X.normalizedSimultaneousIdealBlowupStructure
          (X.nativeProductIdeal I) (X.nativeProductIdeal J) hfin),
      (((r : ℝ) * φ (X.normalizedSimultaneousBaseRestrictionAt (X.nativeProductIdeal I)
          (X.nativeProductIdeal J) hfin y) : ℝ) : EReal) =
        X.normalizedSimultaneousRatioWeightAt (X.nativeProductIdeal I) (X.nativeProductIdeal J)
          hfin y (hnI y) + ((c : ℝ) : EReal))
    (w : X.an) :
    let C := X.normalizedSimultaneousNativeTestConfiguration I J hI hJ hfin A B hA hB hX
    C.gaussNativeModelPotential
        (X.normalizedSimultaneousTwistedRatioLine (X.nativeProductIdeal I) (X.nativeProductIdeal J)
          hfin j n)
        (X.normalizedSimultaneousTwistedRatioLine_isInvertible (X.nativeProductIdeal I)
          (X.nativeProductIdeal J) hfin j n)
        (X.nativeTwistLineSheaf j n)
        (X.normalizedSimultaneousNativeTestConfigurationLineComparison
            I J hI hJ hfin A B hA hB hX j n)
        (X.normalizedSimultaneousNativeTestConfigurationFibreOneLineIso
            I J hI hJ hfin A B hA hB hX j n)
        (X.nativeTwistLineSheaf_isInvertible j n) weightedFSRadius weightedFSRadius_properties.1
        weightedFSRadius_properties.2.1 (X.nativeAnalyticHomeomorph w) =
      (r : ℝ) * φ w - c := by
  intro C
  let z := RelativeSchemeValuedPoint.map C.productTotalMap rfl
    (C.productGaussSource (X.nativeAnalyticHomeomorph w) weightedFSRadius
      weightedFSRadius_properties.1)
  have hbase : X.normalizedSimultaneousBaseRestrictionAt (X.nativeProductIdeal I)
      (X.nativeProductIdeal J) hfin z = w := by
    apply X.nativeAnalyticHomeomorph.injective
    refine (X.nativeAnalyticHomeomorph_normalizedSimultaneousBaseRestrictionAt
      (X.nativeProductIdeal I) (X.nativeProductIdeal J) hfin z).trans ?_
    exact C.twistedRatio_mapOverBase_productGauss
      (X.normalizedSimultaneousOriginalProjection
        (X.nativeProductIdeal I) (X.nativeProductIdeal J) hfin)
      (X.normalizedSimultaneousNativeTestConfiguration_originalProjection I J hI hJ hfin
        A B hA hB hX)
      (X.normalizedSimultaneousOriginalProjection_over_base (X.nativeProductIdeal I)
        (X.nativeProductIdeal J) hfin) weightedFSRadius
      weightedFSRadius_properties.1 (X.nativeAnalyticHomeomorph w)
  have hpot : ((C.gaussNativeModelPotential
        (X.normalizedSimultaneousTwistedRatioLine (X.nativeProductIdeal I) (X.nativeProductIdeal J)
          hfin j n)
        (X.normalizedSimultaneousTwistedRatioLine_isInvertible (X.nativeProductIdeal I)
          (X.nativeProductIdeal J) hfin j n)
        (X.nativeTwistLineSheaf j n)
        (X.normalizedSimultaneousNativeTestConfigurationLineComparison
            I J hI hJ hfin A B hA hB hX j n)
        (X.normalizedSimultaneousNativeTestConfigurationFibreOneLineIso I J hI hJ hfin A B hA hB
          hX j n)
        (X.nativeTwistLineSheaf_isInvertible j n) weightedFSRadius weightedFSRadius_properties.1
        weightedFSRadius_properties.2.1 (X.nativeAnalyticHomeomorph w) : ℝ) : EReal) =
      X.normalizedSimultaneousRatioWeightAt (X.nativeProductIdeal I) (X.nativeProductIdeal J)
        hfin z (hnI z) :=
    X.normalizedSimultaneousNativeModelPotential_eq_ratioWeight I J hI hJ hfin A B
      hA hB hX j n (X.nativeAnalyticHomeomorph w) (hnI z)
  have h := hφ z
  rw [hbase, ← hpot, ← EReal.coe_add] at h
  have h' := EReal.coe_injective h
  linarith

end EnvelopeProperty.ProjSubvariety
