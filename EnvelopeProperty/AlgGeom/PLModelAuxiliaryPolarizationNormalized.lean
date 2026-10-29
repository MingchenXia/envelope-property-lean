import EnvelopeProperty.AlgGeom.PLModelAuxiliaryPolarizationNativeBlowup
import EnvelopeProperty.AlgGeom.PLModelAuxiliaryPolarizationFinitePullback
import EnvelopeProperty.AlgGeom.PLModelAuxiliaryPolarizationBaseChange
import EnvelopeProperty.AlgGeom.AmpleLineTwistGeneration
import EnvelopeProperty.AlgGeom.AmpleTensorLines
import EnvelopeProperty.AlgGeom.NativeProjectivityFromPolynomialFactorization
import EnvelopeProperty.Local.PLOriginalModelCompatibilityAuxiliaryLine
import EnvelopeProperty.Local.PLNormalizedPolarizationComparison
import EnvelopeProperty.AlgGeom.ProjectiveCentralFiberSectionLifting

/-! # A centrally ample tautological twist on the normalized simultaneous PL model

Let `X ⊆ ℙᴹ_k` be a projective subvariety, let `I, J` be homogeneous ideals of `k[t][x₀,…,x_M]`
with finite model logarithms (`hfin`), let `μ : Bl_{IJ}(X × 𝔸¹) ⟶ X × 𝔸¹` be the blowup of the
product ideal and `ν : 𝒳 ⟶ Bl_{IJ}` its normalization (the normal test configuration dominating
`X × 𝔸¹` of the proof of FHX `lem:local-PL-positivity`). On `𝒳` consider the *tautological twist*
`H_q = q_X^* O_X(q) ⊗ ν^*(IJ · O_{Bl})`.

* `normalizedSimultaneousTautologicalTwist_exists_ample`: for some `q > 0`, `H_q` is ample over
  `𝔸¹_k`: on the blowup the twist is very ample (`exists_veryAmple_nativeTautologicalTwist`), and
  ampleness survives the finite pullback along `ν` (`isAmple_finite_pullback`); the
  normalization and coefficient comparisons identify the pullback with `H_q`.
* `normalizedSimultaneousTautologicalTwist_exists_central_ample`: the same `H_q` restricts to an
  ample line on the central fibre `𝒳₀ = 𝒳 ×_{𝔸¹} {0}` (`isAmple_of_isPullback` for
  `ev₀ : k[t] →+* k`). The central fibre may be reducible and nonreduced.

This is the auxiliary polarization of the nef-to-FS argument of the formalized route to FHX
`lem:local-PL-positivity`. Blueprint: `thm:pl-original-normalized-tautological-central-ample`.
-/
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open Scheme.Modules
open scoped Polynomial
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace EnvelopeProperty.ProjSubvariety
open ProjBerk Berkovich Berkovich.RelativeSchemeValuedPoint
open PLModelAuxiliaryPolarization IntegralSchemeNormalization
attribute [local instance] MvPolynomial.gradedAlgebra Scheme.Modules.monoidalCategory
variable {k : Type u} [Field k] {M : ℕ} (X : ProjSubvariety k M)
variable (I J : HomogeneousIdeal (ProjectiveGrading k[X] M))
variable (hfin : ∀ w : X.an,
  modelIdealLog (X.nativeProductIdeal I) gaussModelCoefficient_le_one
    (X.nativeProductGaussPoint w) ≠ ⊥ ∧
  modelIdealLog (X.nativeProductIdeal J) gaussModelCoefficient_le_one
    (X.nativeProductGaussPoint w) ≠ ⊥)

/-- For some `q > 0` the tautological twist `q_X^* O_X(q) ⊗ ν^*(IJ · O_{Bl})` of the normalized
simultaneous PL model is ample over `𝔸¹_k`. -/
theorem normalizedSimultaneousTautologicalTwist_exists_ample :
    ∃ q : ℕ, 0 < q ∧ SchemeLineAmpleness.IsAmple
      (X.normalizedSimultaneousIdealBlowupStructure (X.nativeProductIdeal I)
          (X.nativeProductIdeal J) hfin)
      (X.normalizedSimultaneousTautologicalTwistLine I J hfin (0 : Fin (M + 1)) q) := by
  let I₀ := X.nativeProductIdeal I
  let J₀ := X.nativeProductIdeal J
  let D := I₀ * J₀
  let μ := X.simultaneousIdealBlowupProjection I₀ J₀
  let ν := X.normalizedSimultaneousIdealBlowupProjection I₀ J₀ hfin
  let j := X.nativeProductPolynomialInclusion
  let p := X.nativeProductStructure
  let pB := μ ≫ p
  let : IsIntegral X.NativeProductModel := X.nativeProductModel_isIntegral
  let : IsIntegral (X.simultaneousIdealBlowup I₀ J₀) :=
    X.simultaneousIdealBlowup_isIntegral_of_finiteLogs I₀ J₀ X.triv
      (hfin X.triv).1 (hfin X.triv).2
  let : IsClosedImmersion j := by dsimp [j, nativeProductPolynomialInclusion]; infer_instance
  have hjbase : j ≫ Alterations.projectiveSpaceStructure k[X] M = p :=
    X.nativeProductPolynomialInclusion_over_originalParameter
  obtain ⟨q, hq, hV⟩ := exists_veryAmple_nativeTautologicalTwist p j hjbase D
  let L := nativeTautologicalTwist D j q
  have hL : SchemeLineAmpleness.IsAmple pB L := AmpleLineTwistGeneration.isAmple_of_isVeryAmple hV
  let : IsFinite ν := X.normalizedSimultaneousIdealBlowupProjection_isFinite_anyField I₀ J₀ hfin
  let : IsProjective (ν ≫ pB) :=
    NativeProjectivityFromPolynomialFactorization.of_isProjectiveFactorization _
      (X.normalizedSimultaneousIdealBlowupStructure_isProjectiveFactorization I₀ J₀ hfin)
  have hPull := isAmple_finite_pullback pB L hL ν
  let C := D.comap μ
  have hC : C.IsInvertible := Scheme.IdealSheafData.blowUp.isInvertible_comap_π D
  let : IsIso (C.toModulesComapPullbackMap ν) :=
    cartierModuleComparison_isIso (X.simultaneousIdealBlowup I₀ J₀) hC
  let Oq := MvPolynomial.coordinateHyperplaneTwist (R := k[X]) (0 : Fin (M + 1)) (q : ℤ)
  let A := (Scheme.Modules.pullback μ).obj ((Scheme.Modules.pullback j).obj Oq)
  let KN := X.normalizedSimultaneousTautologicalProductIdeal I J hfin
  let AN := (Scheme.Modules.pullback (X.normalizedSimultaneousOriginalProjection I₀ J₀ hfin)).obj
    (X.nativeTwistLineSheaf (0 : Fin (M + 1)) q)
  let eA : (Scheme.Modules.pullback ν).obj A ≅ AN :=
    (pullbackComp ν μ).app ((Scheme.Modules.pullback j).obj Oq) ≪≫
      (pullbackComp (ν ≫ μ) j).app Oq ≪≫
      X.normalizedSimultaneousPolynomialTwistIso I₀ J₀ hfin (0 : Fin (M + 1)) q
  let eK : (Scheme.Modules.pullback ν).obj C.toModules ≅ KN.toModules :=
    asIso (C.toModulesComapPullbackMap ν)
  let : (Scheme.Modules.pullback ν).Monoidal := pullbackMonoidal ν
  let eL : (Scheme.Modules.pullback ν).obj L ≅
      X.normalizedSimultaneousTautologicalTwistLine I J hfin (0 : Fin (M + 1)) q :=
    (Functor.Monoidal.μIso (Scheme.Modules.pullback ν) A C.toModules).symm ≪≫
      (eA ⊗ᵢ eK) ≪≫ ModularCurves.monoidalTensorObjIso AN KN.toModules
  exact ⟨q, hq, AmpleTensorLines.ample_of_iso hPull eL⟩

/-- For some `q > 0` the tautological twist `H_q` of the normalized simultaneous PL model is ample
over `𝔸¹_k` and its restriction to the central fibre `𝒳₀` is ample over `k`. -/
theorem normalizedSimultaneousTautologicalTwist_exists_central_ample :
    ∃ q : ℕ, 0 < q ∧
      SchemeLineAmpleness.IsAmple (X.normalizedSimultaneousIdealBlowupStructure
          (X.nativeProductIdeal I) (X.nativeProductIdeal J) hfin)
        (X.normalizedSimultaneousTautologicalTwistLine I J hfin (0 : Fin (M + 1)) q) ∧
      SchemeLineAmpleness.IsAmple
        (pullback.snd (X.normalizedSimultaneousIdealBlowupStructure
          (X.nativeProductIdeal I) (X.nativeProductIdeal J) hfin)
          (ProjectiveCentralFiberSectionLifting.zeroMap k))
        ((Scheme.Modules.pullback (ProjectiveCentralFiberSectionLifting.zeroInclusion
          (X.normalizedSimultaneousIdealBlowupStructure
            (X.nativeProductIdeal I) (X.nativeProductIdeal J) hfin))).obj
          (X.normalizedSimultaneousTautologicalTwistLine I J hfin (0 : Fin (M + 1)) q)) := by
  obtain ⟨q, hq, hL⟩ := X.normalizedSimultaneousTautologicalTwist_exists_ample I J hfin
  refine ⟨q, hq, hL, ?_⟩
  let p := X.normalizedSimultaneousIdealBlowupStructure
    (X.nativeProductIdeal I) (X.nativeProductIdeal J) hfin
  exact isAmple_of_isPullback (Polynomial.evalRingHom (0 : k)) p
    (pullback.snd p (ProjectiveCentralFiberSectionLifting.zeroMap k))
    (pullback.fst p (ProjectiveCentralFiberSectionLifting.zeroMap k))
    (IsPullback.of_hasPullback p (ProjectiveCentralFiberSectionLifting.zeroMap k)) _ hL

section TestConfiguration

variable (hI : ∀ (S : Type u) [CommRing S] (f : k →+* S) (a : Sˣ),
  (I.toIdeal.map (MvPolynomial.map (Polynomial.mapRingHom f))).map
    (MvPolynomial.map (parameterScaleHom (a : S))) =
      I.toIdeal.map (MvPolynomial.map (Polynomial.mapRingHom f)))
variable (hJ : ∀ (S : Type u) [CommRing S] (f : k →+* S) (a : Sˣ),
  (J.toIdeal.map (MvPolynomial.map (Polynomial.mapRingHom f))).map
    (MvPolynomial.map (parameterScaleHom (a : S))) =
      J.toIdeal.map (MvPolynomial.map (Polynomial.mapRingHom f)))
variable (A B : ℕ) (hA : MvPolynomial.C (Polynomial.X ^ A) ∈ I.toIdeal)
  (hB : MvPolynomial.C (Polynomial.X ^ B) ∈ J.toIdeal) (hX : X.IsProjNormal)

/-- **Central ampleness of the auxiliary polarization** on the normalized test configuration
`C = normalizedSimultaneousNativeTestConfiguration`: for some `q > 0` the tautological twist
`H_q` (with its `𝔾ₘ`-linearization
`normalizedSimultaneousNativeTestConfigurationTautologicalLineComparison` and fibre-one
identification `normalizedSimultaneousNativeTestConfigurationTautologicalFibreOneLineIso` with
`O_X(q)`) restricts to an ample line on the central fibre of `C`. -/
theorem normalizedSimultaneousNativeTestConfiguration_exists_central_ample_tautologicalTwist :
    ∃ q : ℕ, 0 < q ∧
      SchemeLineAmpleness.IsAmple
        (pullback.snd (X.normalizedSimultaneousNativeTestConfiguration I J hI hJ hfin A B hA hB
          hX).projection (ProjectiveCentralFiberSectionLifting.zeroMap k))
        ((Scheme.Modules.pullback (ProjectiveCentralFiberSectionLifting.zeroInclusion
          (X.normalizedSimultaneousNativeTestConfiguration I J hI hJ hfin A B hA hB
            hX).projection)).obj
          (X.normalizedSimultaneousTautologicalTwistLine I J hfin (0 : Fin (M + 1)) q)) := by
  obtain ⟨q, hq, _, hC⟩ := X.normalizedSimultaneousTautologicalTwist_exists_central_ample I J hfin
  exact ⟨q, hq, hC⟩

end TestConfiguration

end EnvelopeProperty.ProjSubvariety
