import EnvelopeProperty.Local.PLOriginalModelCompatibilityTestConfiguration
import EnvelopeProperty.Local.PLOriginalModelCompatibilityRatioSectionTransport

/-! # The unchanged original ratio section along the actual native noncentral action lift -/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
open Scheme.Modules
open scoped Polynomial LaurentPolynomial CategoryTheory.MonObj
noncomputable section
universe u

namespace EnvelopeProperty.ProjSubvariety
open ProjBerk Berkovich Berkovich.RelativeSchemeValuedPoint NativeTestConfiguration
open SchemeLocalSectionRatioPullback
attribute [local instance] MvPolynomial.gradedAlgebra

variable {k : Type u} [Field k] {M : ℕ} (X : ProjSubvariety k M)
variable (I J : HomogeneousIdeal (ProjectiveGrading k[X] M))
variable (hfin : ∀ w : X.an,
  modelIdealLog (X.nativeProductIdeal I) gaussModelCoefficient_le_one
    (X.nativeProductGaussPoint w) ≠ ⊥ ∧
  modelIdealLog (X.nativeProductIdeal J) gaussModelCoefficient_le_one
    (X.nativeProductGaussPoint w) ≠ ⊥)

/-- Both unchanged original normalized ideal factors are Cartier on the
same original normalization, with no extra factor certificate. -/
theorem normalizedSimultaneousNativeCartierFactors_isInvertible :
    (((X.nativeProductIdeal I).comap (X.simultaneousIdealBlowupProjection
      (X.nativeProductIdeal I) (X.nativeProductIdeal J))).comap
        (X.normalizedSimultaneousIdealBlowupProjection
          (X.nativeProductIdeal I) (X.nativeProductIdeal J) hfin)).IsInvertible ∧
    (((X.nativeProductIdeal J).comap (X.simultaneousIdealBlowupProjection
      (X.nativeProductIdeal I) (X.nativeProductIdeal J))).comap
        (X.normalizedSimultaneousIdealBlowupProjection
          (X.nativeProductIdeal I) (X.nativeProductIdeal J) hfin)).IsInvertible := by
  let : IsIntegral (X.simultaneousIdealBlowup (X.nativeProductIdeal I) (X.nativeProductIdeal J)) :=
    X.simultaneousIdealBlowup_isIntegral_of_finiteLogs
      (X.nativeProductIdeal I) (X.nativeProductIdeal J) X.triv
      (hfin X.triv).1 (hfin X.triv).2
  exact ⟨IntegralSchemeNormalization.cartier_comap _
      (X.simultaneousIdealBlowup_isInvertible (X.nativeProductIdeal I) (X.nativeProductIdeal J)).1,
    IntegralSchemeNormalization.cartier_comap _
      (X.simultaneousIdealBlowup_isInvertible (X.nativeProductIdeal I) (X.nativeProductIdeal J)).2⟩

/-- The entire original normalized noncentral open misses the supports
of both unchanged original Cartier factors, from the original powers. -/
theorem normalizedSimultaneousNoncentralOpen_off_nativeCartierFactors (A B : ℕ)
    (hA : MvPolynomial.C (Polynomial.X ^ A) ∈ I.toIdeal)
    (hB : MvPolynomial.C (Polynomial.X ^ B) ∈ J.toIdeal) :
    X.normalizedSimultaneousNoncentralOpen (X.nativeProductIdeal I) (X.nativeProductIdeal J) hfin ≤
      ((((X.nativeProductIdeal I).comap (X.simultaneousIdealBlowupProjection
        (X.nativeProductIdeal I) (X.nativeProductIdeal J))).comap
          (X.normalizedSimultaneousIdealBlowupProjection
            (X.nativeProductIdeal I) (X.nativeProductIdeal J) hfin)).support.compl) ∧
    X.normalizedSimultaneousNoncentralOpen (X.nativeProductIdeal I) (X.nativeProductIdeal J) hfin ≤
      ((((X.nativeProductIdeal J).comap (X.simultaneousIdealBlowupProjection
        (X.nativeProductIdeal I) (X.nativeProductIdeal J))).comap
          (X.normalizedSimultaneousIdealBlowupProjection
            (X.nativeProductIdeal I) (X.nativeProductIdeal J) hfin)).support.compl) := by
  constructor
  · intro y hy
    rw [Scheme.IdealSheafData.support_comap, Scheme.IdealSheafData.support_comap]
    exact X.parameterOpen_le_compl_nativeProductIdeal_support I A hA hy
  · intro y hy
    rw [Scheme.IdealSheafData.support_comap, Scheme.IdealSheafData.support_comap]
    exact X.parameterOpen_le_compl_nativeProductIdeal_support J B hB hy

variable (hI : ∀ (S : Type u) [CommRing S] (f : k →+* S) (a : Sˣ),
  (I.toIdeal.map (MvPolynomial.map (Polynomial.mapRingHom f))).map
    (MvPolynomial.map (parameterScaleHom (a : S))) =
      I.toIdeal.map (MvPolynomial.map (Polynomial.mapRingHom f)))
variable (hJ : ∀ (S : Type u) [CommRing S] (f : k →+* S) (a : Sˣ),
  (J.toIdeal.map (MvPolynomial.map (Polynomial.mapRingHom f))).map
    (MvPolynomial.map (parameterScaleHom (a : S))) =
      J.toIdeal.map (MvPolynomial.map (Polynomial.mapRingHom f)))

/-- The unchanged canonical ratio comparison along the ACTUAL native
open action lift preserves the original local ratio section, before any
residue or norm comparison. Both factorizations are internally derived. -/
theorem normalizedSimultaneousNativeActionLift_ratioLocalSection
    (A B : ℕ) (hA : MvPolynomial.C (Polynomial.X ^ A) ∈ I.toIdeal)
    (hB : MvPolynomial.C (Polynomial.X ^ B) ∈ J.toIdeal) (hX : X.IsProjNormal) :
    let C := X.normalizedSimultaneousNativeTestConfiguration I J hI hJ hfin A B hA hB hX
    let K := ((X.nativeProductIdeal I).comap (X.simultaneousIdealBlowupProjection
      (X.nativeProductIdeal I) (X.nativeProductIdeal J))).comap
        (X.normalizedSimultaneousIdealBlowupProjection
          (X.nativeProductIdeal I) (X.nativeProductIdeal J) hfin)
    let L := ((X.nativeProductIdeal J).comap (X.simultaneousIdealBlowupProjection
      (X.nativeProductIdeal I) (X.nativeProductIdeal J))).comap
        (X.normalizedSimultaneousIdealBlowupProjection
          (X.nativeProductIdeal I) (X.nativeProductIdeal J) hfin)
    let hL := (X.normalizedSimultaneousNativeCartierFactors_isInvertible I J hfin).2
    let U := X.normalizedSimultaneousNoncentralOpen
      (X.nativeProductIdeal I) (X.nativeProductIdeal J) hfin
    let hU := (X.normalizedSimultaneousNoncentralOpen_off_nativeCartierFactors
      I J hfin A B hA hB).1
    let ha : (𝟙 U.toScheme) ≫ U.ι = C.unitOpenActionLift.left ≫ C.lineActionMap := by
      change 𝟙 _ ≫ C.unitOpenInclusion.left = _
      rw [Category.id_comp]
      exact C.lineActionLift_action.symm
    let qp := C.unitOpenFibreProjection.left ≫ X.normalizedSimultaneousFibreOneNoncentralLift
      (X.nativeProductIdeal I) (X.nativeProductIdeal J) hfin
    let hp : qp ≫ U.ι = C.unitOpenActionLift.left ≫ C.lineProjectionMap := by
      change (C.unitOpenFibreProjection.left ≫ X.normalizedSimultaneousFibreOneNoncentralLift
        (X.nativeProductIdeal I) (X.nativeProductIdeal J) hfin) ≫
          (X.normalizedSimultaneousNoncentralOpen (X.nativeProductIdeal I)
            (X.nativeProductIdeal J) hfin).ι = _
      exact (Category.assoc _ _ _).trans
        ((congrArg (fun g => C.unitOpenFibreProjection.left ≫ g)
          (X.normalizedSimultaneousFibreOneNoncentralLift_inclusion (X.nativeProductIdeal I)
            (X.nativeProductIdeal J) hfin)).trans C.lineActionLift_projection.symm)
    sectionViaFactor (𝟙 U.toScheme) U.ι (C.unitOpenActionLift.left ≫ C.lineActionMap) ha
        (CartierRatioLocalRealization.localSection K L hL U hU) ≫
      (pullbackIsoAlong C.lineActionMap C.lineProjectionMap
        (X.normalizedSimultaneousRatioNativeGmLinearization I J hI hJ hfin)
        C.unitOpenActionLift.left).hom =
    sectionViaFactor qp U.ι (C.unitOpenActionLift.left ≫ C.lineProjectionMap) hp
      (CartierRatioLocalRealization.localSection K L hL U hU) := by
  intro C K L hL U hU ha qp hp
  let N := totalOver k C.projection
  let : ModObj (nativeMultiplicativeGroup k) N :=
    X.normalizedSimultaneousNativeGmModObj I J hI hJ hfin
  exact
      PLOriginalModelCompatibility.RatioSectionTransport.cartierRatioGroupLinearization_localSection
    (nativeMultiplicativeGroup k) N K L
    (X.normalizedSimultaneousNativeCartierFactors_isInvertible I J hfin).1 hL
    (X.normalizedSimultaneousNativeCartierFactor_invariant I J hI hJ I
      (hI k[T;T⁻¹] LaurentPolynomial.C (parameterLaurentUnit k)) hfin)
    (X.normalizedSimultaneousNativeCartierFactor_invariant I J hI hJ J
      (hJ k[T;T⁻¹] LaurentPolynomial.C (parameterLaurentUnit k)) hfin)
    C.unitOpenActionLift.left U U hU hU (𝟙 U.toScheme) qp ha hp

end EnvelopeProperty.ProjSubvariety
