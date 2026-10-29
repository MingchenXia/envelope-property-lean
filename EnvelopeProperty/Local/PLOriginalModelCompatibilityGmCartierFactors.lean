import EnvelopeProperty.Local.PLOriginalModelCompatibilityGmAction
import EnvelopeProperty.Local.PLIdealCartierAction
import EnvelopeProperty.Local.PLIdealNormalizedRatioPullback
import EnvelopeProperty.AlgGeom.CartierRatioGroupCoherence

/-! # Canonical invariant Cartier factors of the original normalized PL action -/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
open scoped Polynomial LaurentPolynomial CategoryTheory.MonObj
noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false

namespace EnvelopeProperty.PLOriginalModelCompatibility

variable {S : Scheme.{u}} (G : Over S) [MonObj G]
variable {A B : Over S} [ModObj G A] [ModObj G B]

/-- Equivariance transports the equality of the entire original action and
projection ideal comaps, including nonreduced ideal sheaf structure. -/
theorem invariantIdeal_comap (f : A ⟶ B) [IsModHom G f]
    (I : B.left.IdealSheafData)
    (hinv : I.comap (ModObj.smul (M := G) (X := B)).left =
      I.comap (pullback.snd G.hom B.hom)) :
    (I.comap f.left).comap (ModObj.smul (M := G) (X := A)).left =
      (I.comap f.left).comap (pullback.snd G.hom A.hom) := by
  have ha : (ModObj.smul (M := G) (X := A)).left ≫ f.left =
      (G ◁ f).left ≫ (ModObj.smul (M := G) (X := B)).left :=
    congrArg (fun a => a.left) (IsModHom.smul_hom (A := G) (f := f))
  rw [← Scheme.IdealSheafData.comap_comp, ← Scheme.IdealSheafData.comap_comp,
    ha, Scheme.IdealSheafData.comap_comp, hinv,
    ← Scheme.IdealSheafData.comap_comp, Over.whiskerLeft_left_snd]

end EnvelopeProperty.PLOriginalModelCompatibility

namespace EnvelopeProperty.ProjSubvariety
open ProjBerk Berkovich Berkovich.RelativeSchemeValuedPoint NativeTestConfiguration
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

/-- The original whole coordinate isomorphism is equivariant for the
explicitly constructed original coordinate and simultaneous-model actions. -/
theorem simultaneousNativeCoordinateIso_isModHom :
    letI := nativeClosedProductIdealGmModObj X.nativeHomogeneousIdeal I J hI hJ
    letI := X.simultaneousIdealBlowupNativeGmModObj I J hI hJ
    IsModHom (nativeMultiplicativeGroup k)
      (X.exists_simultaneousIdealBlowup_nativeCoordinateOverIso I J).choose.hom := by
  let : ModObj (nativeMultiplicativeGroup k)
      (nativeClosedBlowupAsOver X.nativeHomogeneousIdeal I J) :=
    nativeClosedProductIdealGmModObj X.nativeHomogeneousIdeal I J hI hJ
  let : ModObj (nativeMultiplicativeGroup k) (X.simultaneousIdealBlowupAsOver I J) :=
    X.simultaneousIdealBlowupNativeGmModObj I J hI hJ
  let : IsMonHom (Iso.refl (nativeMultiplicativeGroup k)).hom :=
    inferInstanceAs (IsMonHom (𝟙 (nativeMultiplicativeGroup k)))
  exact PLOriginalModelCompatibility.isModHom_ofIso_hom (nativeMultiplicativeGroup k)
    (X.exists_simultaneousIdealBlowup_nativeCoordinateOverIso I J).choose

variable (A : HomogeneousIdeal (ProjectiveGrading k[X] M))
variable (hA : (A.toIdeal.map (MvPolynomial.map (Polynomial.mapRingHom
    (LaurentPolynomial.C : k →+* k[T;T⁻¹])))).map
      (MvPolynomial.map (parameterScaleHom ((parameterLaurentUnit k : k[T;T⁻¹]ˣ) : k[T;T⁻¹]))) =
    A.toIdeal.map (MvPolynomial.map (Polynomial.mapRingHom LaurentPolynomial.C)))

include hA in
/-- The actual original simultaneous-model factor retains its whole ideal
invariance under the explicitly constructed original categorical action. -/
theorem simultaneousNativeCartierFactor_invariant :
    letI := X.simultaneousIdealBlowupNativeGmModObj I J hI hJ
    let B := X.simultaneousIdealBlowupAsOver I J
    let K := (X.nativeProductIdeal A).comap
      (X.simultaneousIdealBlowupProjection (X.nativeProductIdeal I) (X.nativeProductIdeal J))
    K.comap (cartierActionMap (nativeMultiplicativeGroup k) B) =
      K.comap (cartierProjectionMap (nativeMultiplicativeGroup k) B) := by
  let : ModObj (nativeMultiplicativeGroup k)
      (nativeClosedBlowupAsOver X.nativeHomogeneousIdeal I J) :=
    nativeClosedProductIdealGmModObj X.nativeHomogeneousIdeal I J hI hJ
  let : ModObj (nativeMultiplicativeGroup k) (X.simultaneousIdealBlowupAsOver I J) :=
    X.simultaneousIdealBlowupNativeGmModObj I J hI hJ
  let e := (X.exists_simultaneousIdealBlowup_nativeCoordinateOverIso I J).choose
  let : IsModHom (nativeMultiplicativeGroup k) e.hom :=
    X.simultaneousNativeCoordinateIso_isModHom I J hI hJ
  let : IsModHom (nativeMultiplicativeGroup k) e.inv := inferInstance
  let K := (X.nativeProductIdeal A).comap
    (X.simultaneousIdealBlowupProjection (X.nativeProductIdeal I) (X.nativeProductIdeal J))
  let K₀ := nativeClosedPullbackIdeal X.nativeHomogeneousIdeal I J A
  have he : e.hom.left ≫
      X.simultaneousIdealBlowupProjection (X.nativeProductIdeal I) (X.nativeProductIdeal J) =
    (nativeClosedProductIdeal X.nativeHomogeneousIdeal I J).blowUpπ ≫
      X.nativeConstantFamilyModelIso.hom :=
    (X.exists_simultaneousIdealBlowup_nativeCoordinateOverIso I J).choose_spec
  have hK : K.comap e.hom.left = K₀ := by
    dsimp only [K, K₀, nativeClosedPullbackIdeal]
    rw [← Scheme.IdealSheafData.comap_comp, he, Scheme.IdealSheafData.comap_comp,
      X.nativeProductIdeal_comap_constantFamilyModelIso]
  have hKi : K₀.comap e.inv.left = K := by
    rw [← hK, ← Scheme.IdealSheafData.comap_comp]
    have hei : e.inv.left ≫ e.hom.left = 𝟙 _ :=
      congrArg (fun a => a.left) e.inv_hom_id
    rw [hei, Scheme.IdealSheafData.comap_id]
  have hinv : K₀.comap (ModObj.smul (M := nativeMultiplicativeGroup k)
        (X := nativeClosedBlowupAsOver X.nativeHomogeneousIdeal I J)).left =
      K₀.comap (pullback.snd (nativeMultiplicativeGroup k).hom
        (nativeClosedBlowupAsOver X.nativeHomogeneousIdeal I J).hom) :=
    nativeClosedPullbackIdeal_comap_gmSmul X.nativeHomogeneousIdeal I J hI hJ A hA
  have h := PLOriginalModelCompatibility.invariantIdeal_comap
    (nativeMultiplicativeGroup k) e.inv K₀ hinv
  rw [hKi] at h
  exact h

variable (hfin : ∀ w : X.an,
  modelIdealLog (X.nativeProductIdeal I) gaussModelCoefficient_le_one
    (X.nativeProductGaussPoint w) ≠ ⊥ ∧
  modelIdealLog (X.nativeProductIdeal J) gaussModelCoefficient_le_one
    (X.nativeProductGaussPoint w) ≠ ⊥)

include hA in
/-- Canonical original normalization pullback preserves the entire actual
nonradical Cartier factor under the same constructed normalized action. -/
theorem normalizedSimultaneousNativeCartierFactor_invariant :
    letI := X.normalizedSimultaneousNativeGmModObj I J hI hJ hfin
    let N := totalOver k (X.normalizedSimultaneousIdealBlowupStructure
      (X.nativeProductIdeal I) (X.nativeProductIdeal J) hfin)
    let K := ((X.nativeProductIdeal A).comap
      (X.simultaneousIdealBlowupProjection (X.nativeProductIdeal I) (X.nativeProductIdeal J))).comap
        (X.normalizedSimultaneousIdealBlowupProjection
          (X.nativeProductIdeal I) (X.nativeProductIdeal J) hfin)
    K.comap (cartierActionMap (nativeMultiplicativeGroup k) N) =
      K.comap (cartierProjectionMap (nativeMultiplicativeGroup k) N) := by
  let : ModObj (nativeMultiplicativeGroup k) (X.simultaneousIdealBlowupAsOver I J) :=
    X.simultaneousIdealBlowupNativeGmModObj I J hI hJ
  let : ModObj (nativeMultiplicativeGroup k)
      (totalOver k (X.normalizedSimultaneousIdealBlowupStructure
        (X.nativeProductIdeal I) (X.nativeProductIdeal J) hfin)) :=
    X.normalizedSimultaneousNativeGmModObj I J hI hJ hfin
  let : IsModHom (nativeMultiplicativeGroup k)
      (X.normalizedSimultaneousNativeOverProjection I J hfin) :=
    X.normalizedSimultaneousNativeOverProjection_isModHom I J hI hJ hfin
  exact PLOriginalModelCompatibility.invariantIdeal_comap
    (nativeMultiplicativeGroup k) (X.normalizedSimultaneousNativeOverProjection I J hfin)
    ((X.nativeProductIdeal A).comap
      (X.simultaneousIdealBlowupProjection (X.nativeProductIdeal I) (X.nativeProductIdeal J)))
    (X.simultaneousNativeCartierFactor_invariant I J hI hJ A hA)

omit A hA in
/-- The same original normalized ratio line carries its genuine canonical
whole group comparison, derived from the actual original two invariant
Cartier factors and the constructed action. -/
def normalizedSimultaneousRatioNativeGmLinearization :
    letI := X.normalizedSimultaneousNativeGmModObj I J hI hJ hfin
    let N := totalOver k (X.normalizedSimultaneousIdealBlowupStructure
      (X.nativeProductIdeal I) (X.nativeProductIdeal J) hfin)
    (Scheme.Modules.pullback (cartierActionMap (nativeMultiplicativeGroup k) N)).obj
      (X.normalizedSimultaneousRatioLine (X.nativeProductIdeal I) (X.nativeProductIdeal J) hfin) ≅
    (Scheme.Modules.pullback (cartierProjectionMap (nativeMultiplicativeGroup k) N)).obj
      (X.normalizedSimultaneousRatioLine (X.nativeProductIdeal I)
          (X.nativeProductIdeal J) hfin) := by
  let : IsIntegral (X.simultaneousIdealBlowup (X.nativeProductIdeal I) (X.nativeProductIdeal J)) :=
    X.simultaneousIdealBlowup_isIntegral_of_finiteLogs
      (X.nativeProductIdeal I) (X.nativeProductIdeal J) X.triv
      (hfin X.triv).1 (hfin X.triv).2
  let : ModObj (nativeMultiplicativeGroup k)
      (totalOver k (X.normalizedSimultaneousIdealBlowupStructure
        (X.nativeProductIdeal I) (X.nativeProductIdeal J) hfin)) :=
    X.normalizedSimultaneousNativeGmModObj I J hI hJ hfin
  have hI' := IntegralSchemeNormalization.cartier_comap _
    (X.simultaneousIdealBlowup_isInvertible (X.nativeProductIdeal I) (X.nativeProductIdeal J)).1
  have hJ' := IntegralSchemeNormalization.cartier_comap _
    (X.simultaneousIdealBlowup_isInvertible (X.nativeProductIdeal I) (X.nativeProductIdeal J)).2
  have hinvI := X.normalizedSimultaneousNativeCartierFactor_invariant I J hI hJ I
    (hI k[T;T⁻¹] LaurentPolynomial.C (parameterLaurentUnit k)) hfin
  have hinvJ := X.normalizedSimultaneousNativeCartierFactor_invariant I J hI hJ J
    (hJ k[T;T⁻¹] LaurentPolynomial.C (parameterLaurentUnit k)) hfin
  exact cartierRatioGroupLinearization (nativeMultiplicativeGroup k)
    (totalOver k (X.normalizedSimultaneousIdealBlowupStructure
      (X.nativeProductIdeal I) (X.nativeProductIdeal J) hfin)) _ _ hI' hJ' hinvI hinvJ

end EnvelopeProperty.ProjSubvariety
