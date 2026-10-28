import EnvelopeProperty.Global.IntrinsicPSHResumeNumericalCartierCurveOrdersFibre
import EnvelopeProperty.AlgGeom.CurveFiniteMapDegrees
import EnvelopeProperty.AlgGeom.NormalizationCartierModulePullback

/-! # Whole original curve degrees under actual finite dominant maps

Actual Cartier support and fibre projection produce the global degree
formula. No flatness or degree/ratio matching input is introduced.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open Scheme.Modules
universe u
namespace EnvelopeProperty.NumericalNonflatCurveDegrees
open CurveCartierLocalOrders CurveLineDegrees

private theorem weightedLocalOrder_support_finite {k : Type u} [Field k]
    {C : Scheme.{u}} [IsIntegral C]
    (q : C ⟶ Spec (CommRingCat.of k)) (hq : IsProjectiveFactorization q)
    (hdim : topologicalKrullDim C ≤ 1) (I : C.IdealSheafData) (hI : I.IsInvertible) :
    letI : IsProper q := hq.isProper
    letI : IsLocallyNoetherian C := LocallyOfFiniteType.isLocallyNoetherian q
    (Function.support (weightedLocalOrder q I hI)).Finite := by
  let : IsProper q := hq.isProper
  let : IsLocallyNoetherian C := LocallyOfFiniteType.isLocallyNoetherian q
  let : CompactSpace C := QuasiCompact.compactSpace_of_compactSpace q
  let : AlgebraicGeometry.IsNoetherian C :=
    { toIsLocallyNoetherian := inferInstance, toCompactSpace := inferInstance }
  let : Finite I.subscheme := CurveFiniteClosedSubschemes.finite_subscheme hdim I
    (CurveCartierIdealDegrees.support_ne_top I hI)
  have hs : (I.support : Set C).Finite := by
    rw [← I.range_subschemeι]
    exact Set.finite_range I.subschemeι
  apply hs.subset
  intro x hx
  by_contra hn
  apply hx
  unfold weightedLocalOrder
  rw [localOrder_eq_zero_of_not_mem_support I hI x hn, zero_mul]

private theorem finsum_fibres {α β : Type*} (g : α → β) (F : α → ℤ)
    (hf : (Function.support F).Finite) :
    (∑ᶠ x : β, ∑ᶠ y : {y : α // g y = x}, F y.1) = ∑ᶠ y : α, F y := by
  classical
  let s := hf.toFinset
  have hinner (x : β) :
      (∑ᶠ y : {y : α // g y = x}, F y.1) = ∑ y ∈ s with g y = x, F y := by
    calc
      _ = ∑ᶠ y : α, if g y = x then F y else 0 := by
        rw [finsum_subtype_eq_finsum_cond]
        simp_rw [finsum_eq_if]
      _ = ∑ y ∈ s, if g y = x then F y else 0 := by
        apply finsum_eq_sum_of_support_subset
        intro y hy
        have hyF : F y ≠ 0 := by
          intro hz
          apply hy
          simp only [hz, ite_self]
        exact hf.mem_toFinset.mpr hyF
      _ = ∑ y ∈ s with g y = x, F y := by rw [Finset.sum_filter]
  calc
    _ = ∑ᶠ x : β, ∑ y ∈ s with g y = x, F y := finsum_congr hinner
    _ = ∑ y ∈ s, F y := finsum_sum_filter g s F
    _ = ∑ᶠ y : α, F y := (finsum_eq_sum F hf).symm

/-- The actual original geometric Cartier comap has its genuine global degree
scaled by the SAME canonical field degree, with all finite support internal. -/
theorem degree_comap_toModules {k : Type u} [Field k]
    {C D : Scheme.{u}} [IsIntegral C] [IsIntegral D]
    (g : D ⟶ C) [IsFinite g] [IsDominant g]
    (q : C ⟶ Spec (CommRingCat.of k)) (hq : IsProjectiveFactorization q)
    (hdim : topologicalKrullDim C ≤ 1) (I : C.IdealSheafData) (hI : I.IsInvertible) :
    letI : IsProper q := hq.isProper
    letI : CompactSpace C := QuasiCompact.compactSpace_of_compactSpace q
    letI : IsProper (g ≫ q) :=
      (CurveFiniteMapDegrees.finite_comp_projectiveFactorization q hq g).isProper
    letI : CompactSpace D := QuasiCompact.compactSpace_of_compactSpace (g ≫ q)
    degree (g ≫ q) (I.comap g).toModules =
      (NumericalCurveFieldDegree.degree g : ℤ) * degree q I.toModules := by
  let : IsProper q := hq.isProper
  let : CompactSpace C := QuasiCompact.compactSpace_of_compactSpace q
  have hqD := CurveFiniteMapDegrees.finite_comp_projectiveFactorization q hq g
  let : IsProper (g ≫ q) := hqD.isProper
  let : CompactSpace D := QuasiCompact.compactSpace_of_compactSpace (g ≫ q)
  let : IsLocallyNoetherian C := LocallyOfFiniteType.isLocallyNoetherian q
  let : IsLocallyNoetherian D := LocallyOfFiniteType.isLocallyNoetherian (g ≫ q)
  have hdimD : topologicalKrullDim D ≤ 1 :=
    IntegralSchemeDimension.topologicalKrullDim_le_of_isIntegralHom g 1 hdim
  let J := I.comap g
  let hJ : J.IsInvertible := hI.comap_of_dominant_integral g
  have hsD := weightedLocalOrder_support_finite (g ≫ q) hqD hdimD J hJ
  have hsum : (∑ᶠ y : D, weightedLocalOrder (g ≫ q) J hJ y) =
      (NumericalCurveFieldDegree.degree g : ℤ) * ∑ᶠ x : C, weightedLocalOrder q I hI x := by
    calc
      _ = ∑ᶠ x : C, ∑ᶠ y : {y : D // g y = x},
          weightedLocalOrder (g ≫ q) J hJ y.1 :=
        (finsum_fibres g (weightedLocalOrder (g ≫ q) J hJ) hsD).symm
      _ = ∑ᶠ x : C, (NumericalCurveFieldDegree.degree g : ℤ) * weightedLocalOrder q I hI x := by
        apply finsum_congr
        intro x
        exact NumericalCartierCurveOrders.finsum_fibre_weightedLocalOrder g q hq hdim I hI x
      _ = _ := (mul_finsum _ _).symm
  change SchemeCoherentEulerCharacteristic.normalizedEulerCharacteristic (g ≫ q) J.toModules =
    (NumericalCurveFieldDegree.degree g : ℤ) *
      SchemeCoherentEulerCharacteristic.normalizedEulerCharacteristic q I.toModules
  rw [normalizedEulerCharacteristic_eq_neg_finsum (g ≫ q) hqD hdimD J hJ,
    normalizedEulerCharacteristic_eq_neg_finsum q hq hdim I hI, hsum]
  ring

private def ratioPullbackComapIso {C D : Scheme.{u}}
    [IsReduced C] [IsIntegral D] (g : D ⟶ C) [IsDominant g]
    (I J : C.IdealSheafData) (hI : I.IsInvertible) (hJ : J.IsInvertible) :
    (Scheme.Modules.pullback g).obj (I.ratioModule J) ≅
      (I.comap g).ratioModule (J.comap g) := by
  let : IsIso (I.toModulesComapPullbackMap g) :=
    hI.toModulesComapPullbackMap_isIso_of_dominant_integral g
  let : IsIso (J.toModulesComapPullbackMap g) :=
    hJ.toModulesComapPullbackMap_isIso_of_dominant_integral g
  exact I.ratioPullbackIso J hJ g ≪≫
    tensorObjCongr (asIso (I.toModulesComapPullbackMap g))
      (dualIsoObj (asIso (J.toModulesComapPullbackMap g)).symm)

private theorem degree_pullback_ratio {k : Type u} [Field k]
    {C D : Scheme.{u}} [IsIntegral C] [IsIntegral D]
    (g : D ⟶ C) [IsFinite g] [IsDominant g]
    (q : C ⟶ Spec (CommRingCat.of k)) (hq : IsProjectiveFactorization q)
    (hdim : topologicalKrullDim C ≤ 1) (I J : C.IdealSheafData)
    (hI : I.IsInvertible) (hJ : J.IsInvertible) :
    letI : IsProper q := hq.isProper
    letI : CompactSpace C := QuasiCompact.compactSpace_of_compactSpace q
    letI : IsProper (g ≫ q) :=
      (CurveFiniteMapDegrees.finite_comp_projectiveFactorization q hq g).isProper
    letI : CompactSpace D := QuasiCompact.compactSpace_of_compactSpace (g ≫ q)
    degree (g ≫ q) ((Scheme.Modules.pullback g).obj (I.ratioModule J)) =
      (NumericalCurveFieldDegree.degree g : ℤ) * degree q (I.ratioModule J) := by
  let : IsProper q := hq.isProper
  let : CompactSpace C := QuasiCompact.compactSpace_of_compactSpace q
  have hqD := CurveFiniteMapDegrees.finite_comp_projectiveFactorization q hq g
  let : IsProper (g ≫ q) := hqD.isProper
  let : CompactSpace D := QuasiCompact.compactSpace_of_compactSpace (g ≫ q)
  have hdimD : topologicalKrullDim D ≤ 1 :=
    IntegralSchemeDimension.topologicalKrullDim_le_of_isIntegralHom g 1 hdim
  rw [degree_eq_of_iso (g ≫ q) (ratioPullbackComapIso g I J hI hJ)]
  change SchemeCoherentEulerCharacteristic.normalizedEulerCharacteristic (g ≫ q)
      ((I.comap g).ratioModule (J.comap g)) =
    (NumericalCurveFieldDegree.degree g : ℤ) *
      SchemeCoherentEulerCharacteristic.normalizedEulerCharacteristic q (I.ratioModule J)
  rw [CurveCartierIdealDegrees.normalizedEulerCharacteristic_ratioModule
      (g ≫ q) hqD hdimD (I.comap g) (J.comap g)
      (hI.comap_of_dominant_integral g) (hJ.comap_of_dominant_integral g),
    CurveCartierIdealDegrees.normalizedEulerCharacteristic_ratioModule q hq hdim I J hI hJ]
  have hi := degree_comap_toModules g q hq hdim I hI
  have hj := degree_comap_toModules g q hq hdim J hJ
  change SchemeCoherentEulerCharacteristic.normalizedEulerCharacteristic (g ≫ q) (I.comap g).toModules =
    (NumericalCurveFieldDegree.degree g : ℤ) *
      SchemeCoherentEulerCharacteristic.normalizedEulerCharacteristic q I.toModules at hi
  change SchemeCoherentEulerCharacteristic.normalizedEulerCharacteristic (g ≫ q) (J.comap g).toModules =
    (NumericalCurveFieldDegree.degree g : ℤ) *
      SchemeCoherentEulerCharacteristic.normalizedEulerCharacteristic q J.toModules at hj
  rw [hi, hj, mul_sub]

/-- EVERY original invertible projective curve module has its genuine whole
full-Euler degree projected along an actual finite dominant map. No flatness,
normal-target, Cartier ratio or desired degree identity is supplied. -/
theorem degree_pullback {k : Type u} [Field k]
    {C D : Scheme.{u}} [IsIntegral C] [IsIntegral D]
    (g : D ⟶ C) [IsFinite g] [IsDominant g]
    (q : C ⟶ Spec (CommRingCat.of k)) (hq : IsProjectiveFactorization q)
    (hdim : topologicalKrullDim C ≤ 1) (L : C.Modules) (hL : IsInvertible L) :
    letI : IsProper q := hq.isProper
    letI : CompactSpace C := QuasiCompact.compactSpace_of_compactSpace q
    letI : IsProper (g ≫ q) :=
      (CurveFiniteMapDegrees.finite_comp_projectiveFactorization q hq g).isProper
    letI : CompactSpace D := QuasiCompact.compactSpace_of_compactSpace (g ≫ q)
    degree (g ≫ q) ((Scheme.Modules.pullback g).obj L) =
      (NumericalCurveFieldDegree.degree g : ℤ) * degree q L := by
  let : IsProper q := hq.isProper
  let : CompactSpace C := QuasiCompact.compactSpace_of_compactSpace q
  have hqD := CurveFiniteMapDegrees.finite_comp_projectiveFactorization q hq g
  let : IsProper (g ≫ q) := hqD.isProper
  let : CompactSpace D := QuasiCompact.compactSpace_of_compactSpace (g ≫ q)
  obtain ⟨I, J, hI, hJ, ⟨e⟩⟩ := ProjectiveLineCartierRatio.exists_cartier_ratio q hq L hL
  rw [degree_eq_of_iso (g ≫ q) ((Scheme.Modules.pullback g).mapIso e), degree_eq_of_iso q e]
  exact degree_pullback_ratio g q hq hdim I J hI hJ

end EnvelopeProperty.NumericalNonflatCurveDegrees
