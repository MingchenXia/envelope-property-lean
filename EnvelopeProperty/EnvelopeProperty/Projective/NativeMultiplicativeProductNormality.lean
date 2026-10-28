/-
Copyright (c) 2026 Envelope Property Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import EnvelopeProperty.Projective.NativeMultiplicativeGroup
import EnvelopeProperty.Berkovich.SchemeNormalStalks
import Hironaka.Algebra.RegularSmooth.SmoothAt
import Mathlib.RingTheory.Polynomial.IsIntegral
import Mathlib.Topology.Sets.OpenCover

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped Polynomial LaurentPolynomial TensorProduct
noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace EnvelopeProperty.ProjBerk
variable {R : Type u} [CommRing R] {X : Scheme.{u}}

private def multiplicativeProductChartIso (f : X ⟶ Spec (CommRingCat.of R))
    (U : X.affineOpens) :
    Spec (CommRingCat.of (LaurentPolynomial Γ(X, U.1))) ≅
      pullback (pullback.snd (nativeMultiplicativeGroup R).hom f) U.2.fromSpec := by
  let := f.sectionsAlgebra U.1
  have hsquare : Spec.map (CommRingCat.ofHom (algebraMap R Γ(X, U.1))) =
      U.2.fromSpec ≫ f := by
    change Spec.map ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ f.appLE ⊤ U.1 le_top) = _
    rw [Spec.map_comp, ← Scheme.isoSpec_Spec_inv, ← IsAffineOpen.fromSpec_top]
    exact IsAffineOpen.SpecMap_appLE_fromSpec f (isAffineOpen_top _) U.2 le_top
  let e : Γ(X, U.1) ⊗[R] R[T;T⁻¹] ≃ₐ[Γ(X, U.1)] Γ(X, U.1)[T;T⁻¹] :=
    AddMonoidAlgebra.scalarTensorEquiv R Γ(X, U.1)
  exact (Scheme.Spec.mapIso e.toRingEquiv.toCommRingCatIso.op) ≪≫
    (pullbackSpecIso R Γ(X, U.1) R[T;T⁻¹]).symm ≪≫
    pullbackSymmetry _ _ ≪≫
    pullback.congrHom rfl hsquare ≪≫
    (pullbackLeftPullbackSndIso (nativeMultiplicativeGroup R).hom f U.2.fromSpec).symm

private def multiplicativeProductChartMap (f : X ⟶ Spec (CommRingCat.of R))
    (U : X.affineOpens) :
    Spec (CommRingCat.of (LaurentPolynomial Γ(X, U.1))) ⟶
      pullback (nativeMultiplicativeGroup R).hom f :=
  (multiplicativeProductChartIso f U).hom ≫
    pullback.fst (pullback.snd (nativeMultiplicativeGroup R).hom f) U.2.fromSpec

private theorem multiplicativeProductChartMap_isOpenImmersion
    (f : X ⟶ Spec (CommRingCat.of R)) (U : X.affineOpens) :
    IsOpenImmersion (multiplicativeProductChartMap f U) := by
  unfold multiplicativeProductChartMap
  infer_instance

attribute [local instance] multiplicativeProductChartMap_isOpenImmersion

private theorem multiplicativeProductChartMap_opensRange
    (f : X ⟶ Spec (CommRingCat.of R)) (U : X.affineOpens) :
    (multiplicativeProductChartMap f U).opensRange =
      (pullback.snd (nativeMultiplicativeGroup R).hom f) ⁻¹ᵁ U.1 := by
  change ((multiplicativeProductChartIso f U).hom ≫
    pullback.fst (pullback.snd (nativeMultiplicativeGroup R).hom f) U.2.fromSpec).opensRange = _
  rw [Scheme.Hom.opensRange_comp_of_isIso,
    Scheme.Hom.opensRange_pullbackFst, U.2.opensRange_fromSpec]

private def multiplicativeProductUnitSection (f : X ⟶ Spec (CommRingCat.of R)) :
    X ⟶ pullback (nativeMultiplicativeGroup R).hom f := by
  let η : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of R[T;T⁻¹]) :=
    (MonObj.one (X := nativeMultiplicativeGroup R)).left
  have hη : η ≫ (nativeMultiplicativeGroup R).hom = 𝟙 (Spec (CommRingCat.of R)) :=
    (MonObj.one (X := nativeMultiplicativeGroup R)).w
  exact pullback.lift (f ≫ η) (𝟙 _) (by simpa only [Category.assoc,
    Category.id_comp, Category.comp_id] using congrArg (fun g => f ≫ g) hη)

private theorem multiplicativeProductUnitSection_snd (f : X ⟶ Spec (CommRingCat.of R)) :
    multiplicativeProductUnitSection f ≫ pullback.snd (nativeMultiplicativeGroup R).hom f = 𝟙 X := by
  simp [multiplicativeProductUnitSection]

private theorem multiplicativeProductChartOpen_isIntegral [IsIntegral X]
    (f : X ⟶ Spec (CommRingCat.of R)) (U : X.affineOpens) [Nonempty U.1] :
    IsIntegral (((pullback.snd (nativeMultiplicativeGroup R).hom f) ⁻¹ᵁ U.1).toScheme) := by
  let A : Type u := Γ(X, U.1)
  let : IsDomain A := inferInstance
  let : IsDomain A[T;T⁻¹] := IsLocalization.isDomain_of_le_nonZeroDivisors
    A[T;T⁻¹] (powers_le_nonZeroDivisors_of_noZeroDivisors (Polynomial.X_ne_zero : (Polynomial.X : A[X]) ≠ 0))
  let V := (pullback.snd (nativeMultiplicativeGroup R).hom f) ⁻¹ᵁ U.1
  let e := IsOpenImmersion.isoOfRangeEq (multiplicativeProductChartMap f U) V.ι (by
    have hr := congrArg (fun W : (pullback (nativeMultiplicativeGroup R).hom f).Opens =>
        W.carrier) (multiplicativeProductChartMap_opensRange f U)
    change Set.range (multiplicativeProductChartMap f U) = (V : Set _) at hr
    simpa only [Scheme.Opens.range_ι] using hr)
  exact IsIntegral.of_isIso e.hom

private theorem multiplicativeProduct_preimage_cover
    (f : X ⟶ Spec (CommRingCat.of R)) :
    TopologicalSpace.IsOpenCover (fun U : IntegralSchemeNormalization.NonemptyAffineOpen X =>
      (pullback.snd (nativeMultiplicativeGroup R).hom f) ⁻¹ᵁ U.1.1) := by
  apply eq_top_iff.mpr
  intro z _
  have hz : (pullback.snd (nativeMultiplicativeGroup R).hom f) z ∈
      ⨆ U : IntegralSchemeNormalization.NonemptyAffineOpen X, (U.1.1 : X.Opens) := by
    rw [IntegralSchemeNormalization.iSup_nonemptyAffineOpen_eq_top]
    trivial
  obtain ⟨U, hU⟩ := TopologicalSpace.Opens.mem_iSup.mp hz
  exact TopologicalSpace.Opens.mem_iSup.mpr ⟨U, hU⟩

/-- The SAME actual Laurent-group product is integral over ANY commutative
base ring, with no finite-type or Noetherian hypothesis. -/
theorem nativeMultiplicativeGroup_pullback_isIntegral [IsIntegral X]
    (f : X ⟶ Spec (CommRingCat.of R)) :
    IsIntegral (pullback (nativeMultiplicativeGroup R).hom f) := by
  classical
  let P : Scheme.{u} := pullback (nativeMultiplicativeGroup R).hom f
  let π : P ⟶ X := pullback.snd (nativeMultiplicativeGroup R).hom f
  let Ω : IntegralSchemeNormalization.NonemptyAffineOpen X → P.Opens :=
    fun U => π ⁻¹ᵁ U.1.1
  have hcover : TopologicalSpace.IsOpenCover Ω := multiplicativeProduct_preimage_cover f
  let cov := P.openCoverOfIsOpenCover Ω hcover
  have hInt (U : IntegralSchemeNormalization.NonemptyAffineOpen X) :
      IsIntegral ((Ω U).toScheme) := by
    let : Nonempty U.1.1 := U.2
    exact multiplicativeProductChartOpen_isIntegral f U.1
  let : ∀ U : IntegralSchemeNormalization.NonemptyAffineOpen X,
      IsReduced (cov.X U) := fun U => by
    let := hInt U
    change IsReduced ((Ω U).toScheme)
    infer_instance
  let : IsReduced P := IsReduced.of_openCover P cov
  have hpair : Pairwise (fun U V => ¬ Disjoint (Ω U) (Ω V)) := by
    intro U V _ hd
    obtain ⟨x, hxU, hxV⟩ := nonempty_preirreducible_inter U.1.1.isOpen V.1.1.isOpen
      (Set.nonempty_coe_sort.mp U.2) (Set.nonempty_coe_sort.mp V.2)
    let z : P := multiplicativeProductUnitSection f x
    have hz : π z = x :=
      congrArg (fun g : X ⟶ X => g x) (multiplicativeProductUnitSection_snd f)
    have hzU : z ∈ Ω U := by
      change π z ∈ U.1.1
      rw [hz]
      exact hxU
    have hzV : z ∈ Ω V := by
      change π z ∈ V.1.1
      rw [hz]
      exact hxV
    exact Set.disjoint_left.mp (TopologicalSpace.Opens.coe_disjoint.mpr hd) hzU hzV
  let : PreirreducibleSpace P := PreirreducibleSpace.of_isOpenCover hpair hcover (fun U => by
    let := hInt U
    change PreirreducibleSpace ((Ω U).toScheme)
    infer_instance)
  let : Nonempty P := ⟨multiplicativeProductUnitSection f (Classical.choice (inferInstance : Nonempty X))⟩
  let : IrreducibleSpace P := { toPreirreducibleSpace := inferInstance, toNonempty := inferInstance }
  exact isIntegral_of_irreducibleSpace_of_isReduced P

/-- Every original stalk of the SAME Laurent-group pullback is normal when
all original stalks of the integral base scheme are normal. -/
theorem nativeMultiplicativeGroup_pullback_stalk_isIntegrallyClosed [IsIntegral X]
    (f : X ⟶ Spec (CommRingCat.of R))
    (hN : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    (z : (pullback (nativeMultiplicativeGroup R).hom f : Scheme.{u})) :
    IsIntegrallyClosed ((pullback (nativeMultiplicativeGroup R).hom f).presheaf.stalk z) := by
  let P : Scheme.{u} := pullback (nativeMultiplicativeGroup R).hom f
  let π : P ⟶ X := pullback.snd (nativeMultiplicativeGroup R).hom f
  let : IsIntegral P := nativeMultiplicativeGroup_pullback_isIntegral f
  obtain ⟨U, hU, hz, _⟩ := exists_isAffineOpen_mem_and_subset
    (show π z ∈ (⊤ : X.Opens) from trivial)
  let : Nonempty U := ⟨⟨π z, hz⟩⟩
  let A : Type u := Γ(X, U)
  let : IsDomain A := inferInstance
  let : IsIntegrallyClosed A :=
    IntegralSchemeNormalization.affine_sections_isIntegrallyClosed X hN U hU
  let : IsDomain A[T;T⁻¹] := IsLocalization.isDomain_of_le_nonZeroDivisors
    A[T;T⁻¹] (powers_le_nonZeroDivisors_of_noZeroDivisors
      (Polynomial.X_ne_zero : (Polynomial.X : A[X]) ≠ 0))
  let : IsIntegrallyClosed A[T;T⁻¹] :=
    isIntegrallyClosed_of_isLocalization A[T;T⁻¹]
      (Submonoid.powers (Polynomial.X : A[X]))
      (powers_le_nonZeroDivisors_of_noZeroDivisors Polynomial.X_ne_zero)
  have hm : z ∈ (multiplicativeProductChartMap f ⟨U, hU⟩).opensRange := by
    rw [multiplicativeProductChartMap_opensRange]
    exact hz
  obtain ⟨q, hq⟩ := hm
  rw [← hq]
  let B : Type u := A[T;T⁻¹]
  let : IsIntegrallyClosed (Localization.AtPrime q.asIdeal) :=
    isIntegrallyClosed_of_isLocalization (Localization.AtPrime q.asIdeal)
      q.asIdeal.primeCompl q.asIdeal.primeCompl_le_nonZeroDivisors
  exact IsIntegrallyClosed.of_equiv
    ((Spec.stalkIso (CommRingCat.of B) q).commRingCatIsoToRingEquiv.symm.trans
      (asIso ((multiplicativeProductChartMap f ⟨U, hU⟩).stalkMap q)).commRingCatIsoToRingEquiv.symm)

end EnvelopeProperty.ProjBerk
