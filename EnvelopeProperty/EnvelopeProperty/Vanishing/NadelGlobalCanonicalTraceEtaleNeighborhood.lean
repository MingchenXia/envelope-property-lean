import EnvelopeProperty.Vanishing.NadelGlobalCanonicalTraceGenericBranchUnits
import EnvelopeProperty.AlgGeom.Canonical.GenericLineSections
import Mathlib.AlgebraicGeometry.Pullbacks

/-! # The SAME original whole cover is etale on an actual generic neighborhood

The original SNC geometry internally produces a ratio chart, its nonzero
full coefficient product, its actual principal localization and the genuine
factorization of the original generic field point. No etale chart or generic
comparison is supplied by the caller.
-/
noncomputable section
namespace EnvelopeProperty.Vanishing.NadelGlobalCanonicalTraceGenericBranch
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Scheme.Modules
open CanonicalGeometry NadelAuxiliaryMulticover NadelGlobalNormalization
open NadelAdaptedChartMatching NadelGlobalAdaptedModel NadelGlobalAdaptedRoots
open scoped TensorProduct
universe u
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem whole_chart_isPullback {X Y : Scheme.{u}} (π : Y ⟶ X)
    (U : X.affineOpens) (B : Type u) [CommRing B] [Algebra Γ(X, U.1) B]
    (e : Spec (.of B) ≅ (π ⁻¹ᵁ U.1).toScheme)
    (he : e.hom ≫ (π ⁻¹ᵁ U.1).ι ≫ π =
      Spec.map (CommRingCat.ofHom (algebraMap Γ(X, U.1) B)) ≫ U.2.fromSpec) :
    IsPullback (Spec.map (CommRingCat.ofHom (algebraMap Γ(X, U.1) B)))
      (e.hom ≫ (π ⁻¹ᵁ U.1).ι) U.2.fromSpec π := by
  have hsmall : e.hom ≫ (π ∣_ U.1) =
      Spec.map (CommRingCat.ofHom (algebraMap Γ(X, U.1) B)) ≫ U.2.isoSpec.inv := by
    apply (cancel_mono U.1.ι).mp
    simpa only [Category.assoc, morphismRestrict_ι, IsAffineOpen.fromSpec] using he
  have hs : IsPullback e.hom
      (Spec.map (CommRingCat.ofHom (algebraMap Γ(X, U.1) B)))
      (π ∣_ U.1) U.2.isoSpec.inv := IsPullback.of_horiz_isIso ⟨hsmall⟩
  simpa only [IsAffineOpen.fromSpec] using
    (hs.paste_horiz (isPullback_morphismRestrict π U.1).flip).flip

private theorem tensor_projection_etale
    (R B S : Type u) [CommRing R] [CommRing B] [CommRing S]
    [Algebra R B] [Algebra R S] [Algebra.Etale S (S ⊗[R] B)] :
    Etale (pullback.snd
      (Spec.map (CommRingCat.ofHom (algebraMap R B)))
      (Spec.map (CommRingCat.ofHom (algebraMap R S)))) := by
  let : Algebra S (B ⊗[R] S) := Algebra.TensorProduct.rightAlgebra
  let : Algebra.Etale S (B ⊗[R] S) :=
    Algebra.Etale.of_equiv (Algebra.TensorProduct.commRight R S B)
  let e := pullbackSpecIso R B S
  let q := pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap R B)))
    (Spec.map (CommRingCat.ofHom (algebraMap R S)))
  have h : Etale (e.inv ≫ q) := by
    rw [pullbackSpecIso_inv_snd]
    apply (HasRingHomProperty.Spec_iff (P := @Etale)).mpr
    exact RingHom.etale_algebraMap.mpr inferInstance
  let : Etale (e.inv ≫ q) := h
  have hc : Etale (e.hom ≫ (e.inv ≫ q)) := inferInstance
  simpa only [← Category.assoc, Iso.hom_inv_id, Category.id_comp] using hc

variable {X : Scheme.{u}} [IsIntegral X] (F : X.DivisorFamily) (n : ℕ)
    (L : F.ι → X.Modules) (m : F.ι → ℕ)
    (σ : ∀ i, Fin (n + 1) → (unitObj X ⟶
      tensorObj (bundleTensorPower (L i) (m i)) (F.component i).toModules))
    (hL : ∀ i, IsInvertible (L i)) (hD : ∀ i, (F.component i).IsInvertible)
    {k : Type u} [Field k] [PerfectField k]
    (f : X ⟶ Spec (.of k)) [SmoothOfRelativeDimension n f]
    (hG : (NadelBertiniAuxiliaryFamily.auxiliaryFamily F n
      (OriginalData.ideals F n L m σ hL hD)).IsSnc)
    (hRows : ∀ i, (⨆ j, OriginalData.ideals F n L m σ hL hD i j) = ⊤)
    (hm : ∀ i, 0 < m i) (hfield : ∀ i, IsUnit (m i : k))

local notation "π" => normalizedToOriginal (OriginalData.data F n L m σ)

include hL hD f hG hRows hm hfield

/-- Original geometric data internally produce an actual affine open
neighborhood of the original generic point on which the SAME WHOLE cover
is etale, together with the SAME actual generic-point factorization. -/
theorem exists_original_etale_neighborhood :
    ∃ (R : CommRingCat.{u}) (j : Spec R ⟶ X)
      (t : Spec X.functionField ⟶ Spec R),
      IsOpenImmersion j ∧ t ≫ j = X.fromSpecStalk (genericPoint X) ∧
        Etale (pullback.snd π j) := by
  let : Smooth f := SmoothOfRelativeDimension.smooth n f
  let : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace f
  obtain ⟨y, hy, _, _⟩ :=
    exists_isClosed_singleton_mem_specializes isClosed_univ (Set.mem_univ (genericPoint X))
  obtain ⟨j₀, habsent⟩ := Joined.exists_absent_copies F n
    (OriginalData.ideals F n L m σ hL hD) hRows y
  obtain ⟨U, v, hyU, het, e, c, hcinj, hcomp, _habsent, w, hw⟩ :=
    OriginalData.exists_framed_coefficients_at_closed F n L m σ hL hD f hG hy
  let : Nonempty U.1 := ⟨⟨y, hyU⟩⟩
  let A := Γ(X, U.1)
  let B := RatioRing F n L m σ hL hD y U v c j₀ w
  let a := coefficientProduct F n L m σ hL hD y U v c j₀ w
  let S := Localization.Away a
  let β : Spec (.of B) ⟶ Spec (.of A) := Spec.map (CommRingCat.ofHom (algebraMap A B))
  let s : Spec (.of S) ⟶ Spec (.of A) := Spec.map (CommRingCat.ofHom (algebraMap A S))
  let j : Spec (.of S) ⟶ X := s ≫ U.2.fromSpec
  let : IsOpenImmersion s := inferInstance
  let : IsOpenImmersion j := inferInstance
  let _ := f.sectionsAlgebra U.1
  have htame (i : F.ι) : IsUnit (m i : A) := by
    simpa only [map_natCast] using (hfield i).map (algebraMap k A)
  let E := Model.canonicalChart F n L m σ hL hD y U v c j₀ w
    f het hcinj hm htame hG hcomp hyU habsent e hw
  have hE := NadelBoundedCanonicalCharts.canonicalChart_over_original
    F n L m σ hL hD y U v c j₀ w f het hcinj hm htame hG hcomp hyU habsent e hw
  have hp := whole_chart_isPullback π U B E hE
  have hs := (IsPullback.of_hasPullback β s).paste_horiz hp.flip
  let i := hs.isoPullback
  have hi : i.hom ≫ pullback.snd π j = pullback.snd β s := hs.isoPullback_hom_snd
  let : Algebra.Etale S (S ⊗[A] B) :=
    localizedRatio_etale F n L m σ hL hD y U v c j₀ w f hm hfield
  let : Etale (pullback.snd β s) := tensor_projection_etale A B S
  have he : i.inv ≫ pullback.snd β s = pullback.snd π j := by
    rw [← hi, Iso.inv_hom_id_assoc]
  have hq : Etale (pullback.snd π j) := by
    rw [← he]
    infer_instance
  have ha : a ≠ 0 := coefficientProduct_ne_zero F n L m σ hL hD y U v c j₀ w f hG hcomp hyU
  have hga : IsUnit ((X.germToFunctionField U.1) a) := by
    apply isUnit_iff_ne_zero.mpr
    simpa only [map_zero] using (X.germToFunctionField_injective U.1).ne ha
  let φ : S →+* X.functionField :=
    IsLocalization.Away.lift a (g := (X.germToFunctionField U.1).hom) hga
  let t : Spec X.functionField ⟶ Spec (.of S) := Spec.map (CommRingCat.ofHom φ)
  have ht : t ≫ j = X.fromSpecStalk (genericPoint X) := by
    change Spec.map (CommRingCat.ofHom φ) ≫
      (Spec.map (CommRingCat.ofHom (algebraMap A S)) ≫ U.2.fromSpec) = _
    rw [← Category.assoc, ← Spec.map_comp]
    have hφ : CommRingCat.ofHom (algebraMap A S) ≫ CommRingCat.ofHom φ =
        X.germToFunctionField U.1 := by
      apply CommRingCat.hom_ext
      exact IsLocalization.Away.lift_comp a hga
    rw [hφ]
    exact U.2.fromSpecStalk_eq_fromSpecStalk (genericPoint_mem_nonempty_open U.1)
  exact ⟨.of S, j, t, inferInstance, ht, hq⟩

end EnvelopeProperty.Vanishing.NadelGlobalCanonicalTraceGenericBranch
