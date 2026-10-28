import EnvelopeProperty.Vanishing.NadelBertiniSncFlatFibre
import EnvelopeProperty.Vanishing.NadelBertiniGenericOpen
import Mathlib.Algebra.Category.Ring.Constructions
import Mathlib.AlgebraicGeometry.Pullbacks

/-! # Actual affine quotient flatness on an original good-parameter neighbourhood

Only the original global parameter projection is assumed proper. Its actual
good open internally supplies smoothness and hence flatness of the actual
localized affine quotient. The original whole quotient need not be flat.
-/
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open scoped TensorProduct
universe u
namespace EnvelopeProperty.Vanishing.NadelBertiniSncFlatAffine
open NadelBertiniSncFlatBaseChange NadelBertiniSncFlatFibre
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem smooth_of_isPullback_factor_open {X Y P T : Scheme.{u}}
    (f : X ⟶ Y) (U : Y.Opens) [Smooth (f ∣_ U)]
    (q : P ⟶ T) (p : P ⟶ X) (v : T ⟶ U.toScheme)
    (H : IsPullback q p (v ≫ U.ι) f) : Smooth q :=
  MorphismProperty.of_isPullback (H.of_bot' (isPullback_morphismRestrict f U)).flip inferInstance

variable (A : Type u) [CommRing A] {B : Type u} [CommRing B] [Algebra A B]

/-- The SAME original affine principal quotient's actual parameter projection. -/
def quotientStructure (h : B) : Spec (.of (B ⧸ Ideal.span {h})) ⟶ Spec (.of A) :=
  Spec.map (CommRingCat.ofHom (algebraMap A (B ⧸ Ideal.span {h})))

/-- Smoothness of the SAME original affine quotient over an ACTUAL principal
parameter neighbourhood internally proves actual localized quotient flatness. -/
theorem localizedQuotient_flat_of_smooth_basicOpen (g : A) (h : B)
    [Smooth ((quotientStructure A h) ∣_ PrimeSpectrum.basicOpen g)] :
    Module.Flat (Localization.Away g) (localizedQuotient A g h) := by
  let Q := B ⧸ Ideal.span {h}
  let U : (Spec (.of A)).Opens := PrimeSpectrum.basicOpen g
  let e := basicOpenIsoSpecAway (R := CommRingCat.of A) g
  have he : e.inv ≫ U.ι = Spec.map
      (CommRingCat.ofHom (algebraMap A (Localization.Away g))) := by
    have hh : e.hom ≫ Spec.map
        (CommRingCat.ofHom (algebraMap A (Localization.Away g))) = U.ι :=
      basicOpenIsoSpecAway_hom_SpecMap (R := CommRingCat.of A) g
    exact (congrArg (fun m => e.inv ≫ m) hh.symm).trans (e.inv_hom_id_assoc _)
  have H := isPullback_SpecMap_of_isPushout _ _ _ _
    (CommRingCat.isPushout_tensorProduct A (Localization.Away g) Q)
  have H' : IsPullback
      (Spec.map (CommRingCat.ofHom (algebraMap (Localization.Away g) (localizedQuotient A g h))))
      (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight
        (R := A) (A := Localization.Away g) (B := Q)).toRingHom))
      (e.inv ≫ U.ι) (quotientStructure A h) := by
    rw [he]
    exact H
  let : Smooth (Spec.map (CommRingCat.ofHom
      (algebraMap (Localization.Away g) (localizedQuotient A g h)))) :=
    smooth_of_isPullback_factor_open (quotientStructure A h) U _ _ e.inv H'
  let ψ : CommRingCat.of (Localization.Away g) ⟶ CommRingCat.of (localizedQuotient A g h) :=
    CommRingCat.ofHom (algebraMap (Localization.Away g) (localizedQuotient A g h))
  have hflat : Flat (Spec.map ψ) := inferInstance
  exact RingHom.flat_algebraMap_iff.mp ((Flat.SpecMap_iff (f := ψ)).mp hflat)

/-- The ACTUAL affine chart of the ORIGINAL global incidence is flat after actual
localization inside the ORIGINAL proper-image good parameter open. -/
theorem localizedQuotient_flat_of_globalGoodOpen {Y : Scheme.{u}}
    (F : Y ⟶ Spec (.of A)) [LocallyOfFinitePresentation F] [IsProper F]
    (h : B) (ν : Spec (.of (B ⧸ Ideal.span {h})) ⟶ Y) [IsOpenImmersion ν]
    (hν : ν ≫ F = quotientStructure A h) (g : A)
    (hg : PrimeSpectrum.basicOpen g ≤ NadelBertiniGenericOpen.goodOpen F) :
    Module.Flat (Localization.Away g) (localizedQuotient A g h) := by
  have hfp : LocallyOfFinitePresentation (quotientStructure A h) :=
    hν ▸ (inferInstanceAs (LocallyOfFinitePresentation (ν ≫ F)))
  have hpre : (quotientStructure A h) ⁻¹ᵁ PrimeSpectrum.basicOpen g ≤
      (quotientStructure A h).smoothLocus := by
    intro x hx
    have hxF : F (ν x) ∈ NadelBertiniGenericOpen.goodOpen F := by
      have he := congrArg (fun f => f x) hν
      change F (ν x) = quotientStructure A h x at he
      rw [he]
      exact hg hx
    have hloc : ν x ∈ F.smoothLocus := NadelBertiniGenericOpen.goodOpen_preimage_le F hxF
    have he : ν ⁻¹ᵁ F.smoothLocus = (quotientStructure A h).smoothLocus := by
      simpa only [hν] using Scheme.Hom.preimage_smoothLocus_eq ν F
    rw [← he]
    exact hloc
  let : Smooth ((quotientStructure A h) ∣_ PrimeSpectrum.basicOpen g) :=
    NadelBertiniGenericOpen.smooth_morphismRestrict_of_preimage_le_smoothLocus _ _ hpre
  exact localizedQuotient_flat_of_smooth_basicOpen A g h

/-- An actual original field-valued point of an actual original open internally
chooses a principal neighbourhood with unit ORIGINAL scalar image. -/
theorem exists_unit_basicOpen_neighbourhood {K : Type u} [Field K]
    (φ : A →+* K) (V : (Spec (.of A)).Opens)
    (hφ : Spec.map (CommRingCat.ofHom φ) (⊥ : PrimeSpectrum K) ∈ V) :
    ∃ g : A, IsUnit (φ g) ∧ PrimeSpectrum.basicOpen g ≤ V := by
  obtain ⟨_, ⟨g, rfl⟩, hpoint, hsub⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open hφ V.isOpen
  refine ⟨g, ?_, hsub⟩
  apply isUnit_iff_ne_zero.mpr
  change φ g ∉ (⊥ : Ideal K) at hpoint
  simpa only [Ideal.mem_bot] using hpoint

/-- The ORIGINAL good parameter point internally supplies the needed localized
quotient flatness and proves regularity in the ORIGINAL scalar fibre. -/
theorem tensor_regular_of_globalGoodOpen {Y : Scheme.{u}} {K : Type u} [Field K]
    (F : Y ⟶ Spec (.of A)) [LocallyOfFinitePresentation F] [IsProper F]
    (h : B) (hh : IsSMulRegular B h)
    (ν : Spec (.of (B ⧸ Ideal.span {h})) ⟶ Y) [IsOpenImmersion ν]
    (hν : ν ≫ F = quotientStructure A h) (φ : A →+* K)
    (hφ : Spec.map (CommRingCat.ofHom φ) (⊥ : PrimeSpectrum K) ∈
      NadelBertiniGenericOpen.goodOpen F) :
    letI : Algebra A K := φ.toAlgebra
    IsSMulRegular (K ⊗[A] B) ((1 : K) ⊗ₜ[A] h) := by
  obtain ⟨g, hg, hsub⟩ := exists_unit_basicOpen_neighbourhood A φ _ hφ
  let : Module.Flat (Localization.Away g) (localizedQuotient A g h) :=
    localizedQuotient_flat_of_globalGoodOpen A F h ν hν g hsub
  exact tensor_regular_of_localized_flat A g h hh φ hg

end EnvelopeProperty.Vanishing.NadelBertiniSncFlatAffine
