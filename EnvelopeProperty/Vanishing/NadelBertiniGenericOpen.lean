import EnvelopeProperty.Vanishing.NadelBertiniGenericSmooth
import Mathlib.AlgebraicGeometry.Morphisms.Proper

/-! # The actual proper-image Bertini good parameter open

The final characteristic-zero producer proves its whole actual generic fibre
smooth from original regularity, then constructs the literal complement of the
proper image of the original nonsmooth locus. The intermediate stalk proofs
adapt the source proofs in `CurveFibrationMarkedOpenSmooth.lean` without
importing that unvendored module or any of its unrelated curve interfaces.
-/
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
universe u
namespace EnvelopeProperty.Vanishing.NadelBertiniGenericOpen
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {X S : Scheme.{u}}

/-- The original generic fibre's smoothness places EVERY original point over the
original generic point in the ORIGINAL relative smooth locus. -/
theorem genericFiber_le_smoothLocus [IsIntegral S]
    (f : X ⟶ S) [LocallyOfFinitePresentation f]
    [Smooth (f.fiberToSpecResidueField (genericPoint S))]
    (x : X) (hx : f x = genericPoint S) : x ∈ f.smoothLocus := by
  let e := S.fromSpecResidueField (genericPoint S)
  let i := f.fiberι (genericPoint S)
  let q := f.fiberToSpecResidueField (genericPoint S)
  let z := (f.fiberHomeo (genericPoint S)).symm ⟨x, hx⟩
  have hiz : i z = x := f.fiberι_fiberHomeo_symm _ _
  suffices i z ∈ f.smoothLocus by simpa only [hiz] using this
  rw [Scheme.Hom.mem_smoothLocus]
  let : Flat e := NadelBertiniGenericStalks.fromSpecResidueField_flat S
  let : Flat i := by change Flat (pullback.fst f e); infer_instance
  let : IsIso (i.stalkMap z) :=
    NadelBertiniGenericStalks.stalkMap_isIso_of_flat_preimmersion i z
  let : IsIso (e.stalkMap (q z)) :=
    NadelBertiniGenericStalks.stalkMap_isIso_of_flat_preimmersion e (q z)
  have hq : (q.stalkMap z).hom.FormallySmooth := by
    apply Scheme.Hom.mem_smoothLocus.mp
    rw [Scheme.Hom.smoothLocus_eq_top]
    trivial
  have H : ((i ≫ f).stalkMap z).hom.FormallySmooth := by
    have ht : i ≫ f = q ≫ e := pullback.condition
    rw [ht, Scheme.Hom.stalkMap_comp, CommRingCat.hom_comp]
    exact (RingHom.FormallySmooth.respectsIso.cancel_left_isIso
      (e.stalkMap (q z)) (q.stalkMap z)).mpr hq
  rw [Scheme.Hom.stalkMap_comp, CommRingCat.hom_comp] at H
  exact (RingHom.FormallySmooth.respectsIso.cancel_right_isIso
    (f.stalkMap (i z)) (i.stalkMap z)).mp H

/-- The actual source and target open restrictions retain the original smooth
stalk maps whenever the whole original preimage lies in the original locus. -/
theorem smooth_morphismRestrict_of_preimage_le_smoothLocus
    (f : X ⟶ S) [LocallyOfFinitePresentation f] (V : S.Opens)
    (hV : f ⁻¹ᵁ V ≤ f.smoothLocus) : Smooth (f ∣_ V) := by
  apply Scheme.Hom.smoothLocus_eq_top_iff.mp
  apply top_unique
  intro z _
  rw [Scheme.Hom.mem_smoothLocus]
  let i := (f ⁻¹ᵁ V).ι
  have hf : (f.stalkMap (i z)).hom.FormallySmooth :=
    Scheme.Hom.mem_smoothLocus.mp (hV z.property)
  have H : ((i ≫ f).stalkMap z).hom.FormallySmooth := by
    rw [Scheme.Hom.stalkMap_comp, CommRingCat.hom_comp]
    exact (RingHom.FormallySmooth.respectsIso.cancel_right_isIso
      (f.stalkMap (i z)) (i.stalkMap z)).mpr hf
  change (((f ⁻¹ᵁ V).ι ≫ f).stalkMap z).hom.FormallySmooth at H
  rw [← morphismRestrict_ι, Scheme.Hom.stalkMap_comp, CommRingCat.hom_comp] at H
  exact (RingHom.FormallySmooth.respectsIso.cancel_left_isIso
    (V.ι.stalkMap ((f ∣_ V) z)) ((f ∣_ V).stalkMap z)).mp H

/-- The actual complement of the proper image of the ORIGINAL nonsmooth locus. -/
def goodOpen (f : X ⟶ S) [LocallyOfFinitePresentation f] [IsProper f] : S.Opens :=
  ⟨(f '' (f.smoothLocus : Set X)ᶜ)ᶜ,
    (f.isClosedMap _ f.smoothLocus.isOpen.isClosed_compl).isOpen_compl⟩

/-- Every original point over the actual good open belongs to the original locus. -/
theorem goodOpen_preimage_le (f : X ⟶ S)
    [LocallyOfFinitePresentation f] [IsProper f] :
    f ⁻¹ᵁ goodOpen f ≤ f.smoothLocus := by
  intro x hx
  by_contra hbad
  exact hx ⟨x, hbad, rfl⟩

/-- The original morphism restricted to its actual proper-image good open is smooth. -/
theorem goodOpen_smooth (f : X ⟶ S)
    [LocallyOfFinitePresentation f] [IsProper f] : Smooth (f ∣_ goodOpen f) :=
  smooth_morphismRestrict_of_preimage_le_smoothLocus f _ (goodOpen_preimage_le f)

/-- Original regularity and the actual characteristic-zero base field prove that
the actual generic point belongs to the actual proper-image good open. -/
theorem genericPoint_mem_goodOpen {k : Type u} [Field k] [CharZero k]
    [IsIntegral S] [IsRegular X] (p : S ⟶ Spec (.of k)) (f : X ⟶ S)
    [LocallyOfFinitePresentation f] [IsProper f] : genericPoint S ∈ goodOpen f := by
  let := NadelBertiniGenericSmooth.genericFiber_smooth p f
  rintro ⟨x, hxB, hxη⟩
  exact hxB (genericFiber_le_smoothLocus f x hxη)

/-- Actual good parameters are produced from original regularity; whole generic
smoothness, target open, nonemptiness and density are all proved internally. -/
theorem goodOpen_specification {k : Type u} [Field k] [CharZero k]
    [IsIntegral S] [IsRegular X] (p : S ⟶ Spec (.of k)) (f : X ⟶ S)
    [LocallyOfFinitePresentation f] [IsProper f] :
    genericPoint S ∈ goodOpen f ∧ Nonempty (goodOpen f) ∧
      Dense (goodOpen f : Set S) ∧ f ⁻¹ᵁ goodOpen f ≤ f.smoothLocus ∧
      Smooth (f ∣_ goodOpen f) := by
  have hη := genericPoint_mem_goodOpen p f
  exact ⟨hη, ⟨⟨genericPoint S, hη⟩⟩,
    (goodOpen f).isOpen.dense ⟨genericPoint S, hη⟩,
    goodOpen_preimage_le f, goodOpen_smooth f⟩

/-- Smoothness of the ORIGINAL total scheme over the original characteristic-zero
field gives a nonempty dense good open for the actual proper parameter map. -/
theorem goodOpen_specification_of_smooth {k : Type u} [Field k] [CharZero k]
    [IsIntegral S] (p : S ⟶ Spec (.of k)) (f : X ⟶ S)
    [LocallyOfFinitePresentation f] [IsProper f]
    (pX : X ⟶ Spec (.of k)) [Smooth pX] :
    genericPoint S ∈ goodOpen f ∧ Nonempty (goodOpen f) ∧
      Dense (goodOpen f : Set S) ∧ f ⁻¹ᵁ goodOpen f ≤ f.smoothLocus ∧
      Smooth (f ∣_ goodOpen f) := by
  let : IsRegular X := (Scheme.smooth_iff_isRegular pX).mp inferInstance
  exact goodOpen_specification p f

end EnvelopeProperty.Vanishing.NadelBertiniGenericOpen
