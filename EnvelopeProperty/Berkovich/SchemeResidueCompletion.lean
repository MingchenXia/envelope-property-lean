/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Berkovich.SchemeCenterAffine
import EnvelopeProperty.Berkovich.SchemeRelativeAtlas
import EnvelopeProperty.Berkovich.ValuationCompletion

/-! # Genuine completed stalk residue fields and whole native field points -/
open scoped NNReal Topology
open CategoryTheory AlgebraicGeometry
noncomputable section
universe u
namespace EnvelopeProperty.Berkovich.SchemeValuedPoint
variable {X : Scheme.{u}}

/-- The absolute value of the ORIGINAL actual stalk residue valuation. -/
def residueAbs (x : SchemeValuedPoint X) : AbsoluteValue (X.residueField x.point) ℝ :=
  EnvelopeProperty.Valuation.toRealAbs x.residueVal

/-- The genuine completion of the ORIGINAL actual stalk residue field. -/
def H (x : SchemeValuedPoint X) : Type u := x.residueAbs.Completion

instance instNormedFieldH (x : SchemeValuedPoint X) : NormedField (H x) :=
  inferInstanceAs (NormedField (UniformSpace.Completion (WithAbs x.residueAbs)))

instance instCompleteSpaceH (x : SchemeValuedPoint X) : CompleteSpace (H x) :=
  inferInstanceAs (CompleteSpace (UniformSpace.Completion (WithAbs x.residueAbs)))

instance instUltrametricWithAbsResidue (x : SchemeValuedPoint X) :
    IsUltrametricDist (WithAbs x.residueAbs) :=
  IsUltrametricDist.isUltrametricDist_of_forall_norm_add_le_max_norm fun a b =>
    EnvelopeProperty.Valuation.isNonarchimedean_toRealAbs x.residueVal a.ofAbs b.ofAbs

instance instUltrametricH (x : SchemeValuedPoint X) : IsUltrametricDist (H x) :=
  inferInstanceAs (IsUltrametricDist (UniformSpace.Completion (WithAbs x.residueAbs)))

/-- The actual ORIGINAL stalk residue field embeds into its true completion. -/
def residueToH (x : SchemeValuedPoint X) : X.residueField x.point →+* H x :=
  UniformSpace.Completion.coeRingHom.comp (WithAbs.equiv x.residueAbs).symm.toRingHom

/-- Every ORIGINAL residue element retains its actual valuation as its completion norm. -/
theorem norm_residueToH (x : SchemeValuedPoint X) (z : X.residueField x.point) :
    ‖x.residueToH z‖ = x.residueVal z := by
  change ‖((WithAbs.toAbs x.residueAbs z : WithAbs x.residueAbs) :
    UniformSpace.Completion (WithAbs x.residueAbs))‖ = _
  rw [UniformSpace.Completion.norm_coe]
  rfl

/-- The ORIGINAL residue embedding genuinely has dense image. -/
theorem denseRange_residueToH (x : SchemeValuedPoint X) : DenseRange x.residueToH := by
  have he : Set.range (((↑) : WithAbs x.residueAbs → UniformSpace.Completion
      (WithAbs x.residueAbs)) ∘ (WithAbs.equiv x.residueAbs).symm) =
      Set.range ((↑) : WithAbs x.residueAbs → UniformSpace.Completion (WithAbs x.residueAbs)) :=
    (WithAbs.equiv x.residueAbs).symm.surjective.range_comp _
  change Dense (Set.range (((↑) : WithAbs x.residueAbs → UniformSpace.Completion
      (WithAbs x.residueAbs)) ∘ (WithAbs.equiv x.residueAbs).symm))
  rw [he]
  exact UniformSpace.Completion.denseRange_coe

/-- EVERY original section maps through its actual evaluation in the SAME completed residue field. -/
def sectionToH (x : SchemeValuedPoint X) (U : X.Opens) (hx : x.point ∈ U) :
    Γ(X, U) →+* H x := x.residueToH.comp (X.evaluation U x.point hx).hom

/-- The completion retains EVERY original section evaluation, with no boundedness hypothesis. -/
theorem nnnorm_sectionToH (x : SchemeValuedPoint X) (U : X.Opens) (hx : x.point ∈ U)
    (s : Γ(X, U)) : ‖sectionToH x U hx s‖₊ = eval x U hx s :=
  NNReal.eq (norm_residueToH x (X.evaluation U x.point hx s))

/-- The genuine ORIGINAL completed residue-field valued scheme point. -/
def fieldPoint (x : SchemeValuedPoint X) : Spec (CommRingCat.of (H x)) ⟶ X :=
  Spec.map (CommRingCat.ofHom x.residueToH) ≫ X.fromSpecResidueField x.point

/-- Every actual affine neighborhood factors the WHOLE original field point by its genuine section map. -/
theorem fieldPoint_eq_affine (x : SchemeValuedPoint X) {U : X.Opens}
    (hU : IsAffineOpen U) (hx : x.point ∈ U) :
    fieldPoint x = Spec.map (CommRingCat.ofHom (sectionToH x U hx)) ≫ hU.fromSpec := by
  rw [fieldPoint, ← fromSpecResidueField_eq_affine hU x.point hx, ← Category.assoc,
    ← Spec.map_comp]
  rfl

/-- The canonical norm point recovers the ENTIRE ORIGINAL native point through its actual completed field. -/
theorem map_norm_basePoint_fieldPoint (x : SchemeValuedPoint X) :
    map (fieldPoint x) (basePoint (NormedField.valuation (K := H x))) = x := by
  obtain ⟨U, hU, hx, _⟩ := exists_isAffineOpen_mem_and_subset
    (show x.point ∈ (⊤ : X.Opens) from trivial)
  let a := affineOpenSpectrumHomeomorph hU ⟨x, hx⟩
  have hfield : map (Spec.map (CommRingCat.ofHom (sectionToH x U hx)))
      (basePoint (NormedField.valuation (K := H x))) = spectrumHomeomorph.symm a := by
    apply spectrumHomeomorph.injective
    rw [spectrumHomeomorph_map, basePoint, Homeomorph.apply_symm_apply,
      Homeomorph.apply_symm_apply]
    apply Spectrum.ext_val
    intro s
    change ‖sectionToH x U hx s‖₊ = a.val s
    rw [nnnorm_sectionToH]
    exact (affineOpenSpectrumHomeomorph_val_apply hU ⟨x, hx⟩ s).symm
  rw [fieldPoint_eq_affine x hU hx, map_comp, hfield]
  have he := congrArg Subtype.val ((affineOpenSpectrumHomeomorph hU).symm_apply_apply ⟨x, hx⟩)
  rw [affineOpenSpectrumHomeomorph_symm_coe] at he
  change map U.ι (map hU.isoSpec.inv (spectrumHomeomorph.symm a)) = x at he
  simpa only [IsAffineOpen.fromSpec, map_comp] using he

end EnvelopeProperty.Berkovich.SchemeValuedPoint
