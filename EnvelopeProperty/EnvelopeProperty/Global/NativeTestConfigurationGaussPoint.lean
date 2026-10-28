import EnvelopeProperty.Berkovich.SchemePointLaurentGauss
import EnvelopeProperty.Global.NativeTestConfigurationLineTrivialization

/-! # The actual original Gauss product point on a literal test configuration -/
open scoped Polynomial LaurentPolynomial NNReal
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory
noncomputable section
universe u
namespace EnvelopeProperty.NativeTestConfiguration.TestConfiguration
open Berkovich
variable {k : Type u} [Field k] {X : Over (Spec (.of k))}
    (C : TestConfiguration k X) {v : Valuation k ℝ≥0}
    (x : RelativeSchemeValuedPoint v X.hom)

/-- The original noncentral-open point is constructed from the ACTUAL
completed-field product Gauss point and the source-derived whole open iso. -/
def unitGaussPoint (r : ℝ≥0) (hr : 0 < r) : SchemeValuedPoint C.unitOpen.toScheme :=
  SchemeValuedPoint.map C.unitOpenIso.inv.left
    (SchemePointLaurentGauss.productPoint X.hom x r hr).1

/-- The actual original total-space point is obtained through the SAME original inclusion. -/
def totalGaussPoint (r : ℝ≥0) (hr : 0 < r) : SchemeValuedPoint C.total :=
  SchemeValuedPoint.map C.unitOpenInclusion.left (C.unitGaussPoint x r hr)

/-- The WHOLE original X point is recovered, not only its scheme support. -/
theorem unitGaussPoint_originalProjection (r : ℝ≥0) (hr : 0 < r) :
    SchemeValuedPoint.map C.unitOpenOriginalProjection.left (C.unitGaussPoint x r hr) = x.1 := by
  have he : C.unitOpenIso.inv ≫ C.unitOpenOriginalProjection =
      fst X (ProjBerk.nativeMultiplicativeGroup k) := by
    rw [unitOpenOriginalProjection, Iso.inv_hom_id_assoc]
  have he' := congrArg Over.Hom.left he
  change C.unitOpenIso.inv.left ≫ C.unitOpenOriginalProjection.left =
    (fst X (ProjBerk.nativeMultiplicativeGroup k)).left at he'
  let g : (X ⊗ ProjBerk.nativeMultiplicativeGroup k).left ⟶ C.unitOpen.toScheme :=
    C.unitOpenIso.inv.left
  let q : C.unitOpen.toScheme ⟶ X.left := C.unitOpenOriginalProjection.left
  let p : SchemeValuedPoint (X ⊗ ProjBerk.nativeMultiplicativeGroup k).left :=
    (SchemePointLaurentGauss.productPoint X.hom x r hr).1
  change SchemeValuedPoint.map q (SchemeValuedPoint.map g p) = x.1
  change g ≫ q = (fst X (ProjBerk.nativeMultiplicativeGroup k)).left at he'
  rw [← SchemeValuedPoint.map_comp, he']
  exact SchemePointLaurentGauss.productPoint_fst X.hom x r hr

private theorem unitOpenIso_inv_structure :
    C.unitOpenIso.inv ≫ C.unitOpenInclusion ≫ structureOver k C.projection =
      snd X (ProjBerk.nativeMultiplicativeGroup k) ≫ ProjBerk.nativeParameterGroupInclusion k := by
  have he := congrArg (fun a => C.unitOpenIso.inv ≫ a) C.unitOpenIso_structure
  simpa only [Category.assoc, Iso.inv_hom_id_assoc] using he.symm

/-- The entire original polynomial-base valued point is the ACTUAL original Gauss point. -/
theorem totalGaussPoint_projection (r : ℝ≥0) (hr : 0 < r) :
    SchemeValuedPoint.map C.projection (C.totalGaussPoint x r hr) =
      SchemeValuedPoint.spectrumHomeomorph.symm (Berkovich.Spectrum.gauss
        (Berkovich.Spectrum.ofValuation v) r) := by
  have he := congrArg Over.Hom.left C.unitOpenIso_inv_structure
  change C.unitOpenIso.inv.left ≫ C.unitOpenInclusion.left ≫ C.projection =
    (snd X (ProjBerk.nativeMultiplicativeGroup k)).left ≫
      (ProjBerk.nativeParameterGroupInclusion k).left at he
  let g : (X ⊗ ProjBerk.nativeMultiplicativeGroup k).left ⟶ C.unitOpen.toScheme :=
    C.unitOpenIso.inv.left
  let i : C.unitOpen.toScheme ⟶ C.total := C.unitOpenInclusion.left
  let σ : (X ⊗ ProjBerk.nativeMultiplicativeGroup k).left ⟶ Spec (.of k[T;T⁻¹]) :=
    (snd X (ProjBerk.nativeMultiplicativeGroup k)).left
  let τ : Spec (.of k[T;T⁻¹]) ⟶ Spec (.of k[X]) :=
    Spec.map (CommRingCat.ofHom (Polynomial.toLaurent : k[X] →+* k[T;T⁻¹]))
  let p : SchemeValuedPoint (X ⊗ ProjBerk.nativeMultiplicativeGroup k).left :=
    (SchemePointLaurentGauss.productPoint X.hom x r hr).1
  rw [ProjBerk.nativeParameterGroupInclusion_left] at he
  change g ≫ i ≫ C.projection = σ ≫ τ at he
  change SchemeValuedPoint.map C.projection (SchemeValuedPoint.map i (SchemeValuedPoint.map g p)) = _
  rw [← SchemeValuedPoint.map_comp, ← SchemeValuedPoint.map_comp, he,
    SchemeValuedPoint.map_comp]
  have hp : SchemeValuedPoint.map σ p =
      SchemeValuedPoint.spectrumHomeomorph.symm (Berkovich.Spectrum.laurentGauss v r hr) :=
    SchemePointLaurentGauss.productPoint_snd X.hom x r hr
  rw [hp]
  dsimp only [τ]
  apply SchemeValuedPoint.spectrumHomeomorph.injective
  rw [SchemeValuedPoint.spectrumHomeomorph_map]
  simp only [Homeomorph.apply_symm_apply]
  apply Berkovich.Spectrum.ext_val
  intro p
  exact Berkovich.Spectrum.laurentGauss_val_toLaurent v r hr p

/-- The constructed total-space Gauss point prescribes the ENTIRE original
polynomial Gauss valuation, with no supplied point or matching certificate. -/
def relativeGaussPoint (r : ℝ≥0) (hr : 0 < r) :
    RelativeSchemeValuedPoint (Berkovich.Spectrum.gauss
      (Berkovich.Spectrum.ofValuation v) r).val C.projection :=
  ⟨C.totalGaussPoint x r hr, by
    change SchemeValuedPoint.map C.projection (C.totalGaussPoint x r hr) = _
    rw [totalGaussPoint_projection]
    apply SchemeValuedPoint.spectrumHomeomorph.injective
    simp only [Homeomorph.apply_symm_apply, SchemeValuedPoint.basePoint]
    apply Berkovich.Spectrum.ext_val
    intro p
    rw [Berkovich.Spectrum.ofValuation_val]⟩

end EnvelopeProperty.NativeTestConfiguration.TestConfiguration
