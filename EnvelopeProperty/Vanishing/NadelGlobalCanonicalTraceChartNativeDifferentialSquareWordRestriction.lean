import EnvelopeProperty.Vanishing.NadelGlobalCanonicalTraceChartNativeDifferentialSquareData

/-! # Restriction naturality before the native inverse word is assembled

Every map in the original inverse comparison is supplied separately.
The composed/nested functor conversion is checked with opaque functors;
no whole native word is passed as an already constructed morphism.
-/
noncomputable section
namespace EnvelopeProperty.Vanishing.NadelGlobalStructureTrace.WholeFreeChart.NativeDifferentialSquareData
open AlgebraicGeometry CategoryTheory Scheme.Modules CanonicalGeometry
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
local notation:10 A " ⟶ₙ " B =>
  @Quiver.Hom _ (@CategoryStruct.toQuiver _ (@Category.toCategoryStruct _ inferInstance)) A B

/-- Apply the restriction comparison to the original inverse square,
retaining every original source index of its individual maps. -/
theorem restriction_square_original_word_indices
    {C₀ C₁ C₂ E : Type*} [Category C₀] [Category C₁]
    [Category C₂] [Category E]
    (Fg : C₀ ⥤ C₁) (Fp : C₁ ⥤ E) (Fπ : C₀ ⥤ C₂) (Fv : C₂ ⥤ E)
    {R : C₂ ⥤ E} (e : R ≅ Fv) (M : C₀)
    {B : C₂} (d : Fπ.obj M ⟶ₙ B) {L₁ L₂ A T₀ T : E}
    (s : (Fπ ⋙ Fv).obj M ⟶ₙ L₁) (r : L₁ ⟶ₙ L₂)
    (z : L₂ ⟶ₙ (Fg ⋙ Fp).obj M) (a : Fp.obj (Fg.obj M) ⟶ₙ A)
    (P : A ⟶ₙ T) (V : Fv.obj B ⟶ₙ T₀) (H : T₀ ⟶ₙ T)
    (hraw : CategoryStruct.comp (X := Fv.obj (Fπ.obj M)) (Y := Fv.obj B) (Z := T)
        (Fv.map d) (CategoryStruct.comp (X := Fv.obj B) (Y := T₀) (Z := T) V H) =
      CategoryStruct.comp (X := (Fπ ⋙ Fv).obj M) (Y := A) (Z := T)
        (CategoryStruct.comp (X := (Fπ ⋙ Fv).obj M) (Y := L₁) (Z := A) s
          (CategoryStruct.comp (X := L₁) (Y := L₂) (Z := A) r
            (CategoryStruct.comp (X := L₂) (Y := (Fg ⋙ Fp).obj M) (Z := A) z a))) P) :
    R.map d ≫ ((e.app B).hom ≫ V ≫ H) =
      composeOriginalInverseWord Fπ Fv M ((e.app (Fπ.obj M)).hom)
        (CategoryStruct.comp (X := (Fπ ⋙ Fv).obj M) (Y := L₁) (Z := A) s
          (CategoryStruct.comp (X := L₁) (Y := L₂) (Z := A) r
            (CategoryStruct.comp (X := L₂) (Y := (Fg ⋙ Fp).obj M) (Z := A) z a))) ≫ P := by
  let word : (Fπ ⋙ Fv).obj M ⟶ₙ A :=
    CategoryStruct.comp (X := (Fπ ⋙ Fv).obj M) (Y := L₁) (Z := A) s
      (CategoryStruct.comp (X := L₁) (Y := L₂) (Z := A) r
        (CategoryStruct.comp (X := L₂) (Y := (Fg ⋙ Fp).obj M) (Z := A) z a))
  have hn := pushed_square_after_native_comparison_original_indices
    e Fπ M d word (V ≫ H) P hraw
  simpa only [composeOriginalInverseWord, word] using hn

end EnvelopeProperty.Vanishing.NadelGlobalStructureTrace.WholeFreeChart.NativeDifferentialSquareData
