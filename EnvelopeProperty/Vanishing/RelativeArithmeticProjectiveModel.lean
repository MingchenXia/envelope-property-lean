import EnvelopeProperty.Vanishing.ArithmeticOriginalSmoothDimension

/-! # The original closed embedding and dimension-preserving arithmetic descent

The ambient finite-presentation model is retained.  Closed immersion descent
constructs the original source model, and original standard-smooth charts
produce its total relative dimension on a later genuine scalar extension.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
universe u

namespace EnvelopeProperty.Vanishing.RelativeArithmeticProjectiveModel
open Alterations.StableModification.Limits

/-- The original smooth closed subscheme has a produced smooth model inside
the same prescribed ambient coefficient family, with the entire original
closed immersion recovered.  No properness over the coefficient base occurs. -/
theorem exists_smooth_closed_model
    {A k : Type u} [CommRing A] [CommRing k] [Algebra A k]
    {R : Subalgebra A k} {P X : Scheme.{u}}
    (fP : P ⟶ (fgSpecCone R).pt) (f : X ⟶ (fgSpecCone R).pt)
    [QuasiCompact f] [QuasiSeparated f] (n : ℕ) [SmoothOfRelativeDimension n f]
    {i : (FGSubalgebra A R)ᵒᵖ}
    (r : Model ((fgDiagram R).op ⋙ Scheme.Spec) (fgSpecCone R) fP i)
    (hr : r.IsFP) (j : X ⟶ P) [IsClosedImmersion j] (hj : j ≫ fP = f) :
    ∃ (l : (FGSubalgebra A R)ᵒᵖ) (h : l ⟶ i)
      (m : Model ((fgDiagram R).op ⋙ Scheme.Spec) (fgSpecCone R) f l)
      (ι : m.Y ⟶ (r.baseChange h).Y),
      m.IsFP ∧ SmoothOfRelativeDimension n m.fY ∧ IsClosedImmersion ι ∧
        ι ≫ (r.baseChange h).fY = m.fY ∧ m.g ≫ ι = j ≫ (r.baseChange h).g := by
  let : Smooth f := SmoothOfRelativeDimension.smooth n f
  obtain ⟨l, h, m, ι, hm, hι, hιbase, hιoriginal⟩ :=
    exists_closedImmersion_model (D := (fgDiagram R).op ⋙ Scheme.Spec)
      (c := fgSpecCone R) (isLimitFGSpecCone R) r hr f j hj
  obtain ⟨v, b, hn⟩ :=
    ArithmeticOriginalSmooth.exists_relativeDimension_fixed_model_baseChange f n m hm
  let V : Over l := Over.mk b
  let J : (m.baseChange b).Y ⟶ ((r.baseChange h).baseChange b).Y :=
    topBaseChange m (r.baseChange h) ι hιbase V
  let E := r.baseChangeCompIso h b
  let : IsClosedImmersion ι := hι
  let : IsClosedImmersion J :=
    MorphismProperty.of_isPullback
      (isPullback_topBaseChange m (r.baseChange h) ι hιbase V) inferInstance
  have hJbase : J ≫ ((r.baseChange h).baseChange b).fY =
      (m.baseChange b).fY := topBaseChange_snd m (r.baseChange h) ι hιbase V
  have hJoriginal : (m.baseChange b).g ≫ J =
      j ≫ ((r.baseChange h).baseChange b).g :=
    π_topBaseChange m (r.baseChange h) ι hιbase j hιoriginal hj V
  have hbase : (J ≫ E.hom) ≫ (r.baseChange (b ≫ h)).fY =
      (m.baseChange b).fY := by
    rw [Category.assoc, Model.baseChangeCompIso_hom_fY]
    exact hJbase
  have horiginal : (m.baseChange b).g ≫ (J ≫ E.hom) =
      j ≫ (r.baseChange (b ≫ h)).g := by
    rw [← Category.assoc, hJoriginal,
      Category.assoc, Model.g_baseChangeCompIso_hom]
  exact ⟨v, b ≫ h, m.baseChange b, J ≫ E.hom,
    hm.baseChange b, hn, inferInstance, hbase, horiginal⟩

end EnvelopeProperty.Vanishing.RelativeArithmeticProjectiveModel
