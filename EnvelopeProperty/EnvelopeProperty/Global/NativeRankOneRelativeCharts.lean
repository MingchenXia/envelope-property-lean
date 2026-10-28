import EnvelopeProperty.Global.NativeRankOneAnalyticCharts

/-! # Whole native rank-one original charts over the SAME original coefficient field -/
open scoped Classical NNReal Topology
open Topology MvPolynomial AlgebraicGeometry CategoryTheory Opposite
open EnvelopeProperty.Berkovich
noncomputable section
universe u
namespace EnvelopeProperty.MultiModel
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {k K : Type u} [Field k] [Field K] [Algebra k K]
  (X : MultiModel k K 1)

private theorem homogeneousSectionsMap_eq {A : Type u} [CommRing A]
    {σ : Type*} [SetLike σ A] [AddSubgroupClass σ A]
    (𝒜 : ℕ → σ) [GradedRing 𝒜] (f : A) {m : ℕ} (hf : f ∈ 𝒜 m) (hm : 0 < m) :
    (Proj.basicOpenIsoAway 𝒜 f hf hm).hom =
      (Scheme.ΓSpecIso (CommRingCat.of (HomogeneousLocalization.Away 𝒜 f))).inv ≫
        (Proj.basicOpenIsoSpec 𝒜 f hf hm).hom.appTop ≫ (Proj.basicOpen 𝒜 f).topIso.hom := by
  rw [Proj.basicOpenIsoSpec_hom]
  simp only [Scheme.Hom.appTop]
  rw [Proj.basicOpenToSpec_app_top]
  simp only [Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id]
  rfl

/-- The actual homogeneous section isomorphism is the SAME actual native chart pullback. -/
theorem nativeRankOneHomogeneousSectionsIso_eq (i : Fin (X.M 0 + 1)) :
    (X.nativeRankOneHomogeneousSectionsIso i).hom =
      (Scheme.ΓSpecIso (CommRingCat.of (X.nativeRankOneChartRing i))).inv ≫
        (X.nativeRankOneHomogeneousChartIso i).hom.appTop ≫
          (X.nativeRankOneCoordinateOpen i).topIso.hom := by
  exact homogeneousSectionsMap_eq X.nativeTotalGrading (X.coordElem ⟨0, i⟩)
    (X.nativeRankOneCoordinate_mem i) (by decide : 0 < (1 : ℕ))

/-- The SAME original chart section-ring isomorphism is the actual whole scheme-chart pullback. -/
theorem nativeRankOneOriginalSectionsIso_eq (j : X.ChartIndex)
    (hj : ∀ c, X.coord c (j c) ≠ 0) :
    X.nativeRankOneOriginalSectionsIso j hj =
      (Scheme.ΓSpecIso (CommRingCat.of (X.chartAlg j))).symm.trans
        ((Scheme.Γ.mapIso (X.nativeRankOneOriginalChartIso j hj).op).trans
          (X.nativeRankOneCoordinateOpen (j 0)).topIso) := by
  apply Iso.ext
  change _ = (Scheme.ΓSpecIso (CommRingCat.of (X.chartAlg j))).inv ≫
    (Spec.map (CommRingCat.ofHom (X.nativeRankOneChartEquiv j hj).symm.toRingHom)).appTop ≫
      (X.nativeRankOneHomogeneousChartIso (j 0)).hom.appTop ≫
        (X.nativeRankOneCoordinateOpen (j 0)).topIso.hom
  erw [← Category.assoc, ← Scheme.ΓSpecIso_inv_naturality]
  rw [Category.assoc, ← X.nativeRankOneHomogeneousSectionsIso_eq]
  rfl

/-- The actual inverse original chart pullback cancels with the SAME original local section isomorphism. -/
theorem nativeRankOneOriginalSectionsIso_cancel (j : X.ChartIndex)
    (hj : ∀ c, X.coord c (j c) ≠ 0) :
    (X.nativeRankOneOriginalSectionsIso j hj).hom ≫
      (X.nativeRankOneCoordinateOpen (j 0)).topIso.inv ≫
        (X.nativeRankOneOriginalChartIso j hj).inv.appTop =
      (Scheme.ΓSpecIso (CommRingCat.of (X.chartAlg j))).inv := by
  rw [X.nativeRankOneOriginalSectionsIso_eq]
  change ((Scheme.ΓSpecIso (CommRingCat.of (X.chartAlg j))).inv ≫
    (Scheme.Γ.mapIso (X.nativeRankOneOriginalChartIso j hj).op).hom ≫
      (X.nativeRankOneCoordinateOpen (j 0)).topIso.hom) ≫
        (X.nativeRankOneCoordinateOpen (j 0)).topIso.inv ≫
          (Scheme.Γ.mapIso (X.nativeRankOneOriginalChartIso j hj).op).inv = _
  simp only [Category.assoc, Iso.hom_inv_id_assoc, Iso.hom_inv_id, Category.comp_id]

/-- The actual original-chart scheme inclusion into the SAME actual native scheme. -/
def nativeRankOneChartInclusion (j : X.ChartIndex) (hj : ∀ c, X.coord c (j c) ≠ 0) :
    Spec (.of (X.chartAlg j)) ⟶ X.nativeRankOneScheme :=
  (X.nativeRankOneOriginalChartIso j hj).inv ≫ (X.nativeRankOneCoordinateOpen (j 0)).ι

/-- The actual original-chart inclusion is genuinely an open immersion. -/
instance nativeRankOneChartInclusion_isOpenImmersion (j : X.ChartIndex)
    (hj : ∀ c, X.coord c (j c) ≠ 0) : IsOpenImmersion (X.nativeRankOneChartInclusion j hj) := by
  unfold nativeRankOneChartInclusion
  infer_instance

/-- The image of the actual original chart is precisely the SAME original coordinate open. -/
theorem nativeRankOneChartInclusion_opensRange (j : X.ChartIndex)
    (hj : ∀ c, X.coord c (j c) ≠ 0) :
    (X.nativeRankOneChartInclusion j hj).opensRange = X.nativeRankOneCoordinateOpen (j 0) :=
  (Scheme.Hom.opensRange_comp_of_isIso _ _).trans (X.nativeRankOneCoordinateOpen (j 0)).opensRange_ι

/-- The actual original chart inclusion preserves the SAME original coefficient structure map. -/
theorem nativeRankOneChartInclusion_structure (j : X.ChartIndex)
    (hj : ∀ c, X.coord c (j c) ≠ 0) :
    X.nativeRankOneChartInclusion j hj ≫ X.nativeRankOneStructure =
      Spec.map (CommRingCat.ofHom (algebraMap k (X.chartAlg j))) := by
  simpa only [nativeRankOneChartInclusion, Category.assoc] using
    X.nativeRankOneOriginalChartIso_structure j hj

/-- The actual entire native original chart over the SAME base point is the original relative affine spectrum. -/
def nativeRankOneRelativeChartHomeomorph (j : X.ChartIndex)
    (hj : ∀ c, X.coord c (j c) ≠ 0) :
    {y : RelativeSchemeValuedPoint (1 : Valuation k ℝ≥0) X.nativeRankOneStructure //
      y.1.point ∈ X.nativeRankOneCoordinateOpen (j 0)} ≃ₜ
        RelativeSpectrum (1 : Valuation k ℝ≥0) (X.chartAlg j) :=
  ((RelativeSchemeValuedPoint.affineSpectrumHomeomorph).symm.trans
    ((RelativeSchemeValuedPoint.openImmersionHomeomorph (X.nativeRankOneChartInclusion j hj)
      (X.nativeRankOneChartInclusion_structure j hj)).trans
        (Homeomorph.setCongr (by rw [X.nativeRankOneChartInclusion_opensRange])))).symm

/-- The whole inverse native chart point is the original affine point through the actual scheme inclusion. -/
theorem nativeRankOneRelativeChartHomeomorph_symm_coe (j : X.ChartIndex)
    (hj : ∀ c, X.coord c (j c) ≠ 0)
    (x : RelativeSpectrum (1 : Valuation k ℝ≥0) (X.chartAlg j)) :
    ((X.nativeRankOneRelativeChartHomeomorph j hj).symm x).1.1 =
      SchemeValuedPoint.map (X.nativeRankOneChartInclusion j hj)
        (SchemeValuedPoint.spectrumHomeomorph.symm x.1) := rfl

/-- EVERY original chart element retains its SAME actual native local section value under the inverse chart. -/
theorem nativeRankOneRelativeChartHomeomorph_symm_val (j : X.ChartIndex)
    (hj : ∀ c, X.coord c (j c) ≠ 0)
    (x : RelativeSpectrum (1 : Valuation k ℝ≥0) (X.chartAlg j)) (a : X.chartAlg j) :
    x.1.val a = SchemeValuedPoint.eval
      ((X.nativeRankOneRelativeChartHomeomorph j hj).symm x).1.1
      (X.nativeRankOneCoordinateOpen (j 0))
      ((X.nativeRankOneRelativeChartHomeomorph j hj).symm x).2
      ((X.nativeRankOneOriginalSectionsIso j hj).hom a) := by
  simp only [X.nativeRankOneRelativeChartHomeomorph_symm_coe, nativeRankOneChartInclusion,
    SchemeValuedPoint.map_comp, SchemeValuedPoint.eval_map_ι_topIso,
    SchemeValuedPoint.evalTop_map]
  have hs := congrArg (fun f => f a) (X.nativeRankOneOriginalSectionsIso_cancel j hj)
  change (X.nativeRankOneOriginalChartIso j hj).inv.appTop
    ((X.nativeRankOneCoordinateOpen (j 0)).topIso.inv
      ((X.nativeRankOneOriginalSectionsIso j hj).hom a)) =
        (Scheme.ΓSpecIso (CommRingCat.of (X.chartAlg j))).inv a at hs
  erw [hs]
  have h := SchemeValuedPoint.spectrumHomeomorph_val_apply
    (SchemeValuedPoint.spectrumHomeomorph.symm x.1) a
  rw [Homeomorph.apply_symm_apply] at h
  exact h

end EnvelopeProperty.MultiModel
