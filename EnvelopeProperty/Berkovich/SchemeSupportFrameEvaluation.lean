import EnvelopeProperty.Berkovich.SchemeFramedSectionFactor
import EnvelopeProperty.Berkovich.SchemeSupportLineFrames
import EnvelopeProperty.Berkovich.SchemePointLaurentLocalFrame
import EnvelopeProperty.Berkovich.SchemeOpenImmersion

/-! # Actual native support-frame coefficients and local section evaluation -/
open AlgebraicGeometry CategoryTheory Opposite
open scoped NNReal LaurentPolynomial
noncomputable section
universe u
namespace EnvelopeProperty.Berkovich.SchemeSupportFrameEvaluation
open SchemeFramedSectionPullback SchemeLineSectionEvaluation

/-- Every original factor frame computes the actual pullback of its true local coefficient. -/
theorem factorFrameCoefficient {A B C : Scheme.{u}}
    (q : A ⟶ B) (b : B ⟶ C) (h : A ⟶ C) (hq : q ≫ b = h)
    (N : C.Modules) (e : (Scheme.Modules.pullback b).obj N ≅ Scheme.Modules.unitObj B)
    (σ : Γ(N, ⊤)) :
    (Scheme.Modules.frameViaFactor q b h hq e).hom.app ⊤
        (Scheme.Modules.affinePullbackUnitTop h N σ) =
      q.appTop (e.hom.app ⊤ (Scheme.Modules.affinePullbackUnitTop b N σ)) := by
  have he := Scheme.Modules.unitHom_eq_globalScalar
    (pullbackSectionHom b (Scheme.Modules.topSectionHom N σ) ≫ e.hom)
  have hs : pullbackSectionHom b (Scheme.Modules.topSectionHom N σ) ≫ e.hom =
      ModularCurves.unitEndomorphismOfTopSection
        (e.hom.app ⊤ (Scheme.Modules.affinePullbackUnitTop b N σ)) := by
    refine he.trans (congrArg ModularCurves.unitEndomorphismOfTopSection ?_)
    exact congrArg (fun z => e.hom.app ⊤ z)
      (affinePullbackUnitTop_eq_sectionAtOne b N σ).symm
  have ht := frameViaFactor_sectionHom_scalar_apply q b h hq e
    (Scheme.Modules.topSectionHom N σ) _ hs
  have hu := congrArg (fun z : Γ((Scheme.Modules.pullback h).obj N, ⊤) =>
    (Scheme.Modules.frameViaFactor q b h hq e).hom.app ⊤ z)
    (affinePullbackUnitTop_eq_sectionAtOne h N σ)
  exact hu.trans ht

/-- The genuine support factor evaluates every original local scalar by its actual residue map. -/
theorem supportFactor_appTop {Y : Scheme.{u}} (y : SchemeValuedPoint Y)
    (V : Y.Opens) (hy : y.point ∈ V) :
    (SchemeSupportLineFrames.supportGenericFactor y.point V hy).appTop ≫
        (Scheme.ΓSpecIso (Y.residueField y.point)).hom =
      V.topIso.hom ≫ Y.evaluation V y.point hy := by
  let q := SchemeSupportLineFrames.supportGenericFactor y.point V hy
  have hi : V.ι.appLE V ⊤ (by simp) = V.topIso.inv := by
    rw [Scheme.Opens.ι_appLE]
    change Y.presheaf.map _ = Y.presheaf.map _
    exact congrArg Y.presheaf.map (Subsingleton.elim _ _)
  have hc := Scheme.Hom.appLE_comp_appLE q V.ι V ⊤ ⊤ (by simp) (by simp)
  have hqt : q.appLE ⊤ ⊤ (by simp) = q.appTop := by
    simp only [Scheme.Hom.appLE, Scheme.Hom.appTop]
    erw [CategoryTheory.Functor.map_id, Category.comp_id]
  simp only [hi, hqt, q, SchemeSupportLineFrames.supportGenericFactor_comp] at hc
  have hr := SchemeValuedPoint.fromSpecResidueField_appLE_top y.point V hy (by
    rw [SchemeValuedPoint.fromSpecResidueField_preimage_eq_top y.point V hy])
  apply (cancel_epi V.topIso.inv).mp
  rw [← Category.assoc, hc, hr, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]

/-- Actual original local coefficient, regarded on its original scheme open. -/
def localCoefficient {Y : Scheme.{u}} (N : Y.Modules) (V : Y.Opens)
    (e : (Scheme.Modules.pullback V.ι).obj N ≅ Scheme.Modules.unitObj V.toScheme)
    (σ : Γ(N, ⊤)) : Γ(Y, V) :=
  V.topIso.hom (e.hom.app ⊤ (Scheme.Modules.affinePullbackUnitTop V.ι N σ))

/-- The true support residue frame coefficient equals actual local residue evaluation. -/
theorem supportFrame_coefficient {Y : Scheme.{u}} (y : SchemeValuedPoint Y)
    (N : Y.Modules) (V : Y.Opens) (hy : y.point ∈ V)
    (e : (Scheme.Modules.pullback V.ι).obj N ≅ Scheme.Modules.unitObj V.toScheme)
    (σ : Γ(N, ⊤)) :
    residueFrameCoefficient y N (SchemeSupportLineFrames.supportGenericFrame y.point V hy e) σ =
      Y.evaluation V y.point hy (localCoefficient N V e σ) := by
  have hf := factorFrameCoefficient (SchemeSupportLineFrames.supportGenericFactor y.point V hy)
    V.ι (Y.fromSpecResidueField y.point) (SchemeSupportLineFrames.supportGenericFactor_comp y.point V hy)
    N e σ
  have hs := congrArg (Scheme.ΓSpecIso (Y.residueField y.point)).hom.hom hf
  have ht := congrArg (fun f : Γ(V.toScheme, ⊤) ⟶ Y.residueField y.point =>
    f.hom (e.hom.app ⊤ (Scheme.Modules.affinePullbackUnitTop V.ι N σ)))
    (supportFactor_appTop y V hy)
  exact hs.trans ht

/-- Actual native support-frame coefficient values equal actual local section values. -/
theorem supportFrame_value {Y : Scheme.{u}} (y : SchemeValuedPoint Y)
    (N : Y.Modules) (V : Y.Opens) (hy : y.point ∈ V)
    (e : (Scheme.Modules.pullback V.ι).obj N ≅ Scheme.Modules.unitObj V.toScheme)
    (σ : Γ(N, ⊤)) :
    y.residueVal (residueFrameCoefficient y N
        (SchemeSupportLineFrames.supportGenericFrame y.point V hy e) σ) =
      SchemeValuedPoint.eval y V hy (localCoefficient N V e σ) :=
  congrArg y.residueVal (supportFrame_coefficient y N V hy e σ)

/-- Native evaluation on an actual original open equals whole-section evaluation at its actual lift. -/
theorem eval_openTopIso {Y : Scheme.{u}} (V : Y.Opens) (z : SchemeValuedPoint V.toScheme)
    (a : Γ(V.toScheme, ⊤)) :
    SchemeValuedPoint.eval (SchemeValuedPoint.map V.ι z) V z.point.property (V.topIso.hom a) =
      SchemeValuedPoint.eval z ⊤ trivial a := by
  have h := SchemeValuedPoint.eval_map_appIso_inv V.ι z ⊤ trivial a
  have hr := SchemeValuedPoint.eval_restrict (SchemeValuedPoint.map V.ι z)
    (V.ι ''ᵁ ⊤) V V.ι_image_top.ge z.point.property (show Γ(Y, V.ι ''ᵁ ⊤) from a)
  simp only [Scheme.Opens.ι_appIso, Iso.refl_inv] at h
  exact hr.trans h

/-- The support-induced original frame at a genuine open lift evaluates the true local scalar section. -/
theorem supportFrame_value_of_openLift {Y : Scheme.{u}} (N : Y.Modules) (V : Y.Opens)
    (z : SchemeValuedPoint V.toScheme)
    (e : (Scheme.Modules.pullback V.ι).obj N ≅ Scheme.Modules.unitObj V.toScheme)
    (σ : Γ(N, ⊤)) :
    (SchemeValuedPoint.map V.ι z).residueVal
        (residueFrameCoefficient (SchemeValuedPoint.map V.ι z) N
          (SchemeSupportLineFrames.supportGenericFrame (V.ι z.point) V z.point.property e) σ) =
      SchemeValuedPoint.eval z ⊤ trivial
        (e.hom.app ⊤ (Scheme.Modules.affinePullbackUnitTop V.ι N σ)) :=
  (supportFrame_value (SchemeValuedPoint.map V.ι z) N V z.point.property e σ).trans
    (eval_openTopIso V z _)

section Laurent
variable {R : Type u} [CommRing R] {v : Valuation R ℝ≥0}
    {X : Scheme.{u}} (p : X ⟶ Spec (.of R)) (x : RelativeSchemeValuedPoint v p)
    [IsProper p] (hb : ∀ r, v r ≤ 1)

private abbrev firstProjection := FlatGlobalSections.firstProjection (S := R[T;T⁻¹]) p
private abbrev productPoint (r : ℝ≥0) (hr : 0 < r) := (SchemePointLaurentGauss.productPoint p x r hr).1

private theorem productPoint_mem (U : X.Opens) (hc : RelativeSchemeValuedPoint.center hb x ∈ U)
    (r : ℝ≥0) (hr : 0 < r) : (productPoint p x r hr).point ∈ firstProjection p ⁻¹ᵁ U := by
  have h := congrArg SchemeValuedPoint.point (SchemePointLaurentLocalFrame.openPoint_comp p x hb U hc r hr)
  rw [← h]
  exact (SchemePointLaurentLocalFrame.openPoint p x hb U hc r hr).point.property

/-- The actual original product-local frame induces one genuine native product residue frame. -/
def laurentSupportFrame (M : X.Modules) (U : X.Opens)
    (hc : RelativeSchemeValuedPoint.center hb x ∈ U)
    (e : (Scheme.Modules.pullback U.ι).obj M ≅ Scheme.Modules.unitObj U.toScheme)
    (r : ℝ≥0) (hr : 0 < r) :
    (Scheme.Modules.pullback ((FlatGlobalSections.baseChange (S := R[T;T⁻¹]) p).fromSpecResidueField
      (productPoint p x r hr).point)).obj ((Scheme.Modules.pullback (firstProjection p)).obj M) ≅
        Scheme.Modules.unitObj (Spec ((FlatGlobalSections.baseChange (S := R[T;T⁻¹]) p).residueField
          (productPoint p x r hr).point)) :=
  SchemeSupportLineFrames.supportGenericFrame (productPoint p x r hr).point
    (firstProjection p ⁻¹ᵁ U) (productPoint_mem p x hb U hc r hr)
    (SchemeLineSectionEvaluation.localPullbackFrame (firstProjection p) U e)

/-- EVERY original product-section residue coefficient in the actual support frame has its true weighted original norm. -/
theorem laurentSupportFrame_value [CompactSpace X] [X.IsSeparated]
    (M : X.Modules) [M.IsQuasicoherent] (hM : Scheme.Modules.IsInvertible M)
    (U : X.Opens) (hc : RelativeSchemeValuedPoint.center hb x ∈ U)
    (e : (Scheme.Modules.pullback U.ι).obj M ≅ Scheme.Modules.unitObj U.toScheme)
    (r : ℝ≥0) (hr : 0 < r) (σ : SchemeModuleLaurentCoefficients.pulledSections p M) :
    (productPoint p x r hr).residueVal
        (residueFrameCoefficient (productPoint p x r hr) ((Scheme.Modules.pullback (firstProjection p)).obj M)
          (laurentSupportFrame p x hb M U hc e r hr) σ) =
      (SchemeModuleLaurentCoefficients.coefficients p M σ).support.sup
        (fun i => RelativeSchemeValuedPoint.modelLineNorm hb x hM
          (Scheme.Modules.affinePullbackUnitTop (X.fromSpecResidueField x.1.point) M
            (SchemeModuleLaurentCoefficients.coefficients p M σ i)) * r ^ i) := by
  have h := supportFrame_value_of_openLift ((Scheme.Modules.pullback (firstProjection p)).obj M)
    (firstProjection p ⁻¹ᵁ U) (SchemePointLaurentLocalFrame.openPoint p x hb U hc r hr)
    (SchemeLineSectionEvaluation.localPullbackFrame (firstProjection p) U e) σ
  have hv := SchemePointLaurentLocalFrame.localCoefficient_value p x hb M hM U hc e r hr σ
  let F : {y : SchemeValuedPoint (FlatGlobalSections.baseChange (S := R[T;T⁻¹]) p) //
      y.point ∈ firstProjection p ⁻¹ᵁ U} → ℝ≥0 := fun t =>
    t.1.residueVal (residueFrameCoefficient t.1 ((Scheme.Modules.pullback (firstProjection p)).obj M)
      (SchemeSupportLineFrames.supportGenericFrame t.1.point (firstProjection p ⁻¹ᵁ U) t.2
        (SchemeLineSectionEvaluation.localPullbackFrame (firstProjection p) U e)) σ)
  have hp : SchemeValuedPoint.map (firstProjection p ⁻¹ᵁ U).ι
      (SchemePointLaurentLocalFrame.openPoint p x hb U hc r hr) = productPoint p x r hr :=
    SchemePointLaurentLocalFrame.openPoint_comp p x hb U hc r hr
  have hsub : (⟨SchemeValuedPoint.map (firstProjection p ⁻¹ᵁ U).ι
      (SchemePointLaurentLocalFrame.openPoint p x hb U hc r hr),
      (SchemePointLaurentLocalFrame.openPoint p x hb U hc r hr).point.property⟩ :
        {y : SchemeValuedPoint (FlatGlobalSections.baseChange (S := R[T;T⁻¹]) p) //
          y.point ∈ firstProjection p ⁻¹ᵁ U}) =
      ⟨productPoint p x r hr, productPoint_mem p x hb U hc r hr⟩ := Subtype.ext hp
  have hf := congrArg F hsub
  exact hf.symm.trans (h.trans hv)

/-- One actual original support residue frame works for ALL original whole sections. -/
theorem exists_laurentSupportFrame_values [CompactSpace X] [X.IsSeparated]
    (M : X.Modules) [M.IsQuasicoherent] (hM : Scheme.Modules.IsInvertible M)
    (U : X.Opens) (hc : RelativeSchemeValuedPoint.center hb x ∈ U)
    (e : (Scheme.Modules.pullback U.ι).obj M ≅ Scheme.Modules.unitObj U.toScheme)
    (r : ℝ≥0) (hr : 0 < r) :
    ∃ e₀ : (Scheme.Modules.pullback
        ((FlatGlobalSections.baseChange (S := R[T;T⁻¹]) p).fromSpecResidueField
          (productPoint p x r hr).point)).obj ((Scheme.Modules.pullback (firstProjection p)).obj M) ≅
        Scheme.Modules.unitObj (Spec ((FlatGlobalSections.baseChange (S := R[T;T⁻¹]) p).residueField
          (productPoint p x r hr).point)),
      ∀ σ : SchemeModuleLaurentCoefficients.pulledSections p M,
        (productPoint p x r hr).residueVal
          (residueFrameCoefficient (productPoint p x r hr) ((Scheme.Modules.pullback (firstProjection p)).obj M)
            e₀ σ) =
          (SchemeModuleLaurentCoefficients.coefficients p M σ).support.sup
            (fun i => RelativeSchemeValuedPoint.modelLineNorm hb x hM
              (Scheme.Modules.affinePullbackUnitTop (X.fromSpecResidueField x.1.point) M
                (SchemeModuleLaurentCoefficients.coefficients p M σ i)) * r ^ i) :=
  ⟨laurentSupportFrame p x hb M U hc e r hr, laurentSupportFrame_value p x hb M hM U hc e r hr⟩

/-- Genuine original invertibility internally chooses a true proper-center frame and hence ONE product residue frame for EVERY section. -/
theorem exists_laurentSupportFrame_values_of_isInvertible [CompactSpace X] [X.IsSeparated]
    (M : X.Modules) [M.IsQuasicoherent] (hM : Scheme.Modules.IsInvertible M)
    (r : ℝ≥0) (hr : 0 < r) :
    ∃ e₀ : (Scheme.Modules.pullback
        ((FlatGlobalSections.baseChange (S := R[T;T⁻¹]) p).fromSpecResidueField
          (productPoint p x r hr).point)).obj ((Scheme.Modules.pullback (firstProjection p)).obj M) ≅
        Scheme.Modules.unitObj (Spec ((FlatGlobalSections.baseChange (S := R[T;T⁻¹]) p).residueField
          (productPoint p x r hr).point)),
      ∀ σ : SchemeModuleLaurentCoefficients.pulledSections p M,
        (productPoint p x r hr).residueVal
          (residueFrameCoefficient (productPoint p x r hr) ((Scheme.Modules.pullback (firstProjection p)).obj M)
            e₀ σ) =
          (SchemeModuleLaurentCoefficients.coefficients p M σ).support.sup
            (fun i => RelativeSchemeValuedPoint.modelLineNorm hb x hM
              (Scheme.Modules.affinePullbackUnitTop (X.fromSpecResidueField x.1.point) M
                (SchemeModuleLaurentCoefficients.coefficients p M σ i)) * r ^ i) := by
  have hMt := hM
  obtain ⟨ι, U, hU, hframe⟩ := hMt
  have hc : RelativeSchemeValuedPoint.center hb x ∈ iSup U := by rw [hU]; trivial
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hc
  obtain ⟨e⟩ := hframe i
  exact exists_laurentSupportFrame_values p x hb M hM (U i) hi e r hr

/-- The same actual original finite coefficient/weight family, before all points, computes all native support-frame values. -/
theorem laurentSupportFrame_finite_family [CompactSpace X] [X.IsSeparated]
    (M : X.Modules) [M.IsQuasicoherent] (hM : Scheme.Modules.IsInvertible M)
    (G : Finset (SchemeModuleLaurentCoefficients.pulledSections p M))
    (U : X.Opens) (hc : RelativeSchemeValuedPoint.center hb x ∈ U)
    (e : (Scheme.Modules.pullback U.ι).obj M ≅ Scheme.Modules.unitObj U.toScheme)
    (r : ℝ≥0) (hr : 0 < r) :
    G.sup (fun σ => (productPoint p x r hr).residueVal
        (residueFrameCoefficient (productPoint p x r hr) ((Scheme.Modules.pullback (firstProjection p)).obj M)
          (laurentSupportFrame p x hb M U hc e r hr) σ)) =
      (SchemeModuleLaurentCoefficients.terms p M G).sup
        (fun t => RelativeSchemeValuedPoint.modelLineNorm hb x hM
          (Scheme.Modules.affinePullbackUnitTop (X.fromSpecResidueField x.1.point) M t.1) * r ^ t.2) := by
  simp only [laurentSupportFrame_value p x hb M hM U hc e r hr,
    SchemeModuleLaurentCoefficients.terms, Finset.sup_biUnion, Finset.sup_image]
  rfl
end Laurent

end EnvelopeProperty.Berkovich.SchemeSupportFrameEvaluation
