import EnvelopeProperty.Vanishing.ArithmeticCanonicalGlobal
import EnvelopeProperty.Alterations.StableModification.Limits.SpreadAffine
import EnvelopeProperty.Alterations.StableModification.Limits.SpreadProperty

/-! # The original relative dimension spreads on the same fixed family

Actual standard-smooth charts of the original morphism supply models with
the same relative dimension. A finite chart cover and native approximation
then give that property on a later base change of the original fixed model.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

noncomputable section
universe u

namespace EnvelopeProperty.Vanishing.ArithmeticOriginalSmooth

open Alterations.StableModification.Limits

variable {A L : Type u} [CommRing A] [CommRing L] [Algebra A L] {R : Subalgebra A L}
  {X : Scheme.{u}} (f : X ⟶ (fgSpecCone R).pt) (n : ℕ)
  [SmoothOfRelativeDimension n f]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Each original point supplies an actual affine-chart model of the same
relative dimension, with its original whole structural morphism retained. -/
theorem exists_original_standard_chart_model (x : X) :
    ∃ (V : X.Opens) (_ : IsAffineOpen V), x ∈ V ∧
      ∃ (B : FGSubalgebra A R)
        (M : Model ((fgDiagram R).op ⋙ Scheme.Spec) (fgSpecCone R) (V.ι ≫ f) (op B)),
        M.IsFP ∧ SmoothOfRelativeDimension n M.fY := by
  obtain ⟨V, hV, hx, hs⟩ := ArithmeticCanonicalGlobal.exists_standardSmoothChart f n x
  let φ : CommRingCat.of R ⟶ Γ(X, V) :=
    (ArithmeticCanonicalGlobal.relativeConstants f).app (op V)
  let : Algebra R Γ(X, V) := φ.hom.toAlgebra
  let : Algebra.IsStandardSmoothOfRelativeDimension n R Γ(X, V) := hs
  obtain ⟨A₀, B₀, _, _, hA₀, hB₀, ⟨e⟩⟩ :=
    Algebra.IsStandardSmoothOfRelativeDimension.exists_subalgebra_fg A R Γ(X, V) n
  let : Algebra.IsStandardSmoothOfRelativeDimension n A₀ B₀ := hB₀
  let : Algebra.IsStandardSmooth A₀ B₀ := hB₀.isStandardSmooth
  obtain ⟨B, M, hM, hP⟩ := Spread.exists_model_spec_of_tensorEquiv Γ(X, V) A₀ hA₀ B₀ e
  have hscheme : SmoothOfRelativeDimension n
      (Spec.map (CommRingCat.ofHom (algebraMap A₀ B₀))) := by
    rw [HasRingHomProperty.Spec_iff (P := @SmoothOfRelativeDimension n)]
    exact RingHom.locally_of RingHom.isStandardSmoothOfRelativeDimension_respectsIso _
      ((RingHom.isStandardSmoothOfRelativeDimension_algebraMap n).mpr hB₀)
  have htriangle : hV.isoSpec.hom ≫
      Spec.map (CommRingCat.ofHom (algebraMap R Γ(X, V))) = V.ι ≫ f := by
    change hV.isoSpec.hom ≫ Spec.map φ = _
    rw [← ArithmeticCanonicalGlobal.affineChartStructure f hV]
    simp only [IsAffineOpen.fromSpec, ← Category.assoc, Iso.hom_inv_id, Category.id_comp]
  exact ⟨V, hV, hx, B, Spread.modelOfIso M hV.isoSpec (V.ι ≫ f) htriangle,
    Spread.isFP_modelOfIso hM hV.isoSpec (V.ι ≫ f) htriangle,
    hP (@SmoothOfRelativeDimension n) hscheme⟩

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The actual original relative dimension holds on a produced later
coefficient base change of the same original finite-presentation model. -/
theorem exists_relativeDimension_fixed_model_baseChange
    {i : (FGSubalgebra A R)ᵒᵖ}
    (m : Model ((fgDiagram R).op ⋙ Scheme.Spec) (fgSpecCone R) f i)
    (hm : m.IsFP) :
    ∃ (j : (FGSubalgebra A R)ᵒᵖ) (h : j ⟶ i),
      SmoothOfRelativeDimension n (m.baseChange h).fY := by
  classical
  let P : MorphismProperty Scheme.{u} := @SmoothOfRelativeDimension n
  let : MorphismProperty.IsStableUnderBaseChange P :=
    smoothOfRelativeDimension_isStableUnderBaseChange n
  let : IsZariskiLocalAtSource P :=
    @HasRingHomProperty.instIsZariskiLocalAtSource _ _ inferInstance
  let D := (fgDiagram R).op ⋙ Scheme.Spec
  let c := fgSpecCone R
  have hc := isLimitFGSpecCone R
  obtain ⟨hlfp, hqc, hqs⟩ := hm
  have hc' := isLimitBaseChangeCone D c hc m.isPullback
  let : CompactSpace X := Scheme.compactSpace_of_isLimit _ _ hc'
  choose V hV hx B M hM hn using fun x : X => exists_original_standard_chart_model f n x
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover
    (fun x : X => (V x : Set X)) (fun x => (V x).isOpen)
    (by intro x _; exact Set.mem_iUnion.mpr ⟨x, hx x⟩)
  have key (x : s) :
      ∃ (J : Over i) (W : ((baseChangeDiagram D m.fY).obj J).Opens),
        (baseChangeCone D c m.isPullback).π.app J ⁻¹ᵁ W = V x.val ∧
          P (W.ι ≫ pullback.snd m.fY (D.map J.hom)) :=
    Spread.exists_opens_of_isCompact P m hc ⟨hlfp, hqc, hqs⟩
      (V x.val) (hV x.val).isCompact
      (fun W' hW' => by
        subst W'
        exact ⟨op (B x.val), M x.val, hM x.val, hn x.val⟩)
  choose J W hW hPW using key
  obtain ⟨K, hK⟩ := IsCofiltered.inf_objs_exists (Finset.univ.image J)
  let a : ∀ x : s, K ⟶ J x :=
    fun x => (hK (Finset.mem_image_of_mem _ (Finset.mem_univ x))).some
  let U : ((baseChangeDiagram D m.fY).obj K).Opens :=
    ⨆ x : s, (baseChangeDiagram D m.fY).map (a x) ⁻¹ᵁ W x
  have hU : (baseChangeCone D c m.isPullback).π.app K ⁻¹ᵁ U = ⊤ := by
    simp only [U, Scheme.Hom.preimage_iSup, ← Scheme.Hom.comp_preimage,
      (baseChangeCone D c m.isPullback).w, hW]
    apply top_unique
    intro x _
    obtain ⟨y, hy, hyx⟩ := Set.mem_iUnion₂.mp (hs (Set.mem_univ x))
    exact (le_iSup (fun y : s => V y.val) ⟨y, hy⟩) hyx
  obtain ⟨K', b, hb⟩ := exists_map_eq_top _ _ hc' U hU
  refine ⟨K'.left, K'.hom, ?_⟩
  refine IsZariskiLocalAtSource.of_iSup_eq_top (P := P)
    (fun x : s => (baseChangeDiagram D m.fY).map (b ≫ a x) ⁻¹ᵁ W x) ?_
    (fun x => Spread.baseChange_restrict P m (b ≫ a x) (W x) (hPW x))
  simp only [Functor.map_comp, Scheme.Hom.comp_preimage]
  rw [← Scheme.Hom.preimage_iSup]
  exact hb

end EnvelopeProperty.Vanishing.ArithmeticOriginalSmooth
