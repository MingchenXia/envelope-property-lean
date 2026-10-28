import EnvelopeProperty.AlgGeom.SchemeCommonAffineLineFrames
import EnvelopeProperty.AlgGeom.SchemeLineSectionUnitFrames
import EnvelopeProperty.Berkovich.SchemeLocalSectionRatioPullback

/-! # Actual nonvanishing original sections give their own whole original open frames -/
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
universe u
namespace EnvelopeProperty.SchemeLineSectionLocalFrames
open Scheme.Modules SchemeLineSectionEvaluation
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The SAME actual original section, nonzero at the actual point, internally gives a whole open frame with value exactly one. -/
theorem exists_section_frame_at {N : Scheme.{u}} (M : N.Modules) (hM : IsInvertible M)
    (σ : unitObj N ⟶ M) (c : N)
    (hc : c ∉ (LineSectionZeroIdeal.zeroIdeal M hM σ).support) :
    ∃ W : N.Opens, c ∈ W ∧ ∃ e : (pullback W.ι).obj M ≅ unitObj W.toScheme,
      pullbackSectionHom W.ι σ ≫ e.hom = 𝟙 _ := by
  obtain ⟨A,hcA,_,⟨eA⟩,_⟩ := SchemeCommonAffineLineFrames.exists_in_open M (unitObj N)
    hM isInvertible_unit c ⊤ (by trivial)
  let x : A.1.toScheme := ⟨c,hcA⟩
  let β := pullbackSectionHom A.1.ι σ
  let r := SchemeLineSectionUnitFrames.frameScalar eA β
  let I := LineSectionZeroIdeal.zeroIdeal ((pullback A.1.ι).obj M) (hM.pullback A.1.ι) β
  have hxI : x ∉ I.support := by
    change x ∉ (LineSectionZeroIdeal.zeroIdeal ((pullback A.1.ι).obj M) (hM.pullback A.1.ι)
      (pullbackSectionHom A.1.ι σ)).support
    rw [SchemeLineZeroSupportPullback.support_pullback A.1.ι M hM σ]
    exact hc
  let eO : ((pullback A.1.ι).obj M).over ⊤ ≅ SheafOfModules.unit (A.1.toScheme.ringCatSheaf.over ⊤) :=
    (SheafOfModules.overFunctor A.1.toScheme.ringCatSheaf ⊤).mapIso eA
  have hi := LineSectionZeroIdeal.zeroIdeal_ideal_of_frame ((pullback A.1.ι).obj M)
    (hM.pullback A.1.ι) β ⟨⊤,isAffineOpen_top A.1.toScheme⟩ eO
  change I.ideal ⟨⊤,isAffineOpen_top A.1.toScheme⟩ = Ideal.span ({r} : Set Γ(A.1.toScheme,⊤)) at hi
  have hx : x ∈ A.1.toScheme.basicOpen r := by
    by_contra h
    apply hxI
    rw [I.mem_support_iff_of_mem (U := ⟨⊤,isAffineOpen_top A.1.toScheme⟩) trivial,hi,
      A.1.toScheme.zeroLocus_span,A.1.toScheme.zeroLocus_singleton]
    exact h
  let V := A.1.toScheme.basicOpen r
  let k : V.toScheme ⟶ N := V.ι ≫ A.1.ι
  have hk : IsIso (pullbackSectionHom k σ) := by
    let := SchemeLineSectionUnitFrames.basicOpenSection_isIso eA β
    rw [← pullbackSectionHom_comp V.ι A.1.ι σ]
    infer_instance
  let W := k.opensRange
  have hcW : c ∈ W := by
    apply Scheme.Hom.mem_opensRange.mpr
    exact ⟨⟨x,hx⟩,rfl⟩
  have hr : Set.range W.ι ⊆ Set.range k := by
    rw [W.range_ι]
    exact fun y hy => Scheme.Hom.mem_opensRange.mp hy
  let l := IsOpenImmersion.lift k W.ι hr
  have hl : l ≫ k = W.ι := IsOpenImmersion.lift_fac k W.ι hr
  have hw : IsIso (pullbackSectionHom W.ι σ) := by
    rw [← SchemeLocalSectionRatioPullback.sectionViaFactor_global l k W.ι hl σ]
    change IsIso ((pullbackUnitIso l).inv ≫ (pullback l).map (pullbackSectionHom k σ) ≫
      (frameFactorIso l k W.ι hl M).hom)
    let := hk
    infer_instance
  let := hw
  exact ⟨W,hcW,(asIso (pullbackSectionHom W.ι σ)).symm,
    (asIso (pullbackSectionHom W.ι σ)).hom_inv_id⟩
end EnvelopeProperty.SchemeLineSectionLocalFrames
