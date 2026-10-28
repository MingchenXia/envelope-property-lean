import EnvelopeProperty.AlgGeom.SchemeLineSectionLocalFrames
import EnvelopeProperty.Berkovich.SchemeLocalSectionRatioPullback

/-! # True local sections give their own whole frames on opens of the original model -/
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
universe u
namespace EnvelopeProperty.SchemeLocalSectionOriginalFrames
open Scheme.Modules SchemeLineSectionEvaluation SchemeLocalSectionRatioPullback
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The same nonvanishing local section internally gives its inverse section frame on a genuine original-model open. -/
theorem exists_original_section_frame {A N : Scheme.{u}} (j : A ⟶ N) [IsOpenImmersion j]
    (M : N.Modules) (hM : IsInvertible M) (s : unitObj A ⟶ (pullback j).obj M)
    (x : A) (hx : x ∉ (LineSectionZeroIdeal.zeroIdeal ((pullback j).obj M) (hM.pullback j) s).support) :
    ∃ W : N.Opens, j x ∈ W ∧ ∃ i : W.toScheme ⟶ A, IsOpenImmersion i ∧
      ∃ hi : i ≫ j = W.ι, ∃ e : (pullback W.ι).obj M ≅ unitObj W.toScheme,
        sectionViaFactor i j W.ι hi s ≫ e.hom = 𝟙 _ := by
  obtain ⟨V,hxV,eV,heV⟩ := SchemeLineSectionLocalFrames.exists_section_frame_at ((pullback j).obj M)
    (hM.pullback j) s x hx
  have hv : IsIso (pullbackSectionHom V.ι s) := by
    have : IsIso (pullbackSectionHom V.ι s ≫ eV.hom) := by rw [heV]; infer_instance
    exact IsIso.of_isIso_comp_right (pullbackSectionHom V.ι s) eV.hom
  let k := V.ι ≫ j
  let W := k.opensRange
  have hxW : j x ∈ W := Scheme.Hom.mem_opensRange.mpr ⟨⟨x,hxV⟩,rfl⟩
  have hr : Set.range W.ι ⊆ Set.range k := by
    rw [W.range_ι]
    exact fun y hy => Scheme.Hom.mem_opensRange.mp hy
  let l := IsOpenImmersion.lift k W.ι hr
  have hl : l ≫ k = W.ι := IsOpenImmersion.lift_fac k W.ι hr
  let i := l ≫ V.ι
  have hi : i ≫ j = W.ι := by simpa only [i,k,Category.assoc] using hl
  have hs : IsIso (pullbackSectionHom i s) := by
    rw [← pullbackSectionHom_comp l V.ι s]
    change IsIso ((pullbackUnitIso l).inv ≫ (pullback l).map (pullbackSectionHom V.ι s) ≫
      (pullbackComp l V.ι).hom.app ((pullback j).obj M))
    let := hv
    infer_instance
  let t := sectionViaFactor i j W.ι hi s
  have ht : IsIso t := by
    change IsIso (pullbackSectionHom i s ≫ (frameFactorIso i j W.ι hi M).hom)
    let := hs
    infer_instance
  let := ht
  exact ⟨W,hxW,i,inferInstance,hi,(asIso t).symm,(asIso t).hom_inv_id⟩

/-- Every true factor transports an actual whole section-one identity to the SAME native frame-one identity. -/
theorem sectionViaFactor_frameOne {Y A N : Scheme.{u}}
    (q : Y ⟶ A) (j : A ⟶ N) (p : Y ⟶ N) (h : q ≫ j = p) {M : N.Modules}
    (s : unitObj A ⟶ (pullback j).obj M) (e : (pullback j).obj M ≅ unitObj A)
    (he : s ≫ e.hom = 𝟙 _) :
    sectionViaFactor q j p h s ≫ (frameViaFactor q j p h e).hom = 𝟙 _ := by
  simp only [sectionViaFactor,frameViaFactor,Iso.trans_hom,Iso.symm_hom,Functor.mapIso_hom,
    Category.assoc,Iso.hom_inv_id_assoc]
  change (pullbackUnitIso q).inv ≫ (pullback q).map s ≫ (pullback q).map e.hom ≫
    (pullbackUnitIso q).hom = _
  rw [← Category.assoc ((pullback q).map s),← Functor.map_comp,he,CategoryTheory.Functor.map_id,
    Category.id_comp,Iso.inv_hom_id]
end EnvelopeProperty.SchemeLocalSectionOriginalFrames
