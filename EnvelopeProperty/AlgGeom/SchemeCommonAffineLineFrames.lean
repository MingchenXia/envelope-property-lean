import EnvelopeProperty.AlgGeom.SchemeLineZeroSupportPullback
import EnvelopeProperty.AlgGeom.SchemeOriginalAuxiliaryUnitChart
/-! # Genuine common affine frames preserve SAME whole original chart triangles and identities -/
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open Scheme.Modules
open scoped Polynomial
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace EnvelopeProperty.SchemeCommonAffineLineFrames

theorem exists_in_open {N : Scheme.{u}} (M T : N.Modules) (hM : IsInvertible M) (hT : IsInvertible T)
    (c : N) (U : N.Opens) (hc : c ∈ U) :
    ∃ V : N.affineOpens, c ∈ V.1 ∧ V.1 ≤ U ∧
      Nonempty ((pullback V.1.ι).obj M ≅ unitObj V.1.toScheme) ∧
      Nonempty ((pullback V.1.ι).obj T ≅ unitObj V.1.toScheme) := by
  obtain ⟨ι,UM,hUM,eM⟩ := hM
  obtain ⟨κ,UT,hUT,eT⟩ := hT
  have hcM : c ∈ ⨆ i, UM i := by rw [hUM]; trivial
  have hcT : c ∈ ⨆ i, UT i := by rw [hUT]; trivial
  obtain ⟨a,ha⟩ := Opens.mem_iSup.mp hcM
  obtain ⟨b,hb⟩ := Opens.mem_iSup.mp hcT
  obtain ⟨em⟩ := eM a
  obtain ⟨et⟩ := eT b
  obtain ⟨V,hVa,hcV,hVU⟩ := exists_isAffineOpen_mem_and_subset (X := N)
    (U := U ⊓ UM a ⊓ UT b) (x := c) ⟨⟨hc,ha⟩,hb⟩
  have hVm : V ≤ UM a := hVU.trans (inf_le_left.trans inf_le_right)
  have hVt : V ≤ UT b := hVU.trans inf_le_right
  refine ⟨⟨V,hVa⟩,hcV,hVU.trans (inf_le_left.trans inf_le_left),?_,?_⟩
  · exact ⟨frameViaFactor (N.homOfLE hVm) (UM a).ι V.ι (N.homOfLE_ι hVm) em⟩
  · exact ⟨frameViaFactor (N.homOfLE hVt) (UT b).ι V.ι (N.homOfLE_ι hVt) et⟩

theorem exists_in_etale_chart {N A S : Scheme.{u}}
    (j : A ⟶ N) [IsOpenImmersion j] (g : A ⟶ S) [Etale g]
    (c : N) (hc : c ∈ Set.range j) (M T : N.Modules) (hM : IsInvertible M) (hT : IsInvertible T) :
    ∃ V : N.affineOpens, c ∈ V.1 ∧
      ∃ i : V.1.toScheme ⟶ A, IsOpenImmersion i ∧ i ≫ j = V.1.ι ∧ Etale (i ≫ g) ∧
        Nonempty ((pullback V.1.ι).obj M ≅ unitObj V.1.toScheme) ∧
        Nonempty ((pullback V.1.ι).obj T ≅ unitObj V.1.toScheme) := by
  obtain ⟨V,hcV,hV,em,et⟩ := exists_in_open M T hM hT c j.opensRange hc
  have hr : Set.range V.1.ι ⊆ Set.range j := by
    rw [V.1.range_ι]
    exact hV
  let i := IsOpenImmersion.lift j V.1.ι hr
  let : IsOpenImmersion i := inferInstance
  exact ⟨V,hcV,i,inferInstance,IsOpenImmersion.lift_fac j V.1.ι hr,inferInstance,em,et⟩

theorem residual_ideal_restrict {N A B S : Scheme.{u}} (j : A ⟶ N) (i : B ⟶ A)
    (k : B ⟶ N) (h : i ≫ j = k) (g : A ⟶ S) (I : N.IdealSheafData) (J : S.IdealSheafData)
    (hres : I.comap j = J.comap g) : I.comap k = J.comap (i ≫ g) := by
  rw [← h,I.comap_comp,hres,← J.comap_comp]

theorem whole_unit_parameter_restrict {E : Type u} [CommRing E] {A B : Scheme.{u}}
    (i : B ⟶ A) (f g : A ⟶ Spec (.of E[X])) (w : Γ(A,⊤)) (hw : IsUnit w) (e : ℕ)
    (hwhole : SchemeOriginalAuxiliaryUnitChart.polynomialSection f =
      w * (SchemeOriginalAuxiliaryUnitChart.polynomialSection g) ^ e) :
    IsUnit (i.appTop.hom w) ∧
      SchemeOriginalAuxiliaryUnitChart.polynomialSection (i ≫ f) =
        i.appTop.hom w * (SchemeOriginalAuxiliaryUnitChart.polynomialSection (i ≫ g)) ^ e := by
  refine ⟨hw.map i.appTop.hom,?_⟩
  have hp (a : A ⟶ Spec (.of E[X])) :
      SchemeOriginalAuxiliaryUnitChart.polynomialSection (i ≫ a) =
        i.appTop.hom (SchemeOriginalAuxiliaryUnitChart.polynomialSection a) := by
    unfold SchemeOriginalAuxiliaryUnitChart.polynomialSection
    rw [Scheme.Hom.comp_appTop]
    rfl
  rw [hp f,hp g,hwhole,map_mul,map_pow]
end EnvelopeProperty.SchemeCommonAffineLineFrames
