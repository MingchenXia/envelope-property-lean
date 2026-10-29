import EnvelopeProperty.Vanishing.NadelBertiniRestrictionIdeal
import EnvelopeProperty.Vanishing.NadelBertiniRestrictionCover
import EnvelopeProperty.AlgGeom.IdealSheafAffinePullback
import EnvelopeProperty.AlgGeom.SchemeLineSectionFactorization
/-! # The entire original line-section zero ideal commutes with arbitrary actual pullback -/
noncomputable section
open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open Scheme.Modules
universe u
namespace EnvelopeProperty.Vanishing.NadelBertiniFibreIdeals
open SchemeLineSectionEvaluation NadelBertiniRestrictionIdeal NadelBertiniRestrictionCover

theorem exists_affine_frame {X : Scheme.{u}} (L : X.Modules) (hL : IsInvertible L) (x : X) :
    ∃ U : X.affineOpens, x ∈ U.1 ∧ Nonempty ((pullback U.1.ι).obj L ≅ unitObj U.1.toScheme) := by
  obtain ⟨T, V, hV, eV⟩ := hL
  have hx : x ∈ ⨆ t, V t := by rw [hV]; trivial
  obtain ⟨t, ht⟩ := Opens.mem_iSup.mp hx
  obtain ⟨U, hU, hxU, hUV⟩ := exists_isAffineOpen_mem_and_subset ht
  obtain ⟨e⟩ := eV t
  let q := X.homOfLE hUV
  have hq : q ≫ (V t).ι = U.ι := X.homOfLE_ι hUV
  exact ⟨⟨U, hU⟩, hxU, ⟨frameViaFactor q (V t).ι U.ι hq e⟩⟩

private theorem unitEnd_sectionAtOne {X : Scheme.{u}} (r : Γ(X, ⊤)) :
    sectionAtOne (ModularCurves.unitEndomorphismOfTopSection r) = r := by
  change 1 * X.presheaf.map (homOfLE (le_top : (⊤ : X.Opens) ≤ ⊤)).op r = r
  simp

theorem factor_pulled_coefficient {X Y : Scheme.{u}} (f : Y ⟶ X) (L : X.Modules)
    (α : unitObj X ⟶ L) (U : X.Opens) (V : Y.Opens) (q : V.toScheme ⟶ U.toScheme)
    (hq : q ≫ U.ι = V.ι ≫ f) (e : (pullback U.ι).obj L ≅ unitObj U.toScheme) :
    let E := (pullbackComp V.ι f).app L ≪≫ frameViaFactor q U.ι (V.ι ≫ f) hq e
    (show Γ(V.toScheme, ⊤) from sectionAtOne
      (pullbackSectionHom V.ι (pullbackSectionHom f α) ≫ E.hom)) =
      q.appTop (sectionAtOne (pullbackSectionHom U.ι α ≫ e.hom)) := by
  let r : Γ(U.toScheme, ⊤) := sectionAtOne (pullbackSectionHom U.ι α ≫ e.hom)
  have hr : pullbackSectionHom U.ι α ≫ e.hom = ModularCurves.unitEndomorphismOfTopSection r :=
    unitHom_eq_globalScalar _
  have h : pullbackSectionHom V.ι (pullbackSectionHom f α) ≫
      ((pullbackComp V.ι f).app L ≪≫ frameViaFactor q U.ι (V.ι ≫ f) hq e).hom =
      ModularCurves.unitEndomorphismOfTopSection (q.appTop r) := by
    simp only [Iso.trans_hom, Iso.app_hom]
    rw [← Category.assoc, pullbackSectionHom_comp,
      frameViaFactor_sectionHom_scalar q U.ι (V.ι ≫ f) hq e α r hr]
  exact (congrArg sectionAtOne h).trans (unitEnd_sectionAtOne _)

theorem affine_factor_ideal {X Y : Scheme.{u}} (f : Y ⟶ X) (L : X.Modules)
    (hL : IsInvertible L) (α : unitObj X ⟶ L) (U : X.affineOpens) (V : Y.affineOpens)
    (q : V.1.toScheme ⟶ U.1.toScheme) (hq : q ≫ U.1.ι = V.1.ι ≫ f)
    (e : (pullback U.1.ι).obj L ≅ unitObj U.1.toScheme) :
    (((LineSectionZeroIdeal.zeroIdeal L hL α).comap f).comap V.1.ι).ideal
        ⟨⊤, isAffineOpen_top V.1.toScheme⟩ =
      ((LineSectionZeroIdeal.zeroIdeal ((pullback f).obj L) (hL.pullback f)
        (pullbackSectionHom f α)).comap V.1.ι).ideal ⟨⊤, isAffineOpen_top V.1.toScheme⟩ := by
  let I := LineSectionZeroIdeal.zeroIdeal L hL α
  let E := (pullbackComp V.1.ι f).app L ≪≫ frameViaFactor q U.1.ι (V.1.ι ≫ f) hq e
  let : IsAffine U.1.toScheme := U.2
  let : IsAffine V.1.toScheme := V.2
  have hleft : (I.comap f).comap V.1.ι = (I.comap U.1.ι).comap q := by
    rw [← Scheme.IdealSheafData.comap_comp, ← hq, Scheme.IdealSheafData.comap_comp]
  rw [hleft, Scheme.IdealSheafData.comap_ideal_top_of_isAffine_native,
    comap_zeroIdeal_top L hL α U e,
    comap_zeroIdeal_top ((pullback f).obj L) (hL.pullback f) (pullbackSectionHom f α) V E,
    Ideal.map_span, Set.image_singleton, factor_pulled_coefficient f L α U.1 V.1 q hq e]
theorem map_comap_top {Y : Scheme.{u}} (I : Y.IdealSheafData) (U : Y.affineOpens) :
    Ideal.map U.1.topIso.hom.hom ((I.comap U.1.ι).ideal ⟨⊤, isAffineOpen_top U.1.toScheme⟩) = I.ideal U := by
  let V : Y.affineOpens := ⟨U.1.ι ''ᵁ ⊤, (isAffineOpen_top U.1.toScheme).image_of_isOpenImmersion U.1.ι⟩
  have hc : (I.comap U.1.ι).ideal ⟨⊤, isAffineOpen_top U.1.toScheme⟩ = I.ideal V := by
    rw [Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion, Scheme.Opens.ι_appIso]
    change Ideal.comap (RingHom.id _) (I.ideal V) = _
    rw [Ideal.comap_id]
  rw [hc]
  have hi := I.map_ideal' (U := U) (V := V) (eqToHom U.1.ι_image_top.symm).op
  exact hi

theorem zeroIdeal_comap {X Y : Scheme.{u}} (f : Y ⟶ X) (L : X.Modules)
    (hL : IsInvertible L) (α : unitObj X ⟶ L) :
    (LineSectionZeroIdeal.zeroIdeal L hL α).comap f =
      LineSectionZeroIdeal.zeroIdeal ((pullback f).obj L) (hL.pullback f) (pullbackSectionHom f α) := by
  classical
  choose U hyU e using fun y : Y => exists_affine_frame L hL (f y)
  have hmem (y : Y) : y ∈ f ⁻¹ᵁ (U y).1 := hyU y
  choose V hVa hyV hVU using fun y : Y => exists_isAffineOpen_mem_and_subset (hmem y)
  let W : Y → Y.affineOpens := fun y => ⟨V y, hVa y⟩
  have hW : ⨆ y, (W y).1 = ⊤ := by
    apply top_le_iff.mp
    intro y _
    exact Opens.mem_iSup.mpr ⟨y, hyV y⟩
  apply Scheme.IdealSheafData.ext_of_iSup_eq_top W hW
  intro y
  let q := f.resLE (U y).1 (V y) (hVU y)
  have hq : q ≫ (U y).1.ι = (V y).ι ≫ f := f.resLE_comp_ι (hVU y)
  have h := affine_factor_ideal f L hL α (U y) (W y) q hq (e y).some
  have hh := congrArg (Ideal.map (W y).1.topIso.hom.hom) h
  rw [map_comap_top, map_comap_top] at hh
  exact hh

theorem zeroIdeal_iso {X : Scheme.{u}} (M N : X.Modules) (hM : IsInvertible M) (hN : IsInvertible N)
    (e : M ≅ N) (α : unitObj X ⟶ M) :
    LineSectionZeroIdeal.zeroIdeal M hM α = LineSectionZeroIdeal.zeroIdeal N hN (α ≫ e.hom) := by
  classical
  choose W hxW eW using fun x : X => exists_affine_frame N hN x
  have hW : ⨆ x, (W x).1 = ⊤ := by
    apply top_le_iff.mp
    intro x _
    exact Opens.mem_iSup.mpr ⟨x, hxW x⟩
  apply Scheme.IdealSheafData.ext_of_iSup_eq_top W hW
  intro x
  let E := (eW x).some
  let E' := (pullback (W x).1.ι).mapIso e ≪≫ E
  have h : ((LineSectionZeroIdeal.zeroIdeal M hM α).comap (W x).1.ι).ideal
        ⟨⊤, isAffineOpen_top (W x).1.toScheme⟩ =
      ((LineSectionZeroIdeal.zeroIdeal N hN (α ≫ e.hom)).comap (W x).1.ι).ideal
        ⟨⊤, isAffineOpen_top (W x).1.toScheme⟩ := by
    rw [comap_zeroIdeal_top M hM α (W x) E', comap_zeroIdeal_top N hN (α ≫ e.hom) (W x) E]
    have he : pullbackSectionHom (W x).1.ι α ≫ E'.hom =
        pullbackSectionHom (W x).1.ι (α ≫ e.hom) ≫ E.hom := by
      simp only [E', Iso.trans_hom, Functor.mapIso_hom, pullbackSectionHom, Functor.map_comp, Category.assoc]
    rw [he]
  have hh := congrArg (Ideal.map (W x).1.topIso.hom.hom) h
  rw [map_comap_top, map_comap_top] at hh
  exact hh

end EnvelopeProperty.Vanishing.NadelBertiniFibreIdeals
