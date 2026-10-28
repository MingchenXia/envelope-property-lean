import EnvelopeProperty.Vanishing.NadelBertiniAffineIncidence
import EnvelopeProperty.AlgGeom.SchemeLineZeroIdealNativeFrameOrders
import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
/-! # The whole original line-section ideal on the actual affine open chart -/
noncomputable section
open AlgebraicGeometry CategoryTheory Opposite
open Scheme.Modules
universe u
namespace EnvelopeProperty.Vanishing.NadelBertiniRestrictionIdeal
open SchemeLineSectionEvaluation

theorem comap_zeroIdeal_top {X : Scheme.{u}} (L : X.Modules) (hL : IsInvertible L)
    (α : unitObj X ⟶ L) (U : X.affineOpens)
    (e : (pullback U.1.ι).obj L ≅ unitObj U.1.toScheme) :
    ((LineSectionZeroIdeal.zeroIdeal L hL α).comap U.1.ι).ideal
        ⟨⊤, isAffineOpen_top U.1.toScheme⟩ =
      Ideal.span ({(show Γ(U.1.toScheme, ⊤) from sectionAtOne
        (pullbackSectionHom U.1.ι α ≫ e.hom))} : Set Γ(U.1.toScheme, ⊤)) := by
  let I := LineSectionZeroIdeal.zeroIdeal L hL α
  let V : X.affineOpens := ⟨U.1.ι ''ᵁ ⊤, (isAffineOpen_top U.1.toScheme).image_of_isOpenImmersion U.1.ι⟩
  have h := SchemeLineZeroIdealNativeFrameOrders.zeroIdeal_ideal_of_pullback_frame L hL α U e
  have hi := I.map_ideal' (U := U) (V := V) (eqToHom U.1.ι_image_top.symm).op
  change Ideal.map U.1.topIso.hom.hom (I.ideal V) = I.ideal U at hi
  have hh : Ideal.map U.1.topIso.hom.hom (I.ideal V) =
      Ideal.map U.1.topIso.hom.hom (Ideal.span {(show Γ(U.1.toScheme, ⊤) from sectionAtOne (pullbackSectionHom U.1.ι α ≫ e.hom))}) := by
    rw [hi]
    rw [Ideal.map_span, Set.image_singleton]
    exact h
  have he : Function.Injective (Ideal.map U.1.topIso.hom.hom) := by
    intro A B hab
    have hab' := congrArg (Ideal.map U.1.topIso.inv.hom) hab
    simpa only [Ideal.map_map, ← CommRingCat.hom_comp, Iso.hom_inv_id, CommRingCat.hom_id,
      Ideal.map_id] using hab'
  have hv := he hh
  rw [Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion, Scheme.Opens.ι_appIso]
  change Ideal.comap (RingHom.id _) (I.ideal V) = _
  rw [Ideal.comap_id]
  exact hv
end EnvelopeProperty.Vanishing.NadelBertiniRestrictionIdeal
