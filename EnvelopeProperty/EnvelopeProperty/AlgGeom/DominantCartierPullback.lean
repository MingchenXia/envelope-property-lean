/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Berkovich.SchemeIntegralNormalization
import EnvelopeProperty.Berkovich.SchemeIdealPullback
import Hironaka.Scheme.BlowUp.FlatBaseChange
import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant

open CategoryTheory AlgebraicGeometry
noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
namespace AlgebraicGeometry.Scheme.IdealSheafData
variable {X Y : Scheme.{u}} [IsIntegral X] [IsReduced Y]

/-- Every original effective Cartier ideal stays Cartier under an arbitrary
original dominant morphism from an integral scheme. No flatness, QC,
Noetherian or finite-type hypothesis on the original morphism is needed. -/
theorem IsInvertible.comap_of_dominant_integral {J : Y.IdealSheafData}
    (hJ : J.IsInvertible) (f : X ⟶ Y) [IsDominant f] : (J.comap f).IsInvertible := by
  intro x
  obtain ⟨U, hxU, g, hg, hJU⟩ := hJ (f x)
  obtain ⟨W, hW, hxW, hWU⟩ := exists_isAffineOpen_mem_and_subset
    (show x ∈ f ⁻¹ᵁ U.1 from hxU)
  let V : X.affineOpens := ⟨W, hW⟩
  let : Nonempty U.1 := ⟨⟨f x, hxU⟩⟩
  let : Nonempty V.1 := ⟨⟨x, hxW⟩⟩
  let : IsAffine U.1 := U.2
  let : IsAffine V.1 := V.2
  let : IsDominant V.1.ι := Opens.isDominant_ι (V.1.isOpen.dense ⟨x, hxW⟩)
  have hVU : V.1 ≤ f ⁻¹ᵁ U.1 := hWU
  let r := f.resLE U.1 V.1 hVU
  have : IsDominant (r ≫ U.1.ι) := by
    rw [show r ≫ U.1.ι = V.1.ι ≫ f from f.resLE_comp_ι hVU]
    infer_instance
  let : IsDominant r := IsDominant.of_comp_of_isOpenImmersion r U.1.ι
  let : IsSchemeTheoreticallyDominant r := IsSchemeTheoreticallyDominant.of_isDominant r
  have hi : Function.Injective (f.appLE U.1 V.1 hVU) := by
    have hr := r.app_injective (⊤ : U.1.toScheme.Opens)
    change Function.Injective ((f.resLE U.1 V.1 hVU).app ⊤) at hr
    rw [Scheme.Hom.resLE_app_top] at hr
    have hh : Function.Injective
        (U.1.topIso.inv ≫ (U.1.topIso.hom ≫ f.appLE U.1 V.1 hVU ≫ V.1.topIso.inv)) :=
      hr.comp (ConcreteCategory.bijective_of_isIso U.1.topIso.inv).injective
    have he : U.1.topIso.inv ≫
        (U.1.topIso.hom ≫ f.appLE U.1 V.1 hVU ≫ V.1.topIso.inv) =
        f.appLE U.1 V.1 hVU ≫ V.1.topIso.inv := by simp
    rw [he] at hh
    intro a b hab
    exact hh (congrArg V.1.topIso.inv hab)
  have hgn : g ≠ 0 := nonZeroDivisors.ne_zero hg
  have hfn : (f.appLE U.1 V.1 hVU) g ≠ 0 := fun h => hgn (hi (h.trans (map_zero _).symm))
  refine ⟨V, hxW, (f.appLE U.1 V.1 hVU) g,
    mem_nonZeroDivisors_of_ne_zero hfn, ?_⟩
  rw [J.comap_ideal_of_affine_opens f V U hVU,
    hJU, Ideal.map_span, Set.image_singleton]

end AlgebraicGeometry.Scheme.IdealSheafData

namespace EnvelopeProperty.IntegralSchemeNormalization
variable (Y : Scheme.{u}) [IsIntegral Y]

/-- The actual original generic-field normalization retains every original
Cartier ideal, without a finite-normalization or flatness assumption. -/
theorem cartier_comap {J : Y.IdealSheafData} (hJ : J.IsInvertible) :
    (J.comap (projection Y)).IsInvertible := by
  let : IsDominant (projection Y) := ⟨(projection_surjective Y).denseRange⟩
  exact hJ.comap_of_dominant_integral (projection Y)

end EnvelopeProperty.IntegralSchemeNormalization
