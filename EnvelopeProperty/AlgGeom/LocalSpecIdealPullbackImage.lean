/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.AlgGeom.AffineIdealPullbackImage
import Mathlib.AlgebraicGeometry.Stalk

/-! # Actual whole ideal pullback images over original local-ring spectra -/

open CategoryTheory AlgebraicGeometry Opposite
noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace AlgebraicGeometry.Scheme
variable {A : Type u} [CommRing A] [IsLocalRing A] {X : Scheme.{u}}

/-- An ACTUAL morphism from an ORIGINAL local spectrum factors through
EVERY genuine open neighborhood of the actual closed-point image. -/
theorem exists_lift_open_of_closedPoint_mem (f : Spec (CommRingCat.of A) ⟶ X)
    (U : X.Opens) (hU : f (IsLocalRing.closedPoint A) ∈ U) :
    ∃ g : Spec (CommRingCat.of A) ⟶ U.toScheme, g ≫ U.ι = f := by
  have hp : f ⁻¹ᵁ U = ⊤ := preimage_eq_top_of_closedPoint_mem f hU
  have hr : Set.range f ⊆ Set.range U.ι := by
    rw [U.range_ι]
    rintro _ ⟨x, rfl⟩
    have hx : x ∈ f ⁻¹ᵁ U := by rw [hp]; trivial
    exact hx
  exact ⟨IsOpenImmersion.lift U.ι f hr, IsOpenImmersion.lift_fac U.ι f hr⟩

private theorem localSpec_moduleIso_app_injective {T : Scheme.{u}} {M N : T.Modules}
    (e : M ≅ N) (W : T.Opens) : Function.Injective ((e.hom.val.app (op W)).hom) := by
  intro x z hxz
  have h := congrArg (fun s => (e.inv.val.app (op W)).hom s) hxz
  have hi (s : Γ(M, W)) :
      (e.inv.val.app (op W)).hom ((e.hom.val.app (op W)).hom s) = s := by
    exact congrArg (fun q => (q.val.app (op W)).hom s) e.hom_inv_id
  exact (hi x).symm.trans (h.trans (hi z))

namespace IdealSheafData

private theorem module_app_surjective_of_comparison {S : Scheme.{u}}
    {M N P Q R : S.Modules} (p : M ≅ N) (b : M ≅ P) (e : Q ≅ R)
    (φ : N ⟶ Q) (ψ : P ⟶ R)
    (hc : p.hom ≫ φ ≫ e.hom = b.hom ≫ ψ)
    (hψ : Function.Surjective (ψ.app (⊤ : S.Opens))) :
    Function.Surjective (φ.app (⊤ : S.Opens)) := by
  intro t
  obtain ⟨r, hr⟩ := hψ ((e.hom.val.app (op ⊤)).hom t)
  let s := (b.inv.val.app (op ⊤)).hom r
  refine ⟨(p.hom.val.app (op ⊤)).hom s, ?_⟩
  apply localSpec_moduleIso_app_injective e ⊤
  have h := congrArg (fun q => (q.val.app (op ⊤)).hom s) hc
  have hb : (b.hom.val.app (op ⊤)).hom s = r :=
    congrArg (fun q => (q.val.app (op ⊤)).hom r) b.inv_hom_id
  change (e.hom.val.app (op ⊤)).hom
      ((φ.val.app (op ⊤)).hom ((p.hom.val.app (op ⊤)).hom s)) =
    (ψ.val.app (op ⊤)).hom ((b.hom.val.app (op ⊤)).hom s) at h
  exact h.trans ((congrArg ((ψ.val.app (op ⊤)).hom) hb).trans hr)

private theorem comp_toModulesComapPullbackMap_appTop_surjective
    {S T Z : Scheme.{u}} [IsAffine S] [IsAffine T]
    (I : Z.IdealSheafData) (a : S ⟶ T) (b : T ⟶ Z) [IsOpenImmersion b] :
    Function.Surjective ((I.toModulesComapPullbackMap (a ≫ b)).app (⊤ : S.Opens)) := by
  have : IsIso (I.toModulesComapPullbackMap b) :=
    I.toModulesComapPullbackMap_isIso_of_isOpenImmersion b
  exact module_app_surjective_of_comparison
    ((Modules.pullbackComp a b).app I.toModules)
    (asIso ((Modules.pullback a).map (I.toModulesComapPullbackMap b)))
    (toModulesEqualityIso _ _ (I.comap_comp a b))
    (I.toModulesComapPullbackMap (a ≫ b)) ((I.comap b).toModulesComapPullbackMap a)
    (I.toModulesComapPullbackMap_comp a b)
    ((I.comap b).affine_toModulesComapPullbackMap_appTop_surjective a)


/-- For ANY original ideal on ANY original scheme, its ACTUAL canonical
pullback to an original local spectrum is onto the WHOLE original ideal
section module, with no flatness, Cartier or affine-target assumption. -/
theorem localSpec_toModulesComapPullbackMap_appTop_surjective
    (I : X.IdealSheafData) (f : Spec (CommRingCat.of A) ⟶ X) :
    Function.Surjective ((I.toModulesComapPullbackMap f).app (⊤ : (Spec (CommRingCat.of A)).Opens)) := by
  obtain ⟨U, hU⟩ := exists_affineOpens_mem (f (IsLocalRing.closedPoint A))
  obtain ⟨g, hg⟩ := exists_lift_open_of_closedPoint_mem f U.1 hU
  rw [← hg]
  let : IsAffine U.1.toScheme := U.2
  exact comp_toModulesComapPullbackMap_appTop_surjective I g U.1.ι

/-- Over the original local spectrum, the ENTIRE coefficient image of
the ACTUAL inclusion equals the WHOLE geometric pullback ideal. -/
theorem localSpecPullbackInclusionRange_eq (I : X.IdealSheafData)
    (f : Spec (CommRingCat.of A) ⟶ X) :
    I.affinePullbackInclusionRange f =
      (I.comap f).ideal ⟨⊤, isAffineOpen_top (Spec (CommRingCat.of A))⟩ := by
  apply le_antisymm
  · rintro a ⟨s, rfl⟩
    exact ((I.comap f).toModulesSectionsEquiv ⟨⊤, isAffineOpen_top _⟩
      ((I.toModulesComapPullbackMap f).app ⊤ s)).property
  · intro a ha
    let t : Γ((I.comap f).toModules, (⊤ : (Spec (CommRingCat.of A)).Opens)) :=
      ((I.comap f).toModulesSectionsEquiv ⟨⊤, isAffineOpen_top _⟩).symm ⟨a, ha⟩
    obtain ⟨s, hs⟩ := I.localSpec_toModulesComapPullbackMap_appTop_surjective f t
    refine ⟨s, ?_⟩
    exact congrArg (fun z => (z : (I.comap f).toSubmodule.obj (op ⊤)).1) hs

private theorem module_range_eq_span_frame {S : Scheme.{u}} {M : S.Modules}
    (e : M ≅ Modules.unitObj S) (φ : M ⟶ Modules.unitObj S) :
    LinearMap.range (show Γ(M, ⊤) →ₗ[Γ(S, ⊤)] Γ(S, ⊤) from (φ.val.app (op ⊤)).hom) =
      Ideal.span {(show Γ(S, ⊤) from ((e.inv ≫ φ).val.app (op ⊤)).hom (1 : Γ(S, ⊤)))} := by
  apply le_antisymm
  · rintro _ ⟨s, rfl⟩
    have hi : (e.inv.val.app (op ⊤)).hom ((e.hom.val.app (op ⊤)).hom s) = s :=
      congrArg (fun q => (q.val.app (op ⊤)).hom s) e.hom_inv_id
    let c : Γ(S, ⊤) := (e.hom.val.app (op ⊤)).hom s
    have hl := ((e.inv ≫ φ).val.app (op ⊤)).hom.map_smul c (1 : Γ(S, ⊤))
    change (φ.val.app (op ⊤)).hom ((e.inv.val.app (op ⊤)).hom
        (c * (1 : Γ(S, ⊤)))) =
      c * (show Γ(S, ⊤) from ((e.inv ≫ φ).val.app (op ⊤)).hom (1 : Γ(S, ⊤))) at hl
    rw [mul_one, hi] at hl
    have hm : c * (show Γ(S, ⊤) from ((e.inv ≫ φ).val.app (op ⊤)).hom (1 : Γ(S, ⊤))) ∈
        Ideal.span {(show Γ(S, ⊤) from ((e.inv ≫ φ).val.app (op ⊤)).hom (1 : Γ(S, ⊤)))} :=
      Ideal.mul_mem_left _ c (Ideal.mem_span_singleton_self _)
    exact hl.symm ▸ hm
  · apply Ideal.span_le.mpr
    rintro r (rfl : r = _)
    exact ⟨(e.inv.val.app (op ⊤)).hom (1 : Γ(S, ⊤)), rfl⟩

/-- The TRUE coefficient in an ACTUAL pulled-back unit frame generates
the ENTIRE geometric ideal on the original local spectrum, even nonflatly. -/
theorem localSpec_pullbackIdeal_eq_span_frame (I : X.IdealSheafData)
    (f : Spec (CommRingCat.of A) ⟶ X)
    (e : (Modules.pullback f).obj I.toModules ≅ Modules.unitObj (Spec (CommRingCat.of A))) :
    (I.comap f).ideal ⟨⊤, isAffineOpen_top (Spec (CommRingCat.of A))⟩ =
      Ideal.span {(show Γ(Spec (CommRingCat.of A), ⊤) from
        ((e.inv ≫ I.pullbackModuleInclusion f).val.app (op ⊤)).hom
          (1 : Γ(Spec (CommRingCat.of A), ⊤)))} := by
  rw [← I.localSpecPullbackInclusionRange_eq f]
  have hr : I.affinePullbackInclusionRange f =
      LinearMap.range (show Γ((Modules.pullback f).obj I.toModules, ⊤) →ₗ[
          Γ(Spec (CommRingCat.of A), ⊤)] Γ(Spec (CommRingCat.of A), ⊤) from
        ((I.pullbackModuleInclusion f).val.app (op ⊤)).hom) := by
    rw [I.pullbackModuleInclusion_eq f]
    rfl
  rw [hr]
  exact module_range_eq_span_frame e (I.pullbackModuleInclusion f)

end IdealSheafData
end AlgebraicGeometry.Scheme
