/-
Copyright (c) 2026. All rights reserved.
-/
import EnvelopeProperty.Algebra.RegularPrincipalIdealTensor
import EnvelopeProperty.AlgGeom.CartierModuleFlatPullback

open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace TensorProduct
noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
namespace AlgebraicGeometry.Scheme.IdealSheafData
variable {X Y : Scheme.{u}}

/-- Every original affine principal equation of an actual effective Cartier
ideal is regular, including arbitrary nonreduced schemes and empty opens. -/
theorem IsInvertible.generator_mem_nonZeroDivisors {J : X.IdealSheafData}
    (hJ : J.IsInvertible) (U : X.affineOpens) (g : Γ(X, U))
    (hJU : J.ideal U = Ideal.span {g}) : g ∈ nonZeroDivisors Γ(X, U) := by
  have hc : ∀ a : Γ(X, U), g * a = 0 → a = 0 := by
    intro a ha
    apply X.IsSheaf.section_ext
    intro x hx
    obtain ⟨W, hxW, h, hh, hJW⟩ := hJ x
    obtain ⟨s, t, hst, hxs⟩ := exists_basicOpen_le_affine_inter U.2 W.2 x ⟨hx, hxW⟩
    let V := X.affineBasicOpen s
    have hVU : V.1 ≤ U.1 := X.basicOpen_le s
    have hq : ∃ q ∈ nonZeroDivisors Γ(X, V), J.ideal V = Ideal.span {q} := by
      have key : ∀ (O : X.Opens) (hO : IsAffineOpen O), O = X.basicOpen t →
          ∃ q ∈ nonZeroDivisors Γ(X, O), J.ideal ⟨O, hO⟩ = Ideal.span {q} := by
        rintro O hO rfl
        exact exists_regular_generator_affineBasicOpen J W hh hJW t
      exact key V.1 V.2 hst
    obtain ⟨q, hq, hJV⟩ := hq
    let ρ := (X.presheaf.map (homOfLE hVU).op).hom
    have hVg : J.ideal V = Ideal.span {ρ g} := by
      rw [← J.map_ideal hVU, hJU, Ideal.map_span, Set.image_singleton]
      rfl
    have hmem : q ∈ Ideal.span {ρ g} := by
      rw [← hVg, hJV]
      exact Ideal.mem_span_singleton_self q
    obtain ⟨b, hb⟩ := Submodule.mem_span_singleton.mp hmem
    have hga : ρ g * ρ a = 0 := by rw [← map_mul, ha, map_zero]
    have hqa : (ρ a) * q = 0 := by
      calc
        ρ a * q = ρ a * (b * ρ g) := by rw [← hb]; rfl
        _ = b * (ρ g * ρ a) := by ring
        _ = 0 := by rw [hga, mul_zero]
    refine ⟨V.1, hVU, hxs, ?_⟩
    change ρ a = ρ 0
    rw [map_zero]
    exact (mul_right_mem_nonZeroDivisors_eq_zero_iff hq).mp hqa
  exact mem_nonZeroDivisors_iff.mpr ⟨hc, fun a ha => hc a (by rwa [mul_comm])⟩

/-- Affine regular-principal calculation of the original canonical map. -/
private theorem affinePrincipalComparison_isIso [IsAffine X] [IsAffine Y]
    {I : Y.IdealSheafData} (hI : I.IsInvertible) (f : X ⟶ Y)
    (hf : (I.comap f).IsInvertible) (g : Γ(Y, (⊤ : Y.Opens)))
    (hg : g ∈ nonZeroDivisors Γ(Y, (⊤ : Y.Opens)))
    (hgen : I.ideal ⟨⊤, isAffineOpen_top Y⟩ = Ideal.span {g}) :
    IsIso (I.toModulesComapPullbackMap f) := by
  let U : X.affineOpens := ⟨⊤, isAffineOpen_top X⟩
  let V : Y.affineOpens := ⟨⊤, isAffineOpen_top Y⟩
  let := f.appTop.hom.toAlgebra
  have hcomap : (I.comap f).ideal U = Ideal.span {f.appTop.hom g} := by
    rw [I.comap_ideal_top_of_isAffine_native f, hgen, Ideal.map_span, Set.image_singleton]
  have hfg : f.appTop.hom g ∈ nonZeroDivisors Γ(X, U) :=
    hf.generator_mem_nonZeroDivisors U _ hcomap
  have : I.toModules.IsLocallyFree := hI.isLocallyFree_toModules
  have : (I.comap f).toModules.IsLocallyFree := hf.isLocallyFree_toModules
  have : ((Scheme.Modules.pullback f).obj I.toModules).IsQuasicoherent :=
    Scheme.Modules.isQuasicoherent_pullback_of_isAffine f I.toModules
  let e := Scheme.Modules.affinePullbackΓIso f I.toModules
  let a := ((I.toModulesSectionsEquiv V).baseChange Γ(Y, V) Γ(X, U)).trans
    ((EnvelopeProperty.IdealTensorBaseChange.equivOfRegularGenerator Γ(X, U)
      (I.ideal V) g hg hgen hfg).trans
      ((LinearEquiv.ofEq _ _ (I.comap_ideal_top_of_isAffine_native f).symm).trans
        ((I.comap f).toModulesSectionsEquiv U).symm))
  have ha (s : Γ(X, U)) (x : Γ(I.toModules, (⊤ : Y.Opens))) :
      (show (I.comap f).toSubmodule.obj (op (⊤ : X.Opens)) from
        a (s ⊗ₜ[Γ(Y, V)] x)).1 = s * f.appTop.hom
          (x : I.toSubmodule.obj (op (⊤ : Y.Opens))).1 := by
    simp only [a, LinearEquiv.trans_apply, LinearEquiv.baseChange_tmul]
    exact EnvelopeProperty.IdealTensorBaseChange.equivOfRegularGenerator_tmul
      Γ(X, U) (I.ideal V) g hg hgen hfg s _
  have h : ∀ t, (I.toModulesComapPullbackMap f).app ⊤ (e.hom t) = a t := by
    intro t
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul s x =>
      apply Subtype.ext
      exact (I.toModulesComapPullbackMap_affine_tmul f s x).trans (ha s x).symm
    | add x y hx hy => simp only [map_add, hx, hy]
  apply Scheme.Modules.isIso_of_isQuasicoherent_of_isIso_app_top
  rw [ConcreteCategory.isIso_iff_bijective]
  constructor
  · intro x y hxy
    obtain ⟨s, rfl⟩ := e.toLinearEquiv.surjective x
    obtain ⟨t, rfl⟩ := e.toLinearEquiv.surjective y
    exact congrArg e.hom (a.injective ((h s).symm.trans (hxy.trans (h t))))
  · intro y
    obtain ⟨t, ht⟩ := a.surjective y
    exact ⟨e.hom t, (h t).trans ht⟩

/-- The actual geometric Cartier property of the original ideal comap
makes the original canonical module comparison an isomorphism for ANY f.
No flatness, reducedness, integrality, Noetherian or QC assumption is needed. -/
theorem IsInvertible.toModulesComapPullbackMap_isIso_of_isInvertible_comap
    {I : Y.IdealSheafData} (hI : I.IsInvertible) (f : X ⟶ Y)
    (hf : (I.comap f).IsInvertible) : IsIso (I.toModulesComapPullbackMap f) := by
  classical
  have hloc : ∀ x : X, ∃ V : X.affineOpens, x ∈ V.1 ∧
      IsIso ((Scheme.Modules.restrictFunctor V.1.ι).map (I.toModulesComapPullbackMap f)) := by
    intro x
    obtain ⟨U, hxU, g, hg, hIU⟩ := hI (f x)
    obtain ⟨W, hW, hxW, hWU⟩ := exists_isAffineOpen_mem_and_subset
      (show x ∈ f ⁻¹ᵁ U.1 from hxU)
    let V : X.affineOpens := ⟨W, hW⟩
    have hVU : V.1 ≤ f ⁻¹ᵁ U.1 := hWU
    let r := f.resLE U.1 V.1 hVU
    have : IsAffine U.1 := U.2
    have : IsAffine V.1 := V.2
    have hIUr : (I.comap U.1.ι).IsInvertible := hI.comap_of_flat U.1.ι
    have hfr : ((I.comap U.1.ι).comap r).IsInvertible := by
      have he : (I.comap U.1.ι).comap r = (I.comap f).comap V.1.ι := by
        rw [← comap_comp, ← comap_comp, f.resLE_comp_ι hVU]
      rw [he]
      exact hf.comap_of_flat V.1.ι
    have hgen : (I.comap U.1.ι).ideal ⟨⊤, isAffineOpen_top U.1.toScheme⟩ =
        Ideal.span {U.1.topIso.inv.hom g} := by
      have ht := congrArg (Ideal.map U.1.topIso.inv.hom)
        (I.comap_open_ideal_top_map U.2)
      rw [Ideal.map_map] at ht
      have he : U.1.topIso.inv.hom.comp U.1.topIso.hom.hom =
          RingHom.id Γ(U.1.toScheme, (⊤ : U.1.toScheme.Opens)) := by
        ext a
        exact ConcreteCategory.congr_hom U.1.topIso.hom_inv_id a
      rw [he, Ideal.map_id] at ht
      rw [ht, hIU, Ideal.map_span, Set.image_singleton]
    have hgreg : U.1.topIso.inv.hom g ∈
        nonZeroDivisors Γ(U.1.toScheme, (⊤ : U.1.toScheme.Opens)) :=
      map_mem_nonZeroDivisors_of_ringEquiv U.1.topIso.symm.commRingCatIsoToRingEquiv hg
    have hr : IsIso ((I.comap U.1.ι).toModulesComapPullbackMap r) :=
      affinePrincipalComparison_isIso hIUr r hfr _ hgreg hgen
    have hc : IsIso (I.toModulesComapPullbackMap (r ≫ U.1.ι)) :=
      I.toModulesComapPullbackMap_isIso_comp r U.1.ι
        (I.toModulesComapPullbackMap_isIso_of_isOpenImmersion U.1.ι) hr
    have hc' : IsIso (I.toModulesComapPullbackMap (V.1.ι ≫ f)) := by
      exact (congrArg (fun q : V.1.toScheme ⟶ Y =>
        IsIso (I.toModulesComapPullbackMap q)) (f.resLE_comp_ι hVU)).mp hc
    have hp : IsIso ((Scheme.Modules.pullback V.1.ι).map (I.toModulesComapPullbackMap f)) :=
      I.toModulesComapPullbackMap_isIso_pullback_of_comp V.1.ι f hc'
        ((I.comap f).toModulesComapPullbackMap_isIso_of_isOpenImmersion V.1.ι)
    exact ⟨V, hxW,
      (NatIso.isIso_map_iff (Scheme.Modules.restrictFunctorIsoPullback V.1.ι) _).mpr hp⟩
  choose V hxV hV using hloc
  apply Scheme.Modules.isIso_of_isIso_restrict (I.toModulesComapPullbackMap f)
    (fun x => (V x).1) _ hV
  apply top_unique
  intro x _hx
  exact Opens.mem_iSup.mpr ⟨x, hxV x⟩

end AlgebraicGeometry.Scheme.IdealSheafData
