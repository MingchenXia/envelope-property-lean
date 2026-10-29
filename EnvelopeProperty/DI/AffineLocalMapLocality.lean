import EnvelopeProperty.DI.AffineLocalMapRestriction

/-! # Source-quasicoherent affine detection of the original local adjoints

No quasicoherence of an open pushforward target is assumed. The original
restriction adjunction and actual chart factorization detect the maps.
-/
noncomputable section
namespace EnvelopeProperty.DI.AffineLocalMapRestriction
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open CechDegreeOneDescent
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem restrict_injective_into_open_pushforward
    {A B Z : Scheme.{u}} (i : A ⟶ Z) (j : B ⟶ Z) (r : B ⟶ A)
    [IsOpenImmersion i] [IsOpenImmersion j] [IsOpenImmersion r] (h : r ≫ i = j)
    (M : Z.Modules) (N : B.Modules)
    (a b : M ⟶ (Scheme.Modules.pushforward j).obj N)
    (hi : (Scheme.Modules.restrictFunctor i).map a = (Scheme.Modules.restrictFunctor i).map b) :
    a = b := by
  let e : Scheme.Modules.restrictFunctor j ≅
      Scheme.Modules.restrictFunctor i ⋙ Scheme.Modules.restrictFunctor r :=
    Scheme.Modules.restrictFunctorCongr h.symm ≪≫ Scheme.Modules.restrictFunctorComp r i
  have hj : (Scheme.Modules.restrictFunctor j).map a = (Scheme.Modules.restrictFunctor j).map b := by
    apply (cancel_mono (e.hom.app ((Scheme.Modules.pushforward j).obj N))).1
    have he := congrArg (fun t => (Scheme.Modules.restrictFunctor r).map t) hi
    exact (e.hom.naturality a).trans
      ((congrArg (fun t => e.hom.app M ≫ t) he).trans (e.hom.naturality b).symm)
  apply ((Scheme.Modules.restrictAdjunction j).homEquiv M N).symm.injective
  simpa only [Adjunction.homEquiv_counit] using
    congrArg (fun t => t ≫ (Scheme.Modules.restrictAdjunction j).counit.app N) hj

/-- Equality on original sections of ONE containing affine detects entire local maps.
The only quasicoherence premise is on the original source, never on the pushed target. -/
theorem localMap_ext_of_adjoint_at_affine
    {Z : Scheme.{u}} {U V : Z.Opens} (hU : IsAffineOpen U) (hVU : V ≤ U)
    (M N : Z.Modules) [((Scheme.Modules.restrictFunctor hU.fromSpec).obj M).IsQuasicoherent]
    (φ ψ : LocalMap M N V)
    (hΓ : (localAdjoint V φ).val.app (op U) = (localAdjoint V ψ).val.app (op U)) :
    φ = ψ := by
  let P := Cartier.DeligneIllusieLocalContinuationCechModules.factor N V
  let a : M ⟶ P := localAdjoint V φ
  let b : M ⟶ P := localAdjoint V ψ
  let F := Scheme.Modules.restrictFunctor hU.fromSpec
  have hsΓ : (moduleSpecΓFunctor (R := Γ(Z,U))).map (F.map a) =
      (moduleSpecΓFunctor (R := Γ(Z,U))).map (F.map b) := by
    apply (cancel_mono (Cartier.GeometricAffineHomology.moduleSectionsIso hU P).hom).1
    have ha := moduleSections_naturality hU M P a
    have hb := moduleSections_naturality hU M P b
    exact ha.trans ((congrArg
      (fun t => (Cartier.GeometricAffineHomology.moduleSectionsIso hU M).hom ≫ t) hΓ).trans hb.symm)
  have hs : F.map a = F.map b :=
    specMap_ext Γ(Z,U) (F.obj M) (F.obj P) (F.map a) (F.map b) hsΓ
  let r : V.toScheme ⟶ Spec Γ(Z,U) := Z.homOfLE hVU ≫ hU.isoSpec.hom
  have hr : r ≫ hU.fromSpec = V.ι := by
    dsimp only [r]
    rw [Category.assoc, hU.isoSpec_hom_fromSpec, Z.homOfLE_ι]
  let : IsOpenImmersion (r ≫ hU.fromSpec) := hr.symm ▸ inferInstance
  let : IsOpenImmersion r := IsOpenImmersion.of_comp r hU.fromSpec
  have hab : a = b := restrict_injective_into_open_pushforward hU.fromSpec V.ι r hr
    M (N.restrict V.ι) a b hs
  apply ((Scheme.Modules.restrictAdjunction V.ι).homEquiv M (N.restrict V.ι)).injective
  exact hab



/-- The same detector stated directly on original abelian sections. -/
theorem localMap_ext_of_adjoint_sections
    {Z : Scheme.{u}} {U V : Z.Opens} (hU : IsAffineOpen U) (hVU : V ≤ U)
    (M N : Z.Modules) [((Scheme.Modules.restrictFunctor hU.fromSpec).obj M).IsQuasicoherent]
    (φ ψ : LocalMap M N V)
    (hΓ : (localAdjoint V φ).app U = (localAdjoint V ψ).app U) : φ = ψ := by
  apply localMap_ext_of_adjoint_at_affine hU hVU M N φ ψ
  exact (forget₂ (ModuleCat (Z.ringCatSheaf.obj.obj (op U))) AddCommGrpCat).map_injective hΓ

section OriginalReadback
variable {Z : Scheme.{u}} {U : Z.Opens} (hU : IsAffineOpen U)

/-- Naturality of the original inverse-chart comparison for actual global maps. -/
theorem specReadback_naturality (M N : Z.Modules) (a : M ⟶ N) :
    (Scheme.Modules.restrictFunctor hU.isoSpec.inv).map
        ((Scheme.Modules.restrictFunctor U.ι).map a) ≫ (specReadbackIso hU N).hom =
      (specReadbackIso hU M).hom ≫
        (Scheme.Modules.restrictFunctor hU.fromSpec).map a := by
  let G := Scheme.Modules.restrictFunctor hU.isoSpec.inv
  have hc := chartRestriction_naturality hU M N a
  have hc' := congrArg (fun t => G.map t) hc
  simp only [Functor.map_comp] at hc'
  have he := (specReturn hU).hom.naturality
    ((Scheme.Modules.restrictFunctor hU.fromSpec).map a)
  change G.map ((Scheme.Modules.restrictFunctor U.ι).map a) ≫
      G.map (chartRestrictionIso hU N).hom ≫ (specReturn hU).hom.app _ =
    (G.map (chartRestrictionIso hU M).hom ≫ (specReturn hU).hom.app _) ≫ _
  change G.map ((Scheme.Modules.restrictFunctor hU.isoSpec.hom).map
      ((Scheme.Modules.restrictFunctor hU.fromSpec).map a)) ≫
      (specReturn hU).hom.app _ = (specReturn hU).hom.app _ ≫ _ at he
  rw [← Category.assoc, hc', Category.assoc, he, Category.assoc]
  rfl

/-- Readback of an actual restricted global map is its original section map. -/
theorem sectionReadback_restrict (M N : Z.Modules) (a : M ⟶ N) :
    sectionReadback hU M N ((Scheme.Modules.restrictFunctor U.ι).map a) =
      a.val.app (op U) := by
  have h := specReadback_naturality hU M N a
  have h' := congrArg (fun t => (specReadbackIso hU M).inv ≫ t) h
  simp only [Iso.inv_hom_id_assoc] at h'
  unfold sectionReadback
  rw [h']
  have hn := moduleSections_naturality hU M N a
  rw [hn, Iso.inv_hom_id_assoc]

theorem sectionReadback_comp (M N P : Z.Modules)
    (a : LocalMap M N U) (b : LocalMap N P U) :
    sectionReadback hU M P (a ≫ b) =
      sectionReadback hU M N a ≫ sectionReadback hU N P b := by
  have hc : (moduleSpecΓFunctor (R := Γ(Z,U))).map (specReadbackIso hU N).hom ≫
      (moduleSpecΓFunctor (R := Γ(Z,U))).map (specReadbackIso hU N).inv = 𝟙 _ := by
    rw [← Functor.map_comp, Iso.hom_inv_id, CategoryTheory.Functor.map_id]
  simp only [sectionReadback, Functor.map_comp, Category.assoc, Iso.hom_inv_id_assoc]
  rw [reassoc_of% hc]

/-- The original local adjoint, restricted back to the same open, equals
its original map followed by the original unit. -/
theorem restrict_localAdjoint (M N : Z.Modules) (a : LocalMap M N U) :
    (Scheme.Modules.restrictFunctor U.ι).map (localAdjoint U a) =
      a ≫ (Scheme.Modules.restrictFunctor U.ι).map
        (Cartier.DeligneIllusieLocalContinuationCechAugmentation.factorUnit N U) := by
  let adj := Scheme.Modules.restrictAdjunction U.ι
  apply (cancel_mono (adj.counit.app (N.restrict U.ι))).1
  have ha := adj.homEquiv_counit M (N.restrict U.ι) (localAdjoint U a)
  have hi : (adj.homEquiv M (N.restrict U.ι)).symm (localAdjoint U a) = a :=
    (adj.homEquiv M (N.restrict U.ι)).symm_apply_apply a
  rw [← ha, hi, Category.assoc]
  change a = a ≫ ((Scheme.Modules.restrictFunctor U.ι).map (adj.unit.app N) ≫ _)
  rw [adj.left_triangle_components, Category.comp_id]

/-- Exact original-section formula for a local adjoint, with its original unit. -/
theorem localAdjoint_sections (M N : Z.Modules) (a : LocalMap M N U) :
    (localAdjoint U a).val.app (op U) =
      sectionReadback hU M N a ≫
        (Cartier.DeligneIllusieLocalContinuationCechAugmentation.factorUnit N U).val.app (op U) := by
  rw [← sectionReadback_restrict hU M _ (localAdjoint U a),
    restrict_localAdjoint, sectionReadback_comp, sectionReadback_restrict]

end OriginalReadback


open Cartier.DeligneIllusieLocalContinuationCechModules
open Cartier.DeligneIllusieLocalContinuationCechAugmentation

private theorem factor_restriction_isIso {Z : Scheme.{u}} (N : Z.Modules)
    {U V : Z.Opens} (h : V ≤ U) :
    IsIso ((factor N V).presheaf.map (homOfLE h).op) := by
  have hc : V.ι ''ᵁ (V.ι ⁻¹ᵁ U) = V.ι ''ᵁ (V.ι ⁻¹ᵁ V) := by
    simp only [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι,
      inf_eq_left.mpr h, inf_idem]
  dsimp only [factor]
  rw [Scheme.Modules.pushforward_obj_presheaf_map, Scheme.Modules.restrict_map]
  have he : (V.ι.opensFunctor).map
      ((Opens.map V.ι.base).map (homOfLE h)) = eqToHom hc.symm :=
    Subsingleton.elim _ _
  rw [he]
  infer_instance

private theorem affineAdjoint_restrict_sections {Z : Scheme.{u}} {U V : Z.Opens}
    (hU : IsAffineOpen U) (hV : IsAffineOpen V) (h : V ≤ U)
    (M N : Z.Modules)
    [((Scheme.Modules.restrictFunctor hU.fromSpec).obj M).IsQuasicoherent]
    [((Scheme.Modules.restrictFunctor hV.fromSpec).obj M).IsQuasicoherent]
    (lU : M.val.obj (op U) ⟶ N.val.obj (op U))
    (lV : M.val.obj (op V) ⟶ N.val.obj (op V))
    (hcomm : ∀ s, N.presheaf.map (homOfLE h).op (lU.hom s) =
      lV.hom (M.presheaf.map (homOfLE h).op s)) :
    (localAdjoint U (affineLocalMap hU M N lU)).app U ≫ (factorMap N h).app U =
      (localAdjoint V (affineLocalMap hV M N lV)).app U := by
  let φU := affineLocalMap hU M N lU
  let φV := affineLocalMap hV M N lV
  let lUa : Γ(M,U) ⟶ Γ(N,U) := (forget₂ (ModuleCat _) AddCommGrpCat).map lU
  let lVa : Γ(M,V) ⟶ Γ(N,V) := (forget₂ (ModuleCat _) AddCommGrpCat).map lV
  have haU : (localAdjoint U φU).app U = lUa ≫ (factorUnit N U).app U := by
    have ha := localAdjoint_sections hU M N φU
    rw [sectionReadback_affineLocalMap] at ha
    exact congrArg (fun a => (forget₂ (ModuleCat _) AddCommGrpCat).map a) ha
  have haV : (localAdjoint V φV).app V = lVa ≫ (factorUnit N V).app V := by
    have ha := localAdjoint_sections hV M N φV
    rw [sectionReadback_affineLocalMap] at ha
    exact congrArg (fun a => (forget₂ (ModuleCat _) AddCommGrpCat).map a) ha
  have hs : lUa ≫ N.presheaf.map (homOfLE h).op =
      M.presheaf.map (homOfLE h).op ≫ lVa := by
    apply ConcreteCategory.hom_ext
    intro s
    exact hcomm s
  have he : (localAdjoint U φU).app U ≫ (factorMap N h).app U =
      (localAdjoint V φV).app U := by
    let P := factor N V
    let r := P.presheaf.map (homOfLE h).op
    let : IsIso r := factor_restriction_isIso N h
    apply (cancel_mono r).1
    have hu := (factorUnit N V).mapPresheaf.naturality (homOfLE h).op
    have hv := (localAdjoint V φV).mapPresheaf.naturality (homOfLE h).op
    have hf := congrArg (fun a : N ⟶ P => a.app U) (factorUnit_comp_factorMap N h)
    change (factorUnit N U).app U ≫ (factorMap N h).app U =
      (factorUnit N V).app U at hf
    calc
      _ = lUa ≫ (((factorUnit N U).app U ≫ (factorMap N h).app U) ≫ r) := by
        rw [haU]
        simp only [Category.assoc]
      _ = lUa ≫ ((factorUnit N V).app U ≫ r) := by rw [hf]
      _ = lUa ≫ (N.presheaf.map (homOfLE h).op ≫ (factorUnit N V).app V) := by
        exact congrArg (fun t => lUa ≫ t) hu.symm
      _ = (M.presheaf.map (homOfLE h).op ≫ lVa) ≫ (factorUnit N V).app V := by
        rw [← Category.assoc, hs]
      _ = M.presheaf.map (homOfLE h).op ≫ (localAdjoint V φV).app V := by
        rw [Category.assoc, ← haV]
      _ = _ := hv
  exact he

/-- The native original affine construction respects the original section square.
Only the original source is quasicoherent; the target and its pushforwards are arbitrary. -/
theorem affineLocalMap_restrict {Z : Scheme.{u}} {U V : Z.Opens}
    (hU : IsAffineOpen U) (hV : IsAffineOpen V) (h : V ≤ U)
    (M N : Z.Modules)
    [((Scheme.Modules.restrictFunctor hU.fromSpec).obj M).IsQuasicoherent]
    [((Scheme.Modules.restrictFunctor hV.fromSpec).obj M).IsQuasicoherent]
    (lU : M.val.obj (op U) ⟶ N.val.obj (op U))
    (lV : M.val.obj (op V) ⟶ N.val.obj (op V))
    (hcomm : ∀ s, N.presheaf.map (homOfLE h).op (lU.hom s) =
      lV.hom (M.presheaf.map (homOfLE h).op s)) :
    localRestrict h (affineLocalMap hU M N lU) = affineLocalMap hV M N lV := by
  have he := affineAdjoint_restrict_sections hU hV h M N lU lV hcomm
  apply localMap_ext_of_adjoint_sections hU h M N
  rw [localAdjoint_localRestrict, Scheme.Modules.Hom.comp_app]
  exact he

end EnvelopeProperty.DI.AffineLocalMapRestriction


