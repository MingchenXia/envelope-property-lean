import EnvelopeProperty.AlgGeom.ProjectiveCentralFiberEmbeddingNeighborhoodClosedModelScalarActionCover

/-! # Actual finite original whole-model power generators

Every whole evaluation epimorphism below is derived from actual transported
original GLOBAL sections on a true finite original action-open cover.
-/
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
  CartesianMonoidalCategory
open Scheme.Modules
open scoped Polynomial CategoryTheory.MonObj
universe u
namespace EnvelopeProperty.ProjectiveCentralFiberEmbeddingNeighborhoodClosedWholeGenerators
open NativeTestConfiguration CanonicalGeometry SchemeLineSectionEvaluation
open TestConfigurationLaurentExpansionContinuation ProjectiveCentralFiberSectionLifting
open ProjectiveCentralFiberEmbeddingNeighborhoodClosedScalarGroupPoint
open ProjectiveCentralFiberEmbeddingNeighborhoodClosedGroupPointTransport
open ProjectiveCentralFiberEmbeddingNeighborhoodClosedModelScalarActionCover
open ProjectiveCentralFiberEmbeddingNeighborhoodClosedCentralCoordinateFamily
open ProjectiveCentralFiberEmbeddingNeighborhoodClosedCentralSerrePowers
open ProjectiveCentralFiberEmbeddingNeighborhoodClosedMixedCoordinateEmbedding

private def unitTupleMap {Y : Scheme.{u}} {I : Type u} (L : Y.Modules)
    (α : I → (unitObj Y ⟶ L)) : SheafOfModules.free (R := Y.ringCatSheaf) I ⟶ L :=
  L.freeHomEquiv.symm (fun a => L.unitHomEquiv (α a))

private theorem unitTuple_basis {Y : Scheme.{u}} {I : Type u} (L : Y.Modules)
    (α : I → (unitObj Y ⟶ L)) (a : I) :
    SheafOfModules.ιFree a ≫ unitTupleMap L α = α a := by
  apply L.unitHomEquiv.injective
  exact congrFun (L.freeHomEquiv.apply_symm_apply (fun a => L.unitHomEquiv (α a))) a

private theorem unitTuple_epi {Y : Scheme.{u}} {I : Type u} (L : Y.Modules)
    (α : I → (unitObj Y ⟶ L))
    (hcover : ∀ x : Y, ∃ U : Y.Opens, x ∈ U ∧ ∃ a : I,
      IsIso (pullbackSectionHom U.ι (α a))) : Epi (unitTupleMap L α) := by
  let J := {q : Y.Opens × I // IsIso (pullbackSectionHom q.1.ι (α q.2))}
  let U := fun a : J => a.1.1
  have hcov : ∀ x : Y, ∃ (a : J) (y : (U a).toScheme), (U a).ι y = x := by
    intro x
    obtain ⟨V, hx, a, ha⟩ := hcover x
    exact ⟨⟨⟨V,a⟩,ha⟩,⟨x,hx⟩,rfl⟩
  constructor
  intro N f g hfg
  apply SchemeModuleOpenCoverDetection.hom_ext
    (fun a : J => (U a).toScheme) (fun a => (U a).ι) hcov
  intro a
  let F := Scheme.Modules.pullback (U a).ι
  let : IsIso (pullbackSectionHom (U a).ι (α a.1.2)) := a.2
  apply (cancel_epi (pullbackSectionHom (U a).ι (α a.1.2))).mp
  have h : α a.1.2 ≫ f = α a.1.2 ≫ g := by
    have hh := congrArg (fun q => SheafOfModules.ιFree a.1.2 ≫ q) hfg
    have hf : α a.1.2 ≫ f = SheafOfModules.ιFree a.1.2 ≫ (unitTupleMap L α ≫ f) :=
      (congrArg (fun q : unitObj Y ⟶ L => q ≫ f) (unitTuple_basis L α a.1.2).symm).trans
        (Category.assoc _ _ _)
    have hg : α a.1.2 ≫ g = SheafOfModules.ιFree a.1.2 ≫ (unitTupleMap L α ≫ g) :=
      (congrArg (fun q : unitObj Y ⟶ L => q ≫ g) (unitTuple_basis L α a.1.2).symm).trans
        (Category.assoc _ _ _)
    exact hf.trans (hh.trans hg.symm)
  have hh := congrArg F.map h
  have hm : F.map (α a.1.2) ≫ F.map f = F.map (α a.1.2) ≫ F.map g :=
    (F.map_comp (α a.1.2) f).symm.trans (hh.trans (F.map_comp (α a.1.2) g))
  have hp := congrArg (fun q => (pullbackUnitIso (U a).ι).inv ≫ q) hm
  change ((pullbackUnitIso (U a).ι).inv ≫ F.map (α a.1.2)) ≫ F.map f =
    ((pullbackUnitIso (U a).ι).inv ≫ F.map (α a.1.2)) ≫ F.map g
  exact (Category.assoc _ _ _).trans (hp.trans (Category.assoc _ _ _).symm)

private theorem frame_pullback_transport {Y : Scheme.{u}} {L : Y.Modules}
    (a : Y ⟶ Y) (E : (Scheme.Modules.pullback a).obj L ≅ L)
    (α : unitObj Y ⟶ L) (U : Y.Opens) (hα : IsIso (pullbackSectionHom U.ι α)) :
    IsIso (pullbackSectionHom (a ⁻¹ᵁ U).ι (pullbackSectionHom a α ≫ E.hom)) := by
  let V := a ⁻¹ᵁ U
  have hf : IsIso (pullbackSectionHom (V.ι ≫ a) α) :=
    SchemeLineSectionFactorization.isIso_pullbackSectionHom_factor
      (a ∣_ U) U.ι (V.ι ≫ a) (morphismRestrict_ι a U) α hα
  let := hf
  have hc : IsIso (pullbackSectionHom V.ι (pullbackSectionHom a α) ≫
      (Scheme.Modules.pullbackComp V.ι a).hom.app L) := by
    rw [pullbackSectionHom_comp]
    infer_instance
  let := hc
  let : IsIso (pullbackSectionHom V.ι (pullbackSectionHom a α)) :=
    IsIso.of_isIso_comp_right _ ((Scheme.Modules.pullbackComp V.ι a).hom.app L)
  have he : pullbackSectionHom V.ι (pullbackSectionHom a α ≫ E.hom) =
      pullbackSectionHom V.ι (pullbackSectionHom a α) ≫
        (Scheme.Modules.pullback V.ι).map E.hom := by
    simp only [pullbackSectionHom, Functor.map_comp, Category.assoc]
  rw [he]
  infer_instance

private theorem sectionHom_top {Y : Scheme.{u}} (L : Y.Modules) (τ : Γ(L,⊤)) :
    (L.unitHomEquiv (SchemeModuleGlobalSections.sectionHom L τ)).val (op ⊤) = τ := by
  unfold SchemeModuleGlobalSections.sectionHom
  rw [Equiv.apply_symm_apply]
  change L.presheaf.map (𝟙 (op (⊤ : Y.Opens))) τ = τ
  simp

/-- Ordinary central generators and H1 vanishing give TRUE finite generators
on the ENTIRE SAME original model power, by actual original action transport.
No nearby/whole generation or section matching certificate is supplied. -/
theorem exists_finite_power_generators_whole_model
    {k : Type u} [Field k] [Infinite k] {X : Over (Spec (.of k))}
    (C : NativeTestConfiguration.TestConfiguration k X)
    [IsIntegral C.total] [IsDominant C.projection]
    (M : C.total.Modules) (hM : IsInvertible M)
    (linearization :
      (Scheme.Modules.pullback (originalTestConfigurationTotalAction C).left).obj M ≅
        (Scheme.Modules.pullback (snd (ProjBerk.nativeMultiplicativeGroup k)
          (totalOver k C.projection)).left).obj M) (m : ℕ)
    (h₀ : Subsingleton (CategoryTheory.Sheaf.H
      ((Scheme.Modules.pullback (zeroInclusion C.projection)).obj
        (bundleTensorPower M m)).sheaf 1))
    (G₀ : ((Scheme.Modules.pullback (zeroInclusion C.projection)).obj
      (bundleTensorPower M m)).GeneratingSections) (hG₀ : G₀.IsFiniteType) :
    ∃ G : (bundleTensorPower M m).GeneratingSections, G.IsFiniteType := by
  classical
  let L := bundleTensorPower M m
  have hL := TensorPowerBaseIdealGrading.tensorPower_isInvertible hM m
  obtain ⟨g, hg, τ, _hτ, G, hG, hI, hsection⟩ :=
    ProjectiveCentralFiberGeneratorNeighborhood.exists_finite_generators_near_zero
      C.projection C.projection_isProjectiveFactorization L hL h₀ G₀ hG₀
  let W := C.projection ⁻¹ᵁ PrimeSpectrum.basicOpen g
  let τ' : G.I → Γ(L,⊤) := fun a => τ (hI ▸ a)
  have hτW (a : G.I) : affinePullbackUnitTop W.ι L (τ' a) = (G.s a).val (op ⊤) := by
    let N := (Scheme.Modules.pullback W.ι).obj L
    have hh := hsection a
    rw [ProjectiveCentralFiberGeneratorNeighborhood.pullbackSectionHom_sectionHom] at hh
    have hgen : N.unitHomEquiv (SchemeGeneratingSectionsUnit.generatorHom G a) = G.s a :=
      congrFun (N.freeHomEquiv.apply_symm_apply G.s) a
    have ht := congrArg (fun α => (N.unitHomEquiv α).val (op ⊤)) hh
    rw [hgen] at ht
    exact (sectionHom_top N (affinePullbackUnitTop W.ι L (τ' a))).symm.trans ht.symm
  obtain ⟨T, hT⟩ := exists_finite_groupPointAction_cover C g hg
  let I := T × G.I
  let α : I → (unitObj C.total ⟶ L) := fun a =>
    groupPointPowerSectionHom C M linearization (scalarGroupPoint a.1.val) m (τ' a.2)
  have hframe : ∀ x : C.total, ∃ V : C.total.Opens, x ∈ V ∧ ∃ a : I,
      IsIso (pullbackSectionHom V.ι (α a)) := by
    intro x
    have hx : x ∈ ⨆ u ∈ T, groupPointAction C (scalarGroupPoint u) ⁻¹ᵁ W := by
      rw [hT]
      trivial
    obtain ⟨u, hu⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
    obtain ⟨huT, hxu⟩ := TopologicalSpace.Opens.mem_iSup.mp hu
    let xW : W.toScheme := ⟨groupPointAction C (scalarGroupPoint u) x, hxu⟩
    obtain ⟨U, hU, a, ha⟩ := ProjectiveCentralFiberGeneratorNeighborhood.exists_lifted_generator_frame
      W.ι L hL G τ' hτW xW
    refine ⟨groupPointAction C (scalarGroupPoint u) ⁻¹ᵁ U.1, hU,
      (⟨u,huT⟩,a), ?_⟩
    exact frame_pullback_transport (groupPointAction C (scalarGroupPoint u))
      (groupPointPowerIso C M linearization (scalarGroupPoint u) m)
      (SchemeModuleGlobalSections.sectionHom L (τ' a)) U.1 ha
  let H : L.GeneratingSections :=
    { I := I
      s := fun a => L.unitHomEquiv (α a)
      epi := unitTuple_epi L α hframe }
  let : Finite G.I := hG.finite
  exact ⟨H, ⟨inferInstanceAs (Finite I)⟩⟩

/-- ONLY original native central ampleness internally supplies the SAME
positive power's central H1 and finite generators, hence an actual finite
whole-model generating family of that SAME original line power. -/
theorem exists_positive_power_generators_of_central_ample
    {k : Type u} [Field k] [Infinite k] {X : Over (Spec (.of k))}
    (C : NativeTestConfiguration.TestConfiguration k X)
    [IsIntegral C.total] [IsDominant C.projection]
    (L : C.total.Modules) (hL : IsInvertible L)
    (linearization :
      (Scheme.Modules.pullback (originalTestConfigurationTotalAction C).left).obj L ≅
        (Scheme.Modules.pullback (snd (ProjBerk.nativeMultiplicativeGroup k)
          (totalOver k C.projection)).left).obj L)
    (hCentral : SchemeLineAmpleness.IsAmple (pullback.snd C.projection (zeroMap k))
      ((Scheme.Modules.pullback (zeroInclusion C.projection)).obj L)) :
    ∃ m : ℕ, 0 < m ∧ ∃ G : (bundleTensorPower L m).GeneratingSections, G.IsFiniteType := by
  let p := C.projection
  let M := (Scheme.Modules.pullback (zeroInclusion p)).obj L
  obtain ⟨N, hN⟩ := exists_sheafH1_bound_of_ample (pullback.snd p (zeroMap k)) M hCentral
  obtain ⟨_hM, r, hr, n, i₀, _hi₀, _hp₀, ⟨E₀⟩⟩ := hCentral
  let s := r * (N + 1)
  have hs : 0 < s := Nat.mul_pos hr (Nat.succ_pos N)
  have hNs : N ≤ s := (Nat.le_succ N).trans (Nat.le_mul_of_pos_left _ hr)
  obtain ⟨n', ψ, _hψ, _hψp, ⟨Eψ⟩⟩ :=
    mixedTwist_isVeryAmple (R := k) (m := n) (0 : Fin (n + 1)) N
  let i := i₀ ≫ ψ
  let θ := TestConfigurationSectionTransport.tensorPowerPullbackIso (zeroInclusion p) L s
  let E : (Scheme.Modules.pullback i).obj
      (MvPolynomial.coordinateHyperplaneTwist (R := k) (0 : Fin (n' + 1)) 1) ≅
      (Scheme.Modules.pullback (zeroInclusion p)).obj (bundleTensorPower L s) :=
    (frameFactorIso i₀ ψ i rfl
      (MvPolynomial.coordinateHyperplaneTwist (R := k) (0 : Fin (n' + 1)) 1)).symm ≪≫
      (Scheme.Modules.pullback i₀).mapIso Eψ ≪≫
      (OriginalAmpleSerreVanishing.powerMulPullbackTwistIso i₀ M r
        (0 : Fin (n + 1)) E₀.symm (N + 1)).symm ≪≫ θ.symm
  have hH1 : Subsingleton (CategoryTheory.Sheaf.H
      ((Scheme.Modules.pullback (zeroInclusion p)).obj (bundleTensorPower L s)).sheaf 1) := by
    let eH := (CategoryTheory.Sheaf.functorH
      (_root_.Opens.grothendieckTopology (zeroFiber p)) 1).mapIso
        ((Scheme.Modules.toSheaf (zeroFiber p)).mapIso θ)
    exact AddCommGrpCat.subsingleton_of_isZero
      (CategoryTheory.Limits.IsZero.of_iso
        (@AddCommGrpCat.isZero_of_subsingleton _ (hN s hNs)) eH)
  let G₀ := centralCoordinateFamily i (0 : Fin (n' + 1))
    ((Scheme.Modules.pullback (zeroInclusion p)).obj (bundleTensorPower L s)) E
  have hG₀ := centralCoordinateFamily_isFiniteType i (0 : Fin (n' + 1))
    ((Scheme.Modules.pullback (zeroInclusion p)).obj (bundleTensorPower L s)) E
  obtain ⟨G, hG⟩ := exists_finite_power_generators_whole_model C L hL linearization s hH1 G₀ hG₀
  exact ⟨s,hs,G,hG⟩

end EnvelopeProperty.ProjectiveCentralFiberEmbeddingNeighborhoodClosedWholeGenerators
