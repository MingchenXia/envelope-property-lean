import EnvelopeProperty.AlgGeom.ProjectiveCentralFiberEmbeddingNeighborhoodClosedGeneratorIso
import EnvelopeProperty.AlgGeom.ProjectiveCentralFiberGeneratorNeighborhood
import EnvelopeProperty.AlgGeom.SchemeLineSectionFactorization
import EnvelopeProperty.AlgGeom.ProjectiveCentralFiberEmbeddingNeighborhoodClosedRestriction

/-! # Literal original section lifts identify the actual whole central family -/

noncomputable section
open AlgebraicGeometry CategoryTheory Opposite
open Scheme.Modules
universe u
namespace EnvelopeProperty.ProjectiveCentralFiberEmbeddingNeighborhoodClosedGeneratorCentralSections
open SchemeLineSectionEvaluation SchemeLineSectionFactorization ProjectiveCentralFiberSectionLifting

private theorem sectionHom_atOne {X : Scheme.{u}} (L : X.Modules)
    (α : unitObj X ⟶ L) :
    SchemeModuleGlobalSections.sectionHom L (sectionAtOne α) = α := by
  have hone : topSectionHom (unitObj X) (1 : Γ(X, ⊤)) = 𝟙 (unitObj X) :=
    ModularCurves.unitEndomorphismOfTopSection_one
  have h := ModularCurves.topSectionHom_comp (M := unitObj X) (N := L)
    (show Γ(X, ⊤) from 1) α
  exact h.symm.trans ((congrArg (fun q : unitObj X ⟶ unitObj X => q ≫ α) hone).trans
    (Category.id_comp α))

/-- The actual original lifted value internally determines the WHOLE original
generator-Hom, not merely its values at reduced points or stalks. -/
theorem liftedSection_generatorHom {Y Z : Scheme.{u}} (j : Z ⟶ Y)
    (L : Y.Modules) (G₀ : ((Scheme.Modules.pullback j).obj L).GeneratingSections)
    (τ : Γ(L, ⊤)) (i : G₀.I)
    (hτ : affinePullbackUnitTop j L τ = (G₀.s i).val (op ⊤)) :
    pullbackSectionHom j (SchemeModuleGlobalSections.sectionHom L τ) =
      SchemeGeneratingSectionsUnit.generatorHom G₀ i := by
  let M := (Scheme.Modules.pullback j).obj L
  have h := congrFun (M.freeHomEquiv.apply_symm_apply G₀.s) i
  change M.unitHomEquiv (SchemeGeneratingSectionsUnit.generatorHom G₀ i) = G₀.s i at h
  have ht := congrArg (fun q => q.val (op (⊤ : Z.Opens))) h
  change sectionAtOne (SchemeGeneratingSectionsUnit.generatorHom G₀ i) =
    (G₀.s i).val (op ⊤) at ht
  exact (ProjectiveCentralFiberGeneratorNeighborhood.pullbackSectionHom_sectionHom j L τ).trans
    ((congrArg (SchemeModuleGlobalSections.sectionHom M) (hτ.trans ht.symm)).trans
      (sectionHom_atOne M (SchemeGeneratingSectionsUnit.generatorHom G₀ i)))

private theorem isoHom_epi {X : Scheme.{u}} {M N : X.Modules} (E : M ≅ N) :
    Epi E.hom where
  left_cancellation g h heq := by
    simpa only [← Category.assoc, E.inv_hom_id, Category.id_comp] using
      congrArg (fun a => E.inv ≫ a) heq

private abbrev transportedPulledFamily {Y U Z : Scheme.{u}}
    (g : Z ⟶ U) (u : U ⟶ Y) (j : Z ⟶ Y) (hj : g ≫ u = j)
    (L : Y.Modules) (G : ((Scheme.Modules.pullback u).obj L).GeneratingSections) :
    ((Scheme.Modules.pullback j).obj L).GeneratingSections :=
  @SheafOfModules.GeneratingSections.ofEpi _ _ _ _ _ _ _ _
    (ClosedProjectiveGlobalGeneration.pullback_generatingSections g G)
    (frameFactorIso g u j hj L).hom (isoHom_epi (X := Z) (frameFactorIso g u j hj L))

/-- The literal original near-zero index and lifted-section equations DERIVE
equality of the ENTIRE actual central family through the canonical whole
factorization comparison; no family or projective-map matching is input. -/
theorem pulledLiftedFamily_eq {Y U Z : Scheme.{u}}
    (g : Z ⟶ U) (u : U ⟶ Y) (j : Z ⟶ Y) (hj : g ≫ u = j)
    (L : Y.Modules) (G₀ : ((Scheme.Modules.pullback j).obj L).GeneratingSections)
    (τ : G₀.I → Γ(L, ⊤))
    (hτ : ∀ i, affinePullbackUnitTop j L (τ i) = (G₀.s i).val (op ⊤))
    (G : ((Scheme.Modules.pullback u).obj L).GeneratingSections) (hI : G.I = G₀.I)
    (hG : ∀ i : G.I, SchemeGeneratingSectionsUnit.generatorHom G i =
      pullbackSectionHom u (SchemeModuleGlobalSections.sectionHom L (τ (hI ▸ i)))) :
    transportedPulledFamily g u j hj L G = G₀ := by
  let H := ClosedProjectiveGlobalGeneration.pullback_generatingSections g G
  let E := frameFactorIso g u j hj L
  apply ProjectiveCentralFiberEmbeddingNeighborhoodClosedGeneratorIso.generatingSections_eq_of_generatorHom
    (transportedPulledFamily g u j hj L G) G₀ hI
  intro i
  have h₁ : SchemeGeneratingSectionsUnit.generatorHom (transportedPulledFamily g u j hj L G) i =
      SchemeGeneratingSectionsUnit.generatorHom H i ≫ E.hom :=
    @SchemeGeneratingSectionsUnit.generatorHom_ofEpi _ _ _ H E.hom (isoHom_epi (X := Z) E) i
  have h₂ : SchemeGeneratingSectionsUnit.generatorHom H i =
      pullbackSectionHom g (SchemeGeneratingSectionsUnit.generatorHom G i) :=
    SchemeGeneratingSectionsUnit.generatorHom_pullback g G i
  have h₃ := congrArg (pullbackSectionHom g) (hG i)
  exact h₁.trans
    ((congrArg (fun q => q ≫ E.hom) (h₂.trans h₃)).trans
      ((pullbackSectionHom_factor g u j hj
        (SchemeModuleGlobalSections.sectionHom L (τ (hI ▸ i)))).trans
          (liftedSection_generatorHom j L G₀ (τ (hI ▸ i)) (hI ▸ i) (hτ (hI ▸ i)))))

/-- The ACTUAL near-zero lifting producer internally supplies the index and
all lifted-generator equations, the actual central factor closed immersion,
and equality of the WHOLE resulting central generating family. -/
theorem exists_matched_finite_generators_near_zero {k : Type u} [Field k]
    {Y : Scheme.{u}} [IsIntegral Y]
    (p : Y ⟶ Spec (CommRingCat.of (Polynomial k))) [IsDominant p]
    (hp : IsProjectiveFactorization p) (L : Y.Modules) (hL : IsInvertible L)
    (h₀ : Subsingleton (CategoryTheory.Sheaf.H
      ((Scheme.Modules.pullback (zeroInclusion p)).obj L).sheaf 1))
    (G₀ : ((Scheme.Modules.pullback (zeroInclusion p)).obj L).GeneratingSections)
    (hG₀ : G₀.IsFiniteType) :
    ∃ a : Polynomial k, Polynomial.eval 0 a ≠ 0 ∧
      ∃ τ : G₀.I → Γ(L, ⊤),
        (∀ i, affinePullbackUnitTop (zeroInclusion p) L (τ i) = (G₀.s i).val (op ⊤)) ∧
        let W := p ⁻¹ᵁ PrimeSpectrum.basicOpen a
        ∃ G : ((Scheme.Modules.pullback W.ι).obj L).GeneratingSections,
          G.IsFiniteType ∧ ∃ hI : G.I = G₀.I,
            (∀ i : G.I, SchemeGeneratingSectionsUnit.generatorHom G i =
              pullbackSectionHom W.ι (SchemeModuleGlobalSections.sectionHom L (τ (hI ▸ i)))) ∧
            ∃ (jU : zeroFiber p ⟶ W.toScheme) (hj : jU ≫ W.ι = zeroInclusion p),
              IsClosedImmersion jU ∧
                transportedPulledFamily jU W.ι (zeroInclusion p) hj L G = G₀ := by
  obtain ⟨a, ha, τ, hτ, G, hG, hI, hsection⟩ :=
    ProjectiveCentralFiberGeneratorNeighborhood.exists_finite_generators_near_zero
      p hp L hL h₀ G₀ hG₀
  let W := p ⁻¹ᵁ PrimeSpectrum.basicOpen a
  have hrange : Set.range (zeroInclusion p) ⊆ Set.range W.ι := by
    rw [W.range_ι]
    exact ProjectiveCentralFiberEmbeddingNeighborhoodClosedRestriction.central_range_subset_basicOpen
      p a ha
  let jU : zeroFiber p ⟶ W.toScheme := IsOpenImmersion.lift W.ι (zeroInclusion p) hrange
  have hj : jU ≫ W.ι = zeroInclusion p := IsOpenImmersion.lift_fac _ _ _
  have hc : IsClosedImmersion jU := by
    let : IsClosedImmersion (jU ≫ W.ι) :=
      hj.symm ▸ (inferInstance : IsClosedImmersion (zeroInclusion p))
    exact IsClosedImmersion.of_comp jU W.ι
  exact ⟨a, ha, τ, hτ, G, hG, hI, hsection, jU, hj, hc,
    pulledLiftedFamily_eq jU W.ι (zeroInclusion p) hj L G₀ τ hτ G hI hsection⟩

end EnvelopeProperty.ProjectiveCentralFiberEmbeddingNeighborhoodClosedGeneratorCentralSections
