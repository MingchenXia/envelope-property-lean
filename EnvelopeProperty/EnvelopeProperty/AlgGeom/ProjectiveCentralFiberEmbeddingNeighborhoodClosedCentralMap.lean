import EnvelopeProperty.AlgGeom.ProjectiveCentralFiberEmbeddingNeighborhoodClosedCentralCoordinateFamily
import EnvelopeProperty.AlgGeom.ProjectiveCentralFiberEmbeddingNeighborhoodClosedGeneratorCentralSections
import EnvelopeProperty.AlgGeom.ProjectiveCentralFiberEmbeddingNeighborhoodClosedCoefficientImmersion

/-! # The actual lifted original generator map has a closed original central map -/

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial
open Scheme.Modules
universe u
namespace EnvelopeProperty.ProjectiveCentralFiberEmbeddingNeighborhoodClosedCentralMap
open ProjectiveCentralFiberSectionLifting ProjectiveCentralFiberEmbeddingNeighborhood
open ProjectiveCentralFiberEmbeddingNeighborhoodClosedRestriction
open ProjectiveCentralFiberEmbeddingNeighborhoodClosedCentralCoordinateFamily
open GeneratedLineProjectiveMap
open DeJongAlterations.Geometry.BlowupProjectiveEmbedding

private instance isoHom_epi {X : Scheme.{u}} {A B : X.Modules} (E : A ≅ B) :
    Epi E.hom where
  left_cancellation g h heq := by
    simpa only [← Category.assoc, E.inv_hom_id, Category.id_comp] using
      congrArg (fun a => E.inv ≫ a) heq

private theorem projectiveMap_fixedIndex_sections {R : Type u} [CommRing R]
    {X : Scheme.{u}} {M : X.Modules} (p : X ⟶ Spec (CommRingCat.of R))
    (hM : IsInvertible M) {I : Type u} [Fintype I]
    (s t : I → M.sections) (hs : Epi (M.freeHomEquiv.symm s))
    (ht : Epi (M.freeHomEquiv.symm t)) (h : s = t) :
    projectiveMap p hM (⟨I, s, hs⟩ : M.GeneratingSections) =
      projectiveMap p hM (⟨I, t, ht⟩ : M.GeneratingSections) := by
  cases h
  rfl

private theorem familySections_heq {X : Scheme.{u}} {M : X.Modules}
    (F G : M.GeneratingSections) (h : F = G) : HEq F.s G.s := by
  cases h
  rfl

/-- The SAME actual near-zero lifted coordinate family has an ACTUAL closed
central map over the original polynomial base. The original embedding and its
whole geometric line isomorphism are the only central embedding data supplied.
The H1 vanishing remains an explicit intermediate premise. -/
theorem exists_finite_generators_closed_centralMap_near_zero
    {k : Type u} [Field k] {Y : Scheme.{u}} [IsIntegral Y]
    (p : Y ⟶ Spec (CommRingCat.of (Polynomial k))) [IsDominant p]
    (hp : IsProjectiveFactorization p) (L : Y.Modules) (hL : IsInvertible L)
    (h₀ : Subsingleton (CategoryTheory.Sheaf.H
      ((Scheme.Modules.pullback (zeroInclusion p)).obj L).sheaf 1))
    {m : ℕ} (i₀ : zeroFiber p ⟶ DeJongAlterations.projectiveSpace k m)
    [IsClosedImmersion i₀]
    (hi₀ : i₀ ≫ DeJongAlterations.projectiveSpaceStructure k m =
      pullback.snd p (zeroMap k)) (j : Fin (m + 1))
    (E₀ : (Scheme.Modules.pullback i₀).obj (coordinateHyperplaneTwist (R := k) j 1) ≅
      (Scheme.Modules.pullback (zeroInclusion p)).obj L) :
    ∃ a : Polynomial k, Polynomial.eval 0 a ≠ 0 ∧
      let W := p ⁻¹ᵁ PrimeSpectrum.basicOpen a
      ∃ (G : ((Scheme.Modules.pullback W.ι).obj L).GeneratingSections)
        (hF : Fintype G.I),
        let _ := hF
        G.IsFiniteType ∧ G.I = ULift.{u} (Fin (m + 1)) ∧
          IsClosedImmersion (centralMap (W.ι ≫ p)
            (DeJongAlterations.projectiveSpaceStructure (Polynomial k) (Fintype.card G.I))
            (projectiveMap (W.ι ≫ p) (hL.pullback W.ι) G)
            (projectiveMap_structure (W.ι ≫ p) (hL.pullback W.ι) G)) := by
  let M := (Scheme.Modules.pullback (zeroInclusion p)).obj L
  let G₀ := centralCoordinateFamily i₀ j M E₀
  let : Fintype G₀.I := (inferInstance : Fintype (ULift.{u} (Fin (m + 1))))
  have hG₀ : G₀.IsFiniteType := centralCoordinateFamily_isFiniteType i₀ j M E₀
  obtain ⟨a, ha, τ, hτ, G, hG, hI, hsection, jU, hj, hjclosed, hmatch⟩ :=
    ProjectiveCentralFiberEmbeddingNeighborhoodClosedGeneratorCentralSections.exists_matched_finite_generators_near_zero
      p hp L hL h₀ G₀ hG₀
  rcases G with ⟨I, s, hs⟩
  dsimp only at hI
  subst I
  let W := p ⁻¹ᵁ PrimeSpectrum.basicOpen a
  let G : ((Scheme.Modules.pullback W.ι).obj L).GeneratingSections := ⟨G₀.I, s, hs⟩
  let : Fintype G.I := (inferInstance : Fintype G₀.I)
  refine ⟨a, ha, G, inferInstance, hG, rfl, ?_⟩
  let : IsClosedImmersion jU := hjclosed
  let hW := hL.pullback W.ι
  let hM := hL.pullback (zeroInclusion p)
  let H := ClosedProjectiveGlobalGeneration.pullback_generatingSections jU G
  let : Fintype H.I := (inferInstance : Fintype G.I)
  let E := frameFactorIso jU W.ι (zeroInclusion p) hj L
  let T := @SheafOfModules.GeneratingSections.ofEpi _ _ _ _ _ _ _ _ H E.hom
    (isoHom_epi E)
  have hmatch' : T = G₀ := hmatch
  have hiso : projectiveMap (jU ≫ (W.ι ≫ p)) hM T =
      projectiveMap (jU ≫ (W.ι ≫ p)) (hW.pullback jU) H :=
    ProjectiveCentralFiberEmbeddingNeighborhoodClosedGeneratorIso.projectiveMap_of_iso
      (jU ≫ (W.ι ≫ p)) (hW.pullback jU) hM H E
  have hsEq : HEq T.s G₀.s := familySections_heq T G₀ hmatch'
  have hwhole : projectiveMap (jU ≫ (W.ι ≫ p)) hM T =
      projectiveMap (jU ≫ (W.ι ≫ p)) hM G₀ :=
    projectiveMap_fixedIndex_sections (jU ≫ (W.ι ≫ p)) hM
      T.s G₀.s T.epi G₀.epi (eq_of_heq hsEq)
  have hiso₀ := hwhole.symm.trans hiso
  let p₀ := pullback.snd p (zeroMap k)
  have hbase : jU ≫ (W.ι ≫ p) = p₀ ≫ zeroMap k := by
    rw [← Category.assoc, hj]
    exact pullback.condition
  let Φ := projectiveMap (W.ι ≫ p) hW G
  let Φ₀ := projectiveMap p₀ hM G₀
  let ρ := projectiveCoefficientMap (Polynomial.evalRingHom (0 : k)) (Fintype.card G.I)
  have hmaps : jU ≫ Φ = Φ₀ ≫ ρ := by
    have hsource :=
      ProjectiveCentralFiberEmbeddingNeighborhoodClosedGeneratorPullback.projectiveMap_pullback
        jU (W.ι ≫ p) hW G
    have hfirst : jU ≫ Φ = projectiveMap (p₀ ≫ zeroMap k) hM G₀ := by
      exact hsource.trans (hiso₀.symm.trans (congrArg (fun q => projectiveMap q hM G₀) hbase))
    exact hfirst.trans
      (ProjectiveCentralFiberEmbeddingNeighborhoodClosedGeneratorCoefficients.projectiveMap_comp_coefficient
        (Polynomial.evalRingHom (0 : k)) p₀ hM G₀).symm
  let : IsClosedImmersion Φ₀ := by
    have h := centralCoordinateProjectiveMap_isClosedImmersion i₀ j M E₀
    rw [hi₀] at h
    exact h
  let : IsClosedImmersion ρ :=
    ProjectiveCentralFiberEmbeddingNeighborhoodClosedCoefficientImmersion.projectiveEvalZeroMap_isClosedImmersion
      k (Fintype.card G.I)
  let : IsClosedImmersion (jU ≫ Φ) := hmaps.symm ▸
    (inferInstance : IsClosedImmersion (Φ₀ ≫ ρ))
  let c := centralMap (W.ι ≫ p) p W.ι rfl
  let : IsIso c := centralMap_open_isIso p W (central_range_subset_basicOpen p a ha)
  have hcj : c ≫ jU = zeroInclusion (W.ι ≫ p) := by
    apply (cancel_mono W.ι).mp
    rw [Category.assoc, hj]
    exact centralMap_inclusion (W.ι ≫ p) p W.ι rfl
  have hcentralComposite : IsClosedImmersion (zeroInclusion (W.ι ≫ p) ≫ Φ) := by
    have h : IsClosedImmersion ((c ≫ jU) ≫ Φ) := by
      rw [Category.assoc]
      infer_instance
    exact (congrArg (fun q => q ≫ Φ) hcj) ▸ h
  let q := DeJongAlterations.projectiveSpaceStructure (Polynomial k) (Fintype.card G.I)
  have hf : Φ ≫ q = W.ι ≫ p := projectiveMap_structure (W.ι ≫ p) hW G
  let : IsClosedImmersion (centralMap (W.ι ≫ p) q Φ hf ≫ zeroInclusion q) :=
    (centralMap_inclusion (W.ι ≫ p) q Φ hf).symm ▸ hcentralComposite
  exact IsClosedImmersion.of_comp_isClosedImmersion
    (centralMap (W.ι ≫ p) q Φ hf) (zeroInclusion q)

/-- The SAME actual original partial generated map has its WHOLE original
O(1) comparison and, internally, a genuine closed-immersion neighbourhood.
Properness is used only for the original models over their actual base opens. -/
theorem exists_finite_generators_closed_neighborhood_with_twist
    {k : Type u} [Field k] {Y : Scheme.{u}} [IsIntegral Y]
    (p : Y ⟶ Spec (CommRingCat.of (Polynomial k))) [IsDominant p]
    (hp : IsProjectiveFactorization p) (L : Y.Modules) (hL : IsInvertible L)
    (h₀ : Subsingleton (CategoryTheory.Sheaf.H
      ((Scheme.Modules.pullback (zeroInclusion p)).obj L).sheaf 1))
    {m : ℕ} (i₀ : zeroFiber p ⟶ DeJongAlterations.projectiveSpace k m)
    [IsClosedImmersion i₀]
    (hi₀ : i₀ ≫ DeJongAlterations.projectiveSpaceStructure k m =
      pullback.snd p (zeroMap k)) (j : Fin (m + 1))
    (E₀ : (Scheme.Modules.pullback i₀).obj (coordinateHyperplaneTwist (R := k) j 1) ≅
      (Scheme.Modules.pullback (zeroInclusion p)).obj L) :
    ∃ a : Polynomial k, Polynomial.eval 0 a ≠ 0 ∧
      let W := p ⁻¹ᵁ PrimeSpectrum.basicOpen a
      ∃ (G : ((Scheme.Modules.pullback W.ι).obj L).GeneratingSections)
        (hF : Fintype G.I),
        let _ := hF
        G.IsFiniteType ∧ G.I = ULift.{u} (Fin (m + 1)) ∧
          ∃ E : (Scheme.Modules.pullback (projectiveMap (W.ι ≫ p) (hL.pullback W.ι) G)).obj
            (coordinateHyperplaneTwist (R := Polynomial k) (0 : Fin (Fintype.card G.I + 1)) 1) ≅
              (Scheme.Modules.pullback W.ι).obj L,
            (∀ i : G.I, SchemeLineSectionEvaluation.pullbackSectionHom
                (projectiveMap (W.ι ≫ p) (hL.pullback W.ι) G)
                (GeneratedLineAffineTwistFrames.coordinateSectionHom (R := Polynomial k) G 0 i) ≫
                  E.hom = SchemeGeneratingSectionsUnit.generatorHom G i) ∧
              ∃ g : Polynomial k, Polynomial.eval 0 g ≠ 0 ∧
                p ⁻¹ᵁ PrimeSpectrum.basicOpen g ≤ W ∧
                IsClosedImmersion ((projectiveMap (W.ι ≫ p) (hL.pullback W.ι) G) ∣_
                  (DeJongAlterations.projectiveSpaceStructure (Polynomial k) (Fintype.card G.I) ⁻¹ᵁ
                    PrimeSpectrum.basicOpen g)) := by
  obtain ⟨a, ha, G, hF, hG, hI, hcentral⟩ :=
    exists_finite_generators_closed_centralMap_near_zero p hp L hL h₀ i₀ hi₀ j E₀
  let W := p ⁻¹ᵁ PrimeSpectrum.basicOpen a
  let : Fintype G.I := hF
  let : IsProper p := hp.isProper
  let : Surjective p := surjective_of_isDominant_of_isClosed_range p p.isClosedMap.isClosed_range
  let z₀ := zeroMap k (IsLocalRing.closedPoint k)
  have hz₀ : z₀ ∈ PrimeSpectrum.basicOpen a := by
    change (Polynomial.evalRingHom (0 : k)) a ∉ (IsLocalRing.closedPoint k).asIdeal
    rw [show IsLocalRing.closedPoint k = (⊥ : PrimeSpectrum k) from Subsingleton.elim _ _]
    exact ha
  obtain ⟨y, hy⟩ := p.surjective z₀
  have hyW : y ∈ W := by
    change p y ∈ PrimeSpectrum.basicOpen a
    rw [hy]
    exact hz₀
  let : Nonempty W := ⟨⟨y, hyW⟩⟩
  let : IsIntegral W.toScheme := inferInstance
  let Φ := projectiveMap (W.ι ≫ p) (hL.pullback W.ι) G
  let q := DeJongAlterations.projectiveSpaceStructure (Polynomial k) (Fintype.card G.I)
  have hf : Φ ≫ q = W.ι ≫ p := projectiveMap_structure (W.ι ≫ p) (hL.pullback W.ι) G
  let : IsClosedImmersion (centralMap (W.ι ≫ p) q Φ hf) := hcentral
  have hW : Set.range (zeroInclusion p) ⊆ (W : Set Y) :=
    central_range_subset_basicOpen p a ha
  obtain ⟨g, hg, hsubset, hclosed⟩ :=
    ProjectiveCentralFiberEmbeddingNeighborhoodClosedPartial.exists_closedImmersion_neighborhood_partial
      p q W hW Φ hf
  exact ⟨a, ha, G, hF, hG, hI,
    GeneratedLineProjectiveTwist.projectiveTwistIso (W.ι ≫ p) (hL.pullback W.ι) G 0,
    GeneratedLineProjectiveTwist.projectiveTwistIso_sectionHom (W.ι ≫ p) (hL.pullback W.ι) G 0,
    g, hg, hsubset, hclosed⟩

end EnvelopeProperty.ProjectiveCentralFiberEmbeddingNeighborhoodClosedCentralMap
