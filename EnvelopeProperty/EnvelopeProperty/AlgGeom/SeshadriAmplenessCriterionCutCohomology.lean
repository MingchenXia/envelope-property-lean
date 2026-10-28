import EnvelopeProperty.AlgGeom.SeshadriAmplenessCriterionCartierDifference
import EnvelopeProperty.AlgGeom.SchemeCoherentEulerExact
import EnvelopeProperty.AlgGeom.SchemeCoherentEulerAffine
import EnvelopeProperty.AlgGeom.SchemeLineAmpleness
import EnvelopeProperty.AlgGeom.OriginalAmpleSerreVanishing
import EnvelopeProperty.Projective.TestConfigurationSectionTransport
import Mathlib.Algebra.Homology.HomologySequence

/-! # Actual cohomology comparisons for the original Cartier cuts

The objects and arrows below come from the existing closed-ideal exact sequence,
its original invertible tensor functor, and the actual field-linear Cech functor.
The lower dimensional cut may be reducible and nonreduced.
-/
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite
open Scheme.Modules TopCat TopCat.Sheaf
noncomputable section
universe u
namespace EnvelopeProperty.SeshadriAmplenessCriterionCutCohomology
open CategoryTheory.MonoidalCategory
open SchemeCoherentEulerIndex SchemeCoherentEulerExact
attribute [local instance] Scheme.Modules.monoidalCategory Scheme.Modules.symmetricCategory
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private def transportedSequence {C : Type*} [Category* C] [HasZeroMorphisms C]
    (S : ShortComplex C) {A B D : C}
    (a : S.X₁ ≅ A) (b : S.X₂ ≅ B) (d : S.X₃ ≅ D) : ShortComplex C :=
  ShortComplex.mk (a.inv ≫ S.f ≫ b.hom) (b.inv ≫ S.g ≫ d.hom) (by
    simp only [Category.assoc, Iso.hom_inv_id_assoc, S.zero_assoc, zero_comp, comp_zero])

private def transportedSequenceIso {C : Type*} [Category* C] [HasZeroMorphisms C]
    (S : ShortComplex C) {A B D : C}
    (a : S.X₁ ≅ A) (b : S.X₂ ≅ B) (d : S.X₃ ≅ D) :
    S ≅ transportedSequence S a b d :=
  ShortComplex.isoMk a b d (by simp [transportedSequence]) (by simp [transportedSequence])

private def cancelDualLeft {X : Scheme.{u}} (A M : X.Modules) (hA : IsInvertible A) :
    dualObj A ⊗ (A ⊗ M) ≅ M :=
  (α_ (dualObj A) A M).symm ≪≫
    ((β_ (dualObj A) A ≪≫ hA.monoidalEvaluationIso) ⊗ᵢ Iso.refl M) ≪≫ λ_ M

/-- The SAME original section gives the actual multiplication/restriction short
complex. Its arrows are conjugates of the original ideal inclusion and quotient. -/
def sectionCutSequence {X : Scheme.{u}} [IsIntegral X]
    (A M : X.Modules) (hA : IsInvertible A) (hM : IsInvertible M)
    (s : unitObj X ⟶ A) (hs : s ≠ 0) : ShortComplex X.Modules := by
  let I := LineSectionZeroIdeal.zeroIdeal A hA s
  let g := I.subschemeι
  let W := A ⊗ M
  have hW : IsInvertible W := (hA.tensorObj hM).of_iso (ModularCurves.monoidalTensorObjIso A M)
  let : (tensorRight W).IsEquivalence :=
    SchemeInvertibleTensorEquivalence.tensorRight_isEquivalence W hW
  let S := (FiniteClosedIdealEuler.sequence g).map (tensorRight W)
  let P := (Scheme.Modules.pullback g).obj W
  let eI : ModularCurves.idealModule g ≅ dualObj A :=
    (GeometricIdealKernelModuleComparison.toModulesKernelIso I).symm ≪≫
      LineSectionZeroIdeal.dualIso A hA s hs
  let a : S.X₁ ≅ M := (eI ⊗ᵢ Iso.refl W) ≪≫ cancelDualLeft A M hA
  let b : S.X₂ ≅ W :=
    ((ModularCurves.monoidalUnitObjIso X).symm ⊗ᵢ Iso.refl W) ≪≫ λ_ W
  let d : S.X₃ ≅ (pushforward g).obj P :=
    SchemeLineProjectionFormula.lineProjectionFormulaObj g W hW (unitObj I.subscheme) ≪≫
      (pushforward g).mapIso
        (((ModularCurves.monoidalUnitObjIso I.subscheme).symm ⊗ᵢ Iso.refl P) ≪≫ λ_ P)
  exact transportedSequence S a b d

/-- Genuine exactness of the same original section sequence, with no incoming
exactness, cohomology, or compatibility certificate. -/
theorem sectionCutSequence_shortExact {X : Scheme.{u}} [IsIntegral X]
    (A M : X.Modules) (hA : IsInvertible A) (hM : IsInvertible M)
    (s : unitObj X ⟶ A) (hs : s ≠ 0) :
    (sectionCutSequence A M hA hM s hs).ShortExact := by
  dsimp only [sectionCutSequence]
  apply ShortComplex.shortExact_of_iso (transportedSequenceIso _ _ _ _)
  exact SchemeInvertibleTensorEquivalence.tensorRight_shortExact _
    ((hA.tensorObj hM).of_iso (ModularCurves.monoidalTensorObjIso A M)) _
      (FiniteClosedIdealEuler.sequence_shortExact _)

private theorem fieldComplex_isZero_of_native {k : Type u} [Field k]
    {X : Scheme.{u}} [X.IsSeparated] (f : X ⟶ Spec (.of k))
    (M : X.Modules) [M.IsQuasicoherent] {ι : Type u} [Finite ι]
    (U : ι → X.Opens) (hU : IsOpenCover U) (hUa : ∀ i, IsAffineOpen (U i))
    (q : ℕ) (h : Subsingleton (CategoryTheory.Sheaf.H M.sheaf (q + 1))) :
    IsZero (((fieldComplexFunctor f U).obj M).homology (q + 1)) := by
  have hn := cechComplex_exactAt_succ_of_affine_openCover M U hU hUa q h
  have hb := (baseCechComplex_exactAt_iff f M U (q + 1)).mpr hn
  have hz := (HomologicalComplex.exactAt_iff_isZero_homology _ _).mp hb
  exact IsZero.of_iso ((ModuleCat.restrictScalars (baseScalar (k := k))).map_isZero hz)
    (fieldComplexHomologyIso f M U (q + 1))

private theorem pushforward_fieldComplex_isZero_of_native {k : Type u} [Field k]
    {X D : Scheme.{u}} [X.IsSeparated] (g : D ⟶ X) [IsClosedImmersion g]
    (f : X ⟶ Spec (.of k)) (P : D.Modules) [P.IsQuasicoherent]
    {ι : Type u} [Finite ι] [LinearOrder ι]
    (U : ι → X.Opens) (hU : IsOpenCover U) (hUa : ∀ i, IsAffineOpen (U i))
    (q : ℕ) (h : Subsingleton (CategoryTheory.Sheaf.H P.sheaf (q + 1))) :
    IsZero (((fieldComplexFunctor f U).obj ((pushforward g).obj P)).homology (q + 1)) := by
  let : D.IsSeparated := ⟨by
    have hsep : IsSeparated (g ≫ terminal.from X) := inferInstance
    simpa only [terminal.comp_from] using hsep⟩
  let V := fun i => g ⁻¹ᵁ U i
  have hV : IsOpenCover V := g.iSup_preimage_eq_top hU
  have hVa : ∀ i, IsAffineOpen (V i) := fun i => (hUa i).preimage g
  have hz := fieldComplex_isZero_of_native (g ≫ f) P V hV hVa q h
  have hz' : IsZero (fieldCech (g ≫ f) P V (q + 1)) :=
    IsZero.of_iso hz (fieldComplexHomologyIso (g ≫ f) P V (q + 1)).symm
  have hz'' : IsZero (fieldCech f ((pushforward g).obj P) U (q + 1)) :=
    IsZero.of_iso hz' (SchemeCoherentEulerAffine.fieldCechPushforwardIso g f P U (q + 1)).symm
  exact IsZero.of_iso hz'' (fieldComplexHomologyIso f ((pushforward g).obj P) U (q + 1))

private theorem fieldComplex_shortExact {k : Type u} [Field k]
    {X : Scheme.{u}} [X.IsSeparated] (f : X ⟶ Spec (.of k))
    {ι : Type u} [Finite ι] (U : ι → X.Opens) (hUa : ∀ i, IsAffineOpen (U i))
    (S : ShortComplex X.Modules) (hS : S.ShortExact)
    [S.X₁.IsQuasicoherent] [S.X₂.IsQuasicoherent] [S.X₃.IsQuasicoherent] :
    (S.map (fieldComplexFunctor f U)).ShortExact :=
  (hS.map_baseCechComplexFunctor_of_affine_openCover f U hUa).map_of_exact
    ((ModuleCat.restrictScalars (baseScalar (k := k))).mapHomologicalComplex (.up ℕ))

private theorem homologyMap_isIso_of_adjacent_zero {k : Type u} [Field k]
    (S : ShortComplex (CochainComplex (ModuleCat.{u} k) ℕ)) (hS : S.ShortExact)
    (q : ℕ) (hprev : IsZero (S.X₃.homology q)) (hcurr : IsZero (S.X₃.homology (q + 1))) :
    IsIso (HomologicalComplex.homologyMap S.f (q + 1)) := by
  have : Mono (HomologicalComplex.homologyMap S.f (q + 1)) :=
    (hS.homology_exact₁ q (q + 1) rfl).mono_g (hprev.eq_of_src _ _)
  have : Epi (HomologicalComplex.homologyMap S.f (q + 1)) :=
    (hS.homology_exact₂ (q + 1)).epi_f (hcurr.eq_of_tgt _ _)
  exact isIso_of_mono_of_epi _

private theorem sectionCutSequence_fieldShortExact {k : Type u} [Field k]
    {X : Scheme.{u}} [IsIntegral X] [X.IsSeparated]
    (f : X ⟶ Spec (.of k)) {ι : Type u} [Finite ι]
    (U : ι → X.Opens) (hUa : ∀ i, IsAffineOpen (U i))
    (A M : X.Modules) (hA : IsInvertible A) (hM : IsInvertible M)
    (s : unitObj X ⟶ A) (hs : s ≠ 0) :
    ((sectionCutSequence A M hA hM s hs).map (fieldComplexFunctor f U)).ShortExact := by
  let I := LineSectionZeroIdeal.zeroIdeal A hA s
  let W := A ⊗ M
  have hW : IsInvertible W := (hA.tensorObj hM).of_iso (ModularCurves.monoidalTensorObjIso A M)
  let P := (Scheme.Modules.pullback I.subschemeι).obj W
  let : M.IsQuasicoherent := hM.isQuasicoherent
  let : W.IsQuasicoherent := hW.isQuasicoherent
  let : P.IsQuasicoherent := (hW.pullback I.subschemeι).isQuasicoherent
  let : ((pushforward I.subschemeι).obj P).IsQuasicoherent :=
    isQuasicoherent_pushforward_of_isAffineHom I.subschemeι
  let S := sectionCutSequence A M hA hM s hs
  let : S.X₁.IsQuasicoherent := by change M.IsQuasicoherent; infer_instance
  let : S.X₂.IsQuasicoherent := by change W.IsQuasicoherent; infer_instance
  let : S.X₃.IsQuasicoherent := by
    change ((pushforward I.subschemeι).obj P).IsQuasicoherent
    infer_instance
  exact fieldComplex_shortExact f U hUa S (sectionCutSequence_shortExact A M hA hM s hs)

/-- Ordinary vanishing on the SAME actual cut makes the actual multiplication
map epic in the stated positive original field-linear cohomology degree. -/
theorem epi_sectionCut_homologyMap_of_vanishing {k : Type u} [Field k]
    {X : Scheme.{u}} [IsIntegral X] [X.IsSeparated]
    (f : X ⟶ Spec (.of k)) {ι : Type u} [Finite ι] [LinearOrder ι]
    (U : ι → X.Opens) (hU : IsOpenCover U) (hUa : ∀ i, IsAffineOpen (U i))
    (A M : X.Modules) (hA : IsInvertible A) (hM : IsInvertible M)
    (s : unitObj X ⟶ A) (hs : s ≠ 0) (q : ℕ)
    (h : Subsingleton (CategoryTheory.Sheaf.H
      ((Scheme.Modules.pullback (LineSectionZeroIdeal.zeroIdeal A hA s).subschemeι).obj
        (A ⊗ M)).sheaf (q + 1))) :
    Epi (HomologicalComplex.homologyMap
      ((fieldComplexFunctor f U).map (sectionCutSequence A M hA hM s hs).f) (q + 1)) := by
  let g := (LineSectionZeroIdeal.zeroIdeal A hA s).subschemeι
  let P := (Scheme.Modules.pullback g).obj (A ⊗ M)
  let : P.IsQuasicoherent :=
    (((hA.tensorObj hM).of_iso (ModularCurves.monoidalTensorObjIso A M)).pullback g).isQuasicoherent
  have hz := pushforward_fieldComplex_isZero_of_native g f P U hU hUa q h
  have he := sectionCutSequence_fieldShortExact f U hUa A M hA hM s hs
  exact (he.homology_exact₂ (q + 1)).epi_f (hz.eq_of_tgt _ _)

/-- Two adjacent positive vanishings on the SAME actual cut make the actual
multiplication map an isomorphism in the original field-linear cohomology. -/
theorem isIso_sectionCut_homologyMap_of_vanishing {k : Type u} [Field k]
    {X : Scheme.{u}} [IsIntegral X] [X.IsSeparated]
    (f : X ⟶ Spec (.of k)) {ι : Type u} [Finite ι] [LinearOrder ι]
    (U : ι → X.Opens) (hU : IsOpenCover U) (hUa : ∀ i, IsAffineOpen (U i))
    (A M : X.Modules) (hA : IsInvertible A) (hM : IsInvertible M)
    (s : unitObj X ⟶ A) (hs : s ≠ 0) (q : ℕ)
    (hprev : Subsingleton (CategoryTheory.Sheaf.H
      ((Scheme.Modules.pullback (LineSectionZeroIdeal.zeroIdeal A hA s).subschemeι).obj
        (A ⊗ M)).sheaf (q + 1)))
    (hcurr : Subsingleton (CategoryTheory.Sheaf.H
      ((Scheme.Modules.pullback (LineSectionZeroIdeal.zeroIdeal A hA s).subschemeι).obj
        (A ⊗ M)).sheaf (q + 2))) :
    IsIso (HomologicalComplex.homologyMap
      ((fieldComplexFunctor f U).map (sectionCutSequence A M hA hM s hs).f) (q + 2)) := by
  let g := (LineSectionZeroIdeal.zeroIdeal A hA s).subschemeι
  let P := (Scheme.Modules.pullback g).obj (A ⊗ M)
  let : P.IsQuasicoherent :=
    (((hA.tensorObj hM).of_iso (ModularCurves.monoidalTensorObjIso A M)).pullback g).isQuasicoherent
  exact homologyMap_isIso_of_adjacent_zero _
    (sectionCutSequence_fieldShortExact f U hUa A M hA hM s hs) (q + 1)
    (pushforward_fieldComplex_isZero_of_native g f P U hU hUa q hprev)
    (pushforward_fieldComplex_isZero_of_native g f P U hU hUa (q + 1) hcurr)

private theorem nativeH_subsingleton_of_iso {X : Scheme.{u}} {M N : X.Modules}
    (e : M ≅ N) (q : ℕ) (h : Subsingleton (CategoryTheory.Sheaf.H N.sheaf q)) :
    Subsingleton (CategoryTheory.Sheaf.H M.sheaf q) := by
  let eH := (CategoryTheory.Sheaf.functorH (_root_.Opens.grothendieckTopology X) q).mapIso
    ((Scheme.Modules.toSheaf X).mapIso e)
  exact AddCommGrpCat.subsingleton_of_isZero
    (IsZero.of_iso (@AddCommGrpCat.isZero_of_subsingleton _ h) eH)

private theorem unit_finiteType (X : Scheme.{u}) : (unitObj X).IsFiniteType := by
  let : (unitObj X).IsFinitePresentation := isInvertible_unit.isFinitePresentation
  obtain ⟨q, hq⟩ := SheafOfModules.IsFinitePresentation.exists_quasicoherentData (unitObj X)
  refine { exists_localGeneratorsData := ⟨q.localGeneratorsData, ?_⟩ }
  constructor
  intro i
  exact (hq.isFinite_presentation i).isFiniteType_generators

private theorem exists_cut_pullback_power_vanishing {R : Type u}
    [CommRing R] [IsNoetherianRing R] {X D : Scheme.{u}}
    (f : X ⟶ Spec (.of R)) (g : D ⟶ X) (L : X.Modules)
    (h : SchemeLineAmpleness.IsAmple (g ≫ f) ((Scheme.Modules.pullback g).obj L)) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ q : ℕ,
      Subsingleton (CategoryTheory.Sheaf.H
        ((Scheme.Modules.pullback g).obj (CanonicalGeometry.bundleTensorPower L n)).sheaf (q + 1)) := by
  let P := (Scheme.Modules.pullback g).obj L
  obtain ⟨hP, r, hr, d, i, hi, _hif, ⟨E⟩⟩ := h
  let : IsClosedImmersion i := hi
  let : (unitObj D).IsQuasicoherent := isInvertible_unit.isQuasicoherent
  let : (unitObj D).IsFiniteType := unit_finiteType D
  obtain ⟨N, hN⟩ := @OriginalAmpleSerreVanishing.exists_sheafCohomology_bound
    R _ _ (Fin (d + 1)) _ D i hi (unitObj D) P _ _ hP r hr
      (0 : Fin (d + 1)) E.symm
  refine ⟨N, fun n hn q => ?_⟩
  let e : (Scheme.Modules.pullback g).obj (CanonicalGeometry.bundleTensorPower L n) ≅
      unitObj D ⊗ CanonicalGeometry.bundleTensorPower P n :=
    TestConfigurationSectionTransport.tensorPowerPullbackIso g L n ≪≫
      (λ_ (CanonicalGeometry.bundleTensorPower P n)).symm ≪≫
      (ModularCurves.monoidalUnitObjIso D ⊗ᵢ Iso.refl _)
  exact nativeH_subsingleton_of_iso e (q + 1) (hN n hn q)

/-- The actual two-cut span through the SAME dual-B twist gives the original
field-linear higher-cohomology isomorphism. Its four inputs are ordinary native
vanishings on the actual zero subschemes, not a comparison certificate. -/
def twoCutCohomologyIso {k : Type u} [Field k]
    {X : Scheme.{u}} [IsIntegral X] [X.IsSeparated]
    (f : X ⟶ Spec (.of k)) {ι : Type u} [Finite ι] [LinearOrder ι]
    (U : ι → X.Opens) (hU : IsOpenCover U) (hUa : ∀ i, IsAffineOpen (U i))
    (L B M : X.Modules) (hL : IsInvertible L) (hB : IsInvertible B) (hM : IsInvertible M)
    (a : unitObj X ⟶ L ⊗ B) (ha : a ≠ 0) (b : unitObj X ⟶ B) (hb : b ≠ 0) (q : ℕ) :
    let hA := (hL.tensorObj hB).of_iso (ModularCurves.monoidalTensorObjIso L B)
    let I := LineSectionZeroIdeal.zeroIdeal (L ⊗ B) hA a
    let J := LineSectionZeroIdeal.zeroIdeal B hB b
    Subsingleton (CategoryTheory.Sheaf.H ((Scheme.Modules.pullback I.subschemeι).obj (L ⊗ M)).sheaf (q + 1)) →
    Subsingleton (CategoryTheory.Sheaf.H ((Scheme.Modules.pullback I.subschemeι).obj (L ⊗ M)).sheaf (q + 2)) →
    Subsingleton (CategoryTheory.Sheaf.H ((Scheme.Modules.pullback J.subschemeι).obj M).sheaf (q + 1)) →
    Subsingleton (CategoryTheory.Sheaf.H ((Scheme.Modules.pullback J.subschemeι).obj M).sheaf (q + 2)) →
    (fieldCech f (L ⊗ M) U (q + 2) ≅ fieldCech f M U (q + 2)) := by
  dsimp only
  intro hap hac hbp hbc
  let hA : IsInvertible (L ⊗ B) :=
    (hL.tensorObj hB).of_iso (ModularCurves.monoidalTensorObjIso L B)
  let I := LineSectionZeroIdeal.zeroIdeal (L ⊗ B) hA a
  let J := LineSectionZeroIdeal.zeroIdeal B hB b
  let F := dualObj B ⊗ M
  have hF : IsInvertible F :=
    (hB.dual.tensorObj hM).of_iso (ModularCurves.monoidalTensorObjIso (dualObj B) M)
  let eB : B ⊗ F ≅ M :=
    (α_ B (dualObj B) M).symm ≪≫ (hB.monoidalEvaluationIso ⊗ᵢ Iso.refl M) ≪≫ λ_ M
  let eA : (L ⊗ B) ⊗ F ≅ L ⊗ M := α_ L B F ≪≫ (Iso.refl L ⊗ᵢ eB)
  let H := fieldComplexFunctor f U ⋙
    HomologicalComplex.homologyFunctor (ModuleCat.{u} k) (.up ℕ) (q + 2)
  let vA := H.map (sectionCutSequence (L ⊗ B) F hA hF a ha).f
  let vB := H.map (sectionCutSequence B F hB hF b hb).f
  have hvA : IsIso vA := isIso_sectionCut_homologyMap_of_vanishing f U hU hUa
    (L ⊗ B) F hA hF a ha q
      (nativeH_subsingleton_of_iso ((Scheme.Modules.pullback I.subschemeι).mapIso eA) (q + 1) hap)
      (nativeH_subsingleton_of_iso ((Scheme.Modules.pullback I.subschemeι).mapIso eA) (q + 2) hac)
  have hvB : IsIso vB := isIso_sectionCut_homologyMap_of_vanishing f U hU hUa
    B F hB hF b hb q
      (nativeH_subsingleton_of_iso ((Scheme.Modules.pullback J.subschemeι).mapIso eB) (q + 1) hbp)
      (nativeH_subsingleton_of_iso ((Scheme.Modules.pullback J.subschemeι).mapIso eB) (q + 2) hbc)
  letI := hvA
  letI := hvB
  let e : H.obj (L ⊗ M) ≅ H.obj M :=
    (H.mapIso eA).symm ≪≫ (asIso vA).symm ≪≫ asIso vB ≪≫ H.mapIso eB
  exact (fieldComplexHomologyIso f (L ⊗ M) U (q + 2)).symm ≪≫ e ≪≫
    fieldComplexHomologyIso f M U (q + 2)

/-- Genuine native ampleness of the two fixed original cut restrictions
internally supplies ONE bound for every original power and every degree at least
two. The same B/a/b and zero subschemes precede all n/q. No target-X ampleness,
Serre-vanishing, cohomology-matching, or higher-comparison certificate is input. -/
theorem exists_twoCut_powerCohomologyIso_of_ample {k : Type u} [Field k]
    {X : Scheme.{u}} [IsIntegral X] [X.IsSeparated]
    (f : X ⟶ Spec (.of k)) {ι : Type u} [Finite ι]
    (U : ι → X.Opens) (hU : IsOpenCover U) (hUa : ∀ i, IsAffineOpen (U i))
    (L B : X.Modules) (hL : IsInvertible L) (hB : IsInvertible B)
    (a : unitObj X ⟶ L ⊗ B) (ha : a ≠ 0) (b : unitObj X ⟶ B) (hb : b ≠ 0) :
    let hA := (hL.tensorObj hB).of_iso (ModularCurves.monoidalTensorObjIso L B)
    let I := LineSectionZeroIdeal.zeroIdeal (L ⊗ B) hA a
    let J := LineSectionZeroIdeal.zeroIdeal B hB b
    SchemeLineAmpleness.IsAmple (I.subschemeι ≫ f) ((Scheme.Modules.pullback I.subschemeι).obj L) →
    SchemeLineAmpleness.IsAmple (J.subschemeι ≫ f) ((Scheme.Modules.pullback J.subschemeι).obj L) →
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ q : ℕ, Nonempty
      (fieldCech f (CanonicalGeometry.bundleTensorPower L (n + 1)) U (q + 2) ≅
        fieldCech f (CanonicalGeometry.bundleTensorPower L n) U (q + 2)) := by
  classical
  dsimp only
  intro hI hJ
  let hA : IsInvertible (L ⊗ B) :=
    (hL.tensorObj hB).of_iso (ModularCurves.monoidalTensorObjIso L B)
  let I := LineSectionZeroIdeal.zeroIdeal (L ⊗ B) hA a
  let J := LineSectionZeroIdeal.zeroIdeal B hB b
  let : Fintype ι := Fintype.ofFinite ι
  let : LinearOrder ι := LinearOrder.lift' (Fintype.equivFin ι) (Fintype.equivFin ι).injective
  obtain ⟨NI, hNI⟩ := exists_cut_pullback_power_vanishing f I.subschemeι L hI
  obtain ⟨NJ, hNJ⟩ := exists_cut_pullback_power_vanishing f J.subschemeι L hJ
  refine ⟨max NI NJ, fun n hn q => ?_⟩
  have hnI : NI ≤ n + 1 := (le_max_left NI NJ).trans (hn.trans (Nat.le_succ n))
  have hnJ : NJ ≤ n := (le_max_right NI NJ).trans hn
  let P := CanonicalGeometry.bundleTensorPower L n
  have hP : IsInvertible P := TensorPowerBaseIdealGrading.tensorPower_isInvertible hL n
  let e : L ⊗ P ≅ CanonicalGeometry.bundleTensorPower L (n + 1) :=
    β_ L P ≪≫ ModularCurves.monoidalTensorObjIso P L
  let eI := (Scheme.Modules.pullback I.subschemeι).mapIso e
  let c := twoCutCohomologyIso f U hU hUa L B P hL hB hP a ha b hb q
    (nativeH_subsingleton_of_iso eI (q + 1) (hNI (n + 1) hnI q))
    (nativeH_subsingleton_of_iso eI (q + 2) (hNI (n + 1) hnI (q + 1)))
    (hNJ n hnJ q) (hNJ n hnJ (q + 1))
  exact ⟨(fieldCechIso f e U (q + 2)).symm ≪≫ c⟩

/-- The SAME actual nonzero section of the original r-th power gives the
original n-th to (n+r)-th power multiplication/restriction complex. -/
def powerSectionSequence {X : Scheme.{u}} [IsIntegral X]
    (L : X.Modules) (hL : IsInvertible L) (r : ℕ)
    (s : unitObj X ⟶ CanonicalGeometry.bundleTensorPower L r) (hs : s ≠ 0) (n : ℕ) :
    ShortComplex X.Modules := by
  let A := CanonicalGeometry.bundleTensorPower L r
  let M := CanonicalGeometry.bundleTensorPower L n
  let hA := TensorPowerBaseIdealGrading.tensorPower_isInvertible hL r
  let hM := TensorPowerBaseIdealGrading.tensorPower_isInvertible hL n
  let S := sectionCutSequence A M hA hM s hs
  let I := LineSectionZeroIdeal.zeroIdeal A hA s
  let e : A ⊗ M ≅ CanonicalGeometry.bundleTensorPower L (n + r) :=
    β_ A M ≪≫ TensorPowerBaseIdealGrading.tensorPowerAddIso L n r
  exact transportedSequence S (Iso.refl M) e
    ((pushforward I.subschemeι).mapIso ((Scheme.Modules.pullback I.subschemeι).mapIso e))

/-- Exactness of the SAME original fixed-section power complex. -/
theorem powerSectionSequence_shortExact {X : Scheme.{u}} [IsIntegral X]
    (L : X.Modules) (hL : IsInvertible L) (r : ℕ)
    (s : unitObj X ⟶ CanonicalGeometry.bundleTensorPower L r) (hs : s ≠ 0) (n : ℕ) :
    (powerSectionSequence L hL r s hs n).ShortExact := by
  dsimp only [powerSectionSequence]
  apply ShortComplex.shortExact_of_iso (transportedSequenceIso _ _ _ _)
  exact sectionCutSequence_shortExact _ _ _ _ s hs

private theorem powerSectionSequence_homologyMap_epi_of_vanishing {k : Type u} [Field k]
    {X : Scheme.{u}} [IsIntegral X] [X.IsSeparated]
    (f : X ⟶ Spec (.of k)) {ι : Type u} [Finite ι] [LinearOrder ι]
    (U : ι → X.Opens) (hU : IsOpenCover U) (hUa : ∀ i, IsAffineOpen (U i))
    (L : X.Modules) (hL : IsInvertible L) (r : ℕ)
    (s : unitObj X ⟶ CanonicalGeometry.bundleTensorPower L r) (hs : s ≠ 0) (n q : ℕ)
    (h : Subsingleton (CategoryTheory.Sheaf.H
      ((Scheme.Modules.pullback (LineSectionZeroIdeal.zeroIdeal
        (CanonicalGeometry.bundleTensorPower L r)
        (TensorPowerBaseIdealGrading.tensorPower_isInvertible hL r) s).subschemeι).obj
          (CanonicalGeometry.bundleTensorPower L (n + r))).sheaf (q + 1))) :
    Epi (HomologicalComplex.homologyMap
      ((fieldComplexFunctor f U).map (powerSectionSequence L hL r s hs n).f) (q + 1)) := by
  let A := CanonicalGeometry.bundleTensorPower L r
  let M := CanonicalGeometry.bundleTensorPower L n
  let hA := TensorPowerBaseIdealGrading.tensorPower_isInvertible hL r
  let hM := TensorPowerBaseIdealGrading.tensorPower_isInvertible hL n
  let I := LineSectionZeroIdeal.zeroIdeal A hA s
  let S := sectionCutSequence A M hA hM s hs
  let e : A ⊗ M ≅ CanonicalGeometry.bundleTensorPower L (n + r) :=
    β_ A M ≪≫ TensorPowerBaseIdealGrading.tensorPowerAddIso L n r
  let H := fieldComplexFunctor f U ⋙
    HomologicalComplex.homologyFunctor (ModuleCat.{u} k) (.up ℕ) (q + 1)
  have h₀ : Epi (H.map S.f) := epi_sectionCut_homologyMap_of_vanishing f U hU hUa
    A M hA hM s hs q
      (nativeH_subsingleton_of_iso ((Scheme.Modules.pullback I.subschemeι).mapIso e) (q + 1) h)
  have := h₀
  have he : Epi (H.map S.f ≫ H.map e.hom) := by infer_instance
  change Epi (H.map ((Iso.refl M).inv ≫ S.f ≫ e.hom))
  simpa only [Iso.refl_inv, Category.id_comp, Functor.map_comp] using he

/-- Genuine native ampleness on the SAME actual single cut internally supplies
eventual H1 epimorphisms of the SAME fixed-section power multiplication maps.
The actual section is an ordinary input; its later construction by Euler growth
is not assumed here. No H1-stability or H0-surjectivity certificate is input. -/
theorem exists_singleCut_powerHOne_epi_of_ample {k : Type u} [Field k]
    {X : Scheme.{u}} [IsIntegral X] [X.IsSeparated]
    (f : X ⟶ Spec (.of k)) {ι : Type u} [Finite ι]
    (U : ι → X.Opens) (hU : IsOpenCover U) (hUa : ∀ i, IsAffineOpen (U i))
    (L : X.Modules) (hL : IsInvertible L) (r : ℕ)
    (s : unitObj X ⟶ CanonicalGeometry.bundleTensorPower L r) (hs : s ≠ 0) :
    let hA := TensorPowerBaseIdealGrading.tensorPower_isInvertible hL r
    let I := LineSectionZeroIdeal.zeroIdeal (CanonicalGeometry.bundleTensorPower L r) hA s
    SchemeLineAmpleness.IsAmple (I.subschemeι ≫ f) ((Scheme.Modules.pullback I.subschemeι).obj L) →
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → Epi (HomologicalComplex.homologyMap
      ((fieldComplexFunctor f U).map (powerSectionSequence L hL r s hs n).f) 1) := by
  classical
  dsimp only
  intro hI
  let hA := TensorPowerBaseIdealGrading.tensorPower_isInvertible hL r
  let I := LineSectionZeroIdeal.zeroIdeal (CanonicalGeometry.bundleTensorPower L r) hA s
  let : Fintype ι := Fintype.ofFinite ι
  let : LinearOrder ι := LinearOrder.lift' (Fintype.equivFin ι) (Fintype.equivFin ι).injective
  obtain ⟨N, hN⟩ := exists_cut_pullback_power_vanishing f I.subschemeι L hI
  refine ⟨N, fun n hn => ?_⟩
  have hnr : N ≤ n + r := by omega
  exact powerSectionSequence_homologyMap_epi_of_vanishing f U hU hUa L hL r s hs n 0
    (hN (n + r) hnr 0)

#print axioms powerSectionSequence_shortExact
#print axioms exists_singleCut_powerHOne_epi_of_ample
#print axioms twoCutCohomologyIso
#print axioms exists_twoCut_powerCohomologyIso_of_ample
#print axioms epi_sectionCut_homologyMap_of_vanishing
#print axioms isIso_sectionCut_homologyMap_of_vanishing
#print axioms exists_cut_pullback_power_vanishing
#print axioms sectionCutSequence_shortExact
#print axioms pushforward_fieldComplex_isZero_of_native
#print axioms homologyMap_isIso_of_adjacent_zero
end EnvelopeProperty.SeshadriAmplenessCriterionCutCohomology
