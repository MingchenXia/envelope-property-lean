import EnvelopeProperty.AlgGeom.SeshadriAmplenessCriterionSingleCutStability
import Lean

/-! # The same Cartier cut with a fixed original invertible coefficient -/

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open CategoryTheory.MonoidalCategory Scheme.Modules
universe u

namespace EnvelopeProperty.SeshadriAmplenessCriterionFixedCoefficientCutStability
open CanonicalGeometry SchemeCoherentEulerIndex SchemeCoherentEulerExact
open SeshadriAmplenessCriterionCutCohomology
attribute [local instance] Scheme.Modules.monoidalCategory Scheme.Modules.symmetricCategory

/- Read-only reference to the existing compiled private helpers. No environment
mutation or new mathematical axiom is performed. -/
open Lean Elab Term in
elab "existingSingleCutPrivate%" last:ident : term => do
  let env := (← getEnv).setExporting false
  let expected := `EnvelopeProperty.AlgGeom.SeshadriAmplenessCriterionSingleCutStability
  let some idx := env.getModuleIdxFor? `EnvelopeProperty.SeshadriAmplenessCriterionSingleCutStability.sections_surjective_of_hOne_mono | throwError "Missing native provider"
  unless env.header.moduleNames[idx]! == expected do throwError "Wrong native provider"
  let data := env.header.moduleData[idx]!
  let wanted := "_private.EnvelopeProperty.AlgGeom.SeshadriAmplenessCriterionSingleCutStability.0.EnvelopeProperty.SeshadriAmplenessCriterionSingleCutStability." ++ last.getId.toString
  let candidates := data.constNames.filter (fun n => n.toString == wanted)
  unless candidates.size == 1 do throwError "Nonunique actual kernel Name"
  let n := candidates[0]!
  unless env.getModuleIdxFor? n == some idx do throwError "Wrong private owner"
  let some ci := env.find? n | throwError "Missing actual private constant"
  unless ci.isTheorem do throwError "Private is not theorem"
  let expectedLevels := if last.getId == `nat_fixedStep_stabilizes then 0 else 1
  unless ci.levelParams.length == expectedLevels do throwError "Unexpected universe telescope"
  Lean.Meta.mkConstWithFreshMVarLevels n


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

private theorem epi_mapped_transported_first
    {C D : Type*} [Category* C] [Category* D] [HasZeroMorphisms C]
    (F : C ⥤ D) (S : ShortComplex C) {A B Q : C}
    (a : S.X₁ ≅ A) (b : S.X₂ ≅ B) (d : S.X₃ ≅ Q)
    (h : Epi (F.map S.f)) : Epi (F.map (transportedSequence S a b d).f) := by
  have h₁ : Epi (F.map a.inv) := inferInstance
  have h₂ : Epi (F.map b.hom) := inferInstance
  change Epi (F.map (a.inv ≫ S.f ≫ b.hom))
  rw [F.map_comp, F.map_comp]
  exact epi_comp' h₁ (epi_comp' h h₂)

private theorem epi_hOne_mapped_transported_first {k : Type u} [Field k]
    {C : Type*} [Category* C] [HasZeroMorphisms C]
    (F : C ⥤ CochainComplex (ModuleCat.{u} k) ℕ) (S : ShortComplex C)
    {A B Q : C} (a : S.X₁ ≅ A) (b : S.X₂ ≅ B) (d : S.X₃ ≅ Q)
    (h : Epi (HomologicalComplex.homologyMap (F.map S.f) 1)) :
    Epi (HomologicalComplex.homologyMap
      (F.map (transportedSequence S a b d).f) 1) :=
  epi_mapped_transported_first
    (F ⋙ HomologicalComplex.homologyFunctor (ModuleCat.{u} k) (.up ℕ) 1) S a b d h

/-- Ordinary equality elimination keeps both complete short-complex endpoints
and the literal native first-homology map. -/
private theorem epi_hOne_mapped_of_sequence_eq {k : Type u} [Field k]
    {C : Type*} [Category* C] [HasZeroMorphisms C]
    (F : C ⥤ CochainComplex (ModuleCat.{u} k) ℕ) (S T : ShortComplex C)
    (hST : S = T)
    (hS : Epi (HomologicalComplex.homologyMap (F.map S.f) 1)) :
    Epi (HomologicalComplex.homologyMap (F.map T.f) 1) := by
  cases hST
  exact hS

private def fixedCoefficientPowerTensorIso {X : Scheme.{u}}
    (E L : X.Modules) (r n : ℕ) :
    bundleTensorPower L r ⊗ (E ⊗ bundleTensorPower L n) ≅
      E ⊗ bundleTensorPower L (n + r) :=
  (α_ (bundleTensorPower L r) E (bundleTensorPower L n)).symm ≪≫
    (β_ (bundleTensorPower L r) E ⊗ᵢ Iso.refl _) ≪≫
    α_ E (bundleTensorPower L r) (bundleTensorPower L n) ≪≫
    (Iso.refl E ⊗ᵢ (β_ (bundleTensorPower L r) (bundleTensorPower L n) ≪≫
      TensorPowerBaseIdealGrading.tensorPowerAddIso L n r))

private theorem tensorInvertible {X : Scheme.{u}} (E P : X.Modules)
    (hE : IsInvertible E) (hP : IsInvertible P) : IsInvertible (E ⊗ P) :=
  (hE.tensorObj hP).of_iso (ModularCurves.monoidalTensorObjIso E P)

/-- Actual ideal inclusion and quotient for the same original section,
transported to the literal fixed-coefficient power objects. -/
def fixedCoefficientPowerSectionSequence {X : Scheme.{u}} [IsIntegral X]
    (E L : X.Modules) (hE : IsInvertible E) (hL : IsInvertible L) (r : ℕ)
    (s : unitObj X ⟶ bundleTensorPower L r) (hs : s ≠ 0) (n : ℕ) :
    ShortComplex X.Modules := by
  let A := bundleTensorPower L r
  let M := E ⊗ bundleTensorPower L n
  let hA := TensorPowerBaseIdealGrading.tensorPower_isInvertible hL r
  let hM := tensorInvertible E _ hE (TensorPowerBaseIdealGrading.tensorPower_isInvertible hL n)
  let S := sectionCutSequence A M hA hM s hs
  let g := (LineSectionZeroIdeal.zeroIdeal A hA s).subschemeι
  let e := fixedCoefficientPowerTensorIso E L r n
  exact transportedSequence S (Iso.refl M) e
    ((pushforward g).mapIso ((Scheme.Modules.pullback g).mapIso e))

/-- Exactness is inherited from the same original Cartier ideal sequence. -/
theorem fixedCoefficientPowerSectionSequence_shortExact {X : Scheme.{u}} [IsIntegral X]
    (E L : X.Modules) (hE : IsInvertible E) (hL : IsInvertible L) (r : ℕ)
    (s : unitObj X ⟶ bundleTensorPower L r) (hs : s ≠ 0) (n : ℕ) :
    (fixedCoefficientPowerSectionSequence E L hE hL r s hs n).ShortExact := by
  dsimp only [fixedCoefficientPowerSectionSequence]
  apply ShortComplex.shortExact_of_iso (transportedSequenceIso _ _ _ _)
  exact sectionCutSequence_shortExact _ _ _ _ s hs

private theorem finiteType_of_invertible {X : Scheme.{u}} (M : X.Modules)
    (hM : IsInvertible M) : M.IsFiniteType := by
  let : M.IsFinitePresentation := hM.isFinitePresentation
  obtain ⟨q, hq⟩ := SheafOfModules.IsFinitePresentation.exists_quasicoherentData M
  refine { exists_localGeneratorsData := ⟨q.localGeneratorsData, ?_⟩ }
  constructor
  intro i
  exact (hq.isFinite_presentation i).isFiniteType_generators

private theorem nativeH_subsingleton_of_iso {X : Scheme.{u}} {M N : X.Modules}
    (e : M ≅ N) (q : ℕ) (h : Subsingleton (CategoryTheory.Sheaf.H N.sheaf q)) :
    Subsingleton (CategoryTheory.Sheaf.H M.sheaf q) := by
  let eH := (CategoryTheory.Sheaf.functorH (_root_.Opens.grothendieckTopology X) q).mapIso
    ((Scheme.Modules.toSheaf X).mapIso e)
  exact AddCommGrpCat.subsingleton_of_isZero
    (IsZero.of_iso (@AddCommGrpCat.isZero_of_subsingleton _ h) eH)

private theorem exists_cut_pullback_fixedPower_vanishing {k : Type u} [Field k]
    {X D : Scheme.{u}} (f : X ⟶ Spec (.of k)) (g : D ⟶ X)
    (E L : X.Modules) (hE : IsInvertible E)
    (h : SchemeLineAmpleness.IsAmple (g ≫ f) ((Scheme.Modules.pullback g).obj L)) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ q : ℕ,
      Subsingleton (CategoryTheory.Sheaf.H
        ((Scheme.Modules.pullback g).obj (E ⊗ bundleTensorPower L n)).sheaf (q + 1)) := by
  let F := Scheme.Modules.pullback g
  let : F.Monoidal := pullbackMonoidal g
  let P := F.obj L
  let T := F.obj E
  obtain ⟨hP, r, hr, d, i, hi, _hif, ⟨e⟩⟩ := h
  let : IsClosedImmersion i := hi
  let hT := hE.pullback g
  let : T.IsQuasicoherent := hT.isQuasicoherent
  let : T.IsFiniteType := finiteType_of_invertible T hT
  obtain ⟨N, hN⟩ := @OriginalAmpleSerreVanishing.exists_sheafCohomology_bound
    k _ _ (Fin (d + 1)) _ D i hi T P _ _ hP r hr (0 : Fin (d + 1)) e.symm
  refine ⟨N, fun n hn q => ?_⟩
  let eT : F.obj (E ⊗ bundleTensorPower L n) ≅ T ⊗ bundleTensorPower P n :=
    (Functor.Monoidal.μIso F E (bundleTensorPower L n)).symm ≪≫
      (Iso.refl T ⊗ᵢ TestConfigurationSectionTransport.tensorPowerPullbackIso g L n)
  exact nativeH_subsingleton_of_iso eT (q + 1) (hN n hn q)

/-- Cut ampleness with the fixed original coefficient internally produces
eventual epimorphisms of the actual fixed-section H1 maps. -/
theorem exists_fixedCoefficient_singleCut_hOne_epi_of_ample {k : Type u} [Field k]
    {X : Scheme.{u}} [IsIntegral X] [X.IsSeparated]
    (f : X ⟶ Spec (.of k)) {ι : Type u} [Finite ι]
    (U : ι → X.Opens) (hU : IsOpenCover U) (hUa : ∀ i, IsAffineOpen (U i))
    (E L : X.Modules) (hE : IsInvertible E) (hL : IsInvertible L) (r : ℕ)
    (s : unitObj X ⟶ bundleTensorPower L r) (hs : s ≠ 0) :
    let hA := TensorPowerBaseIdealGrading.tensorPower_isInvertible hL r
    let I := LineSectionZeroIdeal.zeroIdeal (bundleTensorPower L r) hA s
    SchemeLineAmpleness.IsAmple (I.subschemeι ≫ f) ((Scheme.Modules.pullback I.subschemeι).obj L) →
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → Epi (HomologicalComplex.homologyMap
      ((fieldComplexFunctor f U).map
        (fixedCoefficientPowerSectionSequence E L hE hL r s hs n).f) 1) := by
  classical
  intro _cutPowerInvertible _cutIdeal hI
  let A := bundleTensorPower L r
  let hA := TensorPowerBaseIdealGrading.tensorPower_isInvertible hL r
  let g := (LineSectionZeroIdeal.zeroIdeal A hA s).subschemeι
  let : Fintype ι := Fintype.ofFinite ι
  let : LinearOrder ι := LinearOrder.lift' (Fintype.equivFin ι) (Fintype.equivFin ι).injective
  obtain ⟨N, hN⟩ := exists_cut_pullback_fixedPower_vanishing f g E L hE hI
  refine ⟨N, fun n hn => ?_⟩
  let M := E ⊗ bundleTensorPower L n
  let hM := tensorInvertible E _ hE (TensorPowerBaseIdealGrading.tensorPower_isInvertible hL n)
  let S := sectionCutSequence A M hA hM s hs
  let e := fixedCoefficientPowerTensorIso E L r n
  let H := fieldComplexFunctor f U ⋙
    HomologicalComplex.homologyFunctor (ModuleCat.{u} k) (.up ℕ) 1
  have h₀ : Epi (H.map S.f) := epi_sectionCut_homologyMap_of_vanishing f U hU hUa
    A M hA hM s hs 0
      (nativeH_subsingleton_of_iso ((Scheme.Modules.pullback g).mapIso e) 1 (hN (n + r) (by omega) 0))
  let P : X.Modules := E ⊗ bundleTensorPower L (n + r)
  let Q : X.Modules := (pushforward g).obj ((Scheme.Modules.pullback g).obj P)
  let a : S.X₁ ≅ M := Iso.refl M
  let b : S.X₂ ≅ P := e
  let d : S.X₃ ≅ Q := (pushforward g).mapIso ((Scheme.Modules.pullback g).mapIso e)
  have h₀' : Epi (HomologicalComplex.homologyMap ((fieldComplexFunctor f U).map S.f) 1) := h₀
  have ht := @epi_hOne_mapped_transported_first k _ X.Modules _ _
    (fieldComplexFunctor f U) S M P Q a b d h₀'
  have hseq : fixedCoefficientPowerSectionSequence E L hE hL r s hs n =
      transportedSequence S a b d := rfl
  exact @epi_hOne_mapped_of_sequence_eq k _ X.Modules _ _
    (fieldComplexFunctor f U) (transportedSequence S a b d)
    (fixedCoefficientPowerSectionSequence E L hE hL r s hs n) hseq.symm ht

/-- Genuine projective coherent finiteness makes the same actual fixed-E
first-cohomology maps eventually isomorphisms, with no stability certificate. -/
theorem exists_fixedCoefficient_singleCut_hOne_isIso_of_ample {k : Type u} [Field k]
    {X : Scheme.{u}} [IsIntegral X] [X.IsSeparated]
    (f : X ⟶ Spec (.of k)) (hf : IsProjectiveFactorization f)
    {ι : Type u} [Finite ι] (U : ι → X.Opens) (hU : IsOpenCover U)
    (hUa : ∀ i, IsAffineOpen (U i))
    (E L : X.Modules) (hE : IsInvertible E) (hL : IsInvertible L) (r : ℕ) (hr : 0 < r)
    (s : unitObj X ⟶ bundleTensorPower L r) (hs : s ≠ 0) :
    let hA := TensorPowerBaseIdealGrading.tensorPower_isInvertible hL r
    let I := LineSectionZeroIdeal.zeroIdeal (bundleTensorPower L r) hA s
    SchemeLineAmpleness.IsAmple (I.subschemeι ≫ f) ((Scheme.Modules.pullback I.subschemeι).obj L) →
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → IsIso (HomologicalComplex.homologyMap
      ((fieldComplexFunctor f U).map
        (fixedCoefficientPowerSectionSequence E L hE hL r s hs n).f) 1) := by
  dsimp only
  intro hI
  obtain ⟨N₀, hN₀⟩ := exists_fixedCoefficient_singleCut_hOne_epi_of_ample
    f U hU hUa E L hE hL r s hs hI
  let V : ℕ → ModuleCat.{u} k := fun n =>
    ((fieldComplexFunctor f U).obj (E ⊗ bundleTensorPower L n)).homology 1
  let v (n : ℕ) : V n ⟶ V (n + r) := HomologicalComplex.homologyMap
    ((fieldComplexFunctor f U).map
      (fixedCoefficientPowerSectionSequence E L hE hL r s hs n).f) 1
  have hfinite (n : ℕ) : Module.Finite k (V n) := by
    let P := E ⊗ bundleTensorPower L n
    have hP := tensorInvertible E _ hE (TensorPowerBaseIdealGrading.tensorPower_isInvertible hL n)
    let : P.IsQuasicoherent := hP.isQuasicoherent
    let : P.IsFiniteType := finiteType_of_invertible P hP
    let : Module.Finite k (fieldCech f P U 1) :=
      SchemeCoherentEulerCharacteristic.fieldCech_finite f hf P U hU hUa 1
    exact Module.Finite.equiv (fieldComplexHomologyIso f P U 1).symm.toLinearEquiv
  have hstep (n : ℕ) (hn : N₀ ≤ n) :
      Module.finrank k (V (n + r)) ≤ Module.finrank k (V n) := by
    let : Module.Finite k (V n) := hfinite n
    have hepi : Epi (v n) := hN₀ n hn
    exact LinearMap.finrank_le_finrank_of_surjective (f := (v n).hom)
      ((ModuleCat.epi_iff_surjective (v n)).mp hepi)
  obtain ⟨N, hN, hdim⟩ := (existingSingleCutPrivate% nat_fixedStep_stabilizes)
    (fun n => Module.finrank k (V n)) r hr N₀ hstep
  refine ⟨N, fun n hn => ?_⟩
  change IsIso (v n)
  let : Module.Finite k (V n) := hfinite n
  let : Module.Finite k (V (n + r)) := hfinite (n + r)
  have hepi : Epi (v n) := hN₀ n (hN.trans hn)
  have hsurj := (ModuleCat.epi_iff_surjective (v n)).mp hepi
  have hinj := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (hdim n hn).symm).mpr hsurj
  have : Mono (v n) := (ModuleCat.mono_iff_injective (v n)).mpr hinj
  have : Epi (v n) := hepi
  exact isIso_of_mono_of_epi _

private theorem fixedCoefficientSequence_standardUnit_factorization
    {X : Scheme.{u}} [IsIntegral X]
    (E L : X.Modules) (hE : IsInvertible E) (hL : IsInvertible L) (r : ℕ)
    (s : unitObj X ⟶ bundleTensorPower L r) (hs : s ≠ 0) (n : ℕ) :
    let g := (LineSectionZeroIdeal.zeroIdeal (bundleTensorPower L r)
      (TensorPowerBaseIdealGrading.tensorPower_isInvertible hL r) s).subschemeι
    ∃ τ : (Scheme.Modules.pullback g).obj (E ⊗ bundleTensorPower L (n + r)) ≅
          (Scheme.Modules.pullback g).obj (E ⊗ bundleTensorPower L (n + r)),
      (fixedCoefficientPowerSectionSequence E L hE hL r s hs n).g =
        (pullbackPushforwardAdjunction g).unit.app (E ⊗ bundleTensorPower L (n + r)) ≫
          (pushforward g).map τ.hom := by
  let A := bundleTensorPower L r
  let M := E ⊗ bundleTensorPower L n
  let hA := TensorPowerBaseIdealGrading.tensorPower_isInvertible hL r
  let hM := tensorInvertible E _ hE (TensorPowerBaseIdealGrading.tensorPower_isInvertible hL n)
  let g := (LineSectionZeroIdeal.zeroIdeal A hA s).subschemeι
  let F := Scheme.Modules.pullback g
  let G := pushforward g
  let adj := pullbackPushforwardAdjunction g
  let e := fixedCoefficientPowerTensorIso E L r n
  obtain ⟨τ, hτ⟩ := (existingSingleCutPrivate% sectionCutSequence_standardUnit_factorization)
    A M hA hM s hs
  refine ⟨(F.mapIso e).symm ≪≫ τ ≪≫ F.mapIso e, ?_⟩
  change e.inv ≫ (sectionCutSequence A M hA hM s hs).g ≫ G.map (F.map e.hom) = _
  rw [hτ]
  have he : e.inv ≫ adj.unit.app (A ⊗ M) =
      adj.unit.app (E ⊗ bundleTensorPower L (n + r)) ≫ G.map (F.map e.inv) :=
    adj.unit.naturality e.inv
  calc
    _ = (e.inv ≫ adj.unit.app (A ⊗ M)) ≫ G.map τ.hom ≫ G.map (F.map e.hom) := by
      simp only [Category.assoc]
      rfl
    _ = (adj.unit.app (E ⊗ bundleTensorPower L (n + r)) ≫ G.map (F.map e.inv)) ≫
        G.map τ.hom ≫ G.map (F.map e.hom) := by rw [he]
    _ = _ := by
      simp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_inv,
        Functor.mapIso_hom, Functor.map_comp, Category.assoc]
      rfl

/-- The literal original standard restriction on the same E tensor powers is
eventually onto, using only projectivity and native ampleness on the same cut. -/
theorem exists_fixedCoefficient_singleCut_sections_surjective_of_ample
    {k : Type u} [Field k] {X : Scheme.{u}} [IsIntegral X] [X.IsSeparated]
    (f : X ⟶ Spec (.of k)) (hf : IsProjectiveFactorization f)
    {ι : Type u} [Finite ι] (U : ι → X.Opens) (hU : IsOpenCover U)
    (hUa : ∀ i, IsAffineOpen (U i))
    (E L : X.Modules) (hE : IsInvertible E) (hL : IsInvertible L) (r : ℕ) (hr : 0 < r)
    (s : unitObj X ⟶ bundleTensorPower L r) (hs : s ≠ 0) :
    let hA := TensorPowerBaseIdealGrading.tensorPower_isInvertible hL r
    let I := LineSectionZeroIdeal.zeroIdeal (bundleTensorPower L r) hA s
    SchemeLineAmpleness.IsAmple (I.subschemeι ≫ f) ((Scheme.Modules.pullback I.subschemeι).obj L) →
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → Function.Surjective
      (((pullbackPushforwardAdjunction I.subschemeι).unit.app
        (E ⊗ bundleTensorPower L (n + r))).app (⊤ : X.Opens)) := by
  dsimp only
  intro hI
  obtain ⟨N, hN⟩ := exists_fixedCoefficient_singleCut_hOne_isIso_of_ample
    f hf U hU hUa E L hE hL r hr s hs hI
  refine ⟨N, fun n hn => ?_⟩
  let g := (LineSectionZeroIdeal.zeroIdeal (bundleTensorPower L r)
    (TensorPowerBaseIdealGrading.tensorPower_isInvertible hL r) s).subschemeι
  let F := Scheme.Modules.pullback g
  let G := pushforward g
  let P := E ⊗ bundleTensorPower L (n + r)
  let S := fixedCoefficientPowerSectionSequence E L hE hL r s hs n
  have hM := tensorInvertible E _ hE (TensorPowerBaseIdealGrading.tensorPower_isInvertible hL n)
  have hP := tensorInvertible E _ hE (TensorPowerBaseIdealGrading.tensorPower_isInvertible hL (n + r))
  let : S.X₁.IsQuasicoherent := by
    change (E ⊗ bundleTensorPower L n).IsQuasicoherent
    exact hM.isQuasicoherent
  let : S.X₂.IsQuasicoherent := by change P.IsQuasicoherent; exact hP.isQuasicoherent
  let : (F.obj P).IsQuasicoherent := (hP.pullback g).isQuasicoherent
  let : S.X₃.IsQuasicoherent := by
    change (G.obj (F.obj P)).IsQuasicoherent
    exact isQuasicoherent_pushforward_of_isAffineHom g
  have : IsIso (HomologicalComplex.homologyMap ((fieldComplexFunctor f U).map S.f) 1) := hN n hn
  have hsurj := SeshadriAmplenessCriterionSingleCutStability.sections_surjective_of_hOne_mono
    f U hU hUa S (fixedCoefficientPowerSectionSequence_shortExact E L hE hL r s hs n)
      inferInstance
  obtain ⟨τ, hτ⟩ := fixedCoefficientSequence_standardUnit_factorization E L hE hL r s hs n
  let eΓ := (SheafOfModules.evaluation X.ringCatSheaf (.op (⊤ : X.Opens))).mapIso (G.mapIso τ)
  intro z
  obtain ⟨x, hx⟩ := hsurj (eΓ.hom z)
  refine ⟨x, eΓ.toLinearEquiv.injective ?_⟩
  change ((G.map τ.hom).app (⊤ : X.Opens))
      (((pullbackPushforwardAdjunction g).unit.app P).app (⊤ : X.Opens) x) = eΓ.hom z
  exact (congrArg (fun v => v.app (⊤ : X.Opens) x) hτ).symm.trans hx

end EnvelopeProperty.SeshadriAmplenessCriterionFixedCoefficientCutStability
