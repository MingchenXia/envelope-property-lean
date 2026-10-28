import EnvelopeProperty.Vanishing.NadelNefBigGlobalPairBaseOpenComposition
import EnvelopeProperty.Vanishing.ArithmeticOriginalLineGenerated
import EnvelopeProperty.AlgGeom.PositivePowerProjectiveGeneration
import EnvelopeProperty.AlgGeom.ProjectiveSegrePullbackSections
import EnvelopeProperty.AlgGeom.SchemeAmpleClosedRestriction
import EnvelopeProperty.AlgGeom.ProjectiveTwistCoefficientPullback

/-! # Actual exceptional positivity over the original arbitrary affine base

The original finite generators give a closed pair over the original field.
The genuine projective coefficient Cartesian square transports that pair to
the original R, so the original relative embedding and Segre construction
give the actual exceptional ample line without a domain restriction on R.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open Scheme.Modules MvPolynomial DeJongAlterations
universe u
namespace EnvelopeProperty.Vanishing.RelativeNadelCoverExceptionalAmple
open CanonicalGeometry NadelNefBigGlobalPairClosed ProjBerk
attribute [local instance] Scheme.Modules.monoidalCategory Scheme.Modules.symmetricCategory
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
private noncomputable instance actualPullbackMonoidal {X Y : Scheme.{u}} (f : Y ⟶ X) :
    (Scheme.Modules.pullback f).Monoidal := pullbackMonoidal f

variable {k R : Type u} [Field k] [CommRing R] [Algebra k R] {X : Scheme.{u}}
    (p : X ⟶ Spec (.of k)) (π : X ⟶ Spec (.of R))
    (hπ : π ≫ Spec.map (CommRingCat.ofHom (algebraMap k R)) = p)
include hπ

/-- Actual coefficient base change identifies the whole target square. -/
theorem targetSquare (s : ℕ) :
    IsPullback (pullback.fst π (projectiveSpaceStructure R s))
      (pullback.snd π (projectiveSpaceStructure R s) ≫
        nativeCoefficientMap (n := s) (algebraMap k R))
      p (projectiveSpaceStructure k s) := by
  have H := (IsPullback.of_hasPullback π (projectiveSpaceStructure R s)).flip.paste_horiz
    (isPullback_nativeCoefficientBaseChange (n := s) (algebraMap k R))
  rw [hπ] at H
  exact H.flip

/-- The actual whole relative target product is the original field product. -/
def targetIso (s : ℕ) :
    pullback π (projectiveSpaceStructure R s) ≅ pullback p (projectiveSpaceStructure k s) :=
  (targetSquare p π hπ s).isoPullback

@[reassoc] theorem targetIso_fst (s : ℕ) :
    (targetIso p π hπ s).hom ≫ pullback.fst p (projectiveSpaceStructure k s) =
      pullback.fst π (projectiveSpaceStructure R s) :=
  (targetSquare p π hπ s).isoPullback_hom_fst

@[reassoc] theorem targetIso_snd (s : ℕ) :
    (targetIso p π hπ s).hom ≫ pullback.snd p (projectiveSpaceStructure k s) =
      pullback.snd π (projectiveSpaceStructure R s) ≫
        nativeCoefficientMap (n := s) (algebraMap k R) :=
  (targetSquare p π hπ s).isoPullback_hom_snd

variable (D : X.IdealSheafData) (B : X.Modules) (hB : IsInvertible B)
    (G : (D.toModules ⊗ B).GeneratingSections) [Fintype G.I]

/-- The original generated field pair, on the whole relative target. -/
def relativePair : D.blowUp ⟶ pullback π (projectiveSpaceStructure R (Fintype.card G.I)) :=
  globalPair D p B hB G ≫ (targetIso p π hπ (Fintype.card G.I)).inv

@[reassoc] theorem relativePair_fst :
    relativePair p π hπ D B hB G ≫ pullback.fst _ _ = D.blowUpπ := by
  have he : (targetIso p π hπ (Fintype.card G.I)).inv ≫
      pullback.fst π (projectiveSpaceStructure R (Fintype.card G.I)) =
      pullback.fst p (projectiveSpaceStructure k (Fintype.card G.I)) := by
    apply (cancel_epi (targetIso p π hπ (Fintype.card G.I)).hom).mp
    rw [Iso.hom_inv_id_assoc]
    exact (targetIso_fst p π hπ (Fintype.card G.I)).symm
  change (globalPair D p B hB G ≫ _) ≫ _ = _
  rw [Category.assoc, he]
  exact globalPair_fst D p B hB G

/-- The SAME original generated relative projective map. -/
def relativeMap : D.blowUp ⟶ projectiveSpace R (Fintype.card G.I) :=
  relativePair p π hπ D B hB G ≫ pullback.snd _ _

@[reassoc] theorem relativeMap_structure :
    relativeMap p π hπ D B hB G ≫ projectiveSpaceStructure R (Fintype.card G.I) =
      D.blowUpπ ≫ π := by
  rw [relativeMap, Category.assoc, ← pullback.condition, ← Category.assoc, relativePair_fst]

@[reassoc] theorem relativeMap_coefficient :
    relativeMap p π hπ D B hB G ≫ nativeCoefficientMap (algebraMap k R) =
      globalMap D p B hB G := by
  have he : (targetIso p π hπ (Fintype.card G.I)).inv ≫
      pullback.snd π (projectiveSpaceStructure R (Fintype.card G.I)) ≫
        nativeCoefficientMap (n := Fintype.card G.I) (algebraMap k R) =
      pullback.snd p (projectiveSpaceStructure k (Fintype.card G.I)) := by
    apply (cancel_epi (targetIso p π hπ (Fintype.card G.I)).hom).mp
    rw [Iso.hom_inv_id_assoc]
    exact (targetIso_snd p π hπ (Fintype.card G.I)).symm
  change ((globalPair D p B hB G ≫ _) ≫ _) ≫ _ = _
  rw [Category.assoc, Category.assoc, he]
  exact globalPair_snd D p B hB G

/-- The actual coefficient lift retains the entire generated exceptional line. -/
def relativeMapTwistIso :
    ProjectiveSegrePullbackSections.line (relativeMap p π hπ D B hB G) ≅
      D.exceptionalDivisor.toModules ⊗ (Scheme.Modules.pullback D.blowUpπ).obj B := by
  let q := relativeMap p π hπ D B hB G
  let H := NadelNefBigGlobalGenerators.comapGenerators D D.blowUpπ B hB G
  let : Fintype H.I := (inferInstance : Fintype G.I)
  let e := ArithmeticOriginalLineGenerated.projectiveTwistIso (D.blowUpπ ≫ p)
    ((Scheme.IdealSheafData.blowUp.isInvertible_comap_π D).isInvertibleModule_toModules.monoidalTensor
      (hB.pullback D.blowUpπ)) H (0 : Fin (Fintype.card G.I + 1))
  exact (Scheme.Modules.pullback q).mapIso
      (ProjectiveTwistCoefficientPullback.coordinatePolePowerPullbackIso
        (algebraMap k R) (0 : Fin (Fintype.card G.I + 1)) 1).symm ≪≫
    (pullbackComp q (nativeCoefficientMap (algebraMap k R))).app _ ≪≫
    (pullbackCongr (relativeMap_coefficient p π hπ D B hB G)).app _ ≪≫ e

variable {m : ℕ} (j : X ⟶ projectiveSpace R m) [IsClosedImmersion j]
    (hj : j ≫ projectiveSpaceStructure R m = π)

private theorem generatedPair_isClosedImmersion :
    IsClosedImmersion (ProjectiveSegrePullbackSections.pair (D.blowUpπ ≫ j)
      (relativeMap p π hπ D B hB G)
      (by rw [Category.assoc, hj, relativeMap_structure])) := by
  let q := projectiveSpaceStructure R (Fintype.card G.I)
  let F := pullback.map π q (projectiveSpaceStructure R m) q j (𝟙 _) (𝟙 _)
    ((Category.comp_id π).trans hj.symm)
    ((Category.comp_id q).trans (Category.id_comp q).symm)
  have hF : IsClosedImmersion F :=
    MorphismProperty.pullbackMap (P := @IsClosedImmersion)
      (inferInstance : IsClosedImmersion j) (inferInstance : IsClosedImmersion (𝟙 _))
      hj.symm (Category.id_comp q).symm
  let : IsClosedImmersion F := hF
  let : IsClosedImmersion (globalPair D p B hB G) :=
    NadelNefBigGlobalPairBaseOpenComposition.globalPair_isClosedImmersion D p B hB G
  let : IsClosedImmersion (relativePair p π hπ D B hB G) := by
    dsimp only [relativePair]
    infer_instance
  have hfac : ProjectiveSegrePullbackSections.pair (D.blowUpπ ≫ j)
      (relativeMap p π hπ D B hB G)
      (by rw [Category.assoc, hj, relativeMap_structure]) =
      relativePair p π hπ D B hB G ≫ F := by
    apply pullback.hom_ext
    · simp only [ProjectiveSegrePullbackSections.pair, F, q, pullback.map,
        Category.assoc, pullback.lift_fst]
      exact (relativePair_fst_assoc p π hπ D B hB G j).symm
    · simp only [ProjectiveSegrePullbackSections.pair, F, q, pullback.map,
        Category.assoc, pullback.lift_snd, Category.comp_id, relativeMap]
  rw [hfac]
  infer_instance

include hj hB G in
private theorem isVeryAmple_generated_exceptional :
    SchemeLineAmpleness.IsVeryAmple (D.blowUpπ ≫ π)
      (D.exceptionalDivisor.toModules ⊗ (Scheme.Modules.pullback D.blowUpπ).obj
        (ProjectiveSegrePullbackSections.line j ⊗ B)) := by
  let q := relativeMap p π hπ D B hB G
  have hq : (D.blowUpπ ≫ j) ≫ projectiveSpaceStructure R m =
      q ≫ projectiveSpaceStructure R (Fintype.card G.I) := by
    rw [Category.assoc, hj, relativeMap_structure]
  let δ := ProjectiveSegrePullbackSections.pair (D.blowUpπ ≫ j) q hq
  let : IsClosedImmersion δ := generatedPair_isClosedImmersion p π hπ D B hB G j hj
  refine ⟨Algebra.Segre.dimension m (Fintype.card G.I),
    ProjectiveSegrePullbackSections.morphism (D.blowUpπ ≫ j) q hq, ?_, ?_, ?_⟩
  · exact IsClosedImmersion.comp δ (Geometry.Segre.segre R m (Fintype.card G.I))
  · exact (ProjectiveSegrePullbackSections.morphism_structure (D.blowUpπ ≫ j) q hq).trans
      ((Category.assoc D.blowUpπ j _).trans (congrArg (fun t => D.blowUpπ ≫ t) hj))
  · let A := (Scheme.Modules.pullback D.blowUpπ).obj (ProjectiveSegrePullbackSections.line j)
    let K := D.exceptionalDivisor.toModules
    let T := (Scheme.Modules.pullback D.blowUpπ).obj B
    exact ⟨ProjectiveSegrePullbackSections.lineIso (D.blowUpπ ≫ j) q hq ≪≫
      ((((pullbackComp D.blowUpπ j).app _).symm) ⊗ᵢ relativeMapTwistIso p π hπ D B hB G) ≪≫
      (α_ A K T).symm ≪≫ ((β_ A K) ⊗ᵢ Iso.refl T) ≪≫ (α_ K A T) ≪≫
      (Iso.refl K ⊗ᵢ Functor.Monoidal.μIso (Scheme.Modules.pullback D.blowUpπ)
        (ProjectiveSegrePullbackSections.line j) B)⟩

omit j hj B hB G in
/-- The original ample line and original coefficient square internally produce
a positive twist making the actual original exceptional line very ample over
the SAME arbitrary R.  No positivity certificate is an input. -/
theorem exists_positive_isVeryAmple_exceptional_tensor_pullback [IsLocallyNoetherian X]
    (C : X.Modules) (hC : SchemeLineAmpleness.IsAmple π C) :
    ∃ r : ℕ, 0 < r ∧ SchemeLineAmpleness.IsVeryAmple (D.blowUpπ ≫ π)
      (D.exceptionalDivisor.toModules ⊗ (Scheme.Modules.pullback D.blowUpπ).obj (bundleTensorPower C r)) := by
  obtain ⟨a, ha, m, j, hj, hjp, ⟨eA⟩⟩ := hC.2
  let : IsClosedImmersion j := hj
  obtain ⟨N, hN⟩ := NadelNefBigGlobalSerreGenerators.exists_eventual_controlled_generators
    j D D.blowUpπ (0 : Fin (m + 1))
  obtain ⟨G, hG, _⟩ := hN N (le_refl N)
  let B := (Scheme.Modules.pullback j).obj (coordinateHyperplaneTwist (R := R) (0 : Fin (m + 1)) (N : ℤ))
  let hB := (coordinateHyperplaneTwist_isInvertible (R := R) (0 : Fin (m + 1)) (N : ℤ)).pullback j
  let := hG
  let : Fintype G.I := Fintype.ofFinite G.I
  have hV := isVeryAmple_generated_exceptional p π hπ D B hB G j hjp
  let E : ProjectiveSegrePullbackSections.line j ⊗ B ≅ bundleTensorPower C (a + a * N) :=
    (eA ⊗ᵢ (PositivePowerProjectiveGeneration.blockTwistIso j C a
      (0 : Fin (m + 1)) eA N).symm) ≪≫
      TensorPowerBaseIdealGrading.tensorPowerAddIso C a (a * N)
  exact ⟨a + a * N, lt_of_lt_of_le ha (Nat.le_add_right _ _),
    SchemeAmpleClosedRestriction.veryAmple_of_iso hV
      (Iso.refl D.exceptionalDivisor.toModules ⊗ᵢ (Scheme.Modules.pullback D.blowUpπ).mapIso E)⟩

omit j hj B hB G in
/-- The actual original exceptional ideal becomes ample over the original R
after an internally produced positive power of the original ample seed. -/
theorem exists_positive_isAmple_exceptional_tensor_pullback [IsLocallyNoetherian X]
    (C : X.Modules) (hC : SchemeLineAmpleness.IsAmple π C) :
    ∃ r : ℕ, 0 < r ∧ SchemeLineAmpleness.IsAmple (D.blowUpπ ≫ π)
      (D.exceptionalDivisor.toModules ⊗ (Scheme.Modules.pullback D.blowUpπ).obj (bundleTensorPower C r)) := by
  obtain ⟨r, hr, hV⟩ := exists_positive_isVeryAmple_exceptional_tensor_pullback p π hπ D C hC
  let L := D.exceptionalDivisor.toModules ⊗ (Scheme.Modules.pullback D.blowUpπ).obj (bundleTensorPower C r)
  let E : bundleTensorPower L 1 ≅ L :=
    (ModularCurves.monoidalTensorObjIso (bundleTensorPower L 0) L).symm ≪≫
      ((ModularCurves.monoidalUnitObjIso D.blowUp).symm ⊗ᵢ Iso.refl L) ≪≫ λ_ L
  exact ⟨r, hr, hV.isInvertible, 1, Nat.zero_lt_one,
    SchemeAmpleClosedRestriction.veryAmple_of_iso hV E.symm⟩

end EnvelopeProperty.Vanishing.RelativeNadelCoverExceptionalAmple
