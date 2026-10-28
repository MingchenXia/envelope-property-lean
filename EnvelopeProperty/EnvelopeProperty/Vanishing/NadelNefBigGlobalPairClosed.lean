import EnvelopeProperty.Vanishing.NadelNefBigGlobalSerreGenerators
import EnvelopeProperty.Vanishing.NadelNefBigAffineIdealGenerators
import EnvelopeProperty.Vanishing.NadelNefBigExceptionalProjectiveClosed
import EnvelopeProperty.AlgGeom.IdealModulePullbackComp
import EnvelopeProperty.AlgGeom.ProjectiveBlowupSequence
import Hironaka.Scheme.BlowUp.Glue.Global
import Mathlib.AlgebraicGeometry.ZariskisMainTheorem

/-! # The same actual twisted-generator map on whole original base blowups

The first producer treats the ENTIRE blowup over a framed affine base, using
the actual source generating family. Its coefficients and their span are
internally derived, and its conclusion concerns the SAME original projective
map. Global target-base gluing is the subsequent obligation. No numerical
big predicate, monomorphism or matching-map certificate is introduced.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.MonoidalCategory Opposite
open Scheme.Modules
universe u

namespace EnvelopeProperty.Vanishing.NadelNefBigGlobalPairClosed

open SchemeGeneratingSectionsUnit SchemeLineSectionEvaluation
open NadelBlowupCanonicalExceptionalGenerators NadelNefBigGlobalFrames
open GeneratedLineProjectiveMap GeneratedLineProjectiveAffineMap
open SchemeGeneratedLineCoefficients
attribute [local instance] Scheme.Modules.monoidalCategory

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem tensorInvertible {Y : Scheme.{u}} {M N : Y.Modules}
    (hM : IsInvertible M) (hN : IsInvertible N) : IsInvertible (M ⊗ N) :=
  (hM.tensorObj hN).of_iso (ModularCurves.monoidalTensorObjIso M N)

section AffineBase

variable {A : Type u} [CommRing A] (I : Ideal A)

variable (B : ((Spec (CommRingCat.of A))).Modules) (hB : IsInvertible B)
  (G : (((originalIdeal I)).toModules ⊗ B).GeneratingSections)
  (e : B ≅ unitObj (Spec (CommRingCat.of A)))

private def sourceGenerators
    (B : (Spec (CommRingCat.of A)).Modules)
    (G : ((originalIdeal I).toModules ⊗ B).GeneratingSections)
    (e : B ≅ unitObj (Spec (CommRingCat.of A))) : ((originalIdeal I)).toModules.GeneratingSections :=
  G.ofEpi (untwist ((originalIdeal I)).toModules B e).hom

private theorem sourceIdeal_map_eq :
    Ideal.map (Scheme.ΓSpecIso (.of A)).hom.hom
      ((originalIdeal I).ideal ⟨⊤, isAffineOpen_top _⟩) = I := by
  have hD : (originalIdeal I).ideal ⟨⊤, isAffineOpen_top _⟩ =
      I.map (Scheme.ΓSpecIso (.of A)).inv.hom := ofIdealTop_ideal_top _
  rw [hD, Ideal.map_map, ← CommRingCat.hom_comp, Iso.inv_hom_id,
    CommRingCat.hom_id, Ideal.map_id]

private def sourceValue (i : G.I) : ((originalIdeal I)).ideal ⟨⊤, isAffineOpen_top _⟩ :=
  @NadelNefBigAffineIdealGenerators.generatorValue (CommRingCat.of A)
    (originalIdeal I) (sourceGenerators I B G e) i

private theorem sourceValue_mem (i : G.I) :
    (Scheme.ΓSpecIso (.of A)).hom.hom (sourceValue I B G e i) ∈ I := by
  have h := Ideal.mem_map_of_mem (Scheme.ΓSpecIso (.of A)).hom.hom
    (sourceValue I B G e i).property
  exact (sourceIdeal_map_eq I).le h

private def sourceCoefficient (i : G.I) : I :=
  ⟨(Scheme.ΓSpecIso (.of A)).hom.hom (sourceValue I B G e i),
    sourceValue_mem I B G e i⟩

private theorem sourceCoefficient_span :
    Ideal.span (Set.range (fun i : G.I => (sourceCoefficient I B G e i : A))) = I := by
  have hs := @NadelNefBigAffineIdealGenerators.span_generatorValues (CommRingCat.of A)
    (originalIdeal I) (sourceGenerators I B G e)
  have hmap := congrArg (Ideal.map (Scheme.ΓSpecIso (.of A)).hom.hom) hs
  rw [Ideal.map_span, ← Set.range_comp] at hmap
  change Ideal.span (Set.range (fun i : G.I => (sourceCoefficient I B G e i : A))) =
    Ideal.map (Scheme.ΓSpecIso (.of A)).hom.hom
      ((originalIdeal I).ideal ⟨⊤, isAffineOpen_top _⟩) at hmap
  exact hmap.trans (sourceIdeal_map_eq I)

private theorem sourceGenerator_eq_originalSection (i : G.I) :
    generatorHom (sourceGenerators I B G e) i =
      originalSection I (sourceCoefficient I B G e i) := by
  apply (cancel_mono ((originalIdeal I)).toModulesInclusion).mp
  rw [originalSection_inclusion]
  rw [unitHom_eq_globalScalar
    (generatorHom (sourceGenerators I B G e) i ≫ ((originalIdeal I)).toModulesInclusion)]
  apply congrArg ModularCurves.unitEndomorphismOfTopSection
  exact (ConcreteCategory.congr_hom (Scheme.ΓSpecIso (.of A)).hom_inv_id
    (sourceValue I B G e i)).symm

private def targetUntwist :
    (((affineBlowUp.exceptionalIdeal I).toModules) ⊗ (pullback (affineBlowUp.π I)).obj B) ≅ ((affineBlowUp.exceptionalIdeal I).toModules) :=
  untwist ((affineBlowUp.exceptionalIdeal I).toModules) ((pullback (affineBlowUp.π I)).obj B) ((pullback (affineBlowUp.π I)).mapIso e ≪≫ pullbackUnitIso (affineBlowUp.π I))

private def transportedGenerators :
    (((affineBlowUp.exceptionalIdeal I).toModules) ⊗ (pullback (affineBlowUp.π I)).obj B).GeneratingSections :=
  NadelNefBigGlobalGenerators.comapGenerators (originalIdeal I) (affineBlowUp.π I) B hB G

private theorem transported_generator_untwist (i : G.I) :
    generatorHom (transportedGenerators I B hB G) i ≫ (targetUntwist I B e).hom =
      exceptionalSection I (sourceCoefficient I B G e i) := by
  have htrans : generatorHom (transportedGenerators I B hB G) i ≫
      (targetUntwist I B e).hom =
      pullbackSectionHom (affineBlowUp.π I)
        (generatorHom G i ≫ (untwist (originalIdeal I).toModules B e).hom) ≫
          (originalIdeal I).toModulesComapPullbackMap (affineBlowUp.π I) :=
    NadelNefBigGlobalFrames.generatorHom_comapGenerators_untwist
      (originalIdeal I) (affineBlowUp.π I) B hB e G i
  have hs : generatorHom G i ≫ (untwist ((originalIdeal I)).toModules B e).hom =
      originalSection I (sourceCoefficient I B G e i) :=
    (generatorHom_ofEpi G (untwist ((originalIdeal I)).toModules B e).hom i).symm.trans
      (sourceGenerator_eq_originalSection I B G e i)
  exact htrans.trans (congrArg (fun s => pullbackSectionHom (affineBlowUp.π I) s ≫
    ((originalIdeal I)).toModulesComapPullbackMap (affineBlowUp.π I)) hs)

variable [Fintype G.I]

/-- The SAME actual source family gives the original twisted exceptional map. -/
def affineFramedMap :
    (affineBlowUp I) ⟶ DeJongAlterations.projectiveSpace A (Fintype.card G.I) := by
  let H := transportedGenerators I B hB G
  let : Fintype H.I := (inferInstance : Fintype G.I)
  exact projectiveMap (affineBlowUp.π I)
    (tensorInvertible (affineBlowUp.isInvertible_exceptionalIdeal I).isInvertibleModule_toModules
      (hB.pullback (affineBlowUp.π I))) (transportedGenerators I B hB G)

private def pivotFrame (a : I) :
    (pullback (affineBlowUp.chart I a)).obj (((affineBlowUp.exceptionalIdeal I).toModules) ⊗ (pullback (affineBlowUp.π I)).obj B) ≅
      unitObj (Spec (.of (affineBlowUpAlgebra I a))) :=
  (pullback (affineBlowUp.chart I a)).mapIso (targetUntwist I B e) ≪≫
    NadelNefBigExceptionalFrames.chartFrame I a

private theorem on_chart (a : I) :
    affineBlowUp.chart I a ≫ affineFramedMap I B hB G =
      affineBlowUp.chart I a ≫
        NadelNefBigExceptionalProjectiveCharts.projectiveMap I
          (sourceCoefficient I B G e) (sourceCoefficient_span I B G e) := by
  let c := affineBlowUp.chart I a
  let H := transportedGenerators I B hB G
  let K := NadelNefBigExceptionalGenerators.generatingSections I
    (sourceCoefficient I B G e) (sourceCoefficient_span I B G e)
  let HC := ClosedProjectiveGlobalGeneration.pullback_generatingSections c H
  let KC := ClosedProjectiveGlobalGeneration.pullback_generatingSections c K
  let : Fintype H.I := (inferInstance : Fintype G.I)
  let : Fintype K.I := (inferInstance : Fintype G.I)
  let : Fintype HC.I := (inferInstance : Fintype G.I)
  let : Fintype KC.I := (inferInstance : Fintype G.I)
  let E := NadelNefBigExceptionalFrames.chartFrame I a
  have hgen (i : G.I) : generatorHom HC i ≫
      (pullback c).map (targetUntwist I B e).hom = generatorHom KC i := by
    rw [generatorHom_pullback, generatorHom_pullback,
      NadelNefBigExceptionalGenerators.generatorHom_generatingSections]
    rw [Category.assoc, ← Functor.map_comp, transported_generator_untwist]
  have hc (i : G.I) : coefficient HC (pivotFrame I B e a) i = coefficient KC E i := by
    have hm : generatorHom HC i ≫ (pivotFrame I B e a).hom = generatorHom KC i ≫ E.hom := by
      exact (Category.assoc _ _ _).symm.trans (congrArg (fun s => s ≫ E.hom) (hgen i))
    exact (coefficient_apply HC (pivotFrame I B e a) i).trans
      ((congrArg (fun s : unitObj (Spec (.of (affineBlowUpAlgebra I a))) ⟶
          unitObj (Spec (.of (affineBlowUpAlgebra I a))) =>
        s.val.app (op ⊤) (1 : Γ(Spec (.of (affineBlowUpAlgebra I a)), ⊤))) hm).trans
          (coefficient_apply KC E i).symm)
  have hH := NadelNefBigGeneratedOpenMap.projectiveMap_on_affine_openMap c (affineBlowUp.π I) _
    (tensorInvertible (affineBlowUp.isInvertible_exceptionalIdeal I).isInvertibleModule_toModules
      (hB.pullback (affineBlowUp.π I))) H (pivotFrame I B e a)
  have hK := NadelNefBigExceptionalProjectiveCharts.on_chart I
    (sourceCoefficient I B G e) (sourceCoefficient_span I B G e) a
  apply hH.trans
  apply Eq.trans ?_ hK.symm
  change (Spec (.of (affineBlowUpAlgebra I a))).isoSpec.hom ≫ _ =
    (Spec (.of (affineBlowUpAlgebra I a))).isoSpec.hom ≫ _
  apply congrArg (fun s => (Spec (.of (affineBlowUpAlgebra I a))).isoSpec.hom ≫ s)
  exact DeJongAlterations.Geometry.FiniteProjective.affineTupleMap_congr rfl
    (congrArg paddedCoefficients (funext hc)) _ _

/-- Whole affine-base identification of the SAME twisted generator map, with
all coefficient identities and ideal generation internally produced. -/
theorem affineFramedMap_eq :
    affineFramedMap I B hB G =
      NadelNefBigExceptionalProjectiveCharts.projectiveMap I
        (sourceCoefficient I B G e) (sourceCoefficient_span I B G e) := by
  apply (affineBlowUp.affineOpenCover I).cover.hom_ext
  intro a
  exact on_chart I B hB G e a

include e

/-- The actual twisted generating map is closed on the ENTIRE original affine
base blowup, not merely on individual source pivot charts. -/
theorem affineFramedMap_isClosedImmersion :
    IsClosedImmersion (affineFramedMap I B hB G) := by
  rw [affineFramedMap_eq I B hB G e]
  exact NadelNefBigExceptionalProjectiveClosed.isClosedImmersion I
    (sourceCoefficient I B G e) (sourceCoefficient_span I B G e)

end AffineBase

section GlobalPair

variable {k : Type u} [Field k] {X : Scheme.{u}}
  (D : X.IdealSheafData) (p : X ⟶ Spec (.of k))
  (B : X.Modules) (hB : IsInvertible B)
  (G : (D.toModules ⊗ B).GeneratingSections) [Fintype G.I]

private def globalGenerators :
    ((D.comap D.blowUpπ).toModules ⊗ (pullback D.blowUpπ).obj B).GeneratingSections :=
  NadelNefBigGlobalGenerators.comapGenerators D D.blowUpπ B hB G

/-- The actual global projective map of the SAME canonically transported
source generators, before any closedness conclusion is made. -/
def globalMap (p : X ⟶ Spec (.of k)) (B : X.Modules) (hB : IsInvertible B)
    (G : (D.toModules ⊗ B).GeneratingSections) [Fintype G.I] : D.blowUp ⟶ DeJongAlterations.projectiveSpace k (Fintype.card G.I) := by
  let H := globalGenerators D B hB G
  let : Fintype H.I := (inferInstance : Fintype G.I)
  exact projectiveMap (D.blowUpπ ≫ p)
    (tensorInvertible (Scheme.IdealSheafData.blowUp.isInvertible_comap_π D).isInvertibleModule_toModules
      (hB.pullback D.blowUpπ)) H

/-- The original structure triangle of the actual generated map. -/
theorem globalMap_structure :
    globalMap D p B hB G ≫
      DeJongAlterations.projectiveSpaceStructure k (Fintype.card G.I) = D.blowUpπ ≫ p := by
  let H := globalGenerators D B hB G
  let : Fintype H.I := (inferInstance : Fintype G.I)
  exact projectiveMap_structure (D.blowUpπ ≫ p)
    (tensorInvertible (Scheme.IdealSheafData.blowUp.isInvertible_comap_π D).isInvertibleModule_toModules
      (hB.pullback D.blowUpπ)) H

/-- The SAME original blowup projection and generated map form the actual
pair into the original product over the original field. -/
def globalPair (p : X ⟶ Spec (.of k)) (B : X.Modules) (hB : IsInvertible B)
    (G : (D.toModules ⊗ B).GeneratingSections) [Fintype G.I] : D.blowUp ⟶ Limits.pullback p
    (DeJongAlterations.projectiveSpaceStructure k (Fintype.card G.I)) :=
  Limits.pullback.lift D.blowUpπ (globalMap D p B hB G) (globalMap_structure D p B hB G).symm

@[reassoc]
theorem globalPair_fst : globalPair D p B hB G ≫ Limits.pullback.fst _ _ = D.blowUpπ :=
  Limits.pullback.lift_fst _ _ _

@[reassoc]
theorem globalPair_snd : globalPair D p B hB G ≫ Limits.pullback.snd _ _ = globalMap D p B hB G :=
  Limits.pullback.lift_snd _ _ _

/-- Properness is internally supplied by the original projective blowup and
the separated original target. No properness of the pair is an input. -/
theorem globalPair_isProper (hp : IsProjectiveFactorization p) :
    IsProper (globalPair D p B hB G) := by
  let : IsProper p := hp.isProper
  let : IsProper (D.blowUpπ ≫ p) :=
    (ProjectiveBlowupSequence.blowup_isProjectiveFactorization D p hp).isProper
  let : IsProper D.blowUpπ := IsProper.of_comp D.blowUpπ p
  let : IsProper (DeJongAlterations.projectiveSpaceStructure k (Fintype.card G.I)) := by
    have hpP : IsProjectiveFactorization
        (DeJongAlterations.projectiveSpaceStructure k (Fintype.card G.I)) :=
      (ProjectiveBlowupSequence.isProjectiveOver_iff _).mp
        ⟨Fintype.card G.I, 𝟙 _, inferInstance, Category.id_comp _⟩
    exact hpP.isProper
  let : IsProper (globalPair D p B hB G ≫ Limits.pullback.fst _ _) :=
    (globalPair_fst D p B hB G).symm ▸ inferInstance
  exact IsProper.of_comp (globalPair D p B hB G) (Limits.pullback.fst _ _)

end GlobalPair

end EnvelopeProperty.Vanishing.NadelNefBigGlobalPairClosed
