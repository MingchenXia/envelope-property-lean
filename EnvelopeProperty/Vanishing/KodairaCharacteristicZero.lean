import EnvelopeProperty.Vanishing.ArithmeticOriginalLinePowerModel
import EnvelopeProperty.Vanishing.ArithmeticOriginalSmoothStage
import EnvelopeProperty.Vanishing.WittKodairaComparisonStage
import EnvelopeProperty.Vanishing.ArithmeticCanonicalSpecializationQuotient
import EnvelopeProperty.Vanishing.ProvedDeligneIllusie

/-! # Kodaira vanishing on the original characteristic-zero scheme

The actual global Witt Deligne--Illusie decomposition, original ample
arithmetic models, dimension-preserving Witt stage, canonical comparisons,
and cohomology specialization are all supplied by proved constructions.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

noncomputable section
universe u

namespace EnvelopeProperty.Vanishing.KodairaCharacteristicZero

open Cartier CanonicalGeometry ProjBerk ArithmeticProjectiveOriginalFamily
open ArithmeticSmoothProjectiveOriginalFamily ArithmeticProjectiveWittFamily
open ArithmeticOriginalSmooth

attribute [local instance] Scheme.Modules.monoidalCategory

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The global Witt decomposition interface at the standard derived-category
universe. Its inhabitant is supplied by `globalWittDecomposition`. -/
def GlobalWittDecompositionInput : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [CharP k p],
    DeligneIllusieInput.WittDecompositionInput.{u,u+1} p k

/-- Every actual smooth separated Witt model has the proved global
decomposition required by the arithmetic specialization argument. -/
theorem globalWittDecomposition : GlobalWittDecompositionInput.{u} := by
  intro p _ k _ _
  exact DeligneIllusieInput.provedWittDecompositionInput p k

private theorem subsingleton_H_of_moduleIso {X : Scheme.{u}} {M N : X.Modules}
    (e : M ≅ N) (j : ℕ) (h : Subsingleton (CategoryTheory.Sheaf.H M.sheaf j)) :
    Subsingleton (CategoryTheory.Sheaf.H N.sheaf j) := by
  let eH := (CategoryTheory.Sheaf.functorH (_root_.Opens.grothendieckTopology X) j).mapIso
    ((SheafOfModules.toSheaf X.ringCatSheaf).mapIso e)
  let : Subsingleton ((CategoryTheory.Sheaf.functorH
    (_root_.Opens.grothendieckTopology X) j).obj
      ((SheafOfModules.toSheaf X.ringCatSheaf).obj M)) := h
  exact ⟨fun x y => (ConcreteCategory.bijective_of_isIso eH.inv).1 (Subsingleton.elim _ _)⟩

/-- Positive Kodaira vanishing for the original smooth characteristic-zero
scheme and original ample line, with the global Witt decomposition proved. -/
theorem kodaira_tensorObj {k : Type u} [Field k] [CharZero k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k))
    (n : ℕ) [SmoothOfRelativeDimension n f]
    (L : X.Modules) (hL : SchemeLineAmpleness.IsAmple f L) (q : ℕ) :
    Subsingleton (CategoryTheory.Sheaf.H
      (Scheme.Modules.tensorObj (canonicalLineSheaf f n) L).sheaf (q + 1)) := by
  let extra : Finset k := ∅
  obtain ⟨d, j, hj, hmodel⟩ :=
    ArithmeticOriginalLinePowerModel.exists_original_ample_model f n L hL extra
  let : IsClosedImmersion j := hj
  obtain ⟨hjp, S, hRS, M, hFT, hnS, hAmpS, ⟨eM⟩⟩ := hmodel
  obtain ⟨D, hSD, hnD, hnW, _, hnp⟩ :=
    exists_relativeDimension_witt_stage_over j extra S hRS hFT n hnS n le_rfl
  let : SmoothOfRelativeDimension n D.baseProjection := hnD
  let : SmoothOfRelativeDimension n D.wittProjection := hnW
  let t := scalarTransition j extra S D.base hRS hSD
  let MD : D.baseFamily.Modules := (Scheme.Modules.pullback t).obj M
  have hAmpD : SchemeLineAmpleness.IsAmple D.baseProjection MD :=
    AmpleScalarBaseChange.isAmple_of_isPullback t (scalarProjection j extra S hRS)
      D.baseProjection (Subalgebra.inclusion hSD).toRingHom
      (isPullback_scalarTransition j extra S D.base hRS hSD) M hAmpS
  let eD : (Scheme.Modules.pullback
      (scalarOriginalMap j extra D.base D.contains_base f hjp)).obj MD ≅ L :=
    ArithmeticOriginalLineFamily.originalPullbackTransitionIso
      j extra f hjp S D.base hRS hSD M ≪≫ eM
  let : Algebra.FiniteType ℤ D.stage := D.finiteType
  let : IsNoetherianRing D.stage := Algebra.FiniteType.isNoetherianRing ℤ _
  let : IsNoetherianRing D.base := isNoetherianRing_of_ringEquiv
    (Localization.Away D.element)
    (ArithmeticSmoothCoefficientBase.localizedCoefficientEquiv D.stage D.element D.nonzero).toRingEquiv
  let MR : D.residueFamily.Modules :=
    (Scheme.Modules.pullback (pullback.fst D.baseProjection
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk D.point.asIdeal))))).obj MD
  have hAmpR : SchemeLineAmpleness.IsAmple D.residueProjection MR :=
    AmpleScalarBaseChange.isAmple D.baseProjection (Ideal.Quotient.mk D.point.asIdeal) MD hAmpD
  let := HasDerivedCategory.standard (SchemeRelativeFrobenius.twist D.prime
    (DeligneIllusieInput.specialFibreStructure D.prime D.residueField D.wittProjection)).Modules
  let := HasDerivedCategory.standard (TopCat.Sheaf AddCommGrpCat.{u}
    (SchemeRelativeFrobenius.twist D.prime
      (DeligneIllusieInput.specialFibreStructure D.prime D.residueField D.wittProjection)))
  have hclosed := WittKodairaComparison.kodaira_tensorObj_on_residueFamily D n hnp
    (globalWittDecomposition D.prime D.residueField) MR hAmpR q
  have hgeneric := ArithmeticCanonicalSpecializationQuotient.squareCanonicalTensor_subsingleton_of_quotient_of_injective
    D.baseProjection (scalarProjection_isProjectiveFactorization j extra D.base D.contains_base)
    n MD hAmpD.isInvertible D.point.asIdeal q hclosed
    (CommRingCat.ofHom (algebraMap D.base k)) Subtype.val_injective
    (scalarOriginalMap j extra D.base D.contains_base f hjp) f
    (isPullback_scalarOriginalMap j extra D.base D.contains_base f hjp)
  exact subsingleton_H_of_moduleIso
    ((ModularCurves.monoidalTensorObjIso _ _).symm ≪≫
      (Iso.refl _ ⊗ᵢ eD) ≪≫ ModularCurves.monoidalTensorObjIso _ _) (q + 1) hgeneric

/-- The same original Kodaira group in native monoidal tensor notation. -/
theorem kodaira {k : Type u} [Field k] [CharZero k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k))
    (n : ℕ) [SmoothOfRelativeDimension n f]
    (L : X.Modules) (hL : SchemeLineAmpleness.IsAmple f L) (q : ℕ) :
    Subsingleton (CategoryTheory.Sheaf.H
      (canonicalLineSheaf f n ⊗ L : X.Modules).sheaf (q + 1)) :=
  subsingleton_H_of_moduleIso (ModularCurves.monoidalTensorObjIso _ _).symm (q + 1)
    (kodaira_tensorObj f n L hL q)

end EnvelopeProperty.Vanishing.KodairaCharacteristicZero
