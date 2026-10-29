import EnvelopeProperty.AlgGeom.FiniteClosedIdealEuler
import EnvelopeProperty.AlgGeom.SchemeLineProjectionFormula
import EnvelopeProperty.AlgGeom.SchemeInvertibleTensorQuasicoherent
import EnvelopeProperty.AlgGeom.LineSectionZeroIdealDual
import EnvelopeProperty.AlgGeom.GeometricIdealKernelModuleComparison
import EnvelopeProperty.AlgGeom.TensorPowerBaseIdealGrading

/-! # Positive-dimensional Cartier cuts for the original full Euler characteristic

This is an intersection-theoretic foundation for the numerical ampleness
criterion. It does not assume or assert a Seshadri or Nakai criterion.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open Scheme.Modules
universe u
namespace EnvelopeProperty.SeshadriAmplenessCriterion

open SchemeCoherentEulerCharacteristic
attribute [local instance] Scheme.Modules.monoidalCategory Scheme.Modules.symmetricCategory

private theorem finiteType_of_invertible {X : Scheme.{u}} (M : X.Modules)
    (hM : IsInvertible M) : M.IsFiniteType := by
  let : M.IsFinitePresentation := hM.isFinitePresentation
  obtain ⟨q, hq⟩ := SheafOfModules.IsFinitePresentation.exists_quasicoherentData M
  apply SheafOfModules.IsFiniteType.mk (R := X.ringCatSheaf)
  refine ⟨q.localGeneratorsData, ?_⟩
  constructor
  intro i
  change (q.presentation i).generators.IsFiniteType
  exact (hq.isFinite_presentation i).isFiniteType_generators

private theorem finiteType_of_iso {X : Scheme.{u}} {M N : X.Modules}
    [M.IsQuasicoherent] [N.IsQuasicoherent] [N.IsFiniteType] (e : M ≅ N) : M.IsFiniteType := by
  apply isFiniteType_of_sections_module_finite M
  intro U
  let : Module.Finite Γ(X, U.1) Γ(N, U.1) :=
    sections_module_finite_of_isFiniteType_of_isAffineOpen N U
  let eU : Γ(M, U.1) ≃ₗ[Γ(X, U.1)] Γ(N, U.1) :=
    ((PresheafOfModules.evaluation (R := X.ringCatSheaf.obj) (op U.1)).mapIso
      ((SheafOfModules.forget X.ringCatSheaf).mapIso e)).toLinearEquiv
  exact Module.Finite.equiv eU.symm

/-- The full Euler characteristic of the SAME original line and its actual
closed restriction differ by the SAME original ideal twist in every dimension.
The closed subscheme need not be finite over the field. -/
theorem eulerCharacteristic_closedRestriction {k : Type u} [Field k] {X D : Scheme.{u}}
    (g : D ⟶ X) [IsClosedImmersion g] [CompactSpace X] [X.IsSeparated]
    (f : X ⟶ Spec (.of k)) (hf : IsProjectiveFactorization f)
    (L : X.Modules) (hL : IsInvertible L) :
    letI : CompactSpace D := QuasiCompact.compactSpace_of_compactSpace g
    eulerCharacteristic f L - eulerCharacteristic f (ModularCurves.idealModule g ⊗ L) =
      eulerCharacteristic (g ≫ f) ((Scheme.Modules.pullback g).obj L) := by
  let : CompactSpace D := QuasiCompact.compactSpace_of_compactSpace g
  let : D.IsSeparated := ⟨by
    have h : IsSeparated (g ≫ terminal.from X) := inferInstance
    simpa only [terminal.comp_from] using h⟩
  let : IsProper f := hf.isProper
  let : LocallyOfFiniteType f := inferInstance
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  let : L.IsQuasicoherent := hL.isQuasicoherent
  let : L.IsFinitePresentation := hL.isFinitePresentation
  let : L.IsFiniteType := finiteType_of_invertible L hL
  let P := (Scheme.Modules.pullback g).obj L
  have hP : IsInvertible P := hL.pullback g
  let : P.IsQuasicoherent := hP.isQuasicoherent
  let : P.IsFinitePresentation := hP.isFinitePresentation
  let : P.IsFiniteType := finiteType_of_invertible P hP
  let : (unitObj X).IsQuasicoherent := isInvertible_unit.isQuasicoherent
  let : (unitObj D).IsQuasicoherent := isInvertible_unit.isQuasicoherent
  let : (unitObj D).IsFinitePresentation := isInvertible_unit.isFinitePresentation
  let : (unitObj D).IsFiniteType := finiteType_of_invertible (unitObj D) isInvertible_unit
  let Q := (pushforward g).obj (unitObj D)
  let T := (pushforward g).obj P
  let : Q.IsQuasicoherent := isQuasicoherent_pushforward_of_isAffineHom g
  let : Q.IsFiniteType := isFiniteType_pushforward_of_isClosedImmersion g
  let : T.IsQuasicoherent := isQuasicoherent_pushforward_of_isAffineHom g
  let : T.IsFiniteType := isFiniteType_pushforward_of_isClosedImmersion g
  let : (ModularCurves.idealModule g).IsQuasicoherent :=
    isQuasicoherent_kernel (FiniteClosedIdealEuler.quotientMap g)
  let : (tensorRight L).IsEquivalence :=
    SchemeInvertibleTensorEquivalence.tensorRight_isEquivalence L hL
  let S := (FiniteClosedIdealEuler.sequence g).map (tensorRight L)
  have hS : S.ShortExact := SchemeInvertibleTensorEquivalence.tensorRight_shortExact
    L hL (FiniteClosedIdealEuler.sequence g) (FiniteClosedIdealEuler.sequence_shortExact g)
  let eL : S.X₂ ≅ L :=
    ((ModularCurves.monoidalUnitObjIso X).symm ⊗ᵢ Iso.refl L) ≪≫ λ_ L
  let eT : S.X₃ ≅ T :=
    SchemeLineProjectionFormula.lineProjectionFormulaObj g L hL (unitObj D) ≪≫
      (pushforward g).mapIso
        (((ModularCurves.monoidalUnitObjIso D).symm ⊗ᵢ Iso.refl P) ≪≫ λ_ P)
  let : S.X₁.IsQuasicoherent :=
    SchemeInvertibleTensorQuasicoherent.isQuasicoherent_tensorRight
      (ModularCurves.idealModule g) L hL
  let : S.X₂.IsQuasicoherent := (isQuasicoherent X).prop_of_iso eL.symm inferInstance
  let : S.X₂.IsFiniteType := finiteType_of_iso eL
  let : S.X₃.IsQuasicoherent := (isQuasicoherent X).prop_of_iso eT.symm inferInstance
  let : S.X₃.IsFiniteType := finiteType_of_iso eT
  let eK : S.X₁ ≅ kernel S.g := hS.fIsKernel.conePointUniqueUpToIso (limit.isLimit _)
  let : (kernel S.g).IsQuasicoherent := isQuasicoherent_kernel S.g
  let : (kernel S.g).IsFiniteType := isFiniteType_kernel S.g
  let : S.X₁.IsFiniteType := finiteType_of_iso eK
  have h := eulerCharacteristic_add f hf S hS
  have hp := SchemeCoherentEulerAffine.eulerCharacteristic_pushforward g f P
  rw [eulerCharacteristic_eq_of_iso f eL, eulerCharacteristic_eq_of_iso f eT, ← hp] at h
  change eulerCharacteristic f L =
    eulerCharacteristic f (ModularCurves.idealModule g ⊗ L) +
      eulerCharacteristic (g ≫ f) ((Scheme.Modules.pullback g).obj L) at h
  omega

/-- The actual zero divisor of a nonzero original section gives the full
Euler difference for the original dual line, without a dimension bound. -/
theorem eulerCharacteristic_sectionCut {k : Type u} [Field k] {X : Scheme.{u}}
    [IsIntegral X] [CompactSpace X] [X.IsSeparated]
    (f : X ⟶ Spec (.of k)) (hf : IsProjectiveFactorization f)
    (A L : X.Modules) (hA : IsInvertible A) (hL : IsInvertible L)
    (s : unitObj X ⟶ A) (hs : s ≠ 0) :
    let I := LineSectionZeroIdeal.zeroIdeal A hA s
    letI : CompactSpace I.subscheme := QuasiCompact.compactSpace_of_compactSpace I.subschemeι
    eulerCharacteristic f L - eulerCharacteristic f (dualObj A ⊗ L) =
      eulerCharacteristic (I.subschemeι ≫ f) ((Scheme.Modules.pullback I.subschemeι).obj L) := by
  let I := LineSectionZeroIdeal.zeroIdeal A hA s
  let : CompactSpace I.subscheme := QuasiCompact.compactSpace_of_compactSpace I.subschemeι
  let eI : ModularCurves.idealModule I.subschemeι ≅ dualObj A :=
    (GeometricIdealKernelModuleComparison.toModulesKernelIso I).symm ≪≫
      LineSectionZeroIdeal.dualIso A hA s hs
  have h := eulerCharacteristic_closedRestriction I.subschemeι f hf L hL
  rwa [eulerCharacteristic_eq_of_iso f (eI ⊗ᵢ Iso.refl L)] at h

/-- Tensoring the SAME original line once gives the actual first full-Euler
difference on the SAME original positive-dimensional section divisor. -/
theorem eulerCharacteristic_sectionFirstDifference {k : Type u} [Field k] {X : Scheme.{u}}
    [IsIntegral X] [CompactSpace X] [X.IsSeparated]
    (f : X ⟶ Spec (.of k)) (hf : IsProjectiveFactorization f)
    (A M : X.Modules) (hA : IsInvertible A) (hM : IsInvertible M)
    (s : unitObj X ⟶ A) (hs : s ≠ 0) :
    let I := LineSectionZeroIdeal.zeroIdeal A hA s
    letI : CompactSpace I.subscheme := QuasiCompact.compactSpace_of_compactSpace I.subschemeι
    eulerCharacteristic f (A ⊗ M) - eulerCharacteristic f M =
      eulerCharacteristic (I.subschemeι ≫ f)
        ((Scheme.Modules.pullback I.subschemeι).obj (A ⊗ M)) := by
  have hAM : IsInvertible (A ⊗ M) :=
    (hA.tensorObj hM).of_iso (ModularCurves.monoidalTensorObjIso A M)
  let e : dualObj A ⊗ (A ⊗ M) ≅ M :=
    (α_ (dualObj A) A M).symm ≪≫
      ((β_ (dualObj A) A ≪≫ hA.monoidalEvaluationIso) ⊗ᵢ Iso.refl M) ≪≫ λ_ M
  have h := eulerCharacteristic_sectionCut f hf A (A ⊗ M) hA hAM s hs
  rwa [eulerCharacteristic_eq_of_iso f e] at h

/-- The finite difference of the ORIGINAL actual tensor powers is the full
Euler characteristic of their ORIGINAL actual Cartier restriction, in every dimension. -/
theorem eulerCharacteristic_tensorPowerFirstDifference {k : Type u} [Field k]
    {X : Scheme.{u}} [IsIntegral X] [CompactSpace X] [X.IsSeparated]
    (f : X ⟶ Spec (.of k)) (hf : IsProjectiveFactorization f)
    (A : X.Modules) (hA : IsInvertible A) (s : unitObj X ⟶ A) (hs : s ≠ 0) (n : ℕ) :
    let I := LineSectionZeroIdeal.zeroIdeal A hA s
    letI : CompactSpace I.subscheme := QuasiCompact.compactSpace_of_compactSpace I.subschemeι
    eulerCharacteristic f (CanonicalGeometry.bundleTensorPower A (n + 1)) -
        eulerCharacteristic f (CanonicalGeometry.bundleTensorPower A n) =
      eulerCharacteristic (I.subschemeι ≫ f)
        ((Scheme.Modules.pullback I.subschemeι).obj (CanonicalGeometry.bundleTensorPower A (n + 1))) := by
  let I := LineSectionZeroIdeal.zeroIdeal A hA s
  let : CompactSpace I.subscheme := QuasiCompact.compactSpace_of_compactSpace I.subschemeι
  let P := CanonicalGeometry.bundleTensorPower A n
  let e : A ⊗ P ≅ CanonicalGeometry.bundleTensorPower A (n + 1) :=
    β_ A P ≪≫ ModularCurves.monoidalTensorObjIso P A
  have h : eulerCharacteristic f (A ⊗ P) - eulerCharacteristic f P =
      eulerCharacteristic (I.subschemeι ≫ f)
        ((Scheme.Modules.pullback I.subschemeι).obj (A ⊗ P)) :=
    eulerCharacteristic_sectionFirstDifference f hf A P hA
      (TensorPowerBaseIdealGrading.tensorPower_isInvertible hA n) s hs
  exact ((congrArg (fun z : ℤ => z - eulerCharacteristic f P)
    (eulerCharacteristic_eq_of_iso f e)).symm.trans h).trans
      (eulerCharacteristic_eq_of_iso (I.subschemeι ≫ f)
        ((Scheme.Modules.pullback I.subschemeι).mapIso e))

end EnvelopeProperty.SeshadriAmplenessCriterion
