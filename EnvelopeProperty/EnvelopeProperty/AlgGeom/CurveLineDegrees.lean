import EnvelopeProperty.AlgGeom.ProjectiveLineCartierRatio
import EnvelopeProperty.AlgGeom.CurveCartierLocalOrders

/-! # Genuine intrinsic degrees of ALL original line bundles on original projective curves -/
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open Scheme.Modules
universe u
namespace EnvelopeProperty.CurveLineDegrees
open SchemeCoherentEulerCharacteristic
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] Scheme.Modules.monoidalCategory Scheme.Modules.symmetricCategory

/-- The original intrinsic line degree: the normalized FULL original
coherent Euler characteristic on the SAME original projective curve. -/
def degree {k : Type u} [Field k] {X : Scheme.{u}} [CompactSpace X]
    (p : X ⟶ Spec (.of k)) (L : X.Modules) : ℤ := normalizedEulerCharacteristic p L

/-- Whole original line isomorphisms preserve this actual intrinsic degree. -/
theorem degree_eq_of_iso {k : Type u} [Field k] {X : Scheme.{u}} [CompactSpace X]
    (p : X ⟶ Spec (.of k)) {L M : X.Modules} (e : L ≅ M) : degree p L = degree p M :=
  normalizedEulerCharacteristic_eq_of_iso p e

/-- The original structure line has zero intrinsic degree. -/
@[simp] theorem degree_unit {k : Type u} [Field k] {X : Scheme.{u}} [CompactSpace X]
    (p : X ⟶ Spec (.of k)) : degree p (unitObj X) = 0 := normalizedEulerCharacteristic_unit p

private theorem tensorInvertible {X : Scheme.{u}} {L M : X.Modules}
    (hL : IsInvertible L) (hM : IsInvertible M) : IsInvertible (L ⊗ M) :=
  (hL.tensorObj hM).of_iso (ModularCurves.monoidalTensorObjIso L M)

private theorem tensor_ideal {k : Type u} [Field k] {X : Scheme.{u}} [CompactSpace X] [X.IsSeparated]
    (I : X.IdealSheafData) (p : X ⟶ Spec (.of k)) (hp : IsProjectiveFactorization p)
    [IsFinite (I.subschemeι ≫ p)] (M : X.Modules) (hM : IsInvertible M) :
    degree p (I.toModules ⊗ M) = degree p I.toModules + degree p M :=
  (degree_eq_of_iso p (ModularCurves.monoidalTensorObjIso I.toModules M)).trans
    (GeometricIdealEulerDegree.normalizedEulerCharacteristic_tensor_toModules I p hp M hM)

private theorem tensor_dual_ideal {k : Type u} [Field k] {X : Scheme.{u}}
    [CompactSpace X] [X.IsSeparated] (I : X.IdealSheafData) (hI : I.IsInvertible)
    (p : X ⟶ Spec (.of k)) (hp : IsProjectiveFactorization p) [IsFinite (I.subschemeι ≫ p)]
    (M : X.Modules) (hM : IsInvertible M) :
    degree p (dualObj I.toModules ⊗ M) = degree p (dualObj I.toModules) + degree p M := by
  have hIM := hI.isInvertibleModule_toModules
  have hDM : IsInvertible (dualObj I.toModules ⊗ M) := tensorInvertible hIM.dual hM
  have h := tensor_ideal I p hp (dualObj I.toModules ⊗ M) hDM
  let e : I.toModules ⊗ (dualObj I.toModules ⊗ M) ≅ M :=
    (α_ I.toModules (dualObj I.toModules) M).symm ≪≫
      (hIM.monoidalEvaluationIso ⊗ᵢ Iso.refl M) ≪≫ λ_ M
  rw [degree_eq_of_iso p e] at h
  have hD := GeometricIdealEulerDegree.normalizedEulerCharacteristic_dual_toModules I hI p hp
  change degree p (dualObj I.toModules) = -degree p I.toModules at hD
  omega

private theorem tensor_ratio {k : Type u} [Field k] {X : Scheme.{u}}
    [CompactSpace X] [X.IsSeparated] (I J : X.IdealSheafData) (hJ : J.IsInvertible)
    (p : X ⟶ Spec (.of k)) (hp : IsProjectiveFactorization p)
    [IsFinite (I.subschemeι ≫ p)] [IsFinite (J.subschemeι ≫ p)]
    (M : X.Modules) (hM : IsInvertible M) :
    degree p (I.ratioModule J ⊗ M) = degree p (I.ratioModule J) + degree p M := by
  let D := dualObj J.toModules
  have hDM : IsInvertible (D ⊗ M) := tensorInvertible hJ.isInvertibleModule_toModules.dual hM
  let e : I.ratioModule J ⊗ M ≅ I.toModules ⊗ (D ⊗ M) :=
    ((ModularCurves.monoidalTensorObjIso I.toModules D).symm ⊗ᵢ Iso.refl M) ≪≫
      α_ I.toModules D M
  rw [degree_eq_of_iso p e, tensor_ideal I p hp (D ⊗ M) hDM,
    tensor_dual_ideal J hJ p hp M hM]
  have hD := GeometricIdealEulerDegree.normalizedEulerCharacteristic_dual_toModules J hJ p hp
  have hR := GeometricIdealEulerDegree.normalizedEulerCharacteristic_ratioModule I J hJ p hp
  change degree p (dualObj J.toModules) = -degree p J.toModules at hD
  change degree p (I.ratioModule J) = degree p I.toModules - degree p J.toModules at hR
  omega

/-- TRUE intrinsic degree is tensor-additive for EVERY pair of SAME
original line bundles on ANY original integral projective curve. Actual
Cartier ratios and their finite closed support are produced internally. -/
theorem degree_tensor {k : Type u} [Field k] {X : Scheme.{u}} [IsIntegral X]
    (p : X ⟶ Spec (.of k)) (hp : IsProjectiveFactorization p)
    (hdim : topologicalKrullDim X ≤ 1) (L M : X.Modules)
    (hL : IsInvertible L) (hM : IsInvertible M) :
    letI : IsProper p := hp.isProper
    letI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace p
    degree p (L ⊗ M) = degree p L + degree p M := by
  let : IsProper p := hp.isProper
  let : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace p
  let : X.IsSeparated := ⟨by rw [← terminal.comp_from p]; infer_instance⟩
  obtain ⟨I, J, hI, hJ, ⟨e⟩⟩ := ProjectiveLineCartierRatio.exists_cartier_ratio p hp L hL
  let : IsFinite (I.subschemeι ≫ p) := CurveCartierIdealDegrees.subscheme_comp_isFinite p hdim I hI
  let : IsFinite (J.subschemeι ≫ p) := CurveCartierIdealDegrees.subscheme_comp_isFinite p hdim J hJ
  rw [degree_eq_of_iso p (e ⊗ᵢ Iso.refl M), degree_eq_of_iso p e]
  exact tensor_ratio I J hJ p hp M hM

/-- The degree of the SAME original sheaf dual is the negative degree of
the original arbitrary line, derived from true tensor additivity/evaluation. -/
theorem degree_dual {k : Type u} [Field k] {X : Scheme.{u}} [IsIntegral X]
    (p : X ⟶ Spec (.of k)) (hp : IsProjectiveFactorization p)
    (hdim : topologicalKrullDim X ≤ 1) (L : X.Modules) (hL : IsInvertible L) :
    letI : IsProper p := hp.isProper
    letI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace p
    degree p (dualObj L) = -degree p L := by
  let : IsProper p := hp.isProper
  let : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace p
  have h := degree_tensor p hp hdim L (dualObj L) hL hL.dual
  have hz := degree_eq_of_iso p (hL.monoidalEvaluationIso ≪≫ ModularCurves.monoidalUnitObjIso X)
  rw [degree_unit] at hz
  omega

/-- Actual whole pullback of the original tensor line has the sum of
intrinsic degrees of the SAME pulled original factors on the original curve. -/
theorem degree_pullback_tensor {k : Type u} [Field k] {C Z : Scheme.{u}} [IsIntegral C]
    (p : C ⟶ Spec (.of k)) (hp : IsProjectiveFactorization p)
    (hdim : topologicalKrullDim C ≤ 1) (i : C ⟶ Z)
    (L M : Z.Modules) (hL : IsInvertible L) (hM : IsInvertible M) :
    letI : IsProper p := hp.isProper
    letI : CompactSpace C := QuasiCompact.compactSpace_of_compactSpace p
    degree p ((Scheme.Modules.pullback i).obj (L ⊗ M)) =
      degree p ((Scheme.Modules.pullback i).obj L) + degree p ((Scheme.Modules.pullback i).obj M) := by
  let : IsProper p := hp.isProper
  let : CompactSpace C := QuasiCompact.compactSpace_of_compactSpace p
  let : (Scheme.Modules.pullback i).Monoidal := pullbackMonoidal i
  rw [degree_eq_of_iso p (Functor.Monoidal.μIso (Scheme.Modules.pullback i) L M).symm]
  exact degree_tensor p hp hdim _ _ (hL.pullback i) (hM.pullback i)


/-- The SAME original Cartier-ratio line has its actual full original
residue-weighted native-order difference as intrinsic degree. -/
theorem degree_ratio {k : Type u} [Field k] {X : Scheme.{u}} [IsIntegral X]
    (p : X ⟶ Spec (.of k)) (hp : IsProjectiveFactorization p)
    (hdim : topologicalKrullDim X ≤ 1) (I J : X.IdealSheafData)
    (hI : I.IsInvertible) (hJ : J.IsInvertible) :
    letI : IsProper p := hp.isProper
    letI : LocallyOfFiniteType p := inferInstance
    letI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian p
    letI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace p
    degree p (I.ratioModule J) =
      (∑ᶠ x : X, CurveCartierLocalOrders.weightedLocalOrder p J hJ x) -
        (∑ᶠ x : X, CurveCartierLocalOrders.weightedLocalOrder p I hI x) :=
  CurveCartierLocalOrders.normalizedEulerCharacteristic_ratio_eq_finsum_difference p hp hdim I J hI hJ

/-- ANY nonzero original whole section computes its SAME arbitrary line's
intrinsic degree by the true native orders of its ACTUAL original zero ideal. -/
theorem degree_eq_zeroSection_orders {k : Type u} [Field k]
    {X : Scheme.{u}} [IsIntegral X] (p : X ⟶ Spec (.of k)) (hp : IsProjectiveFactorization p)
    (hdim : topologicalKrullDim X ≤ 1) (L : X.Modules) (hL : IsInvertible L)
    (s : unitObj X ⟶ L) (hs : s ≠ 0) :
    letI : IsProper p := hp.isProper
    letI : LocallyOfFiniteType p := inferInstance
    letI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian p
    letI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace p
    degree p L = ∑ᶠ x : X, CurveCartierLocalOrders.weightedLocalOrder p
      (LineSectionZeroIdeal.zeroIdeal L hL s)
      (LineSectionZeroIdeal.zeroIdeal_isInvertible_of_ne_zero L hL s hs) x := by
  let : IsProper p := hp.isProper
  let : LocallyOfFiniteType p := inferInstance
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian p
  let : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace p
  let I := LineSectionZeroIdeal.zeroIdeal L hL s
  let hI : I.IsInvertible := LineSectionZeroIdeal.zeroIdeal_isInvertible_of_ne_zero L hL s hs
  have hχ := CurveCartierLocalOrders.normalizedEulerCharacteristic_eq_neg_finsum p hp hdim I hI
  have hd := degree_dual p hp hdim L hL
  have he := degree_eq_of_iso p (IntegralLineImageModules.zeroSectionDualIso L hL s hs)
  change degree p I.toModules = -(∑ᶠ x : X, CurveCartierLocalOrders.weightedLocalOrder p I hI x) at hχ
  change degree p (dualObj L) = degree p I.toModules at he
  change degree p L = ∑ᶠ x : X, CurveCartierLocalOrders.weightedLocalOrder p I hI x
  omega

end EnvelopeProperty.CurveLineDegrees
