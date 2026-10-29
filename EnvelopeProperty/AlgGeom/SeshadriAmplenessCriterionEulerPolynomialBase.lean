import EnvelopeProperty.AlgGeom.SeshadriAmplenessCriterionCartierDifference
import EnvelopeProperty.AlgGeom.SeshadriAmplenessCriterionDimensionDrop
import Mathlib.AlgebraicGeometry.Limits

/-!
# Seshadri Ampleness Criterion Euler Polynomial Base

Actual geometric zero-dimensional base for the Euler polynomial. -/

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory TopologicalSpace Topology Order
open Scheme.Modules
universe u
namespace EnvelopeProperty.SeshadriAmplenessCriterion

/-- A proper original closed subset of an irreducible zero-dimensional
space has no actual points. -/
theorem properClosed_isEmpty_of_dimension_le_zero
    {X : Type u} [TopologicalSpace X] [IrreducibleSpace X]
    (Z : Closeds X) (hZ : Z ≠ ⊤) (hdim : topologicalKrullDim X ≤ 0) : IsEmpty Z := by
  refine ⟨fun z => hZ ?_⟩
  let C : IrreducibleCloseds X :=
    ⟨closure ({z.val} : Set X), isIrreducible_singleton.closure, isClosed_closure⟩
  let T : IrreducibleCloseds X :=
    ⟨Set.univ, IrreducibleSpace.isIrreducible_univ X, isClosed_univ⟩
  have hC : (C : Set X) ⊆ (Z : Set X) :=
    closure_minimal (Set.singleton_subset_iff.mpr z.property) Z.isClosed
  have hmax : IsMax C := krullDim_nonpos_iff_forall_isMax.mp hdim C
  have hTC : T ≤ C := hmax (show C ≤ T from Set.subset_univ _)
  apply SetLike.coe_injective
  apply Set.eq_univ_of_univ_subset
  intro x hx
  exact hC (hTC hx)

/-- The actual zero subscheme of a nonzero original line section is empty
when the original integral ambient has dimension at most zero. -/
theorem sectionZero_isEmpty_of_dimension_le_zero
    {X : Scheme.{u}} [IsIntegral X] (hdim : topologicalKrullDim X ≤ 0)
    (A : X.Modules) (hA : IsInvertible A) (s : unitObj X ⟶ A) (hs : s ≠ 0) :
    IsEmpty (LineSectionZeroIdeal.zeroIdeal A hA s).subscheme := by
  let I := LineSectionZeroIdeal.zeroIdeal A hA s
  have hI : I.IsInvertible := LineSectionZeroIdeal.zeroIdeal_isInvertible_of_ne_zero A hA s hs
  exact properClosed_isEmpty_of_dimension_le_zero I.support
    (CurveCartierIdealDegrees.support_ne_top I hI) hdim

/-- The same original full coherent Euler characteristic vanishes on an
actual empty scheme, using the original section-module carrier. -/
theorem eulerCharacteristic_eq_zero_of_isEmpty
    {k : Type u} [Field k] {X : Scheme.{u}} [IsEmpty X]
    (f : X ⟶ Spec (.of k)) (M : X.Modules) [M.IsQuasicoherent] :
    SchemeCoherentEulerCharacteristic.eulerCharacteristic f M = 0 := by
  let : Subsingleton Γ(M, ⊤) := Module.subsingleton Γ(X, ⊤) Γ(M, ⊤)
  let : Subsingleton (SchemeCoherentEulerIndex.fieldSections f M) :=
    inferInstanceAs (Subsingleton Γ(M, ⊤))
  rw [SchemeCoherentEulerAffine.eulerCharacteristic_eq_finrank_sections]
  simp only [Module.finrank_zero_of_subsingleton, Nat.cast_zero]

/-- Actual categorical zero modules have zero original full Euler sum. -/
theorem eulerCharacteristic_eq_zero_of_isZero
    {k : Type u} [Field k] {X : Scheme.{u}} [CompactSpace X]
    (f : X ⟶ Spec (.of k)) (M : X.Modules) (hM : IsZero M) :
    SchemeCoherentEulerCharacteristic.eulerCharacteristic f M = 0 := by
  unfold SchemeCoherentEulerCharacteristic.eulerCharacteristic
    SchemeCoherentEulerCharacteristic.coverEuler
  apply Finset.sum_eq_zero
  intro n _
  let U := SchemeCoherentEulerIndex.finiteAffineOpens X
  let E : X.Modules ⥤ ModuleCat.{u} k :=
    SchemeCoherentEulerExact.fieldComplexFunctor f U ⋙
      HomologicalComplex.homologyFunctor (ModuleCat.{u} k) (ComplexShape.up ℕ) n
  have hH : IsZero (E.obj M) := E.map_isZero hM
  have hC : IsZero (SchemeCoherentEulerIndex.fieldCech f M U n) :=
    IsZero.of_iso hH (SchemeCoherentEulerExact.fieldComplexHomologyIso f M U n).symm
  let : Subsingleton (SchemeCoherentEulerIndex.fieldCech f M U n) :=
    ModuleCat.subsingleton_of_isZero hC
  simp only [Module.finrank_zero_of_subsingleton, Nat.cast_zero, mul_zero]

attribute [local instance] Scheme.Modules.monoidalCategory Scheme.Modules.symmetricCategory

/-- The genuine arbitrary-line Cartier difference has empty actual cuts
in dimension zero, so it preserves the same original coefficient Euler. -/
theorem eulerCharacteristic_tensor_eq_of_dimension_le_zero
    {k : Type u} [Field k] {X : Scheme.{u}} [IsIntegral X]
    [CompactSpace X] [X.IsSeparated]
    (f : X ⟶ Spec (.of k)) (hf : IsProjectiveFactorization f)
    (hdim : topologicalKrullDim X ≤ 0)
    (L M : X.Modules) (hL : IsInvertible L) (hM : IsInvertible M) :
    SchemeCoherentEulerCharacteristic.eulerCharacteristic f (L ⊗ M) =
      SchemeCoherentEulerCharacteristic.eulerCharacteristic f M := by
  obtain ⟨B, hB, a, b, ha, hb, _⟩ :=
    exists_eulerCharacteristic_powerCartierDifference f hf L hL
  let hA : IsInvertible (L ⊗ B) :=
    (hL.tensorObj hB).of_iso (ModularCurves.monoidalTensorObjIso L B)
  let I := LineSectionZeroIdeal.zeroIdeal (L ⊗ B) hA a
  let J := LineSectionZeroIdeal.zeroIdeal B hB b
  let : IsEmpty I.subscheme := sectionZero_isEmpty_of_dimension_le_zero hdim _ hA a ha
  let : IsEmpty J.subscheme := sectionZero_isEmpty_of_dimension_le_zero hdim B hB b hb
  let hLM : IsInvertible (L ⊗ M) :=
    (hL.tensorObj hM).of_iso (ModularCurves.monoidalTensorObjIso L M)
  let : ((Scheme.Modules.pullback I.subschemeι).obj (L ⊗ M)).IsQuasicoherent :=
    (hLM.pullback I.subschemeι).isQuasicoherent
  let : ((Scheme.Modules.pullback J.subschemeι).obj M).IsQuasicoherent :=
    (hM.pullback J.subschemeι).isQuasicoherent
  have h := eulerCharacteristic_cartierDifference f hf L B M hL hB hM a ha b hb
  change SchemeCoherentEulerCharacteristic.eulerCharacteristic f (L ⊗ M) -
      SchemeCoherentEulerCharacteristic.eulerCharacteristic f M =
    SchemeCoherentEulerCharacteristic.eulerCharacteristic (I.subschemeι ≫ f)
      ((Scheme.Modules.pullback I.subschemeι).obj (L ⊗ M)) -
    SchemeCoherentEulerCharacteristic.eulerCharacteristic (J.subschemeι ≫ f)
      ((Scheme.Modules.pullback J.subschemeι).obj M) at h
  rw [eulerCharacteristic_eq_zero_of_isEmpty (I.subschemeι ≫ f)
      ((Scheme.Modules.pullback I.subschemeι).obj (L ⊗ M)),
    eulerCharacteristic_eq_zero_of_isEmpty (J.subschemeι ≫ f)
      ((Scheme.Modules.pullback J.subschemeι).obj M)] at h
  exact sub_eq_zero.mp (by simpa only [sub_zero] using h)

#check @properClosed_isEmpty_of_dimension_le_zero
#print axioms properClosed_isEmpty_of_dimension_le_zero
#check @sectionZero_isEmpty_of_dimension_le_zero
#print axioms sectionZero_isEmpty_of_dimension_le_zero
#check @eulerCharacteristic_eq_zero_of_isEmpty
#print axioms eulerCharacteristic_eq_zero_of_isEmpty
#check @eulerCharacteristic_eq_zero_of_isZero
#print axioms eulerCharacteristic_eq_zero_of_isZero
#check @eulerCharacteristic_tensor_eq_of_dimension_le_zero
#print axioms eulerCharacteristic_tensor_eq_of_dimension_le_zero
end EnvelopeProperty.SeshadriAmplenessCriterion
