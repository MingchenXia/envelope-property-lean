import EnvelopeProperty.AlgGeom.CurveLineDegrees
import Mathlib.Algebra.Group.Units.Hom

/-! # Intrinsic curve degrees on the SAME original native Picard groups -/
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.MonoidalCategory
open Scheme.Modules
universe u
namespace EnvelopeProperty.CurvePicardDegrees
open CurveLineDegrees
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] Scheme.Modules.monoidalCategory Scheme.Modules.symmetricCategory

/-- Full original Euler degree descends to the ACTUAL original isomorphism quotient. -/
def skeletonDegree {k : Type u} [Field k] {C : Scheme.{u}} [CompactSpace C]
    (p : C ⟶ Spec (.of k)) : Skeleton C.Modules → ℤ :=
  Quotient.lift (degree p) (fun _ _ ⟨e⟩ => degree_eq_of_iso p e)

/-- The descended degree retains the SAME original whole sheaf. -/
@[simp] theorem skeletonDegree_toSkeleton {k : Type u} [Field k]
    {C : Scheme.{u}} [CompactSpace C] (p : C ⟶ Spec (.of k)) (L : C.Modules) :
    skeletonDegree p (toSkeleton L) = degree p L := rfl

/-- An actual original invertible line defines its SAME class in the native Picard group. -/
def lineClass {Z : Scheme.{u}} (L : Z.Modules) (hL : IsInvertible L) : Z.Pic :=
  hL.isUnit_toSkeleton.unit

/-- The actual native Picard class is the isomorphism class of the SAME original line. -/
@[simp] theorem lineClass_val {Z : Scheme.{u}} (L : Z.Modules) (hL : IsInvertible L) :
    (lineClass L hL).val = toSkeleton L := hL.isUnit_toSkeleton.unit_spec

private theorem skeletonDegree_out {k : Type u} [Field k]
    {C : Scheme.{u}} [CompactSpace C] (p : C ⟶ Spec (.of k)) (a : Skeleton C.Modules) :
    skeletonDegree p a = degree p a.out := by
  exact (congrArg (skeletonDegree p) (Quotient.out_eq a)).symm

private theorem representative_invertible {Z : Scheme.{u}} (a : Z.Pic) :
    IsInvertible (a.val.out) := by
  change (Skeleton Z.Modules)ˣ at a
  apply isInvertible_of_isUnit_toSkeleton
  exact Eq.mpr (congrArg (fun q : Skeleton Z.Modules => IsUnit q)
    (show toSkeleton a.val.out = a.val from Quotient.out_eq a.val)) a.isUnit

/-- The actual intrinsic degree is a genuine homomorphism on the ORIGINAL
native Picard group of ANY original integral projective curve. -/
def degreeHom {k : Type u} [Field k] {C : Scheme.{u}} [IsIntegral C]
    (p : C ⟶ Spec (.of k)) (hp : IsProjectiveFactorization p)
    (hdim : topologicalKrullDim C ≤ 1) : C.Pic →* Multiplicative ℤ := by
  let : IsProper p := hp.isProper
  let : CompactSpace C := QuasiCompact.compactSpace_of_compactSpace p
  exact
    { toFun := fun a => Multiplicative.ofAdd (skeletonDegree p a.val)
      map_one' := by
        change skeletonDegree p (1 : Skeleton C.Modules) = 0
        rw [Skeleton.one_eq, skeletonDegree_toSkeleton,
          degree_eq_of_iso p (ModularCurves.monoidalUnitObjIso C), degree_unit]
      map_mul' := by
        intro a b
        change skeletonDegree p (a.val * b.val) = skeletonDegree p a.val + skeletonDegree p b.val
        rw [Skeleton.mul_eq, skeletonDegree_toSkeleton, skeletonDegree_out, skeletonDegree_out]
        exact degree_tensor p hp hdim _ _ (representative_invertible a) (representative_invertible b) }

/-- The native class functional computes the degree of the SAME original line. -/
@[simp] theorem degreeHom_lineClass {k : Type u} [Field k] {C : Scheme.{u}} [IsIntegral C]
    (p : C ⟶ Spec (.of k)) (hp : IsProjectiveFactorization p)
    (hdim : topologicalKrullDim C ≤ 1) (L : C.Modules) (hL : IsInvertible L) :
    letI : IsProper p := hp.isProper
    letI : CompactSpace C := QuasiCompact.compactSpace_of_compactSpace p
    Multiplicative.toAdd (degreeHom p hp hdim (lineClass L hL)) = degree p L := by
  let : IsProper p := hp.isProper
  let : CompactSpace C := QuasiCompact.compactSpace_of_compactSpace p
  change skeletonDegree p (lineClass L hL).val = degree p L
  rw [lineClass_val, skeletonDegree_toSkeleton]

/-- Native monoidal pullback induces the original Picard pullback for every
literal original scheme morphism, without flatness or properness. -/
def picPullback {C Z : Scheme.{u}} (i : C ⟶ Z) : Z.Pic →* C.Pic := by
  let : (Scheme.Modules.pullback i).Monoidal := pullbackMonoidal i
  exact Units.map (Skeleton.monoidHom (Scheme.Modules.pullback i))

/-- Original line classes pull back to the SAME whole original line pullback class. -/
@[simp] theorem picPullback_lineClass {C Z : Scheme.{u}} (i : C ⟶ Z)
    (L : Z.Modules) (hL : IsInvertible L) :
    picPullback i (lineClass L hL) = lineClass ((Scheme.Modules.pullback i).obj L) (hL.pullback i) := by
  apply Units.ext
  change ((Scheme.Modules.pullback i).mapSkeleton.obj (lineClass L hL).val) =
    (lineClass ((Scheme.Modules.pullback i).obj L) (hL.pullback i)).val
  rw [lineClass_val, lineClass_val, Functor.mapSkeleton_obj_toSkeleton]

/-- EVERY actual original curve map gives a genuine degree homomorphism
on SAME native original model Picard group. -/
def curveDegreeHom {k : Type u} [Field k] {C Z : Scheme.{u}} [IsIntegral C]
    (p : C ⟶ Spec (.of k)) (hp : IsProjectiveFactorization p)
    (hdim : topologicalKrullDim C ≤ 1) (i : C ⟶ Z) : Z.Pic →* Multiplicative ℤ :=
  (degreeHom p hp hdim).comp (picPullback i)

/-- This functional retains the literal original curve map and TRUE degree
of the SAME actual original whole line pulled along it. -/
@[simp] theorem curveDegreeHom_lineClass {k : Type u} [Field k]
    {C Z : Scheme.{u}} [IsIntegral C] (p : C ⟶ Spec (.of k)) (hp : IsProjectiveFactorization p)
    (hdim : topologicalKrullDim C ≤ 1) (i : C ⟶ Z) (L : Z.Modules) (hL : IsInvertible L) :
    letI : IsProper p := hp.isProper
    letI : CompactSpace C := QuasiCompact.compactSpace_of_compactSpace p
    Multiplicative.toAdd (curveDegreeHom p hp hdim i (lineClass L hL)) =
      degree p ((Scheme.Modules.pullback i).obj L) := by
  let : IsProper p := hp.isProper
  let : CompactSpace C := QuasiCompact.compactSpace_of_compactSpace p
  change Multiplicative.toAdd (degreeHom p hp hdim (picPullback i (lineClass L hL))) = _
  rw [picPullback_lineClass, degreeHom_lineClass]

end EnvelopeProperty.CurvePicardDegrees
