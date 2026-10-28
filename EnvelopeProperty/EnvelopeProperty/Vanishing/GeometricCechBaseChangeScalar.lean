import EnvelopeProperty.AlgGeom.SchemeScalarModuleOpenRestriction
import ModularCurves.ForMathlib.SchemeModuleOrderedBaseCechPushforward
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings

/-! # The actual ordered section complex with its original coefficient ring

The native complex is restricted through the actual inverse of Gamma-Spec.
Its concrete coordinates are the original scalar-linear section modules;
the original ordered cofaces and alternating differential are retained.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open AlgebraicGeometry.Scheme.Modules
open scoped BigOperators

noncomputable section
universe u

namespace EnvelopeProperty.Vanishing.GeometricCechBaseChange

variable {R : Type u} [CommRing R] {X : Scheme.{u}}
  (p : X ⟶ Spec (.of R)) (M : X.Modules)
  {ι : Type u} [LinearOrder ι] (U : ι → X.Opens)

/-- The original native ordered Cech complex with the literal original R action. -/
def scalarComplex : CochainComplex (ModuleCat.{u} R) ℕ :=
  ((ModuleCat.restrictScalars (Scheme.ΓSpecIso (.of R)).inv.hom).mapHomologicalComplex
    (ComplexShape.up ℕ)).obj (orderedBaseCechComplex p M U)

/-- The literal original finite intersection belonging to an ordered tuple. -/
abbrev intersection (n : ℕ) (i : OrderedCechIndex ι n) : X.Opens :=
  ∏ᶜ fun k : Fin (n + 1) => U (i.1 k)

/-- Every native ordered degree retains its original scalar-linear section coordinates. -/
def objectEquiv (n : ℕ) :
    (scalarComplex p M U).X n ≃ₗ[R]
      (∀ i : OrderedCechIndex ι n,
        SchemeScalarModulePresheaf.openSections p M (intersection U n i)) where
  toFun x := (orderedBaseCechObjectIsoPi p M U n).hom x
  invFun x := (orderedBaseCechObjectIsoPi p M U n).inv x
  left_inv x := ConcreteCategory.congr_hom (orderedBaseCechObjectIsoPi p M U n).hom_inv_id x
  right_inv x := ConcreteCategory.congr_hom (orderedBaseCechObjectIsoPi p M U n).inv_hom_id x
  map_add' x y := (orderedBaseCechObjectIsoPi p M U n).hom.hom.map_add x y
  map_smul' r x := by
    funext i
    exact (congrFun ((orderedBaseCechObjectIsoPi p M U n).hom.hom.map_smul
      ((Scheme.ΓSpecIso (.of R)).inv.hom r) x) i).trans
      ((SchemeScalarModuleOpenRestriction.nativeSectionsIso p M (intersection U n i)).inv.hom.map_smul
        r ((orderedBaseCechObjectIsoPi p M U n).hom x i))

/-- The degreewise coordinate is the SAME original native product projection. -/
theorem objectEquiv_apply (n : ℕ) (x : (scalarComplex p M U).X n)
    (i : OrderedCechIndex ι n) :
    objectEquiv p M U n x i =
      (Pi.π (fun j : OrderedCechIndex ι n => baseCechFactor p M U n j.1) i) x :=
  ConcreteCategory.congr_hom (orderedBaseCechObjectIsoPi_hom_comp_proj p M U n i) x

/-- The original ordered coface with its actual original R-linear action. -/
def coface (n : ℕ) (k : Fin (n + 2)) :
    (scalarComplex p M U).X n ⟶ (scalarComplex p M U).X (n + 1) :=
  (ModuleCat.restrictScalars (Scheme.ΓSpecIso (.of R)).inv.hom).map
    (orderedBaseCechCoface p M U n k)

/-- Each actual coface is original restriction to the ordered larger intersection. -/
theorem coface_apply (n : ℕ) (k : Fin (n + 2))
    (x : (scalarComplex p M U).X n) (i : OrderedCechIndex ι (n + 1)) :
    objectEquiv p M U (n + 1) (coface p M U n k x) i =
      (SchemeScalarModulePresheaf.presheaf p M).map
        (((FormalCoproduct.mk _ U).mapPower
          (SimplexCategory.δ k).toOrderHom.toFun).φ i.1).op
        (objectEquiv p M U n x (i.delete k)) := by
  rw [objectEquiv_apply, objectEquiv_apply]
  exact ConcreteCategory.congr_hom (orderedBaseCechCoface_comp_π p M U n k i) x

/-- The actual scalar complex differential retains the original alternating cofaces. -/
theorem differential_eq_sum (n : ℕ) :
    (scalarComplex p M U).d n (n + 1) =
      ∑ k : Fin (n + 2), (-1 : ℤ) ^ (k : ℕ) • coface p M U n k := by
  change (ModuleCat.restrictScalars (Scheme.ΓSpecIso (.of R)).inv.hom).map
    ((orderedBaseCechComplex p M U).d n (n + 1)) = _
  rw [orderedBaseCechComplex_d, orderedBaseCechDifferential]
  change (ModuleCat.restrictScalars (Scheme.ΓSpecIso (.of R)).inv.hom).map
      (∑ k : Fin (n + 2), (-1 : ℤ) ^ (k : ℕ) • orderedBaseCechCoface p M U n k) =
    ∑ k : Fin (n + 2), (-1 : ℤ) ^ (k : ℕ) •
      (ModuleCat.restrictScalars (Scheme.ΓSpecIso (.of R)).inv.hom).map
        (orderedBaseCechCoface p M U n k)
  simp only [Functor.map_sum, Functor.map_zsmul]

/-- The whole differential is the exact original signed restriction formula. -/
theorem differential_apply (n : ℕ) (x : (scalarComplex p M U).X n)
    (i : OrderedCechIndex ι (n + 1)) :
    objectEquiv p M U (n + 1) ((scalarComplex p M U).d n (n + 1) x) i =
      ∑ k : Fin (n + 2), (-1 : ℤ) ^ (k : ℕ) •
        (SchemeScalarModulePresheaf.presheaf p M).map
          (((FormalCoproduct.mk _ U).mapPower
            (SimplexCategory.δ k).toOrderHom.toFun).φ i.1).op
          (objectEquiv p M U n x (i.delete k)) := by
  rw [differential_eq_sum]
  change objectEquiv p M U (n + 1)
    ((∑ k : Fin (n + 2), (-1 : ℤ) ^ (k : ℕ) • coface p M U n k).hom x) i = _
  simp only [ModuleCat.hom_sum, ModuleCat.hom_zsmul, LinearMap.sum_apply,
    LinearMap.smul_apply, map_sum, map_zsmul, Finset.sum_apply, Pi.smul_apply]
  exact Finset.sum_congr rfl (fun k _ => congrArg (fun z => (-1 : ℤ) ^ (k : ℕ) • z)
    (coface_apply p M U n k x i))

end EnvelopeProperty.Vanishing.GeometricCechBaseChange
