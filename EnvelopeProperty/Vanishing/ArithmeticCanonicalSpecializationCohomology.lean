import EnvelopeProperty.Vanishing.ArithmeticCanonicalSpecializationGeometry
import EnvelopeProperty.Vanishing.SpecializationDerivedGeometricCohomology

/-! # Specialization of the original canonical-twisted coefficient

The actual global canonical model, its invertibility and its field-fibre
comparisons are constructed internally. The closed-fibre cohomology premise
is the intermediate geometric input to specialization, in its native form.
-/

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

noncomputable section
universe u

namespace EnvelopeProperty.Vanishing.ArithmeticCanonicalSpecializationCohomology

open CanonicalGeometry ArithmeticCanonicalGlobalBaseChange ArithmeticCanonicalGlobalComparison
open ArithmeticCanonicalSpecializationGeometry

set_option backward.isDefEq.respectTransparency false

private theorem subsingleton_H_iff_moduleIso {X : Scheme.{u}} {M N : X.Modules}
    (e : M ≅ N) (j : ℕ) :
    Subsingleton (CategoryTheory.Sheaf.H M.sheaf j) ↔
      Subsingleton (CategoryTheory.Sheaf.H N.sheaf j) := by
  let eH := (CategoryTheory.Sheaf.functorH (_root_.Opens.grothendieckTopology X) j).mapIso
    ((SheafOfModules.toSheaf X.ringCatSheaf).mapIso e)
  constructor
  · intro h
    let : Subsingleton ((CategoryTheory.Sheaf.functorH
      (_root_.Opens.grothendieckTopology X) j).obj
        ((SheafOfModules.toSheaf X.ringCatSheaf).obj M)) := h
    exact ⟨fun x y => (ConcreteCategory.bijective_of_isIso eH.inv).1 (Subsingleton.elim _ _)⟩
  · intro h
    let : Subsingleton ((CategoryTheory.Sheaf.functorH
      (_root_.Opens.grothendieckTopology X) j).obj
        ((SheafOfModules.toSheaf X.ringCatSheaf).obj N)) := h
    exact ⟨fun x y => (ConcreteCategory.bijective_of_isIso eH.hom).1 (Subsingleton.elim _ _)⟩

variable {R : Type u} [CommRing R] {Y : Scheme.{u}} (p : Y ⟶ Spec (.of R))

/-- Positive cohomology of the prescribed original Cartesian field fibre
is compared to the same original model on its native categorical fibre. -/
theorem squareCanonicalTensor_subsingleton_H_iff
    {k : Type u} [Field k] (φ : CommRingCat.of R ⟶ CommRingCat.of k)
    {X : Scheme.{u}} (g : X ⟶ Y) (q : X ⟶ Spec (.of k))
    (H : IsPullback g q p (Spec.map φ)) (hp : IsProjectiveFactorization p)
    (n : ℕ) [SmoothOfRelativeDimension n p] (L : Y.Modules)
    (hL : Scheme.Modules.IsInvertible L) (j : ℕ) :
    Subsingleton (CategoryTheory.Sheaf.H
      (Scheme.Modules.tensorObj (canonicalLineSheaf q n)
        ((Scheme.Modules.pullback g).obj L)).sheaf (j + 1)) ↔
      Subsingleton (CategoryTheory.Sheaf.H
        ((Scheme.Modules.pullback (Limits.pullback.fst p (Spec.map φ))).obj
          (canonicalModel p n L)).sheaf (j + 1)) := by
  let e := squareIso p φ g q H
  let π := Limits.pullback.fst p (Spec.map φ)
  let s := Limits.pullback.snd p (Spec.map φ)
  let M := canonicalModel p n L
  let N := (Scheme.Modules.pullback π).obj M
  have hM := canonicalModel_isInvertible p n L hL
  let : N.IsQuasicoherent := (hM.pullback π).isQuasicoherent
  let E : (Scheme.Modules.pullback e.hom).obj N ≅
      Scheme.Modules.tensorObj (canonicalLineSheaf q n) ((Scheme.Modules.pullback g).obj L) :=
    (Scheme.Modules.pullbackComp e.hom π).app M ≪≫
      (Scheme.Modules.pullbackCongr (squareIso_fst p φ g q H)).app M ≪≫
      squareCanonicalTensorIso p φ g q H n L
  exact (subsingleton_H_iff_moduleIso E (j + 1)).symm.trans
    (SchemeIsoGeometry.pullback_subsingleton_H_iff e s
      (nativeField_isProjectiveFactorization p φ hp) N j)

variable [IsNoetherianRing R]

private theorem canonicalModelFibre_subsingleton_of_closed_of_injective
    (hp : IsProjectiveFactorization p) (n : ℕ) [SmoothOfRelativeDimension n p]
    (L : Y.Modules) (hL : Scheme.Modules.IsInvertible L)
    (P : Ideal R) [P.IsMaximal] (j : ℕ)
    (hclosed : Subsingleton (CategoryTheory.Sheaf.H
      (Scheme.Modules.tensorObj (canonicalLineSheaf (fiberStructure P.ResidueField p) n)
        ((Scheme.Modules.pullback (fiberProjection P.ResidueField p)).obj L)).sheaf (j + 1)))
    (F : Type u) [Field F] [Algebra R F] (hRF : Function.Injective (algebraMap R F)) :
    Subsingleton (CategoryTheory.Sheaf.H
      ((Scheme.Modules.pullback (fiberProjection F p)).obj (canonicalModel p n L)).sheaf
        (j + 1)) := by
  let M := canonicalModel p n L
  have hM := canonicalModel_isInvertible p n L hL
  let : Smooth p := SmoothOfRelativeDimension.smooth n p
  let : Flat p := inferInstance
  have hc : Subsingleton (CategoryTheory.Sheaf.H
      ((Scheme.Modules.pullback (fiberProjection P.ResidueField p)).obj M).sheaf (j + 1)) :=
    (subsingleton_H_iff_moduleIso (fieldCanonicalTensorIso p n P.ResidueField L) (j + 1)).mpr hclosed
  exact SpecializationDerivedGeometricCohomology.fibre_cohomology_subsingleton_of_closed_fibre_of_injective
    p hp M hM P j hc F hRF

/-- Actual native canonical-twisted closed-fibre vanishing specializes to
every prescribed injective ambient field. The original model and all its
canonical comparisons are produced internally. -/
theorem nativeCanonicalTensor_subsingleton_of_closed_of_injective
    (hp : IsProjectiveFactorization p) (n : ℕ) [SmoothOfRelativeDimension n p]
    (L : Y.Modules) (hL : Scheme.Modules.IsInvertible L)
    (P : Ideal R) [P.IsMaximal] (j : ℕ)
    (hclosed : Subsingleton (CategoryTheory.Sheaf.H
      (Scheme.Modules.tensorObj (canonicalLineSheaf (fiberStructure P.ResidueField p) n)
        ((Scheme.Modules.pullback (fiberProjection P.ResidueField p)).obj L)).sheaf (j + 1)))
    (F : Type u) [Field F] [Algebra R F] (hRF : Function.Injective (algebraMap R F)) :
    Subsingleton (CategoryTheory.Sheaf.H
      (Scheme.Modules.tensorObj (canonicalLineSheaf (fiberStructure F p) n)
        ((Scheme.Modules.pullback (fiberProjection F p)).obj L)).sheaf (j + 1)) :=
  (subsingleton_H_iff_moduleIso (fieldCanonicalTensorIso p n F L) (j + 1)).mp
    (canonicalModelFibre_subsingleton_of_closed_of_injective p hp n L hL P j hclosed F hRF)

/-- The same specialization reaches an arbitrary prescribed original
Cartesian ambient field square, retaining both its original g and q. -/
theorem squareCanonicalTensor_subsingleton_of_closed_of_injective
    (hp : IsProjectiveFactorization p) (n : ℕ) [SmoothOfRelativeDimension n p]
    (L : Y.Modules) (hL : Scheme.Modules.IsInvertible L)
    (P : Ideal R) [P.IsMaximal] (j : ℕ)
    (hclosed : Subsingleton (CategoryTheory.Sheaf.H
      (Scheme.Modules.tensorObj (canonicalLineSheaf (fiberStructure P.ResidueField p) n)
        ((Scheme.Modules.pullback (fiberProjection P.ResidueField p)).obj L)).sheaf (j + 1)))
    {F : Type u} [Field F] (φ : CommRingCat.of R ⟶ CommRingCat.of F)
    (hφ : Function.Injective φ.hom)
    {X : Scheme.{u}} (g : X ⟶ Y) (q : X ⟶ Spec (.of F))
    (H : IsPullback g q p (Spec.map φ)) :
    Subsingleton (CategoryTheory.Sheaf.H
      (Scheme.Modules.tensorObj (canonicalLineSheaf q n)
        ((Scheme.Modules.pullback g).obj L)).sheaf (j + 1)) := by
  let : Algebra R F := φ.hom.toAlgebra
  have hc := canonicalModelFibre_subsingleton_of_closed_of_injective p hp n L hL P j hclosed F hφ
  exact (squareCanonicalTensor_subsingleton_H_iff p φ g q H hp n L hL j).mpr hc

end EnvelopeProperty.Vanishing.ArithmeticCanonicalSpecializationCohomology
