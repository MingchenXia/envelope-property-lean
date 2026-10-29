import EnvelopeProperty.Vanishing.RelativeArithmeticCohomologyLocalization
import EnvelopeProperty.Vanishing.SpecializationDerivedGeometricCohomology
import EnvelopeProperty.Vanishing.ArithmeticCanonicalSpecializationGeometry

/-! # Canonical specialization for a nonproper arithmetic family

The actual finite affine Čech complex performs both geometric fibre
comparisons. Local freeness is an intermediate hypothesis supplied by
generic freeness of the relative finite cohomology modules. Projectivity
over the arithmetic coefficient ring is never assumed.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open scoped TensorProduct

noncomputable section
universe u

namespace EnvelopeProperty.Vanishing.RelativeCanonicalSpecialization

open CanonicalGeometry ArithmeticCanonicalSpecializationGeometry
  SpecializationDerivedNatural

variable {A T C : Type u} [CommRing A] [CommRing T] [CommRing C]
    [Algebra A T] [Algebra A C] [Algebra T C] [IsScalarTower A T C] [Nontrivial C]
    {Y : Scheme.{u}} [Y.IsSeparated] (p : Y ⟶ Spec (.of A))

/-- The same original module on the two genuine scalar fibres is compared
through its actual finite affine Čech complex and arbitrary-rank free local
homology. Neither scalar fibre is assumed proper over its scalar ring. -/
theorem fibre_subsingleton_of_free_scalar_fibre
    (M : Y.Modules) (hM : Scheme.Modules.IsInvertible M)
    {ι : Type u} [LinearOrder ι] [Finite ι] (U : ι → Y.Opens)
    (hU : IsOpenCover U) (hUaff : ∀ i, IsAffineOpen (U i))
    (hflat : ∀ i, Module.Flat A ((GeometricCechBaseChange.scalarComplex p M U).X i))
    (hfree : ∀ i, Module.Free T
      ((RelativeArithmeticCohomologyLocalization.scalarComplex (T := T)
        (GeometricCechBaseChange.scalarComplex p M U)).homology i))
    (N : ℕ) (hbound : ∀ i, N + 1 ≤ i →
      IsZero ((GeometricCechBaseChange.scalarComplex p M U).X i))
    (q : ℕ)
    (hclosed : Subsingleton (CategoryTheory.Sheaf.H
      ((Scheme.Modules.pullback (FlatGlobalSections.firstProjection (S := C) p)).obj M).sheaf
        (q + 1)))
    (F : Type u) [CommRing F] [Algebra A F] [Algebra T F] [IsScalarTower A T F] :
    Subsingleton (CategoryTheory.Sheaf.H
      ((Scheme.Modules.pullback (FlatGlobalSections.firstProjection (S := F) p)).obj M).sheaf
        (q + 1)) := by
  let K := GeometricCechBaseChange.scalarComplex p M U
  let : ∀ i, Module.Flat A (K.X i) := hflat
  let : ∀ i, Module.Free T
      ((RelativeArithmeticCohomologyLocalization.scalarComplex (T := T) K).homology i) := hfree
  apply (SpecializationDerivedGeometricCohomology.fibre_H_iff_tensor_homology_zero
    (S := F) p M hM U hU hUaff q).mpr
  by_cases hqN : q + 1 ≤ N
  · have hc := (SpecializationDerivedGeometricCohomology.fibre_H_iff_tensor_homology_zero
      (S := C) p M hM U hU hUaff q).mp hclosed
    exact RelativeArithmeticCohomologyLocalization.natural_homology_isZero_of_free_scalar_fibre
      (T := T) K N (hbound (N + 1) le_rfl) (q + 1) (Nat.zero_lt_succ q) hqN hc F
  · have hz : IsZero (K.X (q + 1)) := hbound (q + 1) (by omega)
    let : Subsingleton (K.X (q + 1)) := ModuleCat.subsingleton_of_isZero hz
    apply ShortComplex.isZero_homology_of_isZero_X₂
    change IsZero (ModuleCat.of F (F ⊗[A] K.X (q + 1)))
    exact ModuleCat.isZero_of_subsingleton _

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

omit [Y.IsSeparated] in
/-- A prescribed original field square retains its canonical module and line.
Only the original scheme's relative affine projective map is used for the
scheme-isomorphism cohomology comparison. The family over A can be nonproper. -/
theorem squareCanonicalTensor_subsingleton_H_iff
    {k R : Type u} [Field k] [CommRing R] (φ : CommRingCat.of A ⟶ CommRingCat.of k)
    {X : Scheme.{u}} (a : X ⟶ Y) (f : X ⟶ Spec (.of k))
    (H : IsPullback a f p (Spec.map φ))
    (g : X ⟶ Spec (.of R)) (hg : IsProjectiveFactorization g)
    (n : ℕ) [SmoothOfRelativeDimension n p] (L : Y.Modules)
    (hL : Scheme.Modules.IsInvertible L) (q : ℕ) :
    Subsingleton (CategoryTheory.Sheaf.H
      (Scheme.Modules.tensorObj (canonicalLineSheaf f n)
        ((Scheme.Modules.pullback a).obj L)).sheaf (q + 1)) ↔
      Subsingleton (CategoryTheory.Sheaf.H
        ((Scheme.Modules.pullback (pullback.fst p (Spec.map φ))).obj
          (canonicalModel p n L)).sheaf (q + 1)) := by
  let e := squareIso p φ a f H
  let π := pullback.fst p (Spec.map φ)
  let M := canonicalModel p n L
  let N := (Scheme.Modules.pullback π).obj M
  have hM := canonicalModel_isInvertible p n L hL
  let : N.IsQuasicoherent := (hM.pullback π).isQuasicoherent
  let E : (Scheme.Modules.pullback e.hom).obj N ≅
      Scheme.Modules.tensorObj (canonicalLineSheaf f n) ((Scheme.Modules.pullback a).obj L) :=
    (Scheme.Modules.pullbackComp e.hom π).app M ≪≫
      (Scheme.Modules.pullbackCongr (squareIso_fst p φ a f H)).app M ≪≫
      squareCanonicalTensorIso p φ a f H n L
  exact (subsingleton_H_iff_moduleIso E (q + 1)).symm.trans
    (SchemeIsoGeometry.pullback_subsingleton_H_iff e (e.inv ≫ g)
      (hg.comp_isClosedImmersion e.inv inferInstance) N q)

end EnvelopeProperty.Vanishing.RelativeCanonicalSpecialization
