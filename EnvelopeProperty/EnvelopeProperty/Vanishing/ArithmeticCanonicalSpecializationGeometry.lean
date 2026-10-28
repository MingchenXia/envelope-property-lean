import EnvelopeProperty.Vanishing.ArithmeticCanonicalGlobalComparison
import EnvelopeProperty.Vanishing.SchemeIsoGeometry
import EnvelopeProperty.Projective.FactorizationBaseChange
import ModularCurves.ForMathlib.PullbackTensorMonoidal

/-! # Actual canonical coefficients on prescribed Cartesian field fibres

Both original maps of the Cartesian field square are retained. The native
pullback object and its canonical comparison are constructed internally.
-/

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

noncomputable section
universe u

namespace EnvelopeProperty.Vanishing.ArithmeticCanonicalSpecializationGeometry

open CanonicalGeometry ArithmeticCanonicalGlobalFrames ArithmeticCanonicalGlobalComparison

set_option backward.isDefEq.respectTransparency false

variable {R : Type u} [CommRing R] {Y : Scheme.{u}} (p : Y ⟶ Spec (.of R))

/-- The original whole canonical-twisted model, constructed on the same family. -/
def canonicalModel (n : ℕ) (L : Y.Modules) : Y.Modules :=
  Scheme.Modules.tensorObj (canonicalObject p n) L

theorem canonicalModel_isInvertible (n : ℕ) [SmoothOfRelativeDimension n p]
    (L : Y.Modules) (hL : Scheme.Modules.IsInvertible L) :
    Scheme.Modules.IsInvertible (canonicalModel p n L) :=
  (canonicalObject_isInvertible p n).tensorObj hL

section FieldSquare

variable {k : Type u} [Field k] (φ : CommRingCat.of R ⟶ CommRingCat.of k)
    {X : Scheme.{u}} (g : X ⟶ Y) (q : X ⟶ Spec (.of k))
    (H : IsPullback g q p (Spec.map φ))

private opaque squareIsoData :
    {e : X ≅ Limits.pullback p (Spec.map φ) //
      e.hom ≫ Limits.pullback.fst p (Spec.map φ) = g ∧
      e.hom ≫ Limits.pullback.snd p (Spec.map φ) = q} :=
  ⟨H.isoPullback, H.isoPullback_hom_fst, H.isoPullback_hom_snd⟩

/-- The actual Cartesian square supplies its own native fibre isomorphism. -/
def squareIso : X ≅ Limits.pullback p (Spec.map φ) := (squareIsoData p φ g q H).val

theorem squareIso_fst :
    (squareIso p φ g q H).hom ≫ Limits.pullback.fst p (Spec.map φ) = g :=
  (squareIsoData p φ g q H).property.1

theorem squareIso_snd :
    (squareIso p φ g q H).hom ≫ Limits.pullback.snd p (Spec.map φ) = q :=
  (squareIsoData p φ g q H).property.2

omit g q H in
/-- The literal arbitrary field map gives the original native canonical
comparison with its own two projections. -/
def nativeFieldCanonicalTensorIso (n : ℕ) [SmoothOfRelativeDimension n p] (L : Y.Modules) :
    (Scheme.Modules.pullback (Limits.pullback.fst p (Spec.map φ))).obj
        (canonicalModel p n L) ≅
      Scheme.Modules.tensorObj (canonicalLineSheaf (Limits.pullback.snd p (Spec.map φ)) n)
        ((Scheme.Modules.pullback (Limits.pullback.fst p (Spec.map φ))).obj L) := by
  letI : Algebra R k := φ.hom.toAlgebra
  exact fieldCanonicalTensorIso p n k L

omit g q H in
/-- The native fibre's projective factorization is derived from the same
original projective family and its literal field coefficient map. -/
theorem nativeField_isProjectiveFactorization (hp : IsProjectiveFactorization p) :
    IsProjectiveFactorization (Limits.pullback.snd p (Spec.map φ)) := by
  let : Algebra R k := φ.hom.toAlgebra
  exact ProjectiveFactorizationBaseChange.baseChange (S := k) p hp

/-- Pullback of the original model to the prescribed Cartesian field square
is the actual canonical line for the original q, tensored with the original g-pullback. -/
def squareCanonicalTensorIso (n : ℕ) [SmoothOfRelativeDimension n p] (L : Y.Modules) :
    (Scheme.Modules.pullback g).obj (canonicalModel p n L) ≅
      Scheme.Modules.tensorObj (canonicalLineSheaf q n) ((Scheme.Modules.pullback g).obj L) := by
  let e := squareIso p φ g q H
  let π := Limits.pullback.fst p (Spec.map φ)
  let s := Limits.pullback.snd p (Spec.map φ)
  let eg : (Scheme.Modules.pullback e.hom).obj ((Scheme.Modules.pullback π).obj L) ≅
      (Scheme.Modules.pullback g).obj L :=
    (Scheme.Modules.pullbackComp e.hom π).app L ≪≫
      (Scheme.Modules.pullbackCongr (squareIso_fst p φ g q H)).app L
  exact ((Scheme.Modules.pullbackCongr (squareIso_fst p φ g q H)).app
      (canonicalModel p n L)).symm ≪≫
    ((Scheme.Modules.pullbackComp e.hom π).app (canonicalModel p n L)).symm ≪≫
    (Scheme.Modules.pullback e.hom).mapIso (nativeFieldCanonicalTensorIso p φ n L) ≪≫
    SchemeIsoGeometry.canonicalTensorObjPullbackIso e q s (squareIso_snd p φ g q H)
      ((Scheme.Modules.pullback π).obj L) n ≪≫
    Scheme.Modules.tensorObjCongr (Iso.refl _) eg

end FieldSquare

end EnvelopeProperty.Vanishing.ArithmeticCanonicalSpecializationGeometry
