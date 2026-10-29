import EnvelopeProperty.AlgGeom.AffinePushforwardCohomology
import EnvelopeProperty.Global.ProjectiveAffineCover
import EnvelopeProperty.AlgGeom.SchemeAmpleClosedRestriction
import EnvelopeProperty.AlgGeom.Canonical.CanonicalLineSheaf

/-! # Original geometry transported by actual scheme isomorphisms

The positive cohomology comparison is constructed from the actual module
adjunction unit and native ordered affine Cech comparison.  Ampleness uses
the original positive-power closed-embedding criterion.  Exterior and
canonical modules retain the specified field structure triangle.
-/

open AlgebraicGeometry CategoryTheory TopologicalSpace
open Scheme.Modules
open CategoryTheory.MonoidalCategory

noncomputable section
universe u

namespace EnvelopeProperty.Vanishing.SchemeIsoGeometry

open CanonicalGeometry
attribute [local instance] Scheme.Modules.monoidalCategory

noncomputable local instance {X Y : Scheme.{u}} (g : X ⟶ Y) :
    (Scheme.Modules.pullback g).Monoidal := Scheme.Modules.pullbackMonoidal g

variable {X Y : Scheme.{u}}

/-- The original module unit for an actual scheme isomorphism is derived
from the native pullback equivalence and its actual right adjoint. -/
def pullbackPushforwardUnitIso (e : X ≅ Y) (M : Y.Modules) :
    M ≅ (Scheme.Modules.pushforward e.hom).obj
      ((Scheme.Modules.pullback e.hom).obj M) := by
  let : (Scheme.Modules.pullback e.hom).IsEquivalence := pullback_isEquivalence_of_iso e
  let : (Scheme.Modules.pushforward e.hom).IsEquivalence :=
    (pullbackPushforwardAdjunction e.hom).isEquivalence_right_of_isEquivalence_left
  let : IsIso (pullbackPushforwardAdjunction e.hom).unit := by infer_instance
  exact asIso ((pullbackPushforwardAdjunction e.hom).unit.app M)

/-- An actual isomorphism pullback of the original quasicoherent module
is quasicoherent, via the native restriction/pullback comparison. -/
theorem pullback_isQuasicoherent (e : X ≅ Y) (M : Y.Modules) [M.IsQuasicoherent] :
    ((Scheme.Modules.pullback e.hom).obj M).IsQuasicoherent := by
  let : (M.restrict e.hom).IsQuasicoherent := inferInstance
  exact (isQuasicoherent X).prop_of_iso
    ((restrictFunctorIsoPullback e.hom).app M) inferInstance

private theorem subsingleton_H_of_moduleIso {Z : Scheme.{u}} {M N : Z.Modules}
    (e : M ≅ N) (q : ℕ) (hN : Subsingleton (CategoryTheory.Sheaf.H N.sheaf q)) :
    Subsingleton (CategoryTheory.Sheaf.H M.sheaf q) := by
  let eH := (CategoryTheory.Sheaf.functorH (_root_.Opens.grothendieckTopology Z) q).mapIso
    ((SheafOfModules.toSheaf Z.ringCatSheaf).mapIso e)
  have hzero : Subsingleton
      ((CategoryTheory.Sheaf.functorH (_root_.Opens.grothendieckTopology Z) q).obj
        ((SheafOfModules.toSheaf Z.ringCatSheaf).obj N)) := hN
  let := hzero
  exact ⟨fun x y => (ConcreteCategory.bijective_of_isIso eH.hom).1 (Subsingleton.elim _ _)⟩

/-- Every positive whole native cohomology group of the actual pullback
vanishes exactly when the same original module's group vanishes. -/
theorem pullback_subsingleton_H_iff {R : Type u} [CommRing R]
    (e : X ≅ Y) (p : Y ⟶ Spec (.of R)) (hp : IsProjectiveFactorization p)
    (M : Y.Modules) [M.IsQuasicoherent] (q : ℕ) :
    Subsingleton (CategoryTheory.Sheaf.H
      ((Scheme.Modules.pullback e.hom).obj M).sheaf (q + 1)) ↔
      Subsingleton (CategoryTheory.Sheaf.H M.sheaf (q + 1)) := by
  let N := (Scheme.Modules.pullback e.hom).obj M
  let : Y.IsSeparated := ProjectiveAffineCover.separated p hp
  let : N.IsQuasicoherent := pullback_isQuasicoherent e M
  let Q := (Scheme.Modules.pushforward e.hom).obj N
  obtain ⟨ι, hlin, hfin, U, hUa, hU⟩ := ProjectiveAffineCover.exists_affine_openCover p hp
  let : LinearOrder ι := hlin
  let : Fintype ι := hfin
  have hpush : Subsingleton (CategoryTheory.Sheaf.H N.sheaf (q + 1)) ↔
      Subsingleton (CategoryTheory.Sheaf.H Q.sheaf (q + 1)) :=
    AffinePushforwardCohomology.subsingleton_H_iff_pushforward e.hom p N U hU hUa q
  have eu : M ≅ Q := pullbackPushforwardUnitIso e M
  exact hpush.trans ⟨fun h => subsingleton_H_of_moduleIso eu (q + 1) h,
    fun h => subsingleton_H_of_moduleIso eu.symm (q + 1) h⟩

/-- The original positive-power projective embedding of an ample line
pulls back through the actual closed immersion underlying an isomorphism. -/
theorem isAmple_pullback {R : Type u} [CommRing R]
    (e : X ≅ Y) (p : Y ⟶ Spec (.of R)) {L : Y.Modules}
    (hL : SchemeLineAmpleness.IsAmple p L) :
    SchemeLineAmpleness.IsAmple (e.hom ≫ p) ((Scheme.Modules.pullback e.hom).obj L) :=
  SchemeAmpleClosedRestriction.ample_pullback hL e.hom

/-- The same original ample pullback retains any specified compatible
structural morphism, rather than replacing it by an unrelated map. -/
theorem isAmple_pullback_of_triangle {R : Type u} [CommRing R]
    (e : X ≅ Y) (pX : X ⟶ Spec (.of R)) (pY : Y ⟶ Spec (.of R))
    (he : e.hom ≫ pY = pX) {L : Y.Modules}
    (hL : SchemeLineAmpleness.IsAmple pY L) :
    SchemeLineAmpleness.IsAmple pX ((Scheme.Modules.pullback e.hom).obj L) := by
  simpa only [he] using isAmple_pullback e pY hL

/-- The inverse of the same original isomorphism has the actual inverse
structure triangle, derived from the given whole triangle. -/
theorem inv_structure {S : Scheme.{u}} (e : X ≅ Y) (fX : X ⟶ S) (fY : Y ⟶ S)
    (he : e.hom ≫ fY = fX) : e.inv ≫ fX = fY := by
  rw [← he, ← Category.assoc, e.inv_hom_id, Category.id_comp]

section FieldGeometry

variable {k : Type u} [Field k] (e : X ≅ Y)
    (fX : X ⟶ Spec (.of k)) (fY : Y ⟶ Spec (.of k)) (he : e.hom ≫ fY = fX)

/-- Native field-relative exterior modules pull back along the actual
compatible scheme isomorphism, with the original triangle retained. -/
def exteriorPullbackIso (i : ℕ) :
    (Scheme.Modules.pullback e.hom).obj (exteriorCotangentSheaf fY i) ≅
      exteriorCotangentSheaf fX i :=
  ((restrictFunctorIsoPullback e.hom).app (exteriorCotangentSheaf fY i)).symm ≪≫
    exteriorCotangentSheafOpenImmersionIso fY e.hom i ≪≫
      eqToIso (congrArg (fun f => exteriorCotangentSheaf f i) he)

/-- The original canonical object in the SAME degree has the actual
pullback comparison, as its original top exterior construction. -/
def canonicalPullbackIso (d : ℕ) :
    (Scheme.Modules.pullback e.hom).obj (canonicalLineSheaf fY d) ≅
      canonicalLineSheaf fX d := exteriorPullbackIso e fX fY he d

/-- The actual monoidal pullback retains the original line-first exterior
term and both original structural morphisms. -/
def exteriorTensorPullbackIso (L : Y.Modules) (i : ℕ) :
    (Scheme.Modules.pullback e.hom).obj (L ⊗ exteriorCotangentSheaf fY i) ≅
      (Scheme.Modules.pullback e.hom).obj L ⊗ exteriorCotangentSheaf fX i :=
  (Functor.Monoidal.μIso (Scheme.Modules.pullback e.hom) L
    (exteriorCotangentSheaf fY i)).symm ≪≫
      (Iso.refl _ ⊗ᵢ exteriorPullbackIso e fX fY he i)

/-- Every actual original power and exterior degree is retained by
pullback; the power comparison is constructed natively, not supplied. -/
def hodgeTensorPowerPullbackIso (L : Y.Modules) (m i : ℕ) :
    (Scheme.Modules.pullback e.hom).obj (bundleTensorPower L m ⊗ exteriorCotangentSheaf fY i) ≅
      bundleTensorPower ((Scheme.Modules.pullback e.hom).obj L) m ⊗
        exteriorCotangentSheaf fX i :=
  (Functor.Monoidal.μIso (Scheme.Modules.pullback e.hom) (bundleTensorPower L m)
    (exteriorCotangentSheaf fY i)).symm ≪≫
      (BundleTensorPowerPullback.pullbackIso e.hom L m ⊗ᵢ
        exteriorPullbackIso e fX fY he i)

/-- The actual canonical-first original twist has the whole pullback
comparison in precisely its original tensor order. -/
def canonicalTwistPullbackIso (L : Y.Modules) (d : ℕ) :
    (Scheme.Modules.pullback e.hom).obj (canonicalLineSheaf fY d ⊗ L) ≅
      canonicalLineSheaf fX d ⊗ (Scheme.Modules.pullback e.hom).obj L :=
  (Functor.Monoidal.μIso (Scheme.Modules.pullback e.hom) (canonicalLineSheaf fY d) L).symm ≪≫
    (canonicalPullbackIso e fX fY he d ⊗ᵢ Iso.refl _)

/-- The same comparison for the actual explicitly sheafified coherent
tensor, using its native comparison with the monoidal tensor. -/
def canonicalTensorObjPullbackIso (L : Y.Modules) (d : ℕ) :
    (Scheme.Modules.pullback e.hom).obj
      (Scheme.Modules.tensorObj (canonicalLineSheaf fY d) L) ≅
      Scheme.Modules.tensorObj (canonicalLineSheaf fX d)
        ((Scheme.Modules.pullback e.hom).obj L) :=
  (Scheme.Modules.pullback e.hom).mapIso
      (ModularCurves.monoidalTensorObjIso (canonicalLineSheaf fY d) L).symm ≪≫
    canonicalTwistPullbackIso e fX fY he L d ≪≫
      ModularCurves.monoidalTensorObjIso (canonicalLineSheaf fX d)
        ((Scheme.Modules.pullback e.hom).obj L)

end FieldGeometry
end EnvelopeProperty.Vanishing.SchemeIsoGeometry
