import EnvelopeProperty.Vanishing.FrobeniusCohomology
import EnvelopeProperty.Vanishing.FrobeniusCohomologyDifferentials
import EnvelopeProperty.Vanishing.SmoothExteriorFiniteType
import EnvelopeProperty.AlgGeom.BundleTensorPowerPullback
import EnvelopeProperty.AlgGeom.SchemeLineAmpleness

/-! # Original Hodge cohomology versus the actual perfect-field Frobenius twist

The line is pulled by the genuine first projection.  The differential sheaf
uses the genuine second projection.  Their identification retains the base
automorphism, rather than treating the first projection as a k-morphism.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.MonoidalCategory
open AlgebraicGeometry.Scheme.Modules

noncomputable section
universe u

namespace EnvelopeProperty.Vanishing.FrobeniusCohomologyHodge

open Cartier CanonicalGeometry FrobeniusCohomology FrobeniusCohomologyDifferentials

attribute [local instance] Scheme.Modules.monoidalCategory Scheme.Modules.symmetricCategory

variable {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) (p : ℕ) [Fact p.Prime] [CharP k p] [PerfectRing k p]

/-- Actual base change of the entire original Hodge tensor, for all powers
and exterior degrees; the field automorphism is built into `twistExteriorIso`. -/
def hodgeTwistTensorIso (L : X.Modules) (m i : ℕ) :
    (pullback (twistProjectionIso f p).hom).obj
      (bundleTensorPower L m ⊗ exteriorCotangentSheaf f i) ≅
        bundleTensorPower ((pullback (twistProjectionIso f p).hom).obj L) m ⊗
          exteriorCotangentSheaf (twistStructure f p) i := by
  let π := (twistProjectionIso f p).hom
  letI : (pullback π).Monoidal := Scheme.Modules.pullbackMonoidal π
  exact (Functor.Monoidal.μIso (pullback π) (bundleTensorPower L m)
    (exteriorCotangentSheaf f i)).symm ≪≫
      (BundleTensorPowerPullback.pullbackIso π L m ⊗ᵢ twistExteriorIso f p i)

private theorem subsingleton_H_iff_moduleIso {Y : Scheme.{u}} {M N : Y.Modules}
    (e : M ≅ N) (q : ℕ) :
    Subsingleton (CategoryTheory.Sheaf.H M.sheaf q) ↔
      Subsingleton (CategoryTheory.Sheaf.H N.sheaf q) := by
  let eH := (CategoryTheory.Sheaf.functorH (_root_.Opens.grothendieckTopology Y) q).mapIso
    ((SheafOfModules.toSheaf Y.ringCatSheaf).mapIso e)
  constructor
  · intro h
    let : Subsingleton ((CategoryTheory.Sheaf.functorH
      (_root_.Opens.grothendieckTopology Y) q).obj
        ((SheafOfModules.toSheaf Y.ringCatSheaf).obj M)) := h
    exact ⟨fun x y => (ConcreteCategory.bijective_of_isIso eH.inv).1 (Subsingleton.elim _ _)⟩
  · intro h
    let : Subsingleton ((CategoryTheory.Sheaf.functorH
      (_root_.Opens.grothendieckTopology Y) q).obj
        ((SheafOfModules.toSheaf Y.ringCatSheaf).obj N)) := h
    exact ⟨fun x y => (ConcreteCategory.bijective_of_isIso eH.hom).1 (Subsingleton.elim _ _)⟩

/-- Positive Hodge-cohomology vanishing on the actual Frobenius twist is
equivalent to vanishing on the original smooth projective scheme, in every
exterior degree and every nonnegative tensor power. No cohomology comparison
or scalar-identification certificate is an input. -/
theorem twistHodge_subsingleton_H_iff
    (n : ℕ) [SmoothOfRelativeDimension n f] (L : X.Modules)
    (hL : SchemeLineAmpleness.IsAmple f L) (m i q : ℕ) :
    Subsingleton (CategoryTheory.Sheaf.H
      (bundleTensorPower ((pullback (twistProjectionIso f p).hom).obj L) m ⊗
        exteriorCotangentSheaf (twistStructure f p) i).sheaf (q + 1)) ↔
      Subsingleton (CategoryTheory.Sheaf.H
        (bundleTensorPower L m ⊗ exteriorCotangentSheaf f i).sheaf (q + 1)) := by
  let W := exteriorCotangentSheaf f i
  let A := bundleTensorPower L m
  let M := A ⊗ W
  let : W.IsQuasicoherent := SmoothExteriorFiniteType.isQuasicoherent f n i
  have hA : IsInvertible A :=
    TensorPowerBaseIdealGrading.tensorPower_isInvertible hL.isInvertible m
  let : (W ⊗ A).IsQuasicoherent :=
    SchemeInvertibleTensorQuasicoherent.isQuasicoherent_tensorRight W A hA
  let : M.IsQuasicoherent :=
    (isQuasicoherent X).prop_of_iso (β_ W A) inferInstance
  have hc := twistPullback_subsingleton_H_iff f p hL.isProjectiveFactorization M q
  exact (subsingleton_H_iff_moduleIso (hodgeTwistTensorIso f p L m i) (q + 1)).symm.trans hc

end EnvelopeProperty.Vanishing.FrobeniusCohomologyHodge
