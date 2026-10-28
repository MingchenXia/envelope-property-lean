import EnvelopeProperty.Char0.AmpleNadelInput
import EnvelopeProperty.AlgGeom.ClosedProjectiveRegularityGeneration
import EnvelopeProperty.AlgGeom.SchemeCoherentAmpleTwists
import EnvelopeProperty.AlgGeom.IdealModuleQuasicoherent
import EnvelopeProperty.AlgGeom.Canonical.NativeInvertibility

/-! # Actual regularity produces finite generators of the original multiplier module -/

open AlgebraicGeometry CategoryTheory CategoryTheory.MonoidalCategory TopologicalSpace
open Scheme.Modules MvPolynomial
noncomputable section
universe u

namespace EnvelopeProperty.Char0.MultiplierUniformGenerationRegularity
open CanonicalGeometry
attribute [local instance] Scheme.Modules.monoidalCategory Scheme.Modules.symmetricCategory
  MvPolynomial.gradedAlgebra

/-- A genuine whole-module isomorphism transports ordinary additive-sheaf
cohomology vanishing on the same original scheme. -/
theorem subsingleton_H_of_iso {X : Scheme.{u}} {M N : X.Modules}
    (e : M ≅ N) (q : ℕ) (h : Subsingleton (CategoryTheory.Sheaf.H N.sheaf q)) :
    Subsingleton (CategoryTheory.Sheaf.H M.sheaf q) := by
  let eH := (CategoryTheory.Sheaf.functorH (_root_.Opens.grothendieckTopology X) q).mapIso
    ((SheafOfModules.toSheaf X.ringCatSheaf).mapIso e)
  have hzero : Subsingleton
      ((CategoryTheory.Sheaf.functorH (_root_.Opens.grothendieckTopology X) q).obj
        ((SheafOfModules.toSheaf X.ringCatSheaf).obj N)) := h
  let := hzero
  exact ⟨fun x y => (ConcreteCategory.bijective_of_isIso eH.hom).1 (Subsingleton.elim _ _)⟩

private theorem finiteGenerators_of_iso {X : Scheme.{u}}
    {M N : SheafOfModules.{u} X.ringCatSheaf}
    (G : M.GeneratingSections) [G.IsFiniteType] (e : M ≅ N) :
    ∃ H : N.GeneratingSections, H.IsFiniteType :=
  ⟨G.ofEpi e.hom, inferInstance⟩

private theorem finiteType_of_finitePresentation {X : Scheme.{u}}
    (M : SheafOfModules.{u} X.ringCatSheaf)
    (hM : SheafOfModules.IsFinitePresentation (R := X.ringCatSheaf) M) :
    SheafOfModules.IsFiniteType (R := X.ringCatSheaf) M := by
  let : SheafOfModules.IsFinitePresentation (R := X.ringCatSheaf) M := hM
  infer_instance

/-- The native finite regularity theorem applies to the original whole
multiplier ideal and original total canonical line. Its coherence and finite
type are proved internally, and no generating family of the target is input. -/
theorem exists_generatingSections_of_regularity
    {k R : Type u} [Field k] [CharZero k] [CommRing R]
    {X : Scheme.{u}} [IsIntegral X]
    (p : X ⟶ Spec (.of k)) [Smooth p] (n : ℕ) [SmoothOfRelativeDimension n p]
    {N : ℕ} (i : X ⟶ Proj (homogeneousSubmodule (Fin (N + 1)) R)) [IsClosedImmersion i]
    (I : X.IdealSheafData) (hI : I.stalkIdeal (genericPoint X) ≠ ⊥)
    (c : ℚ) (A : X.Modules) (hA : IsInvertible A)
    (hregular : ∀ q : ℕ, 0 < q → q < N + 1 → Subsingleton (CategoryTheory.Sheaf.H
      (nadelTwistedModule p n I hI c A ⊗
        (pullback i).obj (coordinateHyperplaneTwist (R := R) (0 : Fin (N + 1)) (-(q : ℤ)))).sheaf q)) :
    ∃ G : (nadelTwistedModule p n I hI c A).GeneratingSections, G.IsFiniteType := by
  let J := (schemeMultiplierIdealSheaf p I hI c).toModules
  let T := canonicalLineSheaf p n ⊗ A
  have hT : IsInvertible T :=
    ((canonicalLineSheaf_isInvertible p n).tensorObj hA).of_iso
      (ModularCurves.monoidalTensorObjIso _ _)
  let : J.IsQuasicoherent := (schemeMultiplierIdealSheaf p I hI c).isQuasicoherent_toModules
  let : J.IsFiniteType := finiteType_of_finitePresentation J
    (schemeMultiplierIdealSheaf_isFinitePresentation p I hI c)
  let : (J ⊗ T).IsQuasicoherent :=
    SchemeInvertibleTensorQuasicoherent.isQuasicoherent_tensorRight J T hT
  let : (J ⊗ T).IsFiniteType := SchemeCoherentAmpleTwists.isFiniteType_tensorRight J T hT
  let e : J ⊗ T ≅ nadelTwistedModule p n I hI c A := β_ J T
  have hreg (q : ℕ) (hq : 0 < q) (hqN : q < N + 1) :
      Subsingleton (CategoryTheory.Sheaf.H
        ((J ⊗ T) ⊗ (pullback i).obj
          (coordinateHyperplaneTwist (R := R) (0 : Fin (N + 1)) (-(q : ℤ)))).sheaf q) :=
    subsingleton_H_of_iso (e ⊗ᵢ Iso.refl _) q (hregular q hq hqN)
  obtain ⟨G, hG⟩ := ClosedProjectiveRegularityGeneration.exists_generatingSections_of_regularity
    i (J ⊗ T) (0 : Fin (N + 1)) hreg
  let : G.IsFiniteType := hG
  exact finiteGenerators_of_iso G e

end EnvelopeProperty.Char0.MultiplierUniformGenerationRegularity
