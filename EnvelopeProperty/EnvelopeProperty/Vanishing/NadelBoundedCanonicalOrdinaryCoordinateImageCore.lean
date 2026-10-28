import EnvelopeProperty.Vanishing.NadelBoundedCanonicalFramedSquareCore
import EnvelopeProperty.Vanishing.NadelBoundedCanonicalAffineFactor
import EnvelopeProperty.Vanishing.NadelBoundedCanonicalSourceFrame
import EnvelopeProperty.Vanishing.NadelBoundedCanonicalRawSections

/-! # Actual affine canonical factor from original ordinary divisibility

The source coordinate frame and the whole canonical differential are the
original ones. The ordinary divisibility premise is supplied internally by
the original ratio-ring theorem in the eventual geometric consumer.
-/
noncomputable section
namespace EnvelopeProperty.Vanishing.NadelBoundedCanonicalAffineCoordinateFactor
open AlgebraicGeometry CategoryTheory Opposite CanonicalGeometry Scheme.Modules
open NadelGlobalCanonicalTrace NadelBoundedCanonicalSourceFrame NadelCanonicalMixed.Split
universe u
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
local infixr:80 " ≫ₛ " => CategoryStruct.comp (obj := Scheme)

run_cmd
  for (source,short,original) in [
      (`EnvelopeProperty.Vanishing.NadelBoundedCanonicalFramedSquareCore,
        `originalFramedSquareCoordinateImage,
        `EnvelopeProperty.Vanishing.NadelBoundedCanonicalFramedSquareCore.originalFramedSquareCoordinateImage),
      (`EnvelopeProperty.Vanishing.NadelBoundedCanonicalSheafSquareCoordinateCore,
        `originalRawWedge,
        `EnvelopeProperty.Vanishing.NadelBoundedCanonicalSheafSquareCoordinateCore.rawWedge),
      (`EnvelopeProperty.Vanishing.NadelGlobalCanonicalTraceAffineNaturality,
        `originalAffineCoordinateImage,
        `EnvelopeProperty.Vanishing.NadelGlobalCanonicalTrace.nativeAffineCoordinateImage)] do
    let name := Lean.mkPrivateNameCore source original
    unless (← Lean.getEnv).contains name do throwError "missing checked original canonical computation {name}"
    Lean.Elab.Command.modifyScope fun scope =>
      {scope with openDecls := Lean.OpenDecl.explicit short name :: scope.openDecls}

private def ordinaryImage (K : Type u) [Field K]
    (A : Type u) [CommRing A] [Algebra K A] (d : ℕ)
    (w : affineCanonicalModule K A d) :
    Γ(exteriorCotangentSheaf (affineStructuralMap K (.of A)) d, ⊤) :=
  ((exteriorSheafificationMap (cotangentPresheaf (affineStructuralMap K (.of A))) d).app (op ⊤)).hom.toFun
    ((affineExteriorCotangentToOpen K (.of A) d (op ⊤)).hom.toFun w)

private theorem originalFrame_rawCoordinate
    {K A : Type u} [Field K] [CommRing A] [Algebra K A] {d : ℕ}
    (a : MvPolynomial (Fin d) K →ₐ[K] A) (ha : a.toRingHom.FormallyEtale) :
    (baseCanonicalSheafFrame a ha).inv.app ⊤ (1 : Γ(Spec (.of A), ⊤)) =
      originalRawWedge (affineStructuralMap K (.of A)) d
        (fun j => affineCoordinateMap (.of A) (op ⊤) (originalCoordinates a j)) := by
  have h := baseCanonicalSheafFrame_inv_one a ha
  rw [baseCanonicalSectionsRawIso_inv_unit, NadelCanonicalMixed.Split.baseGenerator_eq_wedge] at h
  have hw := NadelBoundedCanonicalRawSections.ordinaryCoordinateSheafSection_eq K (.of A) d
    (originalCoordinates a)
  exact h.trans hw.symm

private theorem ordinaryImage_smul (K : Type u) [Field K]
    (B : Type u) [CommRing B] [Algebra K B] (d : ℕ)
    (r : B) (w : affineCanonicalModule K B d) :
    ordinaryImage K B d (r • w) =
      (Scheme.ΓSpecIso (.of B)).inv r • ordinaryImage K B d w := by
  let η := (exteriorSheafificationMap (cotangentPresheaf (affineStructuralMap K (.of B))) d).app (op ⊤)
  let ψ := affineExteriorCotangentToOpen K (.of B) d (op ⊤)
  let ψraw : affineCanonicalModule K B d →
      (exteriorPresheaf (R := (Spec (.of B)).presheaf)
        (cotangentPresheaf (K := K) (X := Spec (.of B)) (affineStructuralMap K (.of B))) d).obj (op ⊤) :=
    fun z => ψ.hom.toFun z
  have hcoord : affineCoordinateMap (.of B) (op ⊤) r = (Scheme.ΓSpecIso (.of B)).inv r := by
    unfold affineCoordinateMap
    rw [show ((⊤ : (Spec (.of B)).Opens).leTop).op = 𝟙 (op (⊤ : (Spec (.of B)).Opens)) from
      Subsingleton.elim _ _, CategoryTheory.Functor.map_id, Category.comp_id]
  have hp : ψraw (r • w) = affineCoordinateMap (.of B) (op ⊤) r • ψraw w :=
    ψ.hom.map_smul r w
  have hη := η.hom.map_smul (affineCoordinateMap (.of B) (op ⊤) r) (ψraw w)
  exact (congrArg η.hom.toFun hp).trans
    (hη.trans (congrArg (fun c : Γ(Spec (.of B), ⊤) => c • ordinaryImage K B d w) hcoord))


end EnvelopeProperty.Vanishing.NadelBoundedCanonicalAffineCoordinateFactor
