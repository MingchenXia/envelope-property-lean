import EnvelopeProperty.Vanishing.NadelGlobalCanonicalTraceSpectrum
import EnvelopeProperty.AlgGeom.Canonical.CotangentMorphismFunctoriality

/-! # The same original native differential along arbitrary affine maps

This supplies the actual branched differential used in trace normalization.
The source smoothness produces quasicoherence.  No etaleness, target
smoothness, differential-isomorphism or matching certificate is assumed.
-/
noncomputable section
namespace EnvelopeProperty.Vanishing.NadelGlobalCanonicalTrace
open AlgebraicGeometry CategoryTheory Opposite CanonicalGeometry
open scoped TensorProduct
universe u
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {k : Type u} [Field k] {B C : CommRingCat.{u}}
    (f : Spec B ⟶ Spec (.of k)) (φ : B ⟶ C) (n : ℕ)
    [SmoothOfRelativeDimension n f]

/-- Actual original canonical differential on native original-ring sections,
constructed from the SAME affine unit and SAME sheaf differential. -/
def nativeCanonicalPullbackMap :
    (moduleSpecΓFunctor (R := B)).obj (exteriorCotangentSheaf f n) ⟶
      (ModuleCat.restrictScalars φ.hom).obj
        ((moduleSpecΓFunctor (R := C)).obj
          (exteriorCotangentSheaf (Spec.map φ ≫ f) n)) := by
  letI : (exteriorCotangentSheaf f n).IsQuasicoherent :=
    (canonicalLineSheaf_isInvertible f n).isQuasicoherent
  letI : Algebra B C := φ.hom.toAlgebra
  let M := (moduleSpecΓFunctor (R := B)).obj (exteriorCotangentSheaf f n)
  exact (ModuleCat.extendRestrictScalarsAdj φ.hom).unit.app M ≫
    (ModuleCat.restrictScalars φ.hom).map
      ((AffinePullbackStalkTensorReadback.specPullbackTensorEquiv
        (exteriorCotangentSheaf f n) φ).toModuleIso.hom ≫
          (moduleSpecΓFunctor (R := C)).map
            (exteriorCotangentSheafPullbackMap f (Spec.map φ) n))

/-- On EVERY original section this is the literal original adjoint
canonical differential, including for the actual branched map. -/
theorem nativeCanonicalPullbackMap_apply
    (w : (moduleSpecΓFunctor (R := B)).obj (exteriorCotangentSheaf f n)) :
    nativeCanonicalPullbackMap f φ n w =
      (show (moduleSpecΓFunctor (R := C)).obj
        (exteriorCotangentSheaf (Spec.map φ ≫ f) n) from
        (exteriorCotangentSheafMorphism f (Spec.map φ) n).val.app (op ⊤) w) := by
  let : (exteriorCotangentSheaf f n).IsQuasicoherent :=
    (canonicalLineSheaf_isInvertible f n).isQuasicoherent
  let : Algebra B C := φ.hom.toAlgebra
  change (exteriorCotangentSheafPullbackMap f (Spec.map φ) n).val.app (op ⊤)
    (AffinePullbackStalkTensorReadback.specPullbackTensorEquiv
      (exteriorCotangentSheaf f n) φ ((1 : C) ⊗ₜ[B] w)) = _
  rw [AffinePullbackStalkTensorReadback.specPullbackTensorEquiv_tmul, one_smul]
  have hu : Scheme.Modules.affinePullbackUnitTop (Spec.map φ) (exteriorCotangentSheaf f n) w =
      ((Scheme.Modules.pullbackPushforwardAdjunction (Spec.map φ)).unit.app
        (exteriorCotangentSheaf f n)).val.app (op ⊤) w := by
    change ((Scheme.Modules.pullback (Spec.map φ)).obj (exteriorCotangentSheaf f n)).presheaf.map
      (𝟙 (op (⊤ : (Spec C).Opens))) _ = _
    exact congr($(((Scheme.Modules.pullback (Spec.map φ)).obj
      (exteriorCotangentSheaf f n)).presheaf.map_id (op ⊤)).hom
        (((Scheme.Modules.pullbackPushforwardAdjunction (Spec.map φ)).unit.app
          (exteriorCotangentSheaf f n)).val.app (op ⊤) w))
  rw [hu]
  exact congr($(exteriorCotangentSheafPullbackMap_unit f (Spec.map φ) n).val.app (op ⊤) |>.hom w)

/-- The original sheafification unit retains EVERY raw source top form
under the same actual native canonical differential. -/
theorem nativeCanonicalPullbackMap_raw
    (z : (exteriorCotangentPresheaf f n).obj (op ⊤)) :
    nativeCanonicalPullbackMap f φ n
      ((exteriorSheafificationMap (cotangentPresheaf f) n).app (op ⊤) z) =
      (show (moduleSpecΓFunctor (R := C)).obj
        (exteriorCotangentSheaf (Spec.map φ ≫ f) n) from
        (exteriorSheafificationMap (cotangentPresheaf (Spec.map φ ≫ f)) n).app
          (op ((Spec.map φ) ⁻¹ᵁ ⊤))
            (exteriorCotangentMorphismComponent f (Spec.map φ) n (op ⊤) z)) := by
  rw [nativeCanonicalPullbackMap_apply]
  exact exteriorCotangentSheafMorphism_raw f (Spec.map φ) n ⊤ z

end EnvelopeProperty.Vanishing.NadelGlobalCanonicalTrace
