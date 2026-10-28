import EnvelopeProperty.AlgGeom.Canonical.ExteriorCotangentMorphism
import EnvelopeProperty.AlgGeom.Canonical.NativeInvertibility
import ModularCurves.ForMathlib.AffineModuleBaseChange
import ModularCurves.Picard.InvertibleSheafLocallyFree

/-!
# Actual affine pullback sections of the canonical differential morphism

The genuine affine pullback comparison and its actual unit formula preserve
all raw exterior forms through the original sheaf differential map.
-/

open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace
open scoped TensorProduct

namespace EnvelopeProperty.CanonicalGeometry

universe u
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {K : Type u} [Field K] {X Y : Scheme.{u}}
    (f : X ⟶ Spec (.of K)) (g : Y ⟶ X)

/-- The genuine pullback adjoint preserves the entire actual exterior
sheaf morphism through the actual pullback-pushforward adjunction unit. -/
theorem exteriorCotangentSheafPullbackMap_unit (n : ℕ) :
    (Scheme.Modules.pullbackPushforwardAdjunction g).unit.app
        (exteriorCotangentSheaf f n) ≫
      (Scheme.Modules.pushforward g).map (exteriorCotangentSheafPullbackMap f g n) =
        exteriorCotangentSheafMorphism f g n := by
  have h := ((Scheme.Modules.pullbackPushforwardAdjunction g).homEquiv
    (exteriorCotangentSheaf f n) (exteriorCotangentSheaf (g ≫ f) n)).apply_symm_apply
      (exteriorCotangentSheafMorphism f g n)
  exact ((Scheme.Modules.pullbackPushforwardAdjunction g).homEquiv_unit
    (exteriorCotangentSheaf f n) (exteriorCotangentSheaf (g ≫ f) n)
      (exteriorCotangentSheafPullbackMap f g n)).symm.trans h

/-- On actual affine schemes, smoothness derives source quasicoherence and
the genuine affine pullback comparison retains EVERY original raw form. -/
theorem exteriorCotangentSheafPullbackMap_affine_one_tmul
    [IsAffine X] [IsAffine Y] (n : ℕ) [SmoothOfRelativeDimension n f]
    (z : (exteriorCotangentPresheaf f n).obj (.op ⊤)) :
    letI : (exteriorCotangentSheaf f n).IsQuasicoherent :=
      (canonicalLineSheaf_isInvertible f n).isQuasicoherent
    (exteriorCotangentSheafPullbackMap f g n).val.app (.op ⊤)
      ((Scheme.Modules.affinePullbackΓIso g (exteriorCotangentSheaf f n)).hom
        ((1 : Γ(Y, ⊤)) ⊗ₜ[Γ(X, ⊤)]
          (exteriorSheafificationMap (cotangentPresheaf f) n).app (.op ⊤) z)) =
      (exteriorSheafificationMap (cotangentPresheaf (g ≫ f)) n).app (.op (g ⁻¹ᵁ ⊤))
        (exteriorCotangentMorphismComponent f g n (.op ⊤) z) := by
  let : (exteriorCotangentSheaf f n).IsQuasicoherent :=
    (canonicalLineSheaf_isInvertible f n).isQuasicoherent
  rw [Scheme.Modules.affinePullbackΓIso_hom_one_tmul]
  have hu : Scheme.Modules.affinePullbackUnitTop g (exteriorCotangentSheaf f n)
      ((exteriorSheafificationMap (cotangentPresheaf f) n).app (.op ⊤) z) =
      ((Scheme.Modules.pullbackPushforwardAdjunction g).unit.app
        (exteriorCotangentSheaf f n)).val.app (.op ⊤)
          ((exteriorSheafificationMap (cotangentPresheaf f) n).app (.op ⊤) z) := by
    change ((Scheme.Modules.pullback g).obj (exteriorCotangentSheaf f n)).presheaf.map
      (𝟙 (.op ⊤)) _ = _
    exact congr($(((Scheme.Modules.pullback g).obj
      (exteriorCotangentSheaf f n)).presheaf.map_id (.op ⊤)).hom
        (((Scheme.Modules.pullbackPushforwardAdjunction g).unit.app
          (exteriorCotangentSheaf f n)).val.app (.op ⊤)
            ((exteriorSheafificationMap (cotangentPresheaf f) n).app (.op ⊤) z)))
  rw [hu]
  have h := congr($(exteriorCotangentSheafPullbackMap_unit f g n).val.app (.op ⊤) |>.hom
    ((exteriorSheafificationMap (cotangentPresheaf f) n).app (.op ⊤) z))
  exact h.trans (congr($(exteriorCotangentSheafMorphism_unit f g n).app (.op ⊤) |>.hom z))

/-- Actual pure products retain the literal cotangent images through the
true affine pullback comparison and the true sheaf differential map. -/
theorem exteriorCotangentSheafPullbackMap_affine_one_tmul_wedge
    [IsAffine X] [IsAffine Y] (n : ℕ) [SmoothOfRelativeDimension n f]
    (m : Fin n → (cotangentPresheaf f).obj (.op ⊤)) :
    letI : (exteriorCotangentSheaf f n).IsQuasicoherent :=
      (canonicalLineSheaf_isInvertible f n).isQuasicoherent
    (exteriorCotangentSheafPullbackMap f g n).val.app (.op ⊤)
      ((Scheme.Modules.affinePullbackΓIso g (exteriorCotangentSheaf f n)).hom
        ((1 : Γ(Y, ⊤)) ⊗ₜ[Γ(X, ⊤)] exteriorSheafSection
          (cotangentPresheaf f) n ⊤ m)) =
      exteriorSheafSection (cotangentPresheaf (g ≫ f)) n (g ⁻¹ᵁ ⊤)
        (fun j ↦ cotangentMorphismSemilinear f g (.op ⊤) (m j)) := by
  let : (exteriorCotangentSheaf f n).IsQuasicoherent :=
    (canonicalLineSheaf_isInvertible f n).isQuasicoherent
  exact (exteriorCotangentSheafPullbackMap_affine_one_tmul f g n
    (exteriorPower.ιMulti Γ(X, ⊤) n m)).trans
      (congrArg ((exteriorSheafificationMap (cotangentPresheaf (g ≫ f)) n).app (.op (g ⁻¹ᵁ ⊤)))
        (exteriorCotangentMorphismComponent_wedge f g n (.op ⊤) m))

end
end EnvelopeProperty.CanonicalGeometry
