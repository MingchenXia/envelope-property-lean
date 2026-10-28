import EnvelopeProperty.Vanishing.ArithmeticCanonicalGlobalCover
import EnvelopeProperty.Vanishing.ArithmeticCanonicalPushoutOpenCompatibility
import ModularCurves.Picard.PicComparison
import ModularCurves.Picard.PullbackTensorObj

/-! # Whole arithmetic canonical base change on the actual original family

The actual fixed-base standard-smooth charts internally produce the local
fibre comparisons. Genuine universal-differential functoriality transports
their invertibility to the same whole global map, and native cover detection
proves the global comparison without a model or comparison certificate.
-/

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

noncomputable section
universe u

namespace EnvelopeProperty.Vanishing.ArithmeticCanonicalGlobalComparison

set_option backward.isDefEq.respectTransparency false

private theorem isIso_of_pullback_cover {X : Scheme.{u}} {M N : X.Modules}
    (φ : M ⟶ N) (𝒰 : Scheme.OpenCover.{u} X)
    (h : ∀ i, IsIso ((Scheme.Modules.pullback (𝒰.f i)).map φ)) : IsIso φ := by
  apply Scheme.Modules.isIso_of_bijective_app_on_cover φ
    (fun i => (𝒰.f i).opensRange) 𝒰.iSup_opensRange
  intro i W hW
  let g := 𝒰.f i
  have hi : IsIso ((Scheme.Modules.restrictFunctor g).map φ) :=
    (NatIso.isIso_map_iff (Scheme.Modules.restrictFunctorIsoPullback g) φ).mpr (h i)
  have hb := ConcreteCategory.bijective_of_isIso
    (((Scheme.Modules.restrictFunctor g).map φ).app (g ⁻¹ᵁ W))
  change Function.Bijective (φ.app (g ''ᵁ (g ⁻¹ᵁ W))) at hb
  have he : g ''ᵁ (g ⁻¹ᵁ W) = W := by
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf, inf_eq_right.mpr hW]
  exact Eq.mp (congrArg (fun U => Function.Bijective (φ.app U)) he) hb

open CanonicalGeometry ArithmeticCanonicalGlobal ArithmeticCanonicalGlobalFrames
open ArithmeticCanonicalGlobalBaseChange ArithmeticCanonicalGlobalCover

variable {R : Type u} [CommRing R] (S : Type u) [CommRing S] [Algebra R S]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of R)) (n : ℕ) [SmoothOfRelativeDimension n f]

/-- The actual whole relative canonical differential is invertible on the
native categorical base change of the original smooth arithmetic family.
All charts, their local comparisons and their covering property are derived
internally from the original relative smoothness. -/
theorem canonicalPullback_isIso : IsIso (exteriorPullbackMap S f n) := by
  apply isIso_of_pullback_cover (exteriorPullbackMap S f n) (fiberChartCover f n S)
  intro x
  let : IsIso (exteriorPullbackMap S (chartMap f n x ≫ f) n) :=
    chartCanonicalPullback_isIso f n S x
  change IsIso ((Scheme.Modules.pullback
    (ArithmeticCanonicalPushoutOpenCompatibility.fiberMap S f (chartMap f n x))).map
      (exteriorPullbackMap S f n))
  exact ArithmeticCanonicalPushoutOpenCompatibility.isIso_pullback_exteriorPullbackMap
    S f (chartMap f n x) n

/-- The constructed whole relative canonical line has the existing native
canonical line on the same actual field fibre, with the original scheme and
both native projections retained. -/
def fieldCanonicalIso (k : Type u) [Field k] [Algebra R k] :
    (Scheme.Modules.pullback (fiberProjection k f)).obj (canonicalObject f n) ≅
      canonicalLineSheaf (fiberStructure k f) n :=
  letI := canonicalPullback_isIso k f n
  asIso (exteriorPullbackMap k f n) ≪≫ canonicalObject_fieldIso (fiberStructure k f) n

/-- The actual canonical-twisted global module specializes to the original
line's actual pullback tensor the existing native fibre canonical line.
No fibre comparison or replacement line is a hypothesis. -/
def fieldCanonicalTensorIso (k : Type u) [Field k] [Algebra R k] (L : X.Modules) :
    (Scheme.Modules.pullback (fiberProjection k f)).obj
        (Scheme.Modules.tensorObj (canonicalObject f n) L) ≅
      Scheme.Modules.tensorObj (canonicalLineSheaf (fiberStructure k f) n)
        ((Scheme.Modules.pullback (fiberProjection k f)).obj L) :=
  (Scheme.Modules.nonempty_pullback_tensorObj (fiberProjection k f) (canonicalObject f n) L).some ≪≫
    Scheme.Modules.tensorObjCongr (fieldCanonicalIso f n k) (Iso.refl _)

end EnvelopeProperty.Vanishing.ArithmeticCanonicalGlobalComparison
