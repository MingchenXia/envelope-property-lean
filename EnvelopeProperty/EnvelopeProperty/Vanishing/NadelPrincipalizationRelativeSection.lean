import EnvelopeProperty.Vanishing.NadelPrincipalizationRelativeSectionCore
import EnvelopeProperty.Vanishing.NadelPrincipalizationRelativeSectionTransport

/-! # Original whole relative-canonical differential section on an actual open square

The source and target line comparisons and their entire differential square
are produced internally by actual geometry. They are not theorem inputs.
-/
open AlgebraicGeometry CategoryTheory
open Scheme.Modules
noncomputable section
universe u
namespace EnvelopeProperty.Vanishing.NadelPrincipalizationRelativeSection
open CanonicalGeometry Char0.RoundedCanonicalModule
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {k : Type u} [Field k] {X₀ X B₀ B : Scheme.{u}}
    (f : X₀ ⟶ Spec (.of k)) (g : X ⟶ X₀) (π : B₀ ⟶ X₀)
    (p : B ⟶ X) (v : B ⟶ B₀) (w : p ≫ g = v ≫ π) (n : ℕ)
    [IsOpenImmersion g] [IsOpenImmersion v]

/-- The genuine source comparison is chosen from its proved actual geometric producer. -/
def sourceLineIso : (pullback v).obj ((pullback π).obj (exteriorCotangentSheaf f n)) ≅
    (pullback p).obj (exteriorCotangentSheaf (g ≫ f) n) :=
  Classical.choose (NadelPrincipalizationRelativeSectionCore.existsCompatibleLines f g π p v w n)

/-- The genuine top comparison is chosen from the same proved original square. -/
def targetLineIso : (pullback v).obj (exteriorCotangentSheaf (π ≫ f) n) ≅
    exteriorCotangentSheaf (p ≫ (g ≫ f)) n :=
  Classical.choose (Classical.choose_spec
    (NadelPrincipalizationRelativeSectionCore.existsCompatibleLines f g π p v w n))

/-- The same produced actual comparisons retain the whole original differential map square. -/
theorem lineIso_square :
    (pullback v).map (exteriorCotangentSheafPullbackMap f π n) ≫ (targetLineIso f g π p v w n).hom =
      (sourceLineIso f g π p v w n).hom ≫ exteriorCotangentSheafPullbackMap (g ≫ f) p n :=
  Classical.choose_spec (Classical.choose_spec
    (NadelPrincipalizationRelativeSectionCore.existsCompatibleLines f g π p v w n))

variable [SmoothOfRelativeDimension n f]

private theorem base_smooth : SmoothOfRelativeDimension n (g ≫ f) :=
  (Nat.zero_add n) ▸ (smoothOfRelativeDimension_comp (f := g) (n := 0) (m := n) f)

/-- The whole original relative canonical module is compared through actual
produced line isomorphisms and the genuine tensor-dual Hom-section adjunction. -/
def relativeIso : (pullback v).obj (relative f π n) ≅ relative (g ≫ f) p n := by
  let := base_smooth f g n
  exact NadelPrincipalizationRelativeSectionTransport.transportIso v
    ((pullback π).obj (canonicalLineSheaf f n)) ((canonicalLineSheaf_isInvertible f n).pullback π)
    (canonicalLineSheaf (π ≫ f) n)
    ((pullback p).obj (canonicalLineSheaf (g ≫ f) n)) (canonicalLineSheaf (p ≫ (g ≫ f)) n)
    ((canonicalLineSheaf_isInvertible (g ≫ f) n).pullback p)
    (sourceLineIso f g π p v w n) (targetLineIso f g π p v w n)

/-- The SAME entire original relative-canonical differential section is
preserved by the actually produced whole relative comparison, with no
section, canonical-comparison or vanishing input. -/
theorem relativeIso_section :
    letI := base_smooth f g n
    (pullbackUnitIso v).inv ≫ (pullback v).map (differentialSection f π n) ≫
        (relativeIso f g π p v w n).hom = differentialSection (g ≫ f) p n := by
  let := base_smooth f g n
  exact NadelPrincipalizationRelativeSectionTransport.transport_section v
    ((pullback π).obj (canonicalLineSheaf f n)) ((canonicalLineSheaf_isInvertible f n).pullback π)
    (canonicalLineSheaf (π ≫ f) n)
    ((pullback p).obj (canonicalLineSheaf (g ≫ f) n)) (canonicalLineSheaf (p ≫ (g ≫ f)) n)
    ((canonicalLineSheaf_isInvertible (g ≫ f) n).pullback p)
    (sourceLineIso f g π p v w n) (targetLineIso f g π p v w n)
    (exteriorCotangentSheafPullbackMap f π n) (exteriorCotangentSheafPullbackMap (g ≫ f) p n)
    (lineIso_square f g π p v w n)

end EnvelopeProperty.Vanishing.NadelPrincipalizationRelativeSection
