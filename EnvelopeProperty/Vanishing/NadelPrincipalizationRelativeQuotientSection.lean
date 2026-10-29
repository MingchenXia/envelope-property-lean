import EnvelopeProperty.Vanishing.NadelPrincipalizationRelativeRoundedSection
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels

/-! # The whole original rounded quotient and its same native differential section -/
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Scheme.Modules
noncomputable section
universe u
namespace EnvelopeProperty.Vanishing.NadelPrincipalizationRelativeQuotientSection
open CanonicalGeometry Char0 Char0.RoundedCanonicalModule
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private def quotientIsoAux {Y Z : Scheme.{u}} (j : Y ⟶ Z)
    (A B : Z.Modules) (i : A ⟶ B) (A' B' : Y.Modules) (i' : A' ⟶ B')
    (a : (Scheme.Modules.pullback j).obj A ≅ A') (b : (Scheme.Modules.pullback j).obj B ≅ B')
    (h : (Scheme.Modules.pullback j).map i ≫ b.hom = a.hom ≫ i') :
    (Scheme.Modules.pullback j).obj (cokernel i) ≅ cokernel i' :=
  PreservesCokernel.iso (Scheme.Modules.pullback j) i ≪≫ cokernel.mapIso ((Scheme.Modules.pullback j).map i) i' a b h

private theorem quotientIsoAux_projection {Y Z : Scheme.{u}} (j : Y ⟶ Z)
    (A B : Z.Modules) (i : A ⟶ B) (A' B' : Y.Modules) (i' : A' ⟶ B')
    (a : (Scheme.Modules.pullback j).obj A ≅ A') (b : (Scheme.Modules.pullback j).obj B ≅ B')
    (h : (Scheme.Modules.pullback j).map i ≫ b.hom = a.hom ≫ i') :
    (Scheme.Modules.pullback j).map (cokernel.π i) ≫ (quotientIsoAux j A B i A' B' i' a b h).hom =
      b.hom ≫ cokernel.π i' := by
  change (Scheme.Modules.pullback j).map (cokernel.π i) ≫ (PreservesCokernel.iso (Scheme.Modules.pullback j) i).hom ≫
    (cokernel.mapIso ((Scheme.Modules.pullback j).map i) i' a b h).hom = _
  rw [← Category.assoc, PreservesCokernel.π_iso_hom, cokernel.mapIso_hom, cokernel.π_desc]

variable {k : Type u} [Field k] [CharZero k] {X₀ X B₀ B : Scheme.{u}}
    (f : X₀ ⟶ Spec (.of k)) (g : X ⟶ X₀) (π : B₀ ⟶ X₀)
    (p : B ⟶ X) (v : B ⟶ B₀) (w : p ≫ g = v ≫ π) (n : ℕ)
    [IsOpenImmersion g] [IsOpenImmersion v] [SmoothOfRelativeDimension n f]
    [Smooth (π ≫ f)] (J : B₀.IdealSheafData) (hJ : J.IsIdealOfSncDivisor) (q : ℚ)

/-- The entire SAME original rounded relative-canonical cokernel under
actual open pullback, built from proved whole inclusion comparisons. -/
def quotientIso :
    (Scheme.Modules.pullback v).obj (quotient f π n J hJ q) ≅
      quotient (g ≫ f) p n (J.comap v) (hJ.comap_of_smooth (π ≫ f) v) q :=
  quotientIsoAux v (relativeRounded f π n J hJ q) (relative f π n)
    (relativeRoundedInclusion f π n J hJ q)
    (relativeRounded (g ≫ f) p n (J.comap v) (hJ.comap_of_smooth (π ≫ f) v) q)
    (relative (g ≫ f) p n)
    (relativeRoundedInclusion (g ≫ f) p n (J.comap v) (hJ.comap_of_smooth (π ≫ f) v) q)
    (NadelPrincipalizationRelativeRoundedSection.roundedIso f g π p v w n J hJ q)
    (NadelPrincipalizationRelativeSection.relativeIso f g π p v w n)
    (NadelPrincipalizationRelativeRoundedSection.roundedIso_inclusion f g π p v w n J hJ q).symm

/-- The whole actual quotient projection retains the SAME original
relative and quotient comparisons, with no projection-comparison input. -/
theorem quotientIso_projection :
    (Scheme.Modules.pullback v).map (quotientProjection f π n J hJ q) ≫ (quotientIso f g π p v w n J hJ q).hom =
      (NadelPrincipalizationRelativeSection.relativeIso f g π p v w n).hom ≫
        quotientProjection (g ≫ f) p n (J.comap v) (hJ.comap_of_smooth (π ≫ f) v) q :=
  quotientIsoAux_projection v (relativeRounded f π n J hJ q) (relative f π n)
    (relativeRoundedInclusion f π n J hJ q)
    (relativeRounded (g ≫ f) p n (J.comap v) (hJ.comap_of_smooth (π ≫ f) v) q)
    (relative (g ≫ f) p n)
    (relativeRoundedInclusion (g ≫ f) p n (J.comap v) (hJ.comap_of_smooth (π ≫ f) v) q)
    (NadelPrincipalizationRelativeRoundedSection.roundedIso f g π p v w n J hJ q)
    (NadelPrincipalizationRelativeSection.relativeIso f g π p v w n)
    (NadelPrincipalizationRelativeRoundedSection.roundedIso_inclusion f g π p v w n J hJ q).symm

omit [CharZero k] in
private theorem base_smooth : SmoothOfRelativeDimension n (g ≫ f) :=
  (Nat.zero_add n) ▸ (smoothOfRelativeDimension_comp (f := g) (n := 0) (m := n) f)

/-- The SAME entire original native quotient differential section is
preserved by the actual whole quotient isomorphism; no section or
vanishing assertion is supplied as an input. -/
theorem quotientIso_section :
    letI := base_smooth f g n
    (pullbackUnitIso v).inv ≫ (Scheme.Modules.pullback v).map (quotientDifferentialSection f π n J hJ q) ≫
        (quotientIso f g π p v w n J hJ q).hom =
      quotientDifferentialSection (g ≫ f) p n (J.comap v) (hJ.comap_of_smooth (π ≫ f) v) q := by
  let := base_smooth f g n
  simp only [quotientDifferentialSection, Functor.map_comp, Category.assoc]
  rw [quotientIso_projection]
  simpa only [Category.assoc] using congrArg
    (fun α => α ≫ quotientProjection (g ≫ f) p n (J.comap v)
      (hJ.comap_of_smooth (π ≫ f) v) q)
    (NadelPrincipalizationRelativeSection.relativeIso_section f g π p v w n)

end EnvelopeProperty.Vanishing.NadelPrincipalizationRelativeQuotientSection
