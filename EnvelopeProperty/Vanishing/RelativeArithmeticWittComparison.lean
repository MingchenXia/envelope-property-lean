import EnvelopeProperty.Vanishing.RelativeArithmeticScalarTransition
import EnvelopeProperty.Vanishing.RelativeWittKodairaComparison

/-! # Actual arithmetic closed fibres satisfy relative ample Kodaira

An elementary coefficient lift constructs the actual Witt family and its
whole field-compatible special-fibre isomorphism.  The projective affine
base remains a separate tensor algebra; no properness over the field occurs.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped TensorProduct
universe u

namespace EnvelopeProperty.Vanishing.RelativeArithmeticWittComparison
open Cartier CanonicalGeometry
attribute [local instance] Scheme.Modules.monoidalCategory

variable {A κ : Type u} [CommRing A] [Field κ]
    (ell : ℕ) [Fact ell.Prime] [CharP κ ell] [PerfectRing κ ell]
    {Y : Scheme.{u}} (f : Y ⟶ Spec (.of A))
    (ρ : A →+* κ) (lifted : A →+* DeligneIllusie.WittTwo.Ring ell κ)
    (hred : (DeligneIllusie.WittTwo.reduction ell κ).comp lifted = ρ)

abbrev wittProjection :=
  pullback.snd f (Spec.map (CommRingCat.ofHom lifted))

abbrev residueProjection :=
  pullback.snd f (Spec.map (CommRingCat.ofHom ρ))

include hred

omit [CharP κ ell] [PerfectRing κ ell] in
private theorem spec_reduction :
    Spec.map (CommRingCat.ofHom (DeligneIllusie.WittTwo.reduction ell κ)) ≫
      Spec.map (CommRingCat.ofHom lifted) = Spec.map (CommRingCat.ofHom ρ) := by
  rw [← Spec.map_comp]
  exact congrArg (fun φ : A →+* κ => Spec.map (CommRingCat.ofHom φ)) hred

private def reductionMap :
    pullback f (Spec.map (CommRingCat.ofHom ρ)) ⟶
      pullback f (Spec.map (CommRingCat.ofHom lifted)) :=
  pullback.lift (pullback.fst _ _)
    (pullback.snd _ _ ≫
      Spec.map (CommRingCat.ofHom (DeligneIllusie.WittTwo.reduction ell κ)))
    (by rw [Category.assoc, spec_reduction ell ρ lifted hred]; exact pullback.condition)

omit [CharP κ ell] [PerfectRing κ ell] in
private theorem reduction_isPullback :
    IsPullback (reductionMap ell f ρ lifted hred) (residueProjection f ρ)
      (wittProjection ell f lifted)
      (Spec.map (CommRingCat.ofHom (DeligneIllusie.WittTwo.reduction ell κ))) := by
  have ho : IsPullback (reductionMap ell f ρ lifted hred ≫ pullback.fst _ _)
      (residueProjection f ρ) f
      (Spec.map (CommRingCat.ofHom (DeligneIllusie.WittTwo.reduction ell κ)) ≫
        Spec.map (CommRingCat.ofHom lifted)) := by
    rw [reductionMap, pullback.lift_fst, spec_reduction ell ρ lifted hred]
    exact IsPullback.of_hasPullback _ _
  exact ho.of_right (pullback.lift_snd _ _ _) (IsPullback.of_hasPullback _ _)

/-- The actual original residue fibre is the actual Witt special fibre,
with factor order corrected by the canonical cartesian symmetry. -/
def specialFibreIso :
    pullback f (Spec.map (CommRingCat.ofHom ρ)) ≅
      DeligneIllusieInput.specialFibre ell κ (wittProjection ell f lifted) :=
  (reduction_isPullback ell f ρ lifted hred).isoPullback ≪≫ pullbackSymmetry _ _

omit [CharP κ ell] [PerfectRing κ ell] in
/-- The whole comparison retains exactly the original residue-field structure. -/
theorem specialFibreIso_hom_structure :
    (specialFibreIso ell f ρ lifted hred).hom ≫
      DeligneIllusieInput.specialFibreStructure ell κ (wittProjection ell f lifted) =
        residueProjection f ρ := by
  simp only [specialFibreIso, Iso.trans_hom, Category.assoc,
    pullbackSymmetry_hom_comp_fst, IsPullback.isoPullback_hom_snd]

/-- An actual coefficient lift gives Kodaira on the original residue fibre
for every original relative ample line over the distinct modeled affine base. -/
theorem kodaira_on_residue_fibre
    {B : Type u} [CommRing B] [Algebra A B] [Algebra.FiniteType A B]
    (g : Y ⟶ Spec (.of B))
    (hg : g ≫ Spec.map (CommRingCat.ofHom (algebraMap A B)) = f)
    (n : ℕ) [SmoothOfRelativeDimension n f] [IsSeparated f] (hn : n < ell)
    (M : Y.Modules) (hM : SchemeLineAmpleness.IsAmple g M) (q : ℕ) :
    Subsingleton (CategoryTheory.Sheaf.H
      (canonicalLineSheaf (residueProjection f ρ) n ⊗
        (Scheme.Modules.pullback (pullback.fst f (Spec.map (CommRingCat.ofHom ρ)))).obj M).sheaf
      (q + 1)) := by
  let : Algebra A κ := ρ.toAlgebra
  let D := κ ⊗[A] B
  let : Algebra.FiniteType κ D := Algebra.FiniteType.baseChange (R := A) (A := B) κ
  let : IsNoetherianRing D := Algebra.FiniteType.isNoetherianRing κ D
  let gκ := RelativeArithmeticScalarTransition.relativeMap (S := κ) f g hg
  let Mκ := (Scheme.Modules.pullback
    (pullback.fst f (Spec.map (CommRingCat.ofHom ρ)))).obj M
  have hMκ : SchemeLineAmpleness.IsAmple gκ Mκ :=
    RelativeArithmeticScalarTransition.isAmple (S := κ) f g hg M hM
  let : SmoothOfRelativeDimension n (wittProjection ell f lifted) :=
    @MorphismProperty.IsStableUnderBaseChange.of_isPullback
      Scheme.{u} inferInstance (@SmoothOfRelativeDimension.{u} n)
      (smoothOfRelativeDimension_isStableUnderBaseChange n)
      _ _ _ _ _ _ _ _
      (IsPullback.of_hasPullback f (Spec.map (CommRingCat.ofHom lifted))) inferInstance
  let : IsSeparated (wittProjection ell f lifted) := inferInstance
  exact RelativeWittKodairaComparison.kodaira_of_specialFibreIso ell
    (wittProjection ell f lifted) n hn (residueProjection f ρ) gκ
    (specialFibreIso ell f ρ lifted hred)
    (specialFibreIso_hom_structure ell f ρ lifted hred) Mκ hMκ q

end EnvelopeProperty.Vanishing.RelativeArithmeticWittComparison
