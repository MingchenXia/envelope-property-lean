import EnvelopeProperty.DeligneIllusie.WittTwoOriginalFormPresheaf
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-! # A genuine original lifted affine basis of the ACTUAL special fibre -/
noncomputable section
namespace EnvelopeProperty.DeligneIllusie.WittTwoSpecialFibreBasis
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
universe u
variable (p : ℕ) [Fact p.Prime] (k : Type u) [Field k]
variable {Y : Scheme.{u}} (f : Y ⟶ Spec (CommRingCat.of (WittTwo.Ring p k)))
private abbrev X := WittTwoSpecialFibreOpens.specialFibre p k f
private abbrev j : X p k f ⟶ Y :=
  pullback.snd (Spec.map (CommRingCat.ofHom (WittTwo.reduction p k))) f

/-- The ACTUAL global special-fibre projection is genuinely a closed immersion. -/
theorem projection_isClosedImmersion : IsClosedImmersion (j p k f) := by
  let : IsClosedImmersion (Spec.map (CommRingCat.ofHom (WittTwo.reduction p k))) :=
    IsClosedImmersion.spec_of_surjective _ (WittTwo.reduction_surjective p k)
  infer_instance

/-- The indexed family consists of SAME original inverse-image opens of original affine opens. -/
def affineOpens (U : {U : Y.Opens // IsAffineOpen U}) : (X p k f).Opens :=
  WittTwoSpecialFibreOpens.residueOpen p k f U.val

/-- EVERY member of the actual original lifted basis is genuinely affine. -/
theorem affineOpens_affine (U : {U : Y.Opens // IsAffineOpen U}) :
    IsAffineOpen (affineOpens p k f U) :=
  WittTwoSpecialFibreOpens.residueOpen_affine p k f U.property

/-- GENUINE whole special-fibre topology has this actual original lifted affine basis. -/
theorem isBasis_affineOpens : Opens.IsBasis (Set.range (affineOpens p k f)) := by
  let := projection_isClosedImmersion p k f
  have h := Y.isBasis_affineOpens.of_isInducing (j p k f).isClosedEmbedding.toIsInducing
  convert h using 1
  ext W
  constructor
  · rintro ⟨U,rfl⟩
    exact ⟨U.val,U.property,rfl⟩
  · rintro ⟨U,hU,rfl⟩
    exact ⟨⟨U,hU⟩,rfl⟩

/-- EVERY actual original special-fibre neighborhood has an original lifted affine refinement. -/
theorem exists_affine_refinement {W : (X p k f).Opens} (x : X p k f) (hx : x ∈ W) :
    ∃ U : Y.Opens, IsAffineOpen U ∧ x ∈ WittTwoSpecialFibreOpens.residueOpen p k f U ∧
      WittTwoSpecialFibreOpens.residueOpen p k f U ≤ W := by
  obtain ⟨V,⟨U,rfl⟩,hxV,hVW⟩ :=
    Opens.isBasis_iff_nbhd.mp (isBasis_affineOpens p k f) hx
  exact ⟨U.val,U.property,hxV,hVW⟩

/-- Genuine lifted affine refinements can ALSO lie below ANY specified original lifted neighborhood. -/
theorem exists_affine_refinement_below {V : Y.Opens} {W : (X p k f).Opens}
    (x : X p k f) (hxV : x ∈ WittTwoSpecialFibreOpens.residueOpen p k f V) (hxW : x ∈ W) :
    ∃ U : Y.Opens, IsAffineOpen U ∧ U ≤ V ∧
      x ∈ WittTwoSpecialFibreOpens.residueOpen p k f U ∧
        WittTwoSpecialFibreOpens.residueOpen p k f U ≤ W := by
  obtain ⟨U,hU,hxU,hUW⟩ := exists_affine_refinement p k f x hxW
  have hx : j p k f x ∈ V ⊓ U := ⟨hxV,hxU⟩
  obtain ⟨T,hT,hxT,hTU⟩ := Opens.isBasis_iff_nbhd.mp Y.isBasis_affineOpens hx
  exact ⟨T,hT,fun _ hz => (hTU hz).1,hxT,fun _ hz => hUW (hTU hz).2⟩

end EnvelopeProperty.DeligneIllusie.WittTwoSpecialFibreBasis
