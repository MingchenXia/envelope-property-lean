import EnvelopeProperty.Global.FibreIdealPowers
import EnvelopeProperty.InfinitesimalSchemes
import Mathlib.Algebra.Exact.Basic

/-!
# Whole original affine section quotients of the actual infinitesimal models

The literal original pullback projection has exactly the actual geometric
ideal-power kernel. On EVERY original affine open its entire section ring
is the original quotient, with exact genuine ideal-power section sequence
and all original affine restrictions. No affine quotient comparison is assumed.
-/

open CategoryTheory AlgebraicGeometry Opposite
noncomputable section
universe u

namespace EnvelopeProperty.FibreInfinitesimalSections

open InfinitesimalSchemes

variable {R : Type u} [CommRing R] (I : Ideal R)
    {X : Scheme.{u}} (f : X ⟶ Spec (.of R))

/-- The LITERAL original infinitesimal projection is a genuine closed immersion
for every order, including zero. -/
instance projection_isClosedImmersion (n : ℕ) : IsClosedImmersion (projection I f n) := by
  let : IsClosedImmersion (coefficientScheme I n) :=
    IsClosedImmersion.spec_of_surjective (CommRingCat.ofHom (Ideal.Quotient.mk (I^n)))
      Ideal.Quotient.mk_surjective
  exact inferInstanceAs (IsClosedImmersion (CategoryTheory.Limits.pullback.fst f _))

/-- The ENTIRE original projection kernel is the SAME genuine geometric ideal power. -/
theorem projection_ker (n : ℕ) :
    (projection I f n).ker = FibreIdealPowers.extendedPower I f n := by
  let : IsClosedImmersion (coefficientScheme I n) :=
    IsClosedImmersion.spec_of_surjective (CommRingCat.ofHom (Ideal.Quotient.mk (I^n)))
      Ideal.Quotient.mk_surjective
  rw [projection, Scheme.IdealSheafData.ker_fst_of_isClosedImmersion]
  change (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I^n)))).ker.comap f = _
  rw [Scheme.IdealSheafData.ker_Spec_map_mk (R := CommRingCat.of R) (I^n)]
  apply Scheme.IdealSheafData.ext
  funext U
  change ((specIdealSheaf (I^n)).comap f).ideal U = _
  rw [ideal_comap_specIdealSheaf, FibreIdealPowers.extendedPower_ideal, Ideal.map_pow]

/-- EVERY original affine projection section map has its full actual ideal-power kernel. -/
theorem affine_projection_ker (n : ℕ) (U : X.affineOpens) :
    RingHom.ker ((projection I f n).app U).hom = (I.map (sectionsHom f U.1))^n := by
  rw [← Scheme.Hom.ker_apply, projection_ker, FibreIdealPowers.extendedPower_ideal]

/-- The genuine original projection section map is surjective on EVERY affine open. -/
theorem affine_projection_surjective (n : ℕ) (U : X.affineOpens) :
    Function.Surjective ((projection I f n).app U) :=
  (projection I f n).app_surjective U.1 U.2

/-- The WHOLE original infinitesimal affine section ring is its actual original quotient. -/
def affineQuotientEquiv (n : ℕ) (U : X.affineOpens) :
    Γ(X, U) ⧸ (I.map (sectionsHom f U.1))^n ≃+*
      Γ(model I f n, projection I f n ⁻¹ᵁ U.1) :=
  (Ideal.quotEquivOfEq (affine_projection_ker I f n U).symm).trans
    (RingHom.quotientKerEquivOfSurjective (affine_projection_surjective I f n U))

/-- EVERY original quotient representative is its genuine original projection section. -/
theorem affineQuotientEquiv_mk (n : ℕ) (U : X.affineOpens) (s : Γ(X, U)) :
    affineQuotientEquiv I f n U (Ideal.Quotient.mk ((I.map (sectionsHom f U.1))^n) s) =
      (projection I f n).app U s := by
  simp only [affineQuotientEquiv, RingEquiv.trans_apply, Ideal.quotEquivOfEq_mk,
    RingHom.quotientKerEquivOfSurjective_apply_mk]

/-- Genuine projection vanishing is exactly membership in the SAME entire original ideal power. -/
theorem affine_projection_eq_zero_iff (n : ℕ) (U : X.affineOpens) (s : Γ(X, U)) :
    (projection I f n).app U s = 0 ↔ s ∈ (I.map (sectionsHom f U.1))^n := by
  change s ∈ RingHom.ker ((projection I f n).app U).hom ↔ _
  rw [affine_projection_ker]

/-- The inclusion of the SAME original geometric ideal-power section module. -/
def affineSectionInclusion (n : ℕ) (U : X.affineOpens) :
    Γ(FibreIdealPowers.powerModule I f n, U) →ₗ[Γ(X, U)] Γ(X, U) :=
  ((I.map (sectionsHom f U.1))^n).subtype.comp
    (FibreIdealPowers.affineSectionsEquiv I f n U).toLinearMap

/-- The genuine original ideal-power section inclusion is injective. -/
theorem affineSectionInclusion_injective (n : ℕ) (U : X.affineOpens) :
    Function.Injective (affineSectionInclusion I f n U) :=
  Subtype.val_injective.comp (FibreIdealPowers.affineSectionsEquiv I f n U).injective

/-- The SAME original ideal-power section inclusion followed by the actual
infinitesimal projection section map is an exact pair on EVERY affine open. -/
theorem affineSection_exact (n : ℕ) (U : X.affineOpens) :
    Function.Exact (affineSectionInclusion I f n U) ((projection I f n).app U) := by
  intro s
  rw [affine_projection_eq_zero_iff]
  constructor
  · intro hs
    refine ⟨(FibreIdealPowers.affineSectionsEquiv I f n U).symm ⟨s, hs⟩, ?_⟩
    exact congrArg Subtype.val ((FibreIdealPowers.affineSectionsEquiv I f n U).apply_symm_apply ⟨s, hs⟩)
  · rintro ⟨a, rfl⟩
    exact (FibreIdealPowers.affineSectionsEquiv I f n U a).2

/-- Literal original affine restriction on the ENTIRE actual ideal-power quotients. -/
def affineRestriction (n : ℕ) {U V : X.affineOpens} (h : U ≤ V) :
    Γ(X, V) ⧸ (I.map (sectionsHom f V.1))^n →+*
      Γ(X, U) ⧸ (I.map (sectionsHom f U.1))^n :=
  Ideal.quotientMap _ (X.presheaf.map (homOfLE h).op).hom (by
    rw [← FibreIdealPowers.extendedPower_ideal I f n U,
      ← FibreIdealPowers.extendedPower_ideal I f n V]
    exact (FibreIdealPowers.extendedPower I f n).ideal_le_comap_ideal h)

/-- EVERY quotient representative restricts by the entire original function restriction. -/
theorem affineRestriction_mk (n : ℕ) {U V : X.affineOpens} (h : U ≤ V) (s : Γ(X, V)) :
    affineRestriction I f n h (Ideal.Quotient.mk ((I.map (sectionsHom f V.1))^n) s) =
      Ideal.Quotient.mk ((I.map (sectionsHom f U.1))^n)
        (X.presheaf.map (homOfLE h).op s) := rfl

/-- EVERY actual original inverse-image affine restriction is exactly the
whole quotient restriction under the SAME genuine affine section equivalences. -/
theorem affineQuotientEquiv_restriction (n : ℕ) {U V : X.affineOpens} (h : U ≤ V)
    (s : Γ(X, V) ⧸ (I.map (sectionsHom f V.1))^n) :
    (model I f n).presheaf.map
        (((TopologicalSpace.Opens.map (projection I f n).base).map (homOfLE h)).op)
        (affineQuotientEquiv I f n V s) =
      affineQuotientEquiv I f n U (affineRestriction I f n h s) := by
  induction s using Quotient.inductionOn' with
  | _ s =>
    change (model I f n).presheaf.map _
      (affineQuotientEquiv I f n V (Ideal.Quotient.mk _ s)) =
        affineQuotientEquiv I f n U (affineRestriction I f n h (Ideal.Quotient.mk _ s))
    rw [affineQuotientEquiv_mk, affineRestriction_mk, affineQuotientEquiv_mk]
    exact (congrArg (fun q : Γ(X, V) ⟶ Γ(model I f n, projection I f n ⁻¹ᵁ U.1) => q.hom s)
      ((projection I f n).naturality (homOfLE h).op)).symm

/-- The actual original transition has exactly the SAME original inverse-image open. -/
theorem transition_preimage {n m : ℕ} (h : n ≤ m) (U : X.Opens) :
    transition I f h ⁻¹ᵁ (projection I f m ⁻¹ᵁ U) = projection I f n ⁻¹ᵁ U := by
  rw [← Scheme.Hom.comp_preimage, transition_projection]

/-- The genuine original whole section transition on the SAME inverse-image affine open. -/
def affineTransition {n m : ℕ} (h : n ≤ m) (U : X.affineOpens) :
    Γ(model I f m, projection I f m ⁻¹ᵁ U.1) →+*
      Γ(model I f n, projection I f n ⁻¹ᵁ U.1) :=
  ((transition I f h).appLE (projection I f m ⁻¹ᵁ U.1)
    (projection I f n ⁻¹ᵁ U.1) (transition_preimage I f h U.1).symm.le).hom

/-- The actual whole section transition preserves EVERY original projection section. -/
theorem affineTransition_projection {n m : ℕ} (h : n ≤ m) (U : X.affineOpens) :
    (affineTransition I f h U).comp ((projection I f m).app U).hom =
      ((projection I f n).app U).hom := by
  have hcomp := Scheme.Hom.comp_appLE (transition I f h) (projection I f m)
    U.1 (projection I f n ⁻¹ᵁ U.1) (transition_preimage I f h U.1).symm.le
  simp only [transition_projection, ← Scheme.Hom.app_eq_appLE] at hcomp
  exact congrArg CommRingCat.Hom.hom hcomp.symm

/-- EVERY whole original infinitesimal section transition is the actual
ideal-power quotient factor under the SAME original affine quotient equivalences. -/
theorem affineQuotientEquiv_transition {n m : ℕ} (h : n ≤ m) (U : X.affineOpens)
    (s : Γ(X, U) ⧸ (I.map (sectionsHom f U.1))^m) :
    affineTransition I f h U (affineQuotientEquiv I f m U s) =
      affineQuotientEquiv I f n U
        (Ideal.Quotient.factorPow (I.map (sectionsHom f U.1)) h s) := by
  induction s using Quotient.inductionOn' with
  | _ s =>
    change affineTransition I f h U
      (affineQuotientEquiv I f m U (Ideal.Quotient.mk _ s)) =
        affineQuotientEquiv I f n U (Ideal.Quotient.mk _ s)
    rw [affineQuotientEquiv_mk, affineQuotientEquiv_mk]
    exact RingHom.congr_fun (affineTransition_projection I f h U) s

end EnvelopeProperty.FibreInfinitesimalSections
