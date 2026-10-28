import EnvelopeProperty.DeligneIllusie.WittTwoEtaleRestrictionCoherence
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Morphisms.Etale

/-! # Genuine section rings and lift restrictions on the SAME actual smooth Witt scheme -/
noncomputable section
namespace EnvelopeProperty.DeligneIllusie.WittTwoSchemeAffineRestrictions
open AlgebraicGeometry CategoryTheory Opposite
universe u

/-- The actual structural section algebra, through the original spectrum section equivalence. -/
@[instance_reducible] def sectionAlgebra {R : Type u} [CommRing R] {Y : Scheme.{u}}
    (f : Y ⟶ Spec (CommRingCat.of R)) (U : Y.Opens) : Algebra R Γ(Y,U) :=
  ((Scheme.ΓSpecIso (.of R)).inv ≫ f.appLE ⊤ U le_top).hom.toAlgebra

/-- The SAME actual structure-sheaf restriction as an original structural algebra homomorphism. -/
def restrictionAlgebraHom {R : Type u} [CommRing R] {Y : Scheme.{u}}
    (f : Y ⟶ Spec (CommRingCat.of R)) {U V : Y.Opens} (i : U ⟶ V) :
    letI := sectionAlgebra f V
    letI := sectionAlgebra f U
    Γ(Y,V) →ₐ[R] Γ(Y,U) := by
  let := sectionAlgebra f V
  let := sectionAlgebra f U
  refine { (Y.presheaf.map i.op).hom with commutes' := ?_ }
  intro r
  change (Y.presheaf.map i.op).hom
    (((Scheme.ΓSpecIso (.of R)).inv ≫ f.appLE ⊤ V le_top).hom r) =
    ((Scheme.ΓSpecIso (.of R)).inv ≫ f.appLE ⊤ U le_top).hom r
  have hmap := Scheme.Hom.appLE_map f (U := ⊤) (V := V) (V' := U) le_top i.op
  have he := congrArg (fun z => (Scheme.ΓSpecIso (.of R)).inv ≫ z) hmap
  exact ConcreteCategory.congr_hom he r

/-- Actual smooth scheme geometry proves smoothness of the SAME entire affine section algebra. -/
theorem affine_smooth {R : Type u} [CommRing R] {Y : Scheme.{u}}
    (f : Y ⟶ Spec (CommRingCat.of R)) [Smooth f] {U : Y.Opens} (hU : IsAffineOpen U) :
    letI := sectionAlgebra f U
    Algebra.Smooth R Γ(Y,U) := by
  let := sectionAlgebra f U
  rw [← RingHom.smooth_algebraMap]
  exact (RingHom.Smooth.of_bijective
    (Scheme.ΓSpecIso (.of R)).symm.commRingCatIsoToRingEquiv.bijective).comp
      (f.smooth_appLE (isAffineOpen_top _) hU le_top)

/-- The SAME actual restriction between ANY two original affine opens is genuinely etale. -/
theorem restriction_etale {Y : Scheme.{u}} {U V : Y.Opens}
    (hU : IsAffineOpen U) (hV : IsAffineOpen V) (i : U ⟶ V) :
    (Y.presheaf.map i.op).hom.Etale := by
  have h := Scheme.Hom.etale_appLE (𝟙 Y) hV hU (show U ≤ (𝟙 Y) ⁻¹ᵁ V from i.le)
  have he : ((𝟙 Y : Y ⟶ Y).appLE V U (show U ≤ (𝟙 Y) ⁻¹ᵁ V from i.le)).hom =
      (Y.presheaf.map i.op).hom := by
    apply RingHom.ext
    intro a
    rfl
  exact he ▸ h

variable (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [CharP k p] [PerfectRing k p]
attribute [local instance] WittTwoResidue.reductionAlgebra
  WittTwoRelativeLift.twistBaseAlgebra WittTwoRelativeLift.twistBaseModule
  WittTwoSourceResidue.twistSMul WittTwoRelativeLift.residueCopyAlgebra
  WittTwoLiftDifference.frobeniusAlgebra
  WittTwoOriginalCotangentMaps.originalResidueRing WittTwoOriginalCotangentMaps.residueAlgebra
variable {Y : Scheme.{u}} (f : Y ⟶ Spec (CommRingCat.of (WittTwo.Ring p k))) [Smooth f]

/-- A genuine whole relative Frobenius lift is produced on EVERY actual affine open section ring. -/
theorem exists_affineLift {V : Y.Opens} (hV : IsAffineOpen V) :
    letI := sectionAlgebra f V
    ∃ F : WittTwoLiftDifference.Lift p k Γ(Y,V), ∀ t,
      algebraMap Γ(Y,V) (WittTwoSmoothDifferentials.ResidueAlgebra p k Γ(Y,V)) (F t) =
        WittTwoRelativeLift.residueFrobenius p k Γ(Y,V) t := by
  let := sectionAlgebra f V
  let := affine_smooth f hV
  refine ⟨WittTwoRelativeLift.relativeLift p k Γ(Y,V), ?_⟩
  intro t
  exact AlgHom.congr_fun (WittTwoRelativeLift.relativeLift_reduction p k Γ(Y,V)) t

/-- The target lift and BOTH whole original equations are produced for actual affine restrictions. -/
theorem exists_restrictedLift {U V : Y.Opens} (hU : IsAffineOpen U) (hV : IsAffineOpen V)
    (i : U ⟶ V) :
    letI := sectionAlgebra f V
    letI := sectionAlgebra f U
    ∀ (F : WittTwoLiftDifference.Lift p k Γ(Y,V))
      (_hF : ∀ t, algebraMap Γ(Y,V) (WittTwoSmoothDifferentials.ResidueAlgebra p k Γ(Y,V)) (F t) =
        WittTwoRelativeLift.residueFrobenius p k Γ(Y,V) t),
    ∃ G : WittTwoLiftDifference.Lift p k Γ(Y,U),
      (∀ t, algebraMap Γ(Y,U) (WittTwoSmoothDifferentials.ResidueAlgebra p k Γ(Y,U)) (G t) =
        WittTwoRelativeLift.residueFrobenius p k Γ(Y,U) t) ∧
      (∀ t, (Y.presheaf.map i.op) (F t) =
        G (WittTwoLiftDifferenceNaturality.twistMap p k (restrictionAlgebraHom f i) t)) := by
  let := sectionAlgebra f V
  let := sectionAlgebra f U
  let := affine_smooth f hU
  intro F hF
  have he : (restrictionAlgebraHom f i).toRingHom.Etale := by
    change (Y.presheaf.map i.op).hom.Etale
    exact restriction_etale hU hV i
  exact WittTwoEtaleLiftRestriction.exists_restrictedLift p k (restrictionAlgebraHom f i) F hF he

end EnvelopeProperty.DeligneIllusie.WittTwoSchemeAffineRestrictions
