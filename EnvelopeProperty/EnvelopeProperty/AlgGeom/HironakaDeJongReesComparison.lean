import Hironaka.Scheme.BlowUp.AffineBlowUp.Defs
import DeJongAlterations.Geometry.AffineBlowupFunctor
import ModularCurves.ForMathlib.ProjMapClosedImmersion
import ModularCurves.ForMathlib.ProjToSpecZero

/-! # Identity comparisons of the two actual native Rees projective schemes -/

open CategoryTheory AlgebraicGeometry
noncomputable section
universe u
namespace EnvelopeProperty.HironakaDeJongReesComparison

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {R : Type u} [CommRing R] (I : Ideal R)

/-- The two original gradings agree on the SAME entire original polynomial
Rees subalgebra, including zero ideals and nilpotent coefficients. -/
theorem grading_eq (n : ℕ) : reesAlgebra.grading I n = DeJongAlterations.reesGrading I n := by
  apply Submodule.ext
  intro p
  constructor
  · intro hp
    exact (DeJongAlterations.mem_reesGrading_iff I n p).mpr
      (reesAlgebra.eq_monomial_of_mem_grading hp).1
  · intro hp
    exact reesAlgebra.mem_grading_of_coe_eq_monomial
      ((DeJongAlterations.mem_reesGrading_iff I n p).mp hp)

/-- The literal identity on the original Rees subalgebra is graded in the
original higher-level construction directions. -/
def toDeJong : reesAlgebra.grading I →+*ᵍ DeJongAlterations.reesGrading I where
  toRingHom := RingHom.id _
  map_mem {n _p} hp := (grading_eq I n) ▸ hp

/-- The literal identity in the reverse original grading direction. -/
def toHironaka : DeJongAlterations.reesGrading I →+*ᵍ reesAlgebra.grading I where
  toRingHom := RingHom.id _
  map_mem {n _p} hp := (grading_eq I n).symm ▸ hp

private theorem toDeJong_irrelevant :
    HomogeneousIdeal.irrelevant (DeJongAlterations.reesGrading I) ≤
      (HomogeneousIdeal.irrelevant (reesAlgebra.grading I)).map (toDeJong I) :=
  HomogeneousIdeal.irrelevant_le_map_of_surjective (toDeJong I) (fun p => ⟨p, rfl⟩)

private theorem toHironaka_irrelevant :
    HomogeneousIdeal.irrelevant (reesAlgebra.grading I) ≤
      (HomogeneousIdeal.irrelevant (DeJongAlterations.reesGrading I)).map (toHironaka I) :=
  HomogeneousIdeal.irrelevant_le_map_of_surjective (toHironaka I) (fun p => ⟨p, rfl⟩)

private theorem projMap_identity {A σ : Type u} [CommRing A]
    [SetLike σ A] [AddSubgroupClass σ A] {𝒜 : ℕ → σ} [GradedRing 𝒜]
    (f : 𝒜 →+*ᵍ 𝒜) (hf : f = GradedRingHom.id 𝒜)
    (h : HomogeneousIdeal.irrelevant 𝒜 ≤ (HomogeneousIdeal.irrelevant 𝒜).map f) :
    Proj.map f h = 𝟙 (Proj 𝒜) := by
  subst f
  exact Proj.map_id

/-- The whole original affine Rees projective schemes are actually isomorphic,
using the identity on their SAME original Rees algebra in both directions. -/
def affineIso : DeJongAlterations.affineBlowup I ≅ affineBlowUp I where
  hom := Proj.map (toDeJong I) (toDeJong_irrelevant I)
  inv := Proj.map (toHironaka I) (toHironaka_irrelevant I)
  hom_inv_id := by
    rw [← Proj.map_comp]
    exact projMap_identity _ (GradedRingHom.ext fun _ => rfl) _
  inv_hom_id := by
    rw [← Proj.map_comp]
    exact projMap_identity _ (GradedRingHom.ext fun _ => rfl) _

private theorem degreeZero_coefficients (r : R) :
    ModularCurves.gradedRingHomZero (toDeJong I)
        ((reesAlgebra.gradingZeroEquiv I).symm r) =
      DeJongAlterations.reesDegreeZeroEquiv I r := by
  apply Subtype.ext
  apply Subtype.ext
  exact reesAlgebra.coe_gradingZeroEquiv_symm I r

/-- The entire affine comparison retains the LITERAL original coefficient
projection, as equality of native scheme morphisms over the SAME original spectrum. -/
theorem affineIso_structure :
    (affineIso I).hom ≫ affineBlowUp.π I = DeJongAlterations.affineBlowupStructure I := by
  change Proj.map (toDeJong I) (toDeJong_irrelevant I) ≫
      (Proj.toSpecZero (reesAlgebra.grading I) ≫
        Spec.map (reesAlgebra.gradingZeroEquiv I).symm.toCommRingCatIso.hom) = _
  rw [← Category.assoc, ModularCurves.map_comp_toSpecZero, Category.assoc,
    ← Spec.map_comp]
  unfold DeJongAlterations.affineBlowupStructure
  congr 1

variable {S : Type u} [CommRing S] (J : Ideal S) (φ : R →+* S) (h : I.map φ = J)

/-- EVERY actual coefficient extension commutes with the original identity
comparison on the ENTIRE original polynomial Rees algebra. -/
theorem graded_naturality :
    (DeJongAlterations.reesGradedMapTo I J φ h).comp (toDeJong I) =
      (toDeJong J).comp (reesAlgebra.mapOfLe φ h.le) := by
  apply GradedRingHom.ext
  intro p
  apply Subtype.ext
  exact DeJongAlterations.reesGradedMapTo_apply I J φ h p

private theorem projMap_congr {A B σ τ : Type u} [CommRing A] [CommRing B]
    [SetLike σ A] [AddSubgroupClass σ A] [SetLike τ B] [AddSubgroupClass τ B]
    {𝒜 : ℕ → σ} {ℬ : ℕ → τ} [GradedRing 𝒜] [GradedRing ℬ]
    (f g : 𝒜 →+*ᵍ ℬ) (hfg : f = g)
    (hf : HomogeneousIdeal.irrelevant ℬ ≤ (HomogeneousIdeal.irrelevant 𝒜).map f)
    (hg : HomogeneousIdeal.irrelevant ℬ ≤ (HomogeneousIdeal.irrelevant 𝒜).map g) :
    Proj.map f hf = Proj.map g hg := by
  subst g
  rfl

/-- The WHOLE native affine blowup comparisons commute with EVERY original
coefficient restriction and the LITERAL original ideal-extension scheme morphisms. -/
theorem affineIso_naturality :
    DeJongAlterations.affineBlowupMapTo I J φ h ≫ (affineIso I).hom =
      (affineIso J).hom ≫ affineBlowUp.mapOfEq φ h := by
  change Proj.map (DeJongAlterations.reesGradedMapTo I J φ h) _ ≫
      Proj.map (toDeJong I) _ = Proj.map (toDeJong J) _ ≫
        Proj.map (reesAlgebra.mapOfLe φ h.le) _
  rw [← Proj.map_comp, ← Proj.map_comp]
  exact projMap_congr _ _ (graded_naturality I J φ h) _ _

end EnvelopeProperty.HironakaDeJongReesComparison
