import EnvelopeProperty.AlgGeom.FiniteClosedIdealLocalDegrees
import Mathlib.AlgebraicGeometry.ResidueField

/-! # Actual affine-scheme points, stalks and residue-weighted local degrees -/
open AlgebraicGeometry CategoryTheory TopologicalSpace
noncomputable section
universe u
namespace EnvelopeProperty.AffineSchemeLocalDegrees
open SchemeCoherentEulerIndex FiniteClosedIdealLocalDegrees
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {k : Type u} [Field k] {D : Scheme.{u}}

/-- The literal original coefficient action on the actual original stalk. -/
@[instance_reducible] def stalkAlgebra (f : D ⟶ Spec (.of k)) (x : D) :
    Algebra k (D.presheaf.stalk x) :=
  ((D.presheaf.germ ⊤ x trivial).hom.comp (f.appTop.hom.comp (baseScalar (k := k)))).toAlgebra

/-- The original affine point's actual stalk is the localization of the
SAME entire original section algebra at its actual corresponding prime. -/
def stalkLocalizationAlgEquiv [IsAffine D] (f : D ⟶ Spec (.of k)) (x : D) :
    letI := structureSectionsAlgebra f
    letI := stalkAlgebra f x
    D.presheaf.stalk x ≃ₐ[k]
      Localization.AtPrime ((isAffineOpen_top D).primeIdealOf ⟨x, trivial⟩).asIdeal := by
  letI := structureSectionsAlgebra f
  letI := stalkAlgebra f x
  letI := D.presheaf.algebra_section_stalk (⟨x, trivial⟩ : (⊤ : D.Opens))
  letI : IsScalarTower k Γ(D, ⊤) (D.presheaf.stalk x) :=
    IsScalarTower.of_algebraMap_eq (fun r => rfl)
  letI := (isAffineOpen_top D).isLocalization_stalk ⟨x, trivial⟩
  exact (IsLocalization.algEquiv
    ((isAffineOpen_top D).primeIdealOf ⟨x, trivial⟩).asIdeal.primeCompl
    (D.presheaf.stalk x)
    (Localization.AtPrime ((isAffineOpen_top D).primeIdealOf ⟨x, trivial⟩).asIdeal)).restrictScalars k

/-- The original coefficient action on the SAME actual original residue field. -/
@[instance_reducible] def residueAlgebra (f : D ⟶ Spec (.of k)) (x : D) :
    Algebra k (D.residueField x) := by
  letI := stalkAlgebra f x
  exact IsLocalRing.ResidueField.algebra (D.presheaf.stalk x)

/-- The residue coefficient is literal original evaluation of the original scalar. -/
@[simp] theorem residueAlgebra_algebraMap (f : D ⟶ Spec (.of k)) (x : D) (r : k) :
    letI := residueAlgebra f x
    algebraMap k (D.residueField x) r = D.Γevaluation x (f.appTop (baseScalar r)) := rfl

/-- The actual residue-field comparison is linear over the SAME original field. -/
def residueLocalizationAlgEquiv [IsAffine D] (f : D ⟶ Spec (.of k)) (x : D) :
    letI := structureSectionsAlgebra f
    letI := residueAlgebra f x
    D.residueField x ≃ₐ[k] IsLocalRing.ResidueField
      (Localization.AtPrime ((isAffineOpen_top D).primeIdealOf ⟨x, trivial⟩).asIdeal) := by
  letI := structureSectionsAlgebra f
  letI := stalkAlgebra f x
  letI := residueAlgebra f x
  exact IsLocalRing.ResidueField.mapAlgEquiv (stalkLocalizationAlgEquiv f x)

/-- The actual canonical affine-spectrum identification on the ORIGINAL points. -/
def pointPrimeEquiv [IsAffine D] : D ≃ PrimeSpectrum Γ(D, ⊤) :=
  (Scheme.homeoOfIso D.isoSpec).toEquiv

@[simp] theorem pointPrimeEquiv_eq [IsAffine D] (x : D) :
    pointPrimeEquiv x = (isAffineOpen_top D).primeIdealOf ⟨x, trivial⟩ := by
  rw [IsAffineOpen.primeIdealOf_eq_map_closedPoint]
  rfl

private theorem ringEquiv_length {R S : Type u} [CommRing R] [CommRing S] (e : R ≃+* S) :
    Module.length R R = Module.length S S := by
  let : RingHomSurjective e.toRingHom := ⟨e.surjective⟩
  rw [Module.length, Module.length, WithBot.unbot_inj,
    Order.krullDim_eq_of_orderIso
      (Submodule.orderIsoMapComapOfBijective e.toRingHom.toSemilinearMap e.bijective)]

/-- The true local length and true residue degree at the SAME original affine point. -/
theorem local_degree_eq [IsAffine D] (f : D ⟶ Spec (.of k)) (x : D) :
    letI := structureSectionsAlgebra f
    letI := residueAlgebra f x
    (Module.length (D.presheaf.stalk x) (D.presheaf.stalk x)).toNat *
        Module.finrank k (D.residueField x) =
      (Module.length (Localization.AtPrime (pointPrimeEquiv x).asIdeal)
        (Localization.AtPrime (pointPrimeEquiv x).asIdeal)).toNat *
        Module.finrank k (IsLocalRing.ResidueField
          (Localization.AtPrime (pointPrimeEquiv x).asIdeal)) := by
  let := structureSectionsAlgebra f
  let := stalkAlgebra f x
  let := residueAlgebra f x
  rw [pointPrimeEquiv_eq]
  rw [ringEquiv_length (stalkLocalizationAlgEquiv f x).toRingEquiv,
    (residueLocalizationAlgEquiv f x).toLinearEquiv.finrank_eq]

/-- The actual original finite affine scheme degree is the true sum over
its ORIGINAL points, stalk lengths and residue fields over the original field. -/
theorem finrank_sections_eq_sum_points [IsAffine D] (f : D ⟶ Spec (.of k))
    (hfinite : letI := structureSectionsAlgebra f; Module.Finite k Γ(D, ⊤)) :
    letI := structureSectionsAlgebra f
    Module.finrank k Γ(D, ⊤) =
      ∑ᶠ x : D, letI := residueAlgebra f x
        (Module.length (D.presheaf.stalk x) (D.presheaf.stalk x)).toNat *
          Module.finrank k (D.residueField x) := by
  let := structureSectionsAlgebra f
  let : Module.Finite k Γ(D, ⊤) := hfinite
  rw [FiniteAlgebraLocalDegrees.finrank_eq_sum_local_length_mul_residue_finrank Γ(D, ⊤)]
  symm
  apply finsum_eq_of_bijective pointPrimeEquiv pointPrimeEquiv.bijective
  intro x
  exact local_degree_eq f x

/-- For an ACTUAL finite closed subscheme, the SAME native ideal's full
Euler degree is minus the TRUE stalk-and-residue sum over its ORIGINAL points. -/
theorem normalizedEulerCharacteristic_idealModule_eq_neg_sum_points {X : Scheme.{u}}
    (g : D ⟶ X) [IsClosedImmersion g] [CompactSpace X] [X.IsSeparated]
    (f : X ⟶ Spec (.of k)) (hf : IsProjectiveFactorization f) [IsFinite (g ≫ f)] :
    SchemeCoherentEulerCharacteristic.normalizedEulerCharacteristic f (ModularCurves.idealModule g) =
      -((∑ᶠ x : D, letI := residueAlgebra (g ≫ f) x
        (Module.length (D.presheaf.stalk x) (D.presheaf.stalk x)).toNat *
          Module.finrank k (D.residueField x)) : ℕ) := by
  have : IsAffine D := isAffine_of_isAffineHom (g ≫ f)
  let := structureSectionsAlgebra (g ≫ f)
  rw [FiniteClosedIdealEuler.normalizedEulerCharacteristic_idealModule g f hf,
    (structureFieldSectionsIso (g ≫ f)).toLinearEquiv.finrank_eq,
    finrank_sections_eq_sum_points (g ≫ f) (structureSections_finite g f hf)]

end EnvelopeProperty.AffineSchemeLocalDegrees
