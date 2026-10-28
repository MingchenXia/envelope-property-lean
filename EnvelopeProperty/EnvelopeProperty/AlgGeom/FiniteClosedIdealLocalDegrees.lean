import EnvelopeProperty.AlgGeom.FiniteClosedIdealEuler
import EnvelopeProperty.AlgGeom.FiniteAlgebraLocalDegrees

/-! # Actual original finite closed-ideal degree as residue-weighted local lengths -/
open CategoryTheory Limits AlgebraicGeometry Opposite
open Scheme.Modules
noncomputable section
universe u
namespace EnvelopeProperty.FiniteClosedIdealLocalDegrees
open SchemeCoherentEulerIndex SchemeCoherentEulerCharacteristic
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {k : Type u} [Field k] {X D : Scheme.{u}}

/-- The SAME original field acts on the SAME entire original structure-section ring. -/
@[instance_reducible] def structureSectionsAlgebra (f : D ⟶ Spec (.of k)) : Algebra k Γ(D, ⊤) :=
  (f.appTop.hom.comp (baseScalar (k := k))).toAlgebra

/-- The actual original field-linear structure sections are the SAME original
ring with exactly its original structure coefficient action. -/
def structureFieldSectionsIso (f : D ⟶ Spec (.of k)) :
    letI := structureSectionsAlgebra f
    fieldSections f (unitObj D) ≅ ModuleCat.of k Γ(D, ⊤) := by
  letI := structureSectionsAlgebra f
  refine ModuleCat.isoMk (Iso.refl _) ?_
  intro r
  ext s
  let a : Γ(D, ⊤) := s
  change f.appTop.hom (baseScalar r) * a =
    D.presheaf.map ((initialOpOfTerminal isTerminalTop).to (op (⊤ : D.Opens)))
      (f.appTop.hom (baseScalar r)) * a
  rw [show (initialOpOfTerminal isTerminalTop).to (op (⊤ : D.Opens)) = 𝟙 _ from
    Subsingleton.elim _ _]
  simp

/-- Genuine original projective geometry makes the SAME original structure-section algebra finite. -/
theorem structureSections_finite (g : D ⟶ X) [IsClosedImmersion g]
    (f : X ⟶ Spec (.of k)) (hf : IsProjectiveFactorization f) :
    letI := structureSectionsAlgebra (g ≫ f)
    Module.Finite k Γ(D, ⊤) := by
  let := structureSectionsAlgebra (g ≫ f)
  let : Module.Finite k (fieldSections (g ≫ f) (unitObj D)) :=
    FiniteClosedIdealEuler.fieldSections_finite g f hf
  exact Module.Finite.equiv (structureFieldSectionsIso (g ≫ f)).toLinearEquiv

/-- The SAME original closed-scheme degree is the true residue-weighted sum
of lengths over the SAME original entire section ring and prime localizations. -/
theorem fieldDegree_eq_sum_local_degrees (g : D ⟶ X) [IsClosedImmersion g]
    (f : X ⟶ Spec (.of k)) (hf : IsProjectiveFactorization f) :
    letI := structureSectionsAlgebra (g ≫ f)
    Module.finrank k (fieldSections (g ≫ f) (unitObj D)) =
      ∑ᶠ p : PrimeSpectrum Γ(D, ⊤),
        (Module.length (Localization.AtPrime p.asIdeal) (Localization.AtPrime p.asIdeal)).toNat *
          Module.finrank k (IsLocalRing.ResidueField (Localization.AtPrime p.asIdeal)) := by
  let := structureSectionsAlgebra (g ≫ f)
  let : Module.Finite k Γ(D, ⊤) := structureSections_finite g f hf
  rw [(structureFieldSectionsIso (g ≫ f)).toLinearEquiv.finrank_eq]
  exact FiniteAlgebraLocalDegrees.finrank_eq_sum_local_length_mul_residue_finrank Γ(D, ⊤)

/-- The SAME actual original native ideal has normalized full Euler
characteristic minus its TRUE original residue-weighted local degree sum. -/
theorem normalizedEulerCharacteristic_idealModule_eq_neg_sum (g : D ⟶ X)
    [IsClosedImmersion g] [CompactSpace X] [X.IsSeparated]
    (f : X ⟶ Spec (.of k)) (hf : IsProjectiveFactorization f) [IsFinite (g ≫ f)] :
    letI := structureSectionsAlgebra (g ≫ f)
    normalizedEulerCharacteristic f (ModularCurves.idealModule g) =
      -((∑ᶠ p : PrimeSpectrum Γ(D, ⊤),
        (Module.length (Localization.AtPrime p.asIdeal) (Localization.AtPrime p.asIdeal)).toNat *
          Module.finrank k (IsLocalRing.ResidueField (Localization.AtPrime p.asIdeal))) : ℕ) := by
  let := structureSectionsAlgebra (g ≫ f)
  rw [FiniteClosedIdealEuler.normalizedEulerCharacteristic_idealModule g f hf,
    fieldDegree_eq_sum_local_degrees g f hf]

end EnvelopeProperty.FiniteClosedIdealLocalDegrees
