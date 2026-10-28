import EnvelopeProperty.Global.FibreIdealPowers
import EnvelopeProperty.AlgGeom.ReesFormalChartSheaf

/-!
# Original ideal-power sheaves in the same actual Rees chart coordinates

The genuine original sections homomorphism equals the coefficient map of
the actual Rees chart. The whole original ideal-power sections and every
restriction are transported to these SAME coordinates, with no supplied
comparison premise.
-/

open CategoryTheory AlgebraicGeometry Opposite
noncomputable section
universe u

namespace EnvelopeProperty.FibreIdealPowerCoordinates

variable {R : Type u} [CommRing R] {X : Scheme.{u}} (f : X ⟶ Spec (.of R))

/-- The original whole sections homomorphism is the coefficient homomorphism
of the SAME actual original affine chart. -/
theorem sectionsHom_eq_chartCoefficient {U : X.Opens} (hU : IsAffineOpen U) :
    sectionsHom f U = FcReesFormalRestriction.chartCoefficient f hU := by
  have hspec : Spec.map (CommRingCat.ofHom (sectionsHom f U)) = hU.fromSpec ≫ f := by
    calc
      _ = hU.isoSpec.inv ≫
          (hU.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom (sectionsHom f U))) := by simp
      _ = hU.isoSpec.inv ≫ (U.ι ≫ f) := by
        rw [isoSpec_hom_specMap_sectionsHom f ⟨U, hU⟩]
      _ = hU.fromSpec ≫ f := by rw [← Category.assoc, IsAffineOpen.isoSpec_inv_ι]
  have hpre := congrArg Spec.preimage hspec
  rw [Spec.preimage_map] at hpre
  exact congrArg CommRingCat.Hom.hom hpre

variable (I : Ideal R)

/-- The original ENTIRE geometric ideal power evaluates to the image ideal
power for the SAME actual Rees chart coefficient homomorphism. -/
theorem extendedPower_ideal_chart (d : ℕ) (U : X.affineOpens) :
    (FibreIdealPowers.extendedPower I f d).ideal U =
      (I.map (FcReesFormalRestriction.chartCoefficient f U.2))^d := by
  rw [FibreIdealPowers.extendedPower_ideal, sectionsHom_eq_chartCoefficient f U.2]

/-- WHOLE original ideal-power sections in the SAME actual Rees chart. -/
def affineChartSectionsEquiv (d : ℕ) (U : X.affineOpens) :
    Γ(FibreIdealPowers.powerModule I f d, U) ≃ₗ[Γ(X, U)]
      ↥((I.map (FcReesFormalRestriction.chartCoefficient f U.2))^d) :=
  ((FibreIdealPowers.extendedPower I f d).toModulesSectionsEquiv U).trans
    (LinearEquiv.ofEq _ _ (extendedPower_ideal_chart f I d U))

/-- The actual whole equivalence retains EVERY underlying original function. -/
theorem affineChartSectionsEquiv_apply (d : ℕ) (U : X.affineOpens)
    (s : Γ(FibreIdealPowers.powerModule I f d, U)) :
    ((affineChartSectionsEquiv f I d U s :
        ↥((I.map (FcReesFormalRestriction.chartCoefficient f U.2))^d)) : Γ(X, U)) =
      ((FibreIdealPowers.extendedPower I f d).toModulesSectionsEquiv U s : Γ(X, U)) := rfl

/-- EVERY affine restriction in the SAME Rees coordinates is the literal
original whole function restriction. -/
theorem affineChartSectionsEquiv_restriction (d : ℕ) {U V : X.affineOpens} (h : U ≤ V)
    (s : Γ(FibreIdealPowers.powerModule I f d, V)) :
    ((affineChartSectionsEquiv f I d U
        ((FibreIdealPowers.powerModule I f d).presheaf.map (homOfLE h).op s) :
        ↥((I.map (FcReesFormalRestriction.chartCoefficient f U.2))^d)) : Γ(X, U)) =
      X.presheaf.map (homOfLE h).op
        ((affineChartSectionsEquiv f I d V s :
          ↥((I.map (FcReesFormalRestriction.chartCoefficient f V.2))^d)) : Γ(X, V)) := rfl

end EnvelopeProperty.FibreIdealPowerCoordinates
