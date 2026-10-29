import EnvelopeProperty.Vanishing.NadelPrincipalization
import EnvelopeProperty.AlgGeom.ProjectiveStrongResolution

/-! # Geometric properties of the actual original Nadel principalization

Nonemptiness and integrality of the actual last scheme are proved from the
original generic nonvanishing, rather than supplied as resolution data.
-/

open AlgebraicGeometry CategoryTheory TopologicalSpace
noncomputable section
universe u

namespace EnvelopeProperty.Vanishing.NadelPrincipalization

/-- The original generic point lies in the actual ideal's unit locus. -/
theorem genericPoint_mem_unitLocus {X : Scheme.{u}} [IsIntegral X]
    (I : X.IdealSheafData) (hI : I.stalkIdeal (genericPoint X) ≠ ⊥) :
    genericPoint X ∈ I.support.compl := by
  intro h
  have hm := (I.mem_support_iff_stalkIdeal_le_maximalIdeal (genericPoint X)).mp h
  rw [IsLocalRing.maximalIdeal_eq_bot] at hm
  exact hI (le_bot_iff.mp hm)

/-- The same actual unit locus is a nonempty dense open in the original scheme. -/
theorem unitLocus_dense {X : Scheme.{u}} [IsIntegral X]
    (I : X.IdealSheafData) (hI : I.stalkIdeal (genericPoint X) ≠ ⊥) :
    Dense (I.support.compl : Set X) :=
  I.support.compl.isOpen.dense ⟨genericPoint X, genericPoint_mem_unitLocus I hI⟩

variable {k : Type u} [Field k] [CharZero k] {X : Scheme.{u}} [IsIntegral X]
    (f : X ⟶ Spec (.of k)) (hp : IsProjectiveFactorization f)
    (n : ℕ) [SmoothOfRelativeDimension n f]
    (I : X.IdealSheafData) (hI : I.stalkIdeal (genericPoint X) ≠ ⊥)

/-- The actual final principalization scheme is nonempty, internally. -/
theorem last_nonempty : Nonempty (sequence f hp n I hI).last := by
  let U := I.support.compl
  let : IsIso ((sequence f hp n I hI).composite ∣_ U) := isIso_restrict_compl f hp n I hI
  let : Nonempty U := ⟨⟨genericPoint X, genericPoint_mem_unitLocus I hI⟩⟩
  let : Nonempty ((sequence f hp n I hI).composite ⁻¹ᵁ U) :=
    Nonempty.map (inv ((sequence f hp n I hI).composite ∣_ U)) inferInstance
  exact Nonempty.map ((sequence f hp n I hI).composite ⁻¹ᵁ U).ι inferInstance

/-- The original actual finite blowup sequence ends in an integral scheme. -/
theorem last_isIntegral : IsIntegral (sequence f hp n I hI).last := by
  let : Nonempty (sequence f hp n I hI).last := last_nonempty f hp n I hI
  exact ProjectiveStrongResolution.isIntegral_last (sequence f hp n I hI)

/-- Properness of the actual composite over the same original scheme. -/
theorem composite_isProper : IsProper (sequence f hp n I hI).composite := by
  let : IsProper f := hp.isProper
  let : IsLocallyNoetherian X := f.isLocallyNoetherian_of_field
  exact (sequence f hp n I hI).isProper_composite

/-- A produced dense isomorphism locus, with its actual original open. -/
theorem exists_dense_isIso :
    ∃ U : X.Opens, Dense (U : Set X) ∧
      IsIso ((sequence f hp n I hI).composite ∣_ U) :=
  ⟨I.support.compl, unitLocus_dense I hI, isIso_restrict_compl f hp n I hI⟩

end EnvelopeProperty.Vanishing.NadelPrincipalization
