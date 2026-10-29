import EnvelopeProperty.Vanishing.NadelAdaptedChartMatchingFiniteFamily
import EnvelopeProperty.Vanishing.NadelMixedKummerPresentation
import EnvelopeProperty.Vanishing.NadelKummerCoverTowerBasis

/-! # Genuine finite free structure of the WHOLE varying-degree quotient

The actual whole quotient is compared, by BOTH universal properties, with
the native successive original root tower. Its native finite basis is
transported to the whole quotient, retaining all disconnected factors.
-/

noncomputable section
universe u
namespace EnvelopeProperty.Vanishing.NadelAdaptedChartMatching.VaryingFinite
open NadelMixedKummer
variable {R : Type u} [CommRing R] {q : ℕ} (N : Fin q → ℕ) (c : Fin q → R)
  (hpositive : ∀ i, 0 < N i)

/-- The actual quotient map to the WHOLE original varying-degree tower. -/
def toFamily : Ring N c →+* VaryingFamily.Ring N c :=
  evaluate N c (VaryingFamily.structureMap N c) (VaryingFamily.root N c)
    (VaryingFamily.root_pow N c hpositive)

/-- The actual whole tower evaluation into the original simultaneous quotient. -/
def fromFamily : VaryingFamily.Ring N c →+* Ring N c :=
  VaryingFamily.evaluate N c hpositive (algebraMap R (Ring N c)) (root N c) (root_pow N c)

/-- The WHOLE varying-degree quotient and native original root tower are
actually isomorphic; no comparison map or desired basis is supplied as input. -/
def ringEquiv : Ring N c ≃+* VaryingFamily.Ring N c := by
  refine RingEquiv.ofRingHom (toFamily N c hpositive) (fromFamily N c hpositive) ?_ ?_
  · apply VaryingFamily.hom_ext N c
    · dsimp only [toFamily, fromFamily]
      rw [RingHom.comp_assoc, VaryingFamily.evaluate_structure, evaluate_structure]
      rfl
    · intro i
      change toFamily N c hpositive (fromFamily N c hpositive _) = _
      dsimp only [toFamily, fromFamily]
      rw [VaryingFamily.evaluate_root, evaluate_root]
      rfl
  · apply hom_ext
    · dsimp only [toFamily, fromFamily]
      rw [RingHom.comp_assoc, evaluate_structure, VaryingFamily.evaluate_structure]
      rfl
    · intro i
      change fromFamily N c hpositive (toFamily N c hpositive _) = _
      dsimp only [toFamily, fromFamily]
      rw [evaluate_root, VaryingFamily.evaluate_root]
      rfl

/-- The actual whole tower comparison is over the SAME original ring. -/
def algEquiv :
    let _ : Algebra R (VaryingFamily.Ring N c) := (VaryingFamily.structureMap N c).toAlgebra
    Ring N c ≃ₐ[R] VaryingFamily.Ring N c := by
  let : Algebra R (VaryingFamily.Ring N c) := (VaryingFamily.structureMap N c).toAlgebra
  exact {
    toRingEquiv := ringEquiv N c hpositive
    commutes' := fun z => congrArg (fun f : R →+* VaryingFamily.Ring N c => f z)
      (evaluate_structure N c (VaryingFamily.structureMap N c) (VaryingFamily.root N c)
        (VaryingFamily.root_pow N c hpositive)) }

variable [Nontrivial R]

/-- The native whole successive power basis transports to the SAME entire
original quotient, with no assumption on its connectedness or reducedness. -/
def basis : Module.Basis (NadelKummerCover.Tower.basisIndex (VaryingFamily.degree N) q)
    R (Ring N c) := by
  let : Algebra R (VaryingFamily.Ring N c) := (VaryingFamily.structureMap N c).toAlgebra
  exact (NadelKummerCover.Tower.basis (VaryingFamily.degree N) (VaryingFamily.coefficient c) q).map
    (algEquiv N c hpositive).symm.toLinearEquiv

include hpositive in
/-- The WHOLE varying-degree root quotient is free over the original ring. -/
theorem free : Module.Free R (Ring N c) := Module.Free.of_basis (basis N c hpositive)

include hpositive in
/-- The WHOLE varying-degree root quotient is finite over the original ring. -/
theorem finite : Module.Finite R (Ring N c) := by
  let := NadelKummerCover.Tower.basisIndex_finite (VaryingFamily.degree N) q
  exact Module.Finite.of_basis (basis N c hpositive)

include hpositive in
/-- Genuine flatness is derived from the actual WHOLE original basis. -/
theorem flat : Module.Flat R (Ring N c) := by
  have : Module.Free R (Ring N c) := free N c hpositive
  infer_instance

end EnvelopeProperty.Vanishing.NadelAdaptedChartMatching.VaryingFinite
