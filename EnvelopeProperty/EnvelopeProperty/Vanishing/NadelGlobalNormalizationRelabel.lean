import EnvelopeProperty.Vanishing.NadelMixedKummerPresentation

/-! # Whole simultaneous root quotients retain ALL original roots under finite relabelling

The actual quotient universal properties construct both maps, rather than
receiving a desired whole chart equivalence as input.
-/

noncomputable section
universe u
namespace EnvelopeProperty.Vanishing.NadelGlobalNormalization.Relabel
open NadelMixedKummer
variable {R : Type u} [CommRing R] {q r : ℕ} (N : Fin q → ℕ) (c : Fin q → R) (e : Fin q ≃ Fin r)

private theorem forwardRoots_pow (i : Fin q) :
    root (fun j => N (e.symm j)) (fun j => c (e.symm j)) (e i) ^ N i =
      algebraMap R _ (c i) := by
  simpa only [e.symm_apply_apply] using
    root_pow (fun j => N (e.symm j)) (fun j => c (e.symm j)) (e i)

/-- The actual whole forward original-root relabelling map. -/
def forward : Ring N c →+* Ring (fun j => N (e.symm j)) (fun j => c (e.symm j)) :=
  evaluate N c (algebraMap R _)
    (fun i => root (fun j => N (e.symm j)) (fun j => c (e.symm j)) (e i)) (forwardRoots_pow N c e)

/-- The actual whole inverse original-root relabelling map. -/
def backward : Ring (fun j => N (e.symm j)) (fun j => c (e.symm j)) →+* Ring N c :=
  evaluate (fun j => N (e.symm j)) (fun j => c (e.symm j)) (algebraMap R _)
    (fun j => root N c (e.symm j)) (fun j => root_pow N c (e.symm j))

/-- BOTH whole original-root identities prove the actual entire ring relabelling. -/
def ringEquiv : Ring N c ≃+* Ring (fun j => N (e.symm j)) (fun j => c (e.symm j)) := by
  refine RingEquiv.ofRingHom (forward N c e) (backward N c e) ?_ ?_
  · apply hom_ext
    · dsimp only [forward, backward]
      rw [RingHom.comp_assoc, evaluate_structure, evaluate_structure]
      rfl
    · intro j
      change forward N c e (backward N c e _) = _
      dsimp only [forward, backward]
      rw [evaluate_root, evaluate_root, e.apply_symm_apply]
      rfl
  · apply hom_ext
    · dsimp only [forward, backward]
      rw [RingHom.comp_assoc, evaluate_structure, evaluate_structure]
      rfl
    · intro i
      change backward N c e (forward N c e _) = _
      dsimp only [forward, backward]
      rw [evaluate_root, evaluate_root, e.symm_apply_apply]
      rfl

/-- The actual WHOLE relabelling retains the SAME original coefficient ring. -/
def algEquiv : Ring N c ≃ₐ[R] Ring (fun j => N (e.symm j)) (fun j => c (e.symm j)) :=
  { toRingEquiv := ringEquiv N c e
    commutes' := fun a => congrArg (fun f : R →+* _ => f a) (evaluate_structure N c (algebraMap R _)
      (fun i => root (fun j => N (e.symm j)) (fun j => c (e.symm j)) (e i)) (forwardRoots_pow N c e)) }

/-- Every SAME original root keeps its original position under the actual relabelling. -/
theorem algEquiv_root (i : Fin q) : algEquiv N c e (root N c i) =
    root (fun j => N (e.symm j)) (fun j => c (e.symm j)) (e i) :=
  evaluate_root N c (algebraMap R _)
    (fun i => root (fun j => N (e.symm j)) (fun j => c (e.symm j)) (e i))
    (forwardRoots_pow N c e) i

end EnvelopeProperty.Vanishing.NadelGlobalNormalization.Relabel
