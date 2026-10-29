import EnvelopeProperty.Vanishing.NadelAdaptedChartMatchingBaseChange

/-! # The genuine SAME whole quotient under an actual coefficient-ring isomorphism -/

open AlgebraicGeometry CategoryTheory
noncomputable section
universe u
namespace EnvelopeProperty.Vanishing.NadelAdaptedChartMatching.ChangeRing
open NadelMixedKummer
variable {R S : Type u} [CommRing R] [CommRing S] {q : ℕ}
  (N : Fin q → ℕ) (c : Fin q → R) (e : R ≃+* S)

/-- The actual reverse coefficient-ring map, fixing EVERY original root. -/
def backward : Ring N (fun i => e.toRingHom (c i)) →+* Ring N c :=
  evaluate N (fun i => e.toRingHom (c i)) ((algebraMap R (Ring N c)).comp e.symm.toRingHom)
    (root N c) (fun i => by
      change root N c i ^ N i = algebraMap R (Ring N c) (e.symm (e (c i)))
      rw [e.symm_apply_apply]
      exact root_pow N c i)


/-- The actual whole coefficient-ring comparison is an isomorphism, proved
on BOTH coefficient maps and every SAME original root. -/
def equiv : Ring N c ≃+* Ring N (fun i => e.toRingHom (c i)) := by
  refine RingEquiv.ofRingHom (BaseChange.map N c e.toRingHom) (backward N c e) ?_ ?_
  · apply hom_ext
    · rw [RingHom.comp_assoc]
      change (BaseChange.map N c e.toRingHom).comp
        ((backward N c e).comp (algebraMap S (Ring N (fun i => e.toRingHom (c i))))) = _
      rw [show (backward N c e).comp (algebraMap S (Ring N (fun i => e.toRingHom (c i)))) =
        (algebraMap R (Ring N c)).comp e.symm.toRingHom from evaluate_structure _ _ _ _ _]
      rw [← RingHom.comp_assoc, BaseChange.map_structure]
      ext s
      change algebraMap S (Ring N (fun i => e.toRingHom (c i))) (e (e.symm s)) = _
      rw [e.apply_symm_apply]
      rfl
    · intro i
      change BaseChange.map N c e.toRingHom (backward N c e _) = _
      rw [show backward N c e (root N (fun i => e.toRingHom (c i)) i) = root N c i from evaluate_root _ _ _ _ _ i,
        BaseChange.map_root]
      rfl
  · apply hom_ext
    · rw [RingHom.comp_assoc, BaseChange.map_structure, ← RingHom.comp_assoc]
      rw [show (backward N c e).comp (algebraMap S (Ring N (fun i => e.toRingHom (c i)))) =
        (algebraMap R (Ring N c)).comp e.symm.toRingHom from evaluate_structure _ _ _ _ _]
      ext r
      change algebraMap R (Ring N c) (e.symm (e r)) = _
      rw [e.symm_apply_apply]
      rfl
    · intro i
      change backward N c e (BaseChange.map N c e.toRingHom _) = _
      rw [BaseChange.map_root]
      exact evaluate_root _ _ _ _ _ i

/-- The actual original coefficient triangle is retained in the whole comparison. -/
theorem equiv_structure : (equiv N c e).toRingHom.comp (algebraMap R (Ring N c)) =
    (algebraMap S (Ring N (fun i => e.toRingHom (c i)))).comp e.toRingHom := BaseChange.map_structure _ _ _

/-- Every SAME original whole root is retained by the coefficient-ring comparison. -/
theorem equiv_root (i : Fin q) : equiv N c e (root N c i) =
    root N (fun i => e.toRingHom (c i)) i := BaseChange.map_root _ _ _ _

end EnvelopeProperty.Vanishing.NadelAdaptedChartMatching.ChangeRing
