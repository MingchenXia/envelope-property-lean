import EnvelopeProperty.Vanishing.NadelMixedKummerPresentation

/-! # Actual whole scaling isomorphisms of simultaneous original root quotients -/

noncomputable section
universe u
namespace EnvelopeProperty.Vanishing.NadelCanonicalMixed

open NadelMixedKummer
variable {R : Type u} [CommRing R] {q : ℕ} (N : Fin q → ℕ)
    (c h : Fin q → R) (a : Fin q → Rˣ)
    (hc : ∀ i, c i = (a i : R) ^ N i * h i)

/-- The original unit factors scale every actual root on the entire simultaneous quotient. -/
def scaleHom : Ring N c →+* Ring N h :=
  evaluate N c (algebraMap R (Ring N h))
    (fun i => algebraMap R (Ring N h) (a i : R) * root N h i) (by
      intro i
      rw [mul_pow, root_pow, ← map_pow, ← map_mul, hc i])

/-- The actual inverse units reverse every original root scaling on the whole quotient. -/
def unscaleHom : Ring N h →+* Ring N c :=
  evaluate N h (algebraMap R (Ring N c))
    (fun i => algebraMap R (Ring N c) ((a i)⁻¹ : Rˣ) * root N c i) (by
      intro i
      rw [mul_pow, root_pow, ← map_pow, ← map_mul, hc i]
      congr 1
      rw [← mul_assoc, ← mul_pow]
      simp)

/-- Every original coefficient is preserved by the actual whole scaling map. -/
theorem scaleHom_structure : (scaleHom N c h a hc).comp (algebraMap R (Ring N c)) =
    algebraMap R (Ring N h) := evaluate_structure _ _ _ _ _

/-- Every original coefficient is preserved by its actual inverse. -/
theorem unscaleHom_structure : (unscaleHom N c h a hc).comp (algebraMap R (Ring N h)) =
    algebraMap R (Ring N c) := evaluate_structure _ _ _ _ _

/-- Each original root has its genuine scaled image, on every whole factor. -/
theorem scaleHom_root (i : Fin q) :
    scaleHom N c h a hc (root N c i) = algebraMap R (Ring N h) (a i : R) * root N h i :=
  evaluate_root _ _ _ _ _ i

/-- Each original root has its genuine inverse-scaled image. -/
theorem unscaleHom_root (i : Fin q) :
    unscaleHom N c h a hc (root N h i) =
      algebraMap R (Ring N c) ((a i)⁻¹ : Rˣ) * root N c i :=
  evaluate_root _ _ _ _ _ i

/-- Both actual whole universal properties prove a coefficient-preserving scaling equivalence; no component is selected. -/
def rescaleAlgEquiv : Ring N c ≃ₐ[R] Ring N h := by
  let f := scaleHom N c h a hc
  let g := unscaleHom N c h a hc
  have hfg : f.comp g = RingHom.id _ := by
    apply hom_ext
    · rw [RingHom.comp_assoc, unscaleHom_structure, scaleHom_structure]
      rfl
    · intro i
      change f (g (root N h i)) = root N h i
      rw [unscaleHom_root, map_mul, scaleHom_root]
      have hs := congrArg (fun z : R →+* Ring N h => z ((a i)⁻¹ : Rˣ))
        (scaleHom_structure N c h a hc)
      change f (algebraMap R (Ring N c) ((a i)⁻¹ : Rˣ)) = _ at hs
      rw [hs, ← mul_assoc, ← map_mul]
      simp
  have hgf : g.comp f = RingHom.id _ := by
    apply hom_ext
    · rw [RingHom.comp_assoc, scaleHom_structure, unscaleHom_structure]
      rfl
    · intro i
      change g (f (root N c i)) = root N c i
      rw [scaleHom_root, map_mul, unscaleHom_root]
      have hs := congrArg (fun z : R →+* Ring N c => z (a i : R))
        (unscaleHom_structure N c h a hc)
      change g (algebraMap R (Ring N h) (a i : R)) = _ at hs
      rw [hs, ← mul_assoc, ← map_mul]
      simp
  exact { toRingEquiv := RingEquiv.ofRingHom f g hfg hgf
          commutes' := fun r => congrArg (fun z : R →+* Ring N h => z r)
            (scaleHom_structure N c h a hc) }

end EnvelopeProperty.Vanishing.NadelCanonicalMixed
