import EnvelopeProperty.Vanishing.NadelGlobalCanonicalTraceAffineNaturality

/-! # Literal native global sections of the original field-map transport

The explicit source and target objects keep elaboration from guessing
large dependent sheaf-module records.  This is exactly the original
section functor applied to equality of the original structural maps.
-/
noncomputable section
namespace EnvelopeProperty.Vanishing.NadelGlobalCanonicalTrace
open AlgebraicGeometry CategoryTheory Opposite CanonicalGeometry
universe u
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

variable {K : Type u} [Field K] (B : CommRingCat.{u})

/-- Literal original canonical section transport along equality of the
same original field structural morphisms. -/
def canonicalFieldSectionsMap
    {f₁ f₂ : Spec B ⟶ Spec (.of K)} (h : f₁ = f₂) (d : ℕ) :
    (moduleSpecΓFunctor (R := B)).obj (exteriorCotangentSheaf f₁ d) ⟶
      (moduleSpecΓFunctor (R := B)).obj (exteriorCotangentSheaf f₂ d) :=
  (moduleSpecΓFunctor (R := B)).map
    (X := exteriorCotangentSheaf f₁ d) (Y := exteriorCotangentSheaf f₂ d)
    (eqToHom (congrArg (fun f => exteriorCotangentSheaf f d) h))

/-- The actual global section functor preserves the original identity. -/
theorem canonicalFieldSectionsMap_refl
    (f : Spec B ⟶ Spec (.of K)) (d : ℕ) :
    canonicalFieldSectionsMap B (rfl : f = f) d =
      𝟙 ((moduleSpecΓFunctor (R := B)).obj (exteriorCotangentSheaf f d)) := by
  exact CategoryTheory.Functor.map_id (moduleSpecΓFunctor (R := B))
    (exteriorCotangentSheaf f d)

/-- Every tuple of original regular functions retains its native
coordinate wedge through the original field structural equality. -/
theorem canonicalFieldSectionsMap_coordinate
    {f₁ f₂ : Spec B ⟶ Spec (.of K)} (h : f₁ = f₂) (d : ℕ)
    (z : Fin d → Γ(Spec B, ⊤)) :
    (canonicalFieldSectionsMap B h d).hom.toFun
      (exteriorSheafSection (cotangentPresheaf f₁) d ⊤
        (fun j => (cotangentPresheafDerivation f₁).d (z j))) =
    exteriorSheafSection (cotangentPresheaf f₂) d ⊤
      (fun j => (cotangentPresheafDerivation f₂).d (z j)) := by
  cases h
  rw [canonicalFieldSectionsMap_refl]
  rfl

end EnvelopeProperty.Vanishing.NadelGlobalCanonicalTrace
