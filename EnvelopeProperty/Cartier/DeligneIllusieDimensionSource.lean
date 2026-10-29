import EnvelopeProperty.Cartier.DeligneIllusieDimensionBound
import EnvelopeProperty.Cartier.DeligneIllusieGradedSourceHomology

/-!
# Deligne Illusie Dimension Source

Removing actual zero exterior-form summands from the original DI source. -/

noncomputable section

namespace EnvelopeProperty.Cartier.DeligneIllusieDimensionSource

open AlgebraicGeometry CategoryTheory Category Limits HomologicalComplex

universe u

variable {k : Type u} [Field k] {X : Scheme.{u}}
  (f : X ⟶ Spec (.of k)) (p : ℕ) [Fact p.Prime] [CharP k p]

local notation "S" => (fun q : ℕ =>
  Functor.obj (single (Scheme.Modules (SchemeRelativeFrobenius.twist p f)) (ComplexShape.up ℕ) q)
    (CanonicalGeometry.exteriorCotangentSheaf
      (DeligneIllusieDimensionBound.twistStructure f p) q))

/-- The actual finite coproduct of original true-twist form sheaves in their own degrees. -/
def source (r : ℕ) : CochainComplex (SchemeRelativeFrobenius.twist p f).Modules ℕ :=
  ∐ fun q : Fin r => (S) q.val

variable (n : ℕ)

/-- The literal coproduct of the original inclusions at the unchanged natural degree. -/
def sourceInclusion (hp : n < p) : source f p (n + 1) ⟶ source f p p :=
  Sigma.desc (fun q : Fin (n + 1) =>
    Sigma.ι (fun a : Fin p => (S) a.val) (q.castLE (Nat.succ_le_of_lt hp)))

private def sourceProjection : source f p p ⟶ source f p (n + 1) :=
  Sigma.desc (fun q : Fin p =>
    if h : q.val < n + 1 then
      Sigma.ι (fun a : Fin (n + 1) => (S) a.val) ⟨q.val, h⟩
    else (0 : (S) q.val ⟶ ∐ fun a : Fin (n + 1) => (S) a.val))

variable [SmoothOfRelativeDimension n f]

/-- Actual geometric dimension vanishing makes precisely this original inclusion invertible. -/
theorem sourceInclusion_isIso (hp : n < p) : IsIso (sourceInclusion f p n hp) := by
  refine ⟨⟨sourceProjection f p n, ?_, ?_⟩⟩
  · dsimp only [sourceInclusion, sourceProjection, source]
    apply Sigma.hom_ext
    intro q
    rw [← assoc, Sigma.ι_desc, Sigma.ι_desc]
    simp only [Fin.val_castLE, dif_pos q.isLt, comp_id]
  · dsimp only [sourceInclusion, sourceProjection, source]
    apply Sigma.hom_ext
    intro q
    by_cases hq : q.val < n + 1
    · rw [← assoc, Sigma.ι_desc, dif_pos hq, Sigma.ι_desc, comp_id]
      rfl
    · have hnq : n < q.val := by omega
      have hz : IsZero ((S) q.val) :=
        (single (SchemeRelativeFrobenius.twist p f).Modules (ComplexShape.up ℕ) q.val).map_isZero
          (DeligneIllusieDimensionBound.twist_exteriorCotangentSheaf_isZero f n p q.val hnq)
      exact hz.eq_of_src _ _

/-- The canonical actual source isomorphism, with the original inclusion as its forward map. -/
def sourceIso (hp : n < p) : source f p (n + 1) ≅ source f p p := by
  let := sourceInclusion_isIso f p n hp
  exact asIso (sourceInclusion f p n hp)

/-- Each original small summand maps to the original big summand at exactly the same degree. -/
theorem ι_sourceIso_hom (hp : n < p) (q : Fin (n + 1)) :
    Sigma.ι (fun a : Fin (n + 1) => (S) a.val) q ≫ (sourceIso f p n hp).hom =
      Sigma.ι (fun a : Fin p => (S) a.val) (q.castLE (Nat.succ_le_of_lt hp)) := by
  exact Sigma.ι_desc _ q

end EnvelopeProperty.Cartier.DeligneIllusieDimensionSource
