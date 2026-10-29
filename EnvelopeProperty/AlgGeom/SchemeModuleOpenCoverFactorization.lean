import EnvelopeProperty.AlgGeom.SchemeModuleOpenCoverDetection
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.CategoryTheory.Abelian.Exact

/-! # Genuine whole module-map factorization detected on an actual original open cover -/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
noncomputable section
universe u v
namespace EnvelopeProperty.SchemeModuleOpenCoverDetection

/-- A SAME entire original map factors through an actual original
monomorphism iff its SAME native pullbacks factor through the SAME pulled
monomorphism on an actual original open-immersion point cover. No affine,
quasicoherent, flatness, exactness or gluing certificate is an input. -/
theorem factorization_iff {X : Scheme.{u}} {ι : Type v} (Y : ι → Scheme.{u})
    (j : (i : ι) → Y i ⟶ X) [∀ i, IsOpenImmersion (j i)]
    (hcover : ∀ x : X, ∃ (i : ι) (y : Y i), j i y = x)
    {A B I : X.Modules} (inc : I ⟶ B) [Mono inc] (δ : A ⟶ B) :
    (∃ θ : A ⟶ I, θ ≫ inc = δ) ↔
      ∀ i, ∃ θ : (Scheme.Modules.pullback (j i)).obj A ⟶
        (Scheme.Modules.pullback (j i)).obj I,
        θ ≫ (Scheme.Modules.pullback (j i)).map inc =
          (Scheme.Modules.pullback (j i)).map δ := by
  constructor
  · rintro ⟨θ, hθ⟩ i
    refine ⟨(Scheme.Modules.pullback (j i)).map θ, ?_⟩
    exact ((Scheme.Modules.pullback (j i)).map_comp θ inc).symm.trans
      (congrArg (Scheme.Modules.pullback (j i)).map hθ)
  · intro h
    have hz : δ ≫ cokernel.π inc = 0 := by
      apply (eq_zero_iff Y j hcover _).mpr
      intro i
      let F := Scheme.Modules.pullback (j i)
      obtain ⟨θ, hθ⟩ := h i
      calc
        F.map (δ ≫ cokernel.π inc) = F.map δ ≫ F.map (cokernel.π inc) := F.map_comp _ _
        _ = θ ≫ F.map inc ≫ F.map (cokernel.π inc) := by rw [← hθ, Category.assoc]
        _ = θ ≫ F.map (inc ≫ cokernel.π inc) := by rw [F.map_comp]
        _ = 0 := by rw [cokernel.condition, F.map_zero, comp_zero]
    let T := ShortComplex.mk inc (cokernel.π inc) (cokernel.condition inc)
    have he : T.Exact := ShortComplex.exact_cokernel inc
    exact he.lift' δ hz

end EnvelopeProperty.SchemeModuleOpenCoverDetection
