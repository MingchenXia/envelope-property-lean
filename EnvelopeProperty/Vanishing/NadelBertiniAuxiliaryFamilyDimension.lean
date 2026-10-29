import Hironaka.Resolution.Algebraic.Monomial.Geometric.Nerve

/-! # Actual dimension bound and whole empty intersections of original SNC members -/
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open scoped Classical
universe u
namespace EnvelopeProperty.Vanishing.NadelBertiniAuxiliaryFamilyDimension
variable {k : Type u} [Field k] [PerfectField k] {X : Scheme.{u}}

/-- Native SNC coordinates and the actual arbitrary-point smooth dimension
formula bound the number of original members through ANY original point. -/
theorem card_members_through_le (p : X ⟶ Spec (.of k)) (n : ℕ)
    [SmoothOfRelativeDimension n p] (F : X.DivisorFamily) (hF : F.IsSnc) (x : X) :
    (Finset.univ.filter (fun i : F.ι => x ∈ (F.component i).support)).card ≤ n :=
  Hironaka.Monomial.PieceFamily.card_filter_mem_support_le p hF x

/-- Any n+1 distinctly indexed actual original SNC members have whole
scheme-theoretic empty intersection, with no closed-point hypothesis. -/
theorem sum_eq_top_of_injective_succ (p : X ⟶ Spec (.of k)) (n : ℕ)
    [SmoothOfRelativeDimension n p] (F : X.DivisorFamily) (hF : F.IsSnc)
    (v : Fin (n + 1) → F.ι) (hv : Function.Injective v) :
    (⨆ j, F.component (v j)) = ⊤ := by
  classical
  apply (Scheme.IdealSheafData.support_eq_bot_iff _).mp
  rw [Scheme.IdealSheafData.support_iSup]
  apply le_bot_iff.mp
  intro x hx
  have hmem : ∀ j, x ∈ (F.component (v j)).support :=
    fun j => (Closeds.mem_iInf.mp hx) j
  let w : Fin (n + 1) → {i : F.ι // x ∈ (F.component i).support} := fun j => ⟨v j, hmem j⟩
  have hw : Function.Injective w := by
    intro i j hij
    exact hv (congrArg Subtype.val hij)
  have hc := Fintype.card_le_of_injective w hw
  have hn := card_members_through_le p n F hF x
  rw [Fintype.card_fin, Fintype.card_subtype] at hc
  have : False := by omega
  exact this.elim

end EnvelopeProperty.Vanishing.NadelBertiniAuxiliaryFamilyDimension
