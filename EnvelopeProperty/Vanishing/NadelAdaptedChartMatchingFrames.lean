import EnvelopeProperty.AlgGeom.CyclicSectionSNCUniformFramedCharts

/-! # Common ORIGINAL frames on actual joined SNC coordinates

The frames and coordinates are produced from local invertibility and the
original SNC family. No adapted chart, coefficient or normalization comparison
is an input.
-/

open AlgebraicGeometry CategoryTheory Scheme.Modules
noncomputable section
universe u v
namespace EnvelopeProperty.Vanishing.NadelAdaptedChartMatching
variable {X : Scheme.{u}}

/-- Finitely many ORIGINAL line modules have actual frames on one genuine
common affine neighbourhood inside the given original open. -/
theorem exists_common_frames_in {q : ℕ} (L : Fin q → X.Modules)
    (hL : ∀ i, IsInvertible (L i)) (y : X) (V : X.Opens) (hy : y ∈ V) :
    ∃ U : X.affineOpens, y ∈ U.1 ∧ U.1 ≤ V ∧
      Nonempty (∀ i, (pullback U.1.ι).obj (L i) ≅ unitObj U.1.toScheme) := by
  induction q generalizing V with
  | zero =>
      obtain ⟨U, hUa, hyU, hUV⟩ := exists_isAffineOpen_mem_and_subset (X := X) hy
      exact ⟨⟨U, hUa⟩, hyU, hUV, ⟨fun i => Fin.elim0 i⟩⟩
  | succ q ih =>
      obtain ⟨W, hyW, hWV, ⟨e₀⟩, _⟩ := SchemeCommonAffineLineFrames.exists_in_open
        (L 0) (unitObj X) (hL 0) isInvertible_unit y V hy
      obtain ⟨U, hyU, hUW, ⟨e⟩⟩ := ih (fun i => L i.succ) (fun i => hL i.succ) W.1 hyW
      let e₀' : (pullback U.1.ι).obj (L 0) ≅ unitObj U.1.toScheme :=
        frameViaFactor (X.homOfLE hUW) W.1.ι U.1.ι (X.homOfLE_ι hUW) e₀
      exact ⟨U, hyU, hUW.trans hWV, ⟨Fin.cases e₀' e⟩⟩

/-- The actual original SNC producer and local invertibility INTERNALLY give
one etale coordinate chart with frames of EVERY original finite line. The
same original component labels, coordinate injection and absent ideals remain. -/
theorem exists_framed_snc_chart_at_closed {k : Type u} [Field k] [PerfectField k]
    (f : X ⟶ Spec (.of k)) (n : ℕ) [SmoothOfRelativeDimension n f]
    (F : X.DivisorFamily) (hF : F.IsSnc) {q : ℕ} (L : Fin q → X.Modules)
    (hL : ∀ i, IsInvertible (L i)) {y : X} (hy : IsClosed ({y} : Set X)) :
    ∃ (U : X.affineOpens) (v : Fin n → Γ(X, U.1)), y ∈ U.1 ∧
      Etale (toAffineSpace f U.1 v) ∧
      Nonempty (∀ i, (pullback U.1.ι).obj (L i) ≅ unitObj U.1.toScheme) ∧
      ∃ c : {i : F.ι // y ∈ (F.component i).support} → Fin n,
        Function.Injective c ∧
        (∀ i, (F.component i.1).ideal U = Ideal.span {v (c i)}) ∧
        ∀ i, y ∉ (F.component i).support → (F.component i).comap U.1.ι = ⊤ := by
  obtain ⟨V, v, hyV, het, c, hcinj, hcomp, habsent⟩ :=
    Char0.exists_snc_etale_chart_at_closed f n hF hy
  obtain ⟨U, hyU, hUV, e⟩ := exists_common_frames_in L hL y V.1 hyV
  let w : Fin n → Γ(X, U.1) := fun j => X.presheaf.map (homOfLE hUV).op (v j)
  refine ⟨U, w, hyU, ?_, e, c, hcinj, ?_, ?_⟩
  · have : Etale (toAffineSpace f V.1 v) := het
    exact etale_toAffineSpace_restrict f hUV v
  · intro i
    change (F.component i.1).ideal U =
      Ideal.span {(X.presheaf.map (homOfLE hUV).op).hom (v (c i))}
    rw [← (F.component i.1).map_ideal hUV, hcomp i, Ideal.map_span, Set.image_singleton]
    rfl
  · intro i hi
    rw [← X.homOfLE_ι hUV, Scheme.IdealSheafData.comap_comp, habsent i hi,
      Scheme.IdealSheafData.comap_top]

/-- Empty WHOLE original row intersection produces an actually absent
original auxiliary member at the specified point. -/
theorem exists_absent_member {J : Type v} (A : J → X.IdealSheafData)
    (hA : (⨆ j, A j) = ⊤) (y : X) : ∃ j, y ∉ (A j).support := by
  classical
  by_contra! h
  have hy : y ∈ (⨆ j, A j).support := by
    rw [Scheme.IdealSheafData.support_iSup]
    exact TopologicalSpace.Closeds.mem_iInf.mpr h
  rw [hA, Scheme.IdealSheafData.support_top] at hy
  change False at hy
  exact hy

end EnvelopeProperty.Vanishing.NadelAdaptedChartMatching
