import EnvelopeProperty.AlgGeom.CyclicSectionSNCAffineOriginalCoefficient

/-! # Genuine original framed charts with one fixed global component index

The native original divisor family already has a finite index type. Its actual
chart equations extend by 1 on absent components, retaining every original
component label and the same original multiplicity function on the whole cover.
-/

noncomputable section
universe u
namespace EnvelopeProperty.CyclicSectionSNCUniformFramedCharts
open AlgebraicGeometry CategoryTheory Scheme.Modules Ideal
open CanonicalGeometry CyclicSectionGlobalCoverFrames
open scoped BigOperators Classical
variable {X : Scheme.{u}}

/-- Actual original component equations, extended by 1 on the original absent labels. -/
def uniformBranches {F : Scheme.DivisorFamily X} (x₀ : X) (U : X.affineOpens)
    {m : ℕ} (v : Fin m → Γ(X, U.1))
    (c : {i : F.ι // x₀ ∈ (F.component i).support} → Fin m) (i : F.ι) : Γ(X, U.1) :=
  if hi : x₀ ∈ (F.component i).support then v (c ⟨i, hi⟩) else 1

/-- Every SAME original component has its actual globally labelled whole affine generator. -/
theorem uniformBranches_ideal {F : Scheme.DivisorFamily X} (x₀ : X) (U : X.affineOpens)
    {m : ℕ} (v : Fin m → Γ(X, U.1))
    (c : {i : F.ι // x₀ ∈ (F.component i).support} → Fin m)
    (hcomp : ∀ i, (F.component i.1).ideal U = span {v (c i)})
    (habsent : ∀ i, x₀ ∉ (F.component i).support → (F.component i).comap U.1.ι = ⊤) :
    ∀ i, (F.component i).ideal U = span {uniformBranches x₀ U v c i} := by
  intro i
  by_cases hi : x₀ ∈ (F.component i).support
  · simpa only [uniformBranches, dif_pos hi] using hcomp ⟨i, hi⟩
  · simpa only [uniformBranches, dif_neg hi, Ideal.span_singleton_one] using
      ideal_eq_top_of_comap_ι_eq_top (F.component i) U (habsent i hi)

/-- The SAME actual original globally indexed chart sections are all nonzero. -/
theorem uniformBranches_ne_zero [IsIntegral X] {F : Scheme.DivisorFamily X}
    (x₀ : X) (U : X.affineOpens) {m : ℕ} (v : Fin m → Γ(X, U.1))
    (c : {i : F.ι // x₀ ∈ (F.component i).support} → Fin m)
    (hf : ∀ i, v (c i) ≠ 0) (y : X) (hy : y ∈ U.1) :
    ∀ i, uniformBranches x₀ U v c i ≠ 0 := by
  let : Nonempty U.1 := ⟨⟨y, hy⟩⟩
  intro i
  by_cases hi : x₀ ∈ (F.component i).support
  · simpa only [uniformBranches, dif_pos hi] using hf ⟨i, hi⟩
  · simpa only [uniformBranches, dif_neg hi] using (one_ne_zero : (1 : Γ(X, U.1)) ≠ 0)

/-- The original exponent function on the SAME original full family retains the exact active product. -/
theorem uniformBranches_prod {F : Scheme.DivisorFamily X} (a : F.ι → ℕ)
    (x₀ : X) (U : X.affineOpens) {m : ℕ} (v : Fin m → Γ(X, U.1))
    (c : {i : F.ι // x₀ ∈ (F.component i).support} → Fin m) :
    (∏ i : F.ι, uniformBranches x₀ U v c i ^ a i) = ∏ i, v (c i) ^ a i.1 := by
  have hmissing : (∏ i : {i : F.ι // x₀ ∉ (F.component i).support},
      uniformBranches x₀ U v c i.1 ^ a i.1) = 1 := by
    apply Finset.prod_eq_one
    intro i _
    simp only [uniformBranches, dif_neg i.2, one_pow]
  rw [← Fintype.prod_subtype_mul_prod_subtype (fun i : F.ι => x₀ ∈ (F.component i).support)
    (fun i => uniformBranches x₀ U v c i ^ a i), hmissing, mul_one]
  apply Finset.prod_congr rfl
  intro i _
  simp only [uniformBranches, dif_pos i.2]

variable (L : X.Modules) (hL : IsInvertible L) (n : ℕ)
  (s : unitObj X ⟶ bundleTensorPower L n)
local notation "J₀" => LineSectionZeroIdeal.zeroIdeal (bundleTensorPower L n)
  (TensorPowerBaseIdealGrading.tensorPower_isInvertible hL n) s

/-- Original geometry internally refines the SAME actual SNC chart to full-original-index framed equations. -/
theorem exists_uniform_framed_chart_in [IsIntegral X] {k : Type u} [Field k]
    (f : X ⟶ Spec (.of k)) [Smooth f] {F : Scheme.DivisorFamily X} (hF : F.IsSnc)
    (a : F.ι → ℕ) (hJF : J₀ = ∏ i, F.component i ^ a i)
    (x₀ : X) (V : X.affineOpens) {m : ℕ} (v : Fin m → Γ(X, V.1))
    (c : {i : F.ι // x₀ ∈ (F.component i).support} → Fin m)
    (hcomp : ∀ i, (F.component i.1).ideal V = span {v (c i)})
    (habsent : ∀ i, x₀ ∉ (F.component i).support → (F.component i).comap V.1.ι = ⊤)
    (y : X) (hy : y ∈ V.1) :
    ∃ (U : X.affineOpens) (_hyU : y ∈ U.1) (hUV : U.1 ≤ V.1),
      ∃ e : (pullback U.1.ι).obj L ≅ unitObj U.1.toScheme,
        ∃ (g : F.ι → Γ(X, U.1)) (b : (Γ(X, U.1))ˣ),
          g = uniformBranches x₀ U (fun j => X.presheaf.map (homOfLE hUV).op (v j)) c ∧
          (∀ i, (F.component i).ideal U = span {g i}) ∧ (∀ i, g i ≠ 0) ∧
          U.1.topIso.hom (sectionCoefficient L n s U.1.ι e) =
            (b : Γ(X, U.1)) * ∏ i : F.ι, g i ^ a i ∧
          U.1.topIso.hom (sectionCoefficient L n s U.1.ι e) ≠ 0 := by
  obtain ⟨U, hyU, hUV, e, b, hf, hs, hne⟩ :=
    CyclicSectionSNCAffineOriginalCoefficient.exists_affine_factorization L hL n s f hF
      a hJF x₀ V v c hcomp habsent y hy
  let w : Fin m → Γ(X, U.1) := fun j => X.presheaf.map (homOfLE hUV).op (v j)
  have hcompU (i : {i : F.ι // x₀ ∈ (F.component i).support}) :
      (F.component i.1).ideal U = span {w (c i)} := by
    change (F.component i.1).ideal U = span {(X.presheaf.map (homOfLE hUV).op).hom (v (c i))}
    rw [← (F.component i.1).map_ideal hUV, hcomp i, Ideal.map_span, Set.image_singleton]
    rfl
  have habsentU (i : F.ι) (hi : x₀ ∉ (F.component i).support) :
      (F.component i).comap U.1.ι = ⊤ := by
    rw [← X.homOfLE_ι hUV, Scheme.IdealSheafData.comap_comp, habsent i hi,
      Scheme.IdealSheafData.comap_top]
  refine ⟨U, hyU, hUV, e, uniformBranches x₀ U w c, b, rfl,
    uniformBranches_ideal x₀ U w c hcompU habsentU,
    uniformBranches_ne_zero x₀ U w c hf y hyU, ?_, hne⟩
  simpa only [uniformBranches_prod] using hs

/-- The SAME original SNC data and invertibility internally produce a genuine framed chart at EVERY point. -/
theorem exists_uniform_framed_chart_at [IsIntegral X] {k : Type u} [Field k] [PerfectField k]
    (f : X ⟶ Spec (.of k)) (d : ℕ) [SmoothOfRelativeDimension d f]
    {F : Scheme.DivisorFamily X} (hF : F.IsSnc)
    (a : F.ι → ℕ) (hJF : J₀ = ∏ i, F.component i ^ a i) (y : X) :
    ∃ U : X.affineOpens, y ∈ U.1 ∧
      ∃ e : (pullback U.1.ι).obj L ≅ unitObj U.1.toScheme,
        ∃ (g : F.ι → Γ(X, U.1)) (b : (Γ(X, U.1))ˣ),
          (∀ i, (F.component i).ideal U = span {g i}) ∧ (∀ i, g i ≠ 0) ∧
          U.1.topIso.hom (sectionCoefficient L n s U.1.ι e) =
            (b : Γ(X, U.1)) * ∏ i : F.ι, g i ^ a i ∧
          U.1.topIso.hom (sectionCoefficient L n s U.1.ι e) ≠ 0 := by
  let : Smooth f := SmoothOfRelativeDimension.smooth d f
  let : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace f
  obtain ⟨x₀, hx₀, _, hyx₀⟩ :=
    exists_isClosed_singleton_mem_specializes isClosed_univ (Set.mem_univ y)
  obtain ⟨V, v, hxV, _, c, _, hcomp, habsent⟩ :=
    Char0.exists_snc_etale_chart_at_closed f d hF hx₀
  have hyV := hyx₀.mem_open V.1.isOpen hxV
  obtain ⟨U, hyU, _, e, g, b, _, hI, hg, hs, hne⟩ :=
    exists_uniform_framed_chart_in L hL n s f hF a hJF x₀ V v c hcomp habsent y hyV
  exact ⟨U, hyU, e, g, b, hI, hg, hs, hne⟩

/-- Actual original geometry gives a FINITE genuine framed affine cover with one SAME original component index. -/
theorem exists_finite_uniform_framed_cover [IsIntegral X] {k : Type u} [Field k] [PerfectField k]
    (f : X ⟶ Spec (.of k)) (d : ℕ) [SmoothOfRelativeDimension d f] [CompactSpace X]
    {F : Scheme.DivisorFamily X} (hF : F.IsSnc)
    (a : F.ι → ℕ) (hJF : J₀ = ∏ i, F.component i ^ a i) :
    ∃ t : Finset X.affineOpens, (∀ y : X, ∃ U ∈ t, y ∈ U.1) ∧
      ∀ U ∈ t, Nonempty U.1 ∧ ∃ e : (pullback U.1.ι).obj L ≅ unitObj U.1.toScheme,
        ∃ (g : F.ι → Γ(X, U.1)) (b : (Γ(X, U.1))ˣ),
          (∀ i, (F.component i).ideal U = span {g i}) ∧ (∀ i, g i ≠ 0) ∧
          U.1.topIso.hom (sectionCoefficient L n s U.1.ι e) =
            (b : Γ(X, U.1)) * ∏ i : F.ι, g i ^ a i ∧
          U.1.topIso.hom (sectionCoefficient L n s U.1.ι e) ≠ 0 := by
  choose U hmem e g b hI hg hs hne using
    fun y : X => exists_uniform_framed_chart_at L hL n s f d hF a hJF y
  have hcover : (Set.univ : Set X) ⊆ ⋃ y : X, ((U y).1 : Set X) := by
    intro y _
    exact Set.mem_iUnion.mpr ⟨y, hmem y⟩
  obtain ⟨q, hq⟩ := isCompact_univ.elim_finite_subcover
    (fun y : X => ((U y).1 : Set X)) (fun y => (U y).1.isOpen) hcover
  refine ⟨q.image U, ?_, ?_⟩
  · intro y
    obtain ⟨z, hz⟩ := Set.mem_iUnion.mp (hq (Set.mem_univ y))
    obtain ⟨hzq, hyz⟩ := Set.mem_iUnion.mp hz
    exact ⟨U z, Finset.mem_image.mpr ⟨z, hzq, rfl⟩, hyz⟩
  · intro V hV
    obtain ⟨y, _, rfl⟩ := Finset.mem_image.mp hV
    exact ⟨⟨⟨y, hmem y⟩⟩, e y, g y, b y, hI y, hg y, hs y, hne y⟩

end EnvelopeProperty.CyclicSectionSNCUniformFramedCharts
