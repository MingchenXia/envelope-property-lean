import EnvelopeProperty.Char0.SNCFactors
import EnvelopeProperty.Char0.SNCCharts

/-! # Actual SNC branch equations in the original scheme stalks

Actual affine component equations give prime, pairwise nonassociated retained
germs and unit removed germs in the SAME original stalk. The conclusions are
derived from the original SNC family and actual regular stalk parameters.
The existing finite adapted cover is enriched with these proved conditions.
-/

noncomputable section
universe u v
namespace EnvelopeProperty.CyclicSectionSNCStalkBranches
open AlgebraicGeometry CategoryTheory IsLocalRing Ideal
open scoped Classical
variable {X : Scheme.{u}}

private theorem stalkIdeal_eq_span_germ (I : X.IdealSheafData) (U : X.affineOpens)
    (g : Γ(X, U.1)) (hI : I.ideal U = span {g}) (x : X) (hx : x ∈ U.1) :
    I.stalkIdeal x = span {X.presheaf.germ U.1 x hx g} := by
  rw [Scheme.IdealSheafData.stalkIdeal_eq_map_germ I U hx, hI,
    Ideal.map_span, Set.image_singleton]

/-- Actual original affine branch germs are associated to distinct actual parameters at this point. -/
theorem exists_stalk_parameters_associated {k : Type u} [Field k]
    (f : X ⟶ Spec (.of k)) [Smooth f] {F : Scheme.DivisorFamily X} (hF : F.IsSnc)
    {J : Type v} (U : X.affineOpens) (b : J → F.ι) (hb : Function.Injective b)
    (g : J → Γ(X, U.1)) (hgen : ∀ j, (F.component (b j)).ideal U = span {g j})
    (x : X) (hx : x ∈ U.1) :
    ∃ (m : ℕ) (z : Fin m → X.presheaf.stalk x), IsRegularSystemOfParameters z ∧
      ∃ d : {j : J // x ∈ (F.component (b j)).support} → Fin m,
        Function.Injective d ∧ ∀ j,
          Associated (X.presheaf.germ U.1 x hx (g j.1)) (z (d j)) := by
  have := isRegularLocalRing_stalk f x
  obtain ⟨m, z, hz, c, hcinj, hc⟩ := hF.2 x
  let d : {j : J // x ∈ (F.component (b j)).support} → Fin m :=
    fun j => c ⟨b j.1, j.2⟩
  refine ⟨m, z, hz, d, ?_, ?_⟩
  · intro i j hij
    apply Subtype.ext
    apply hb
    exact congrArg Subtype.val (hcinj hij)
  · intro j
    apply Ideal.span_singleton_eq_span_singleton.mp
    exact (stalkIdeal_eq_span_germ (F.component (b j.1)) U (g j.1) (hgen j.1) x hx).symm.trans
      (hc ⟨b j.1, j.2⟩)

/-- A retained SAME original affine branch equation has a prime actual germ. -/
theorem prime_germ_of_mem {k : Type u} [Field k]
    (f : X ⟶ Spec (.of k)) [Smooth f] {F : Scheme.DivisorFamily X} (hF : F.IsSnc)
    {J : Type v} (U : X.affineOpens) (b : J → F.ι) (hb : Function.Injective b)
    (g : J → Γ(X, U.1)) (hgen : ∀ j, (F.component (b j)).ideal U = span {g j})
    (x : X) (hx : x ∈ U.1) (j : {j : J // x ∈ (F.component (b j)).support}) :
    Prime (X.presheaf.germ U.1 x hx (g j.1)) := by
  have := isRegularLocalRing_stalk f x
  obtain ⟨m, z, hz, d, _, ha⟩ := exists_stalk_parameters_associated f hF U b hb g hgen x hx
  exact (ha j).symm.prime (prime_of_parameters hz.1.symm hz.2 (d j))

/-- Distinct retained original component labels give nonassociated actual original germs. -/
theorem pairwise_not_associated_germs {k : Type u} [Field k]
    (f : X ⟶ Spec (.of k)) [Smooth f] {F : Scheme.DivisorFamily X} (hF : F.IsSnc)
    {J : Type v} (U : X.affineOpens) (b : J → F.ι) (hb : Function.Injective b)
    (g : J → Γ(X, U.1)) (hgen : ∀ j, (F.component (b j)).ideal U = span {g j})
    (x : X) (hx : x ∈ U.1) :
    Pairwise (fun i j : {j : J // x ∈ (F.component (b j)).support} =>
      ¬ Associated (X.presheaf.germ U.1 x hx (g i.1)) (X.presheaf.germ U.1 x hx (g j.1))) := by
  have := isRegularLocalRing_stalk f x
  obtain ⟨m, z, hz, d, hdinj, ha⟩ := exists_stalk_parameters_associated f hF U b hb g hgen x hx
  intro i j hij hassoc
  have hdij : d i ≠ d j := fun h => hij (hdinj h)
  exact not_dvd_of_ne hz.1.symm hz.2 hdij
    (((ha i).symm.trans hassoc).trans (ha j)).dvd

/-- An actual affine generator of an original component absent at the point has an actual unit germ. -/
theorem isUnit_germ_of_notMem_support (I : X.IdealSheafData) (U : X.affineOpens)
    (g : Γ(X, U.1)) (hI : I.ideal U = span {g}) (x : X) (hx : x ∈ U.1)
    (habsent : x ∉ I.support) : IsUnit (X.presheaf.germ U.1 x hx g) := by
  apply Ideal.span_singleton_eq_top.mp
  rw [← stalkIdeal_eq_span_germ I U g hI x hx,
    Scheme.IdealSheafData.stalkIdeal_eq_top_of_notMem_support I habsent]

/-- All actual original stalk branch conditions follow internally from the geometric SNC data. -/
theorem stalk_branches {k : Type u} [Field k]
    (f : X ⟶ Spec (.of k)) [Smooth f] {F : Scheme.DivisorFamily X} (hF : F.IsSnc)
    {J : Type v} (U : X.affineOpens) (b : J → F.ι) (hb : Function.Injective b)
    (g : J → Γ(X, U.1)) (hgen : ∀ j, (F.component (b j)).ideal U = span {g j})
    (x : X) (hx : x ∈ U.1) :
    (∀ j : {j : J // x ∈ (F.component (b j)).support},
      Prime (X.presheaf.germ U.1 x hx (g j.1))) ∧
    Pairwise (fun i j : {j : J // x ∈ (F.component (b j)).support} =>
      ¬ Associated (X.presheaf.germ U.1 x hx (g i.1)) (X.presheaf.germ U.1 x hx (g j.1))) ∧
    (∀ j, x ∉ (F.component (b j)).support → IsUnit (X.presheaf.germ U.1 x hx (g j))) ∧
    ∀ j, X.presheaf.germ U.1 x hx (g j) ≠ 0 := by
  have := isRegularLocalRing_stalk f x
  have hp := prime_germ_of_mem f hF U b hb g hgen x hx
  refine ⟨hp, pairwise_not_associated_germs f hF U b hb g hgen x hx, ?_, ?_⟩
  · intro j hj
    exact isUnit_germ_of_notMem_support (F.component (b j)) U (g j) (hgen j) x hx hj
  · intro j
    by_cases hj : x ∈ (F.component (b j)).support
    · exact (hp ⟨j, hj⟩).ne_zero
    · exact (isUnit_germ_of_notMem_support (F.component (b j)) U (g j) (hgen j) x hx hj).ne_zero

/-- The SAME existing finite actual adapted SNC cover has all branch conditions at EVERY chart point. -/
theorem exists_finite_snc_etale_cover_stalk_branches {k : Type u} [Field k] [PerfectField k]
    (f : X ⟶ Spec (.of k)) (n : ℕ) [SmoothOfRelativeDimension n f] [CompactSpace X]
    {F : Scheme.DivisorFamily X} (hF : F.IsSnc) :
    ∃ t : Finset X.affineOpens, (∀ y : X, ∃ U ∈ t, y ∈ U.1) ∧
      ∀ U ∈ t, ∃ (x : X) (v : Fin n → Γ(X, U.1)), IsClosed ({x} : Set X) ∧
        x ∈ U.1 ∧ Etale (toAffineSpace f U.1 v) ∧
        ∃ c : {i : F.ι // x ∈ (F.component i).support} → Fin n,
          Function.Injective c ∧
          (∀ i, (F.component i.1).ideal U = span {v (c i)}) ∧
          (∀ i, x ∉ (F.component i).support → (F.component i).comap U.1.ι = ⊤) ∧
          ∀ (y : X) (hy : y ∈ U.1),
            (∀ i : {i : {i : F.ι // x ∈ (F.component i).support} //
                y ∈ (F.component i.1).support},
              Prime (X.presheaf.germ U.1 y hy (v (c i.1)))) ∧
            Pairwise (fun i j : {i : {i : F.ι // x ∈ (F.component i).support} //
                y ∈ (F.component i.1).support} =>
              ¬ Associated (X.presheaf.germ U.1 y hy (v (c i.1)))
                (X.presheaf.germ U.1 y hy (v (c j.1)))) ∧
            (∀ i : {i : F.ι // x ∈ (F.component i).support},
              y ∉ (F.component i.1).support → IsUnit (X.presheaf.germ U.1 y hy (v (c i)))) ∧
            ∀ i : {i : F.ι // x ∈ (F.component i).support},
              X.presheaf.germ U.1 y hy (v (c i)) ≠ 0 := by
  have : Smooth f := SmoothOfRelativeDimension.smooth n f
  obtain ⟨t, ht, hcharts⟩ := Char0.exists_finite_snc_etale_cover f n hF
  refine ⟨t, ht, ?_⟩
  intro U hU
  obtain ⟨x, v, hx, hxU, het, c, hcinj, hgen, habsent⟩ := hcharts U hU
  refine ⟨x, v, hx, hxU, het, c, hcinj, hgen, habsent, ?_⟩
  intro y hy
  exact stalk_branches f hF U (fun i : {i : F.ι // x ∈ (F.component i).support} => i.1)
    Subtype.val_injective (fun i => v (c i)) hgen y hy

end EnvelopeProperty.CyclicSectionSNCStalkBranches
