import EnvelopeProperty.Vanishing.NadelGlobalCanonicalTraceBoundedRootDifferential
import EnvelopeProperty.Vanishing.NadelCanonicalTensorBaseChange

/-! # The actual whole mixed top differential has every branch-root factor

The SNC injection selects distinct positions of the original coordinate
wedge.  Each factor comes from the original variable-unit root equation.
-/
noncomputable section
namespace EnvelopeProperty.Vanishing.NadelGlobalCanonicalTrace
open AlgebraicGeometry CategoryTheory CanonicalGeometry
open NadelMixedKummer NadelCanonicalMixed NadelCanonicalBaseChange
universe u
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem nativeAlternatingFactor
    {R M V : Type u} {E J : Type} [CommRing R] [AddCommGroup M] [Module R M]
    [AddCommGroup V] [Module R V] [Fintype E] [Fintype J]
    (f : M [⋀^J]→ₗ[R] V) (e : E ↪ J) (v : J → M) (r : E → R)
    (h : ∀ i, ∃ w : M, v (e i) = r i • w) :
    ∃ w : V, f v = (∏ i, r i) • w := by
  classical
  choose w hw using h
  let c : J → R := fun j => if hj : ∃ i, e i = j then r (Classical.choose hj) else 1
  let z : J → M := fun j => if hj : ∃ i, e i = j then w (Classical.choose hj) else v j
  have hc (i : E) : c (e i) = r i := by
    have hi : ∃ a, e a = e i := ⟨i, rfl⟩
    dsimp only [c]
    rw [dif_pos hi]
    exact congrArg r (e.injective (Classical.choose_spec hi))
  have hv : v = fun j => c j • z j := by
    funext j
    by_cases hj : ∃ i, e i = j
    · dsimp only [c, z]
      rw [dif_pos hj, dif_pos hj]
      exact (congrArg v (Classical.choose_spec hj)).symm.trans (hw (Classical.choose hj))
    · simp only [c, z, dif_neg hj, one_smul]
  have hp : (∏ j, c j) = ∏ i, r i := by
    let s : Finset J := Finset.univ.image e
    have hs : (∏ j ∈ s, c j) = ∏ j, c j := by
      apply Finset.prod_subset (Finset.subset_univ s)
      intro j _ hj
      have hn : ¬∃ i, e i = j := by
        rintro ⟨i, hi⟩
        exact hj (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, hi⟩)
      exact dif_neg hn
    calc
      _ = ∏ j ∈ s, c j := hs.symm
      _ = ∏ i, c (e i) := by
        dsimp only [s]
        rw [Finset.prod_image]
        intro i _ j _ hij
        exact e.injective hij
      _ = ∏ i, r i := Finset.prod_congr rfl (fun i _ => hc i)
  refine ⟨f z, ?_⟩
  calc
    f v = f (fun j => c j • z j) := congrArg f hv
    _ = (∏ j, c j) • f z := AlternatingMap.map_smul_univ f c z
    _ = (∏ i, r i) • f z := congrArg (fun a : R => a • f z) hp

variable {k A : Type u} [Field k] [CommRing A] [Algebra k A]
    {n q : ℕ} (x : Fin n → A) (N : Fin q → ℕ) (I : Set (Fin q))
    (σ : I ↪ Fin n) (u : Fin q → Aˣ)
attribute [local instance] Classical.propDecidable
local notation "Bₘ" => mixedRing x N I σ u

/-- The SAME whole ordinary pulled coordinate top form is divisible by
ALL original active root powers, simultaneously.  The producer uses the
actual root equations and SNC injection, with no bounded-image premise. -/
theorem mixedCoordinateTopDifferential_factor (hN : ∀ i, 0 < N i) :
    ∃ w : affineCanonicalModule k Bₘ n,
      topPullback (R := k) (A := A) (B := Bₘ) n
        (exteriorPower.ιMulti A n (fun j => KaehlerDifferential.D k A (x j))) =
      (∏ i : I, root N (mixedCoefficient x I σ u) i.1 ^ (N i.1 - 1)) • w := by
  classical
  rw [topPullback_wedge]
  simp only [KaehlerDifferential.map_D]
  apply nativeAlternatingFactor (exteriorPower.ιMulti Bₘ n) σ
    (fun j => KaehlerDifferential.D k Bₘ (algebraMap A Bₘ (x j)))
    (fun i : I => root N (mixedCoefficient x I σ u) i.1 ^ (N i.1 - 1))
  intro i
  exact ⟨_, mixedBranchDifferential_factor x N I σ u hN i⟩

end EnvelopeProperty.Vanishing.NadelGlobalCanonicalTrace
