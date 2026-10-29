import EnvelopeProperty.Vanishing.NadelAdaptedChartMatchingCoefficients
import EnvelopeProperty.Vanishing.NadelMixedKummerDimensionGeometry

/-! # Actual original SNC generators give the WHOLE mixed Kummer source

The active set and distinct coordinate embedding are constructed from the
SAME original component labels and native SNC coordinate injection.
-/

open AlgebraicGeometry CategoryTheory
noncomputable section
universe u
namespace EnvelopeProperty.Vanishing.NadelAdaptedChartMatching.OriginalMixed
open NadelMixedKummer CyclicSectionSNCUniformFramedCharts
variable {X : Scheme.{u}} (F : X.DivisorFamily) (y : X) (U : X.affineOpens)
  {n q : ℕ} (v : Fin n → Γ(X, U.1))
  (c : {i : F.ι // y ∈ (F.component i).support} → Fin n)
  (hcinj : Function.Injective c) (ell : Fin q ↪ F.ι)

/-- The active SAME original labels at the specified actual original point. -/
def active : Set (Fin q) := {i | y ∈ (F.component (ell i)).support}

/-- The distinct original coordinate columns, internally constructed by
composing the SAME original label injection with native SNC coordinates. -/
def coordinates : active F y ell ↪ Fin n :=
  ⟨fun i => c ⟨ell i.1, i.2⟩, by
    intro i j hij
    apply Subtype.ext
    apply ell.injective
    exact congrArg Subtype.val (hcinj hij)⟩

/-- The WHOLE coefficient from an actual original SNC generator and its
actual original unit; absent components retain their complete unit equations. -/
def coefficient (w : Fin q → (Γ(X, U.1))ˣ) (i : Fin q) : Γ(X, U.1) :=
  (w i : Γ(X, U.1)) * uniformBranches y U v c (ell i)

/-- The actual original coefficient formula IS the precise mixed formula;
the active set and coordinate embedding are constructed, not supplied. -/
theorem coefficient_eq_mixed (w : Fin q → (Γ(X, U.1))ˣ) (i : Fin q) :
    coefficient F y U v c ell w i =
      mixedCoefficient v (active F y ell) (coordinates F y c hcinj ell) w i := by
  classical
  by_cases hi : y ∈ (F.component (ell i)).support
  · rw [coefficient, uniformBranches, dif_pos hi, mixedCoefficient,
      dif_pos (show i ∈ active F y ell from hi)]
    rfl
  · rw [coefficient, uniformBranches, dif_neg hi, mul_one, mixedCoefficient,
      dif_neg (show i ∉ active F y ell from hi)]

variable {k : Type u} [Field k] (f : X ⟶ Spec (.of k))
  (het : Etale (toAffineSpace f U.1 v)) (N : Fin q → ℕ)
  (w : Fin q → (Γ(X, U.1))ˣ) (hN : ∀ i, 0 < N i)
  (htame : ∀ i, IsUnit (N i : Γ(X, U.1)))

include hcinj het hN htame in
/-- The ACTUAL whole original-generator root quotient is smooth of the
SAME original dimension, from the native original etale coordinate map. -/
theorem smoothOfRelativeDimension :
    let _ := f.sectionsAlgebra U.1
    SmoothOfRelativeDimension n
      (Dimension.SmoothSourceDimension.structureMap (k := k) N (coefficient F y U v c ell w)) := by
  let _ := f.sectionsAlgebra U.1
  exact Dimension.SmoothSourceDimension.smoothOfRelativeDimension v
    ((etale_toAffineSpace_iff f U.2 v).mp het) N (coefficient F y U v c ell w)
    (active F y ell) (coordinates F y c hcinj ell) w
    (coefficient_eq_mixed F y U v c hcinj ell w) hN htame

include hcinj het hN htame in
/-- EVERY actual original source-prime localization is normal, on the
WHOLE possibly disconnected root quotient, with no domain hypothesis on it. -/
theorem localization_isIntegrallyClosed
    (p : Ideal (Ring N (coefficient F y U v c ell w))) [p.IsPrime] :
    IsIntegrallyClosed (Localization.AtPrime p) := by
  let _ := f.sectionsAlgebra U.1
  exact SmoothSource.localization_isIntegrallyClosed v
    ((etale_toAffineSpace_iff f U.2 v).mp het) N (coefficient F y U v c ell w)
    (active F y ell) (coordinates F y c hcinj ell) w
    (coefficient_eq_mixed F y U v c hcinj ell w) hN htame p

end EnvelopeProperty.Vanishing.NadelAdaptedChartMatching.OriginalMixed
