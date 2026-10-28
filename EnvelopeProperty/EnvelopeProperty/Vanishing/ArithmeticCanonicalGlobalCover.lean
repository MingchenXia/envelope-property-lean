import EnvelopeProperty.Vanishing.ArithmeticCanonicalGlobalAffineBaseChange

/-! # Actual standard-smooth arithmetic charts and their fibre comparisons

The covering spectra and original structural maps are chosen from actual
relative smoothness. Their native categorical fibre differentials are
proved invertible internally; no chart or comparison certificate is input.
-/

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

noncomputable section
universe u

namespace EnvelopeProperty.Vanishing.ArithmeticCanonicalGlobalCover

open ArithmeticCanonicalGlobal ArithmeticCanonicalGlobalFrames
open ArithmeticCanonicalGlobalBaseChange ArithmeticCanonicalGlobalAffineBaseChange

set_option backward.isDefEq.respectTransparency false

variable {R : Type u} [CommRing R] {X : Scheme.{u}} (f : X ⟶ Spec (.of R))
    (n : ℕ) [SmoothOfRelativeDimension n f]

def chartScheme (x : X) : Scheme.{u} :=
  Spec (.of Γ(X, (selectedChart f n x).val))

def chartMap (x : X) : chartScheme f n x ⟶ X :=
  (selectedChart f n x).property.1.fromSpec

instance chartScheme_isAffine (x : X) : IsAffine (chartScheme f n x) := by
  dsimp [chartScheme]
  infer_instance

instance chartMap_isOpenImmersion (x : X) : IsOpenImmersion (chartMap f n x) := by
  exact (selectedChart f n x).property.1.isOpenImmersion_fromSpec

theorem chartMap_opensRange (x : X) :
    (chartMap f n x).opensRange = (selectedChart f n x).val :=
  (selectedChart f n x).property.1.opensRange_fromSpec

theorem chartMap_covers (x : X) : ∃ y, chartMap f n x y = x := by
  have hx : x ∈ (chartMap f n x).opensRange := by
    rw [chartMap_opensRange]
    exact (selectedChart f n x).property.2.1
  exact hx

/-- The actual covering spectra of the original arithmetic family. -/
def chartCover : X.OpenCover :=
  Scheme.Cover.mkOfCovers X (chartScheme f n) (chartMap f n)
    (fun x => ⟨x, chartMap_covers f n x⟩)

theorem chartCover_iSup_opensRange :
    ⨆ x, (chartMap f n x).opensRange = ⊤ :=
  (chartCover f n).iSup_opensRange

/-- Each derived covering spectrum retains the original whole structural
triangle and the actual scalar algebra on its original affine open. -/
theorem chartStructure_eq (x : X) :
    letI : Algebra R Γ(X, (selectedChart f n x).val) :=
      ((relativeConstants f).app (.op (selectedChart f n x).val)).hom.toAlgebra
    chartMap f n x ≫ f = affineStructure R (.of Γ(X, (selectedChart f n x).val)) :=
  affineChartStructure f (selectedChart f n x).property.1

omit [SmoothOfRelativeDimension n f] in
private theorem affineChartWholeStandardSmooth
    {V : X.Opens} (hV : IsAffineOpen V)
    (hs : RingHom.IsStandardSmoothOfRelativeDimension n
      ((relativeConstants f).app (.op V)).hom) :
    RingHom.IsStandardSmoothOfRelativeDimension n
      ((relativeConstants (hV.fromSpec ≫ f)).app (.op ⊤)).hom := by
  let A : CommRingCat.{u} := .of Γ(X, V)
  let : Algebra R A := ((relativeConstants f).app (.op V)).hom.toAlgebra
  let : Algebra.IsStandardSmoothOfRelativeDimension n R A := hs
  let Q : (Spec A ⟶ Spec (.of R)) → Prop := fun h =>
    RingHom.IsStandardSmoothOfRelativeDimension n
      ((relativeConstants h).app (.op ⊤)).hom
  exact Eq.mp (congrArg Q (affineChartStructure f hV).symm)
    (affineSpecStandardSmooth R A n)

/-- Actual relative smoothness of the original family derives invertibility
of its actual canonical base-change differential on every covering spectrum. -/
theorem chartCanonicalPullback_isIso (S : Type u) [CommRing S] [Algebra R S] (x : X) :
    IsIso (exteriorPullbackMap S (chartMap f n x ≫ f) n) := by
  have h := AlgebraicGeometry.smoothOfRelativeDimension_comp
    (n := 0) (m := n) (chartMap f n x) f
  let : SmoothOfRelativeDimension n (chartMap f n x ≫ f) := by
    simpa only [Nat.zero_add] using h
  exact affineCanonicalPullback_isIso S (chartMap f n x ≫ f) n
    (affineChartWholeStandardSmooth f n (selectedChart f n x).property.1
      (selectedChart f n x).property.2.2)

/-- The actual native pullback of the derived affine cover covers the same
whole categorical arithmetic fibre. -/
def fiberChartCover (S : Type u) [CommRing S] [Algebra R S] :
    (fiberScheme S f).OpenCover :=
  (chartCover f n).pullbackCoverOfLeft f (baseMap (R := R) S)

theorem fiberChartCover_iSup_opensRange (S : Type u) [CommRing S] [Algebra R S] :
    ⨆ x, ((fiberChartCover f n S).f x).opensRange = ⊤ :=
  (fiberChartCover f n S).iSup_opensRange

end EnvelopeProperty.Vanishing.ArithmeticCanonicalGlobalCover
