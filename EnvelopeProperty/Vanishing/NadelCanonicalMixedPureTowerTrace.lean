import EnvelopeProperty.Vanishing.NadelCanonicalMixedPureTowerCanonical

/-! # Whole intrinsic canonical trace on all original pure active/inactive layers

The base R is the coefficient ring of this original pure algebra. No trace
through a separate auxiliary faithfully-flat coefficient cover is inserted.
-/

noncomputable section
universe u
namespace EnvelopeProperty.Vanishing.NadelCanonicalMixed.Split

open CategoryTheory ModuleCat CanonicalGeometry NadelCanonicalBaseChange NadelAdaptedChartMatching
open NadelFiniteDualityTower NadelKummerCover
variable {k R : Type u} [CommRing k] [Nontrivial k] [CommRing R] [Algebra k R] [Nontrivial R]
    {n q : ℕ} (N : Fin q → ℕ) (I : Set (Fin q)) (σ : I ↪ Fin n) (hN : ∀ i, 0 < N i)
    (a : MvPolynomial (Fin n) k →ₐ[k] R) (ha : a.toRingHom.FormallyEtale)
    (htame : ∀ i, IsUnit (N i : R))
local notation "x" => originalCoordinates a
local notation "h" => pureCoefficient x I σ
local notation "A₀" => ActiveRing N I h
local notation "B₀" => SplitRing N I h

omit [Nontrivial k] [Nontrivial R] in
/-- The genuine exterior pullbacks through the SAME original coefficient tower compose on the actual base generator. -/
theorem splitTopPullback_comp_generator :
    topPullback (R := k) (A := A₀) (B := B₀) n
      (topPullback (R := k) (A := R) (B := A₀) n (affineCanonicalGenerator (baseDifferentialBasis a ha))) =
    topPullback (R := k) (A := R) (B := B₀) n (affineCanonicalGenerator (baseDifferentialBasis a ha)) := by
  have hA : topPullback (R := k) (A := R) (B := A₀) n
      (affineCanonicalGenerator (baseDifferentialBasis a ha)) =
      exteriorPower.ιMulti A₀ n (fun j => KaehlerDifferential.D k A₀ (algebraMap R A₀ (x j))) := by
    rw [baseGenerator_eq_wedge, topPullback_wedge]
    congr 1
    funext j
    exact KaehlerDifferential.map_D k k R A₀ (x j)
  have hB : topPullback (R := k) (A := R) (B := B₀) n
      (affineCanonicalGenerator (baseDifferentialBasis a ha)) =
      exteriorPower.ιMulti B₀ n (fun j => KaehlerDifferential.D k B₀ (algebraMap R B₀ (x j))) := by
    rw [baseGenerator_eq_wedge, topPullback_wedge]
    congr 1
    funext j
    exact KaehlerDifferential.map_D k k R B₀ (x j)
  rw [hA, topPullback_wedge, hB]
  congr 1
  funext j
  rw [KaehlerDifferential.map_D]
  exact congrArg (KaehlerDifferential.D k B₀) (IsScalarTower.algebraMap_apply R A₀ B₀ (x j)).symm

omit [Nontrivial k] [Nontrivial R] in
include ha in
/-- Genuine exterior pullbacks compose on EVERY original base top form, with the true original coefficient paths. -/
theorem splitTopPullback_comp (w : affineCanonicalModule k R n) :
    topPullback (R := k) (A := A₀) (B := B₀) n
      (topPullback (R := k) (A := R) (B := A₀) n w) =
    topPullback (R := k) (A := R) (B := B₀) n w := by
  rw [affineCanonical_eq_smul_generator (baseDifferentialBasis a ha) w]
  simp only [map_smulₛₗ]
  rw [splitTopPullback_comp_generator N I σ a ha]
  exact congrArg (fun r : B₀ => r • topPullback (R := k) (A := R) (B := B₀) n
    (affineCanonicalGenerator (baseDifferentialBasis a ha)))
      (IsScalarTower.algebraMap_apply R A₀ B₀ _).symm

omit [Nontrivial k] in
include hN in
/-- Native algebra trace on the whole original pure tower is the genuine trace of the entire inactive trace. -/
theorem splitTrace_trace (c : B₀) :
    Algebra.trace R A₀ (Algebra.trace A₀ B₀ c) = Algebra.trace R B₀ c := by
  let : Nontrivial A₀ := activeRing_nontrivial N I σ hN a
  let : Finite (Tower.basisIndex (VaryingFamily.degree (activeDegree N I)) q) :=
    Tower.basisIndex_finite (VaryingFamily.degree (activeDegree N I)) q
  let : Finite (Tower.basisIndex (VaryingFamily.degree (inactiveDegree N I)) q) :=
    Tower.basisIndex_finite (VaryingFamily.degree (inactiveDegree N I)) q
  exact Algebra.trace_trace_of_basis
    (VaryingFinite.basis (activeDegree N I) h (activeDegree_positive N I hN))
    (VaryingFinite.basis (inactiveDegree N I) (fun _ => (1 : A₀)) (inactiveDegree_positive N I hN)) c

/-- Whole pure canonical trace is intrinsically normalized on EVERY genuine original base top form, retaining all original factors. -/
theorem splitCanonicalCounit_pulled_topform (c : B₀) (w : affineCanonicalModule k R n) :
    splitCanonicalCounit N I σ hN a ha htame (c • topPullback (R := k) (A := R) (B := B₀) n w) =
      Algebra.trace R B₀ c • w := by
  let : Nontrivial A₀ := activeRing_nontrivial N I σ hN a
  let τ := unitCoverCanonicalCounit (inactiveDegree N I) (fun _ => (1 : A₀ˣ))
    (inactiveDegree_positive N I hN) (inactiveDegree_tame N I σ a htame)
      (activeDifferentialBasis N I σ hN a ha)
  have hunit : τ (c • topPullback (R := k) (A := R) (B := B₀) n w) =
      Algebra.trace A₀ B₀ c • topPullback (R := k) (A := R) (B := A₀) n w := by
    have hc := congrArg (fun z : affineCanonicalModule k B₀ n => τ (c • z))
      (splitTopPullback_comp N I σ a ha w).symm
    exact hc.trans (unitCoverCanonicalCounit_pulled_topform (inactiveDegree N I) (fun _ => (1 : A₀ˣ))
      (inactiveDegree_positive N I hN) (inactiveDegree_tame N I σ a htame)
        (activeDifferentialBasis N I σ hN a ha) c _)
  calc
    _ = activeCanonicalCounit N I σ hN a ha
        (τ (c • topPullback (R := k) (A := R) (B := B₀) n w)) :=
      splitCanonicalCounit_composition N I σ hN a ha htame _
    _ = activeCanonicalCounit N I σ hN a ha
        (Algebra.trace A₀ B₀ c • topPullback (R := k) (A := R) (B := A₀) n w) :=
      congrArg (fun z : affineCanonicalModule k A₀ n => activeCanonicalCounit N I σ hN a ha z) hunit
    _ = Algebra.trace R A₀ (Algebra.trace A₀ B₀ c) • w :=
      activeCanonicalCounit_pulled_topform N I σ hN a ha _ w
    _ = _ := congrArg (fun r : R => r • w) (splitTrace_trace N I σ hN a c)

end EnvelopeProperty.Vanishing.NadelCanonicalMixed.Split
