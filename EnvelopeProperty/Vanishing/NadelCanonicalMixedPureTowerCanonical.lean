import EnvelopeProperty.Vanishing.NadelCanonicalMixedActiveJacobian
import EnvelopeProperty.Vanishing.NadelCanonicalMixedUnitCanonical

/-! # Actual canonical duality on the entire pure active/inactive tower -/

noncomputable section
universe u
namespace EnvelopeProperty.Vanishing.NadelCanonicalMixed.Split

open CategoryTheory ModuleCat CanonicalGeometry NadelFiniteDualityTower NadelAdaptedChartMatching
variable {k R : Type u} [CommRing k] [Nontrivial k] [CommRing R] [Algebra k R] [Nontrivial R]
    {n q : ℕ} (N : Fin q → ℕ) (I : Set (Fin q)) (σ : I ↪ Fin n) (hN : ∀ i, 0 < N i)
    (a : MvPolynomial (Fin n) k →ₐ[k] R) (ha : a.toRingHom.FormallyEtale)
    (htame : ∀ i, IsUnit (N i : R))
attribute [local instance] Classical.propDecidable
local notation "x" => originalCoordinates a
local notation "h" => pureCoefficient x I σ
local notation "A₀" => ActiveRing N I h
local notation "B₀" => SplitRing N I h

include hN in
/-- The SAME original active monic degrees remain positive, including each actual degree-one unused row. -/
theorem activeDegree_positive (i : Fin q) : 0 < activeDegree N I i := by
  unfold activeDegree
  split_ifs with hh
  · exact hN i
  · exact Nat.zero_lt_one

include hN in
/-- The complete inactive unit-root layer retains each SAME positive original degree. -/
theorem inactiveDegree_positive (i : Fin q) : 0 < inactiveDegree N I i := by
  unfold inactiveDegree
  split_ifs with hh
  · exact Nat.zero_lt_one
  · exact hN i

omit [Nontrivial k] [Nontrivial R] in
include htame in
/-- Every SAME original inactive degree is genuinely tame over the actual active quotient. -/
theorem inactiveDegree_tame (i : Fin q) : IsUnit ((inactiveDegree N I i : ℕ) : A₀) := by
  unfold inactiveDegree
  split_ifs with hh
  · simpa only [Nat.cast_one] using (isUnit_one : IsUnit (1 : A₀))
  · simpa only [map_natCast] using (htame i).map (algebraMap R A₀)

omit [Nontrivial k] in
include hN in
/-- The whole actual active quotient is nonzero, by the original simultaneous monic tower. -/
theorem activeRing_nontrivial : Nontrivial A₀ := by
  let : Nontrivial (VaryingFamily.Ring (activeDegree N I) h) :=
    independentRootRing_nontrivial (VaryingFamily.degree (activeDegree N I))
      (VaryingFamily.coefficient h) q
  exact (VaryingFinite.ringEquiv (activeDegree N I) h (activeDegree_positive N I hN)).toEquiv.nontrivial

/-- Actual étale Kähler base change constructs the genuine top differential frame on the entire inactive layer. -/
def splitDifferentialBasis : Module.Basis (Fin n) B₀ (KaehlerDifferential k B₀) :=
  unitCoverDifferentialBasis (inactiveDegree N I) (fun _ => (1 : A₀ˣ))
    (inactiveDegree_positive N I hN) (inactiveDegree_tame N I σ a htame)
      (activeDifferentialBasis N I σ hN a ha)

/-- Native right-adjoint composition gives genuine canonical duality on the WHOLE active and inactive original layers together. -/
def splitCanonicalIso : ModuleCat.of B₀ (affineCanonicalModule k B₀ n) ≅
    (coextendScalars (coefficientHom N I h)).obj (ModuleCat.of R (affineCanonicalModule k R n)) := by
  let : Nontrivial A₀ := activeRing_nontrivial N I σ hN a
  exact unitCoverCanonicalIso (inactiveDegree N I) (fun _ => (1 : A₀ˣ))
      (inactiveDegree_positive N I hN) (inactiveDegree_tame N I σ a htame)
        (activeDifferentialBasis N I σ hN a ha) ≪≫
    (coextendScalars (algebraMap A₀ B₀)).mapIso (activeCanonicalIso N I σ hN a ha) ≪≫
      (coextensionCompIso (algebraMap R A₀) (algebraMap A₀ B₀)).app
        (ModuleCat.of R (affineCanonicalModule k R n))

/-- The whole native pure-tower canonical counit retains its actual original composite coefficient map. -/
def splitCanonicalCounit :
    (restrictScalars (coefficientHom N I h)).obj (ModuleCat.of B₀ (affineCanonicalModule k B₀ n)) ⟶
      ModuleCat.of R (affineCanonicalModule k R n) :=
  (restrictScalars (coefficientHom N I h)).map (splitCanonicalIso N I σ hN a ha htame).hom ≫
    (restrictCoextendScalarsAdj (coefficientHom N I h)).counit.app
      (ModuleCat.of R (affineCanonicalModule k R n))

/-- The actual entire pure canonical trace is precisely whole inactive-unit trace followed by the original active canonical counit. -/
theorem splitCanonicalCounit_composition (w : affineCanonicalModule k B₀ n) :
    splitCanonicalCounit N I σ hN a ha htame w =
      letI : Nontrivial A₀ := activeRing_nontrivial N I σ hN a
      activeCanonicalCounit N I σ hN a ha
        (unitCoverCanonicalCounit (inactiveDegree N I) (fun _ => (1 : A₀ˣ))
          (inactiveDegree_positive N I hN) (inactiveDegree_tame N I σ a htame)
            (activeDifferentialBasis N I σ hN a ha) w) := by
  let : Nontrivial A₀ := activeRing_nontrivial N I σ hN a
  change (coextensionCompIso (algebraMap R A₀) (algebraMap A₀ B₀)).hom.app
    (ModuleCat.of R (affineCanonicalModule k R n))
      (((coextendScalars (algebraMap A₀ B₀)).map (activeCanonicalIso N I σ hN a ha).hom)
        ((unitCoverCanonicalIso (inactiveDegree N I) (fun _ => (1 : A₀ˣ))
          (inactiveDegree_positive N I hN) (inactiveDegree_tame N I σ a htame)
            (activeDifferentialBasis N I σ hN a ha)).hom w)) (1 : B₀) = _
  rw [coextensionCompIso_hom_apply]
  rfl

end EnvelopeProperty.Vanishing.NadelCanonicalMixed.Split
