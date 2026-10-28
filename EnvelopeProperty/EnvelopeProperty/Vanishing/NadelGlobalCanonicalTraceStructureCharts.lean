import EnvelopeProperty.Vanishing.NadelGlobalCanonicalTraceStructureDegree

/-! # The original whole adapted cover produces its actual free atlas

The chart data contain a genuine whole-algebra basis and the actual
normalization isomorphism over the base. No trace or overlap certificate
is a field. Every original point receives such data internally.
-/
noncomputable section
namespace EnvelopeProperty.Vanishing.NadelGlobalStructureTrace
open AlgebraicGeometry CategoryTheory Scheme.Modules
open CanonicalGeometry NadelAuxiliaryMulticover NadelGlobalNormalization
open NadelAdaptedChartMatching NadelGlobalAdaptedModel NadelGlobalAdaptedRoots
universe u
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- A genuine complete affine chart of the SAME original projection,
with actual basis data and actual scalar projection, but no trace map. -/
structure WholeFreeChart {X Y : Scheme.{u}} (π : Y ⟶ X) (D : ℕ) where
  base : X.affineOpens
  coeff : CommRingCat.{u}
  algebra : Algebra Γ(X, base.1) coeff
  basis : let _ := algebra; Module.Basis (Fin D) Γ(X, base.1) coeff
  comparison : Spec coeff ≅ (π ⁻¹ᵁ base.1).toScheme
  overBase : let _ := algebra
    comparison.hom ≫ (π ⁻¹ᵁ base.1).ι ≫ π =
      Spec.map (CommRingCat.ofHom (algebraMap Γ(X, base.1) coeff)) ≫ base.2.fromSpec

private def wholeBasisFin {R : Type u} [CommRing R] [Nontrivial R] {q : ℕ}
    (N : Fin q → ℕ) (c : Fin q → R) (hN : ∀ i, 0 < N i) :
    Module.Basis (Fin (NadelWholeCoverDegree.degree N)) R (NadelMixedKummer.Ring N c) := by
  classical
  let I := NadelKummerCover.Tower.basisIndex (VaryingFamily.degree N) q
  let : Finite I := NadelKummerCover.Tower.basisIndex_finite (VaryingFamily.degree N) q
  let : Fintype I := Fintype.ofFinite I
  have hcard : Fintype.card I = NadelWholeCoverDegree.degree N := by
    rw [← Nat.card_eq_fintype_card, NadelWholeCoverDegree.basisIndex_card N hN]
  exact (VaryingFinite.basis N c hN).reindex ((Fintype.equivFin I).trans (finCongr hcard))

variable {X : Scheme.{u}} [IsIntegral X] (F : X.DivisorFamily) (n : ℕ)
    (L : F.ι → X.Modules) (m : F.ι → ℕ)
    (σ : ∀ i, Fin (n + 1) → (unitObj X ⟶
      tensorObj (bundleTensorPower (L i) (m i)) (F.component i).toModules))
    (hL : ∀ i, IsInvertible (L i)) (hD : ∀ i, (F.component i).IsInvertible)
    {k : Type u} [Field k] [PerfectField k]
    (f : X ⟶ Spec (.of k)) [SmoothOfRelativeDimension n f]
    (hG : (NadelBertiniAuxiliaryFamily.auxiliaryFamily F n
      (OriginalData.ideals F n L m σ hL hD)).IsSnc)
    (hRows : ∀ i, (⨆ j, OriginalData.ideals F n L m σ hL hD i j) = ⊤)
    (hm : ∀ i, 0 < m i) (hfield : ∀ i, IsUnit (m i : k))

local notation "π" => normalizedToOriginal (OriginalData.data F n L m σ)
local notation "D" => NadelWholeCoverDegree.degree (Joined.degree F n m)

include hL hD f hG hRows hm hfield

/-- Original geometry supplies an actual WHOLE rank-D free chart around
EVERY original point, including all original normalized components. -/
theorem exists_whole_free_chart_at_point (x : X) :
    ∃ C : WholeFreeChart π D, x ∈ C.base.1 := by
  let : Smooth f := SmoothOfRelativeDimension.smooth n f
  let : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace f
  obtain ⟨y, hy, _, hxy⟩ :=
    exists_isClosed_singleton_mem_specializes isClosed_univ (Set.mem_univ x)
  obtain ⟨j₀, habsent⟩ := Joined.exists_absent_copies F n
    (OriginalData.ideals F n L m σ hL hD) hRows y
  obtain ⟨U, v, hyU, het, e, c, hcinj, hcomp, _habsent, w, hw⟩ :=
    OriginalData.exists_framed_coefficients_at_closed F n L m σ hL hD f hG hy
  let : Nonempty U.1 := ⟨⟨y, hyU⟩⟩
  let : IsDomain Γ(X, U.1) := IsIntegral.component_integral U.1
  have htame (i : F.ι) : IsUnit (m i : Γ(X, U.1)) := by
    let _ := f.sectionsAlgebra U.1
    simpa only [map_natCast] using (hfield i).map (algebraMap k Γ(X, U.1))
  let B := RatioRing F n L m σ hL hD y U v c j₀ w
  let coeff := ratioCoefficients F n L m σ hL hD y U v c j₀ w
  have hN : ∀ i, 0 < Joined.degree F n m i := fun i => hm (Joined.row F n i)
  let C : WholeFreeChart π D :=
    { base := U
      coeff := .of B
      algebra := inferInstance
      basis := wholeBasisFin (Joined.degree F n m) coeff hN
      comparison := Model.canonicalChart F n L m σ hL hD y U v c j₀ w
        f het hcinj hm htame hG hcomp hyU habsent e hw
      overBase := NadelBoundedCanonicalCharts.canonicalChart_over_original
        F n L m σ hL hD y U v c j₀ w f het hcinj hm htame hG hcomp hyU habsent e hw }
  exact ⟨C, hxy.mem_open U.1.isOpen hyU⟩

/-- A chosen actual chart, derived from the original producer rather than
an atlas or basis supplied by a caller. -/
def producedWholeFreeChart (x : X) : WholeFreeChart π D :=
  Classical.choose (exists_whole_free_chart_at_point F n L m σ hL hD
    f hG hRows hm hfield x)

/-- The internally produced actual charts cover every original base point. -/
theorem mem_producedWholeFreeChart (x : X) :
    x ∈ (producedWholeFreeChart F n L m σ hL hD f hG hRows hm hfield x).base.1 :=
  Classical.choose_spec (exists_whole_free_chart_at_point F n L m σ hL hD
    f hG hRows hm hfield x)

end EnvelopeProperty.Vanishing.NadelGlobalStructureTrace
