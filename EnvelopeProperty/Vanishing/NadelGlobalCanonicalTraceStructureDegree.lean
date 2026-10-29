import EnvelopeProperty.Vanishing.NadelBoundedCanonicalCharts
import EnvelopeProperty.Vanishing.NadelWholeCoverDegree
import Mathlib.AlgebraicGeometry.Morphisms.FlatRank

/-! # Whole native rank from the actual complete affine ratio charts

Only a produced free chart is used to compute rank. No assertion is made
that the algebra on an arbitrary affine open is globally free.
-/
noncomputable section
namespace EnvelopeProperty.Vanishing.NadelGlobalStructureTrace
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Scheme.Modules
universe u
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem finrank_via_whole_free_chart
    {X Y : Scheme.{u}} (π : Y ⟶ X) [IsFinite π] [Flat π]
    (U : X.affineOpens) (B : Type u) [CommRing B] [Algebra Γ(X, U.1) B]
    [Module.Finite Γ(X, U.1) B] [Module.Free Γ(X, U.1) B]
    (e : Spec (.of B) ≅ (π ⁻¹ᵁ U.1).toScheme)
    (h : e.hom ≫ (π ⁻¹ᵁ U.1).ι ≫ π =
      Spec.map (CommRingCat.ofHom (algebraMap Γ(X, U.1) B)) ≫ U.2.fromSpec)
    (x : U.1.toScheme) :
    π.finrank (U.1.ι x) = Module.finrank Γ(X, U.1) B := by
  let : IsAffine U.1.toScheme := U.2
  let b : Spec (.of B) ⟶ Spec Γ(X, U.1) :=
    Spec.map (CommRingCat.ofHom (algebraMap Γ(X, U.1) B))
  have hsmall : e.hom ≫ (π ∣_ U.1) = b ≫ U.2.isoSpec.inv := by
    apply (cancel_mono U.1.ι).mp
    simpa only [Category.assoc, morphismRestrict_ι, IsAffineOpen.fromSpec] using h
  have hs : IsPullback e.hom b (π ∣_ U.1) U.2.isoSpec.inv :=
    IsPullback.of_horiz_isIso ⟨hsmall⟩
  have hp := hs.paste_horiz (isPullback_morphismRestrict π U.1).flip
  let p : Spec Γ(X, U.1) := U.2.isoSpec.hom x
  have hr := Scheme.Hom.finrank_of_isPullback
    (e.hom ≫ (π ⁻¹ᵁ U.1).ι) b π (U.2.isoSpec.inv ≫ U.1.ι) hp p
  have hx : (U.2.isoSpec.inv ≫ U.1.ι) p = U.1.ι x := by
    dsimp only [p]
    rw [Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply U.2.isoSpec.hom U.2.isoSpec.inv,
      Iso.hom_inv_id]
    rfl
  rw [hx] at hr
  have hb := Scheme.Hom.finrank_SpecMap_algebraMap Γ(X, U.1) B p
  rw [Module.rankAtStalk_eq_finrank_of_free] at hb
  exact hr.symm.trans hb

open CanonicalGeometry NadelAuxiliaryMulticover NadelGlobalNormalization
open NadelAdaptedChartMatching NadelGlobalAdaptedModel NadelGlobalAdaptedRoots

/-- The SAME entire native normalized adapted cover has the product of
ALL original root degrees as its actual finite-flat rank at EVERY point.
Every required original free chart and its rank are produced internally. -/
theorem whole_finrank_eq_degree
    {X : Scheme.{u}} [IsIntegral X] (F : X.DivisorFamily) (n : ℕ)
    (L : F.ι → X.Modules) (m : F.ι → ℕ)
    (σ : ∀ i, Fin (n + 1) → (unitObj X ⟶
      tensorObj (bundleTensorPower (L i) (m i)) (F.component i).toModules))
    (hL : ∀ i, IsInvertible (L i)) (hD : ∀ i, (F.component i).IsInvertible)
    {k : Type u} [Field k] [PerfectField k]
    (f : X ⟶ Spec (.of k)) [SmoothOfRelativeDimension n f]
    (hG : (NadelBertiniAuxiliaryFamily.auxiliaryFamily F n
      (OriginalData.ideals F n L m σ hL hD)).IsSnc)
    (hRows : ∀ i, (⨆ j, OriginalData.ideals F n L m σ hL hD i j) = ⊤)
    (hm : ∀ i, 0 < m i) (hfield : ∀ i, IsUnit (m i : k)) (x : X) :
    (normalizedToOriginal (OriginalData.data F n L m σ)).finrank x =
      NadelWholeCoverDegree.degree (Joined.degree F n m) := by
  let π := normalizedToOriginal (OriginalData.data F n L m σ)
  obtain ⟨hfinite, hflat, _⟩ :=
    finite_flat_smooth F n L m σ hL hD f hG hRows hm hfield
  let : IsFinite π := hfinite
  let : Flat π := hflat
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
  let N := Joined.degree F n m
  let coeff := ratioCoefficients F n L m σ hL hD y U v c j₀ w
  have hN : ∀ i, 0 < N i := fun i => hm (Joined.row F n i)
  let : Module.Finite Γ(X, U.1) B := VaryingFinite.finite N coeff hN
  let : Module.Free Γ(X, U.1) B := VaryingFinite.free N coeff hN
  let C := Model.canonicalChart F n L m σ hL hD y U v c j₀ w
    f het hcinj hm htame hG hcomp hyU habsent e hw
  have hC := NadelBoundedCanonicalCharts.canonicalChart_over_original
    F n L m σ hL hD y U v c j₀ w f het hcinj hm htame hG hcomp hyU habsent e hw
  have hxU : x ∈ U.1 := hxy.mem_open U.1.isOpen hyU
  have hwhole := finrank_via_whole_free_chart π U B C hC ⟨x, hxU⟩
  exact hwhole.trans (NadelWholeCoverDegree.finrank_eq_degree N coeff hN)

end EnvelopeProperty.Vanishing.NadelGlobalStructureTrace
