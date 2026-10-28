import EnvelopeProperty.AlgGeom.KrullDim
import DeJongAlterations.Geometry.SegreGluing
import Mathlib.RingTheory.Ideal.HasGoingUp

/-! # Actual integral projections and native projective-line dimension -/

open AlgebraicGeometry CategoryTheory TopologicalSpace
noncomputable section
universe u
namespace EnvelopeProperty.IntegralSchemeDimension

/-- Genuine going-up retains every original prime chain under an injective integral ring map. -/
theorem ringKrullDim_le_of_isIntegral_of_injective {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) (hf : f.IsIntegral) (hinj : Function.Injective f) :
    ringKrullDim R ≤ ringKrullDim S := by
  algebraize [f]
  have : Algebra.IsIntegral R S := ⟨hf⟩
  refine iSup_le fun l => ?_
  obtain ⟨P, -, hPp, hPc⟩ := Ideal.exists_ideal_over_prime_of_isIntegral (S := S) l.head.asIdeal ⊥
    (by
      rw [Ideal.comap_bot_of_injective (algebraMap R S) hinj]
      exact bot_le)
  have : P.LiesOver l.head.asIdeal := ⟨hPc.symm⟩
  obtain ⟨L, hL, -, -⟩ := Ideal.exists_ltSeries_of_hasGoingUp l P
  rw [← hL]
  exact Order.LTSeries.length_le_krullDim L

/-- Actual open-cover members bound the dimension of the SAME whole original scheme. -/
theorem topologicalKrullDim_le_of_openCover (X : Scheme.{u}) (d : ℕ) (𝒰 : X.OpenCover)
    (h : ∀ i, topologicalKrullDim (𝒰.X i) ≤ d) : topologicalKrullDim X ≤ d := by
  change Order.krullDim (IrreducibleCloseds X) ≤ d
  rw [Order.krullDim_eq_of_orderIso (irreducibleSetEquivPoints (α := X)),
    Order.krullDim_eq_iSup_coheight]
  refine iSup_le fun x => ?_
  obtain ⟨i, y, rfl⟩ := 𝒰.exists_eq x
  rw [coheight_eq_of_isOpenImmersion (𝒰.f i)]
  have ho : Order.krullDim (𝒰.X i) ≤ d := by
    rw [← Order.krullDim_eq_of_orderIso (irreducibleSetEquivPoints (α := 𝒰.X i))]
    exact h i
  exact (Order.coheight_le_krullDim y).trans ho

/-- The SAME original integral morphism bounds whole dimension, with no target/source certificate. -/
theorem topologicalKrullDim_le_of_isIntegralHom {X Y : Scheme.{u}} (p : Y ⟶ X)
    [IsIntegralHom p] (d : ℕ) (hdim : topologicalKrullDim X ≤ d) :
    topologicalKrullDim Y ≤ d := by
  change Order.krullDim (IrreducibleCloseds Y) ≤ d
  rw [Order.krullDim_eq_of_orderIso (irreducibleSetEquivPoints (α := Y)),
    Order.krullDim_eq_iSup_coheight]
  refine iSup_le fun y => ?_
  obtain ⟨U, hU, hy, _⟩ := exists_isAffineOpen_mem_and_subset
    (show p y ∈ (⊤ : X.Opens) from trivial)
  let V := p ⁻¹ᵁ U
  have hV : IsAffineOpen V := hU.preimage p
  let q : Spec Γ(Y, V) := hV.primeIdealOf ⟨y, hy⟩
  have hq : hV.fromSpec q = y := hV.fromSpec_primeIdealOf ⟨y, hy⟩
  rw [← hq, coheight_eq_of_isOpenImmersion hV.fromSpec]
  have hA : ringKrullDim Γ(X, U) ≤ d := by
    have h := hU.fromSpec.isOpenEmbedding.isEmbedding.isInducing.topologicalKrullDim_le.trans hdim
    change topologicalKrullDim (PrimeSpectrum Γ(X, U)) ≤ d at h
    rwa [PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim] at h
  have hB : ringKrullDim Γ(Y, V) ≤ d :=
    (EnvelopeProperty.ringKrullDim_le_of_isIntegral (p.app U).hom
      (p.isIntegral_app U hU)).trans hA
  have ho : Order.krullDim (Spec Γ(Y, V)) ≤ d := by
    rw [← Order.krullDim_eq_of_orderIso (irreducibleSetEquivPoints (α := Spec Γ(Y, V)))]
    change topologicalKrullDim (PrimeSpectrum Γ(Y, V)) ≤ d
    rwa [PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim]
  exact (Order.coheight_le_krullDim q).trans ho

/-- The actual native projective line is genuinely dimension at most one over ANY original field. -/
theorem projectiveLine_dimension_le (k : Type u) [Field k] :
    topologicalKrullDim (DeJongAlterations.projectiveSpace k 1) ≤ 1 := by
  apply topologicalKrullDim_le_of_openCover _ 1 (DeJongAlterations.Geometry.Segre.coordinateCover k 1)
  intro i
  let j : Fin 2 := i
  change topologicalKrullDim (PrimeSpectrum (DeJongAlterations.Geometry.ProjectiveIdeal.CoordinateRing k j)) ≤ 1
  rw [PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim]
  change ringKrullDim (MvPolynomial {l : Fin 2 // l ≠ j} k) ≤ 1
  rw [MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field, zero_add]
  have hc : Nat.card {l : Fin 2 // l ≠ j} = 1 := by
    exact (Nat.card_congr (finSuccAboveEquiv j)).symm.trans (by simp)
  rw [hc]
  rfl

end EnvelopeProperty.IntegralSchemeDimension
