import EnvelopeProperty.AlgGeom.NoetherianDomainNeighborhood
import Hironaka.Algebra.RegularSmooth.SmoothImpliesRegular
import Hironaka.Algebra.Local.Regular
import Mathlib.RingTheory.TensorProduct.Maps
import Mathlib.RingTheory.Flat.Stability
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.Flat.Localization

/-! # Finite actual integral principal covers of smooth scalar extensions

The original smooth algebra need not be a domain. Its genuine regular local
rings produce actual principal domain neighbourhoods, and compactness selects
finitely many of those SAME neighbourhoods. Coefficients, whole original ideals
and products retain their literal tensor inclusion/localization maps.
-/

noncomputable section
open scoped Classical TensorProduct
namespace EnvelopeProperty.Char0.SmoothAffineDomainCover

universe u v
variable (k R : Type u) [Field k] [CommRing R] [Algebra k R] [Algebra.Smooth k R]

/-- The original smooth prime internally produces an actual integral smooth
principal neighbourhood, without a local-domain certificate. -/
theorem exists_principal_domain_neighbourhood (p : PrimeSpectrum R) :
    ∃ s ∉ p.asIdeal, IsDomain (Localization.Away s) ∧
      Algebra.Smooth k (Localization.Away s) := by
  let : IsNoetherianRing R := Algebra.FiniteType.isNoetherianRing k R
  let : IsRegularLocalRing (Localization.AtPrime p.asIdeal) :=
    Algebra.IsSmoothAt.isRegularLocalRing (k := k) p.asIdeal
  obtain ⟨s, hs, hdom⟩ := NoetherianDomainNeighborhood.exists_away_isDomain p.asIdeal
  let : Algebra.Smooth R (Localization.Away s) := Algebra.Smooth.of_isLocalization_Away s
  exact ⟨s, hs, hdom, Algebra.Smooth.comp k R (Localization.Away s)⟩

/-- Compactness selects FINITELY MANY SAME actual original integral principal
neighbourhoods. Their literal localization maps lift EVERY original prime. -/
theorem exists_finite_principal_domain_cover :
    ∃ (n : ℕ) (g : Fin n → R), Ideal.span (Set.range g) = ⊤ ∧
      (∀ i, IsDomain (Localization.Away (g i)) ∧
        Algebra.Smooth k (Localization.Away (g i))) ∧
      (∀ p : PrimeSpectrum R, ∃ (i : Fin n)
        (q : PrimeSpectrum (Localization.Away (g i))),
          PrimeSpectrum.comap (algebraMap R (Localization.Away (g i))) q = p) := by
  choose s hs hdom hsm using exists_principal_domain_neighbourhood k R
  have hcov : (Set.univ : Set (PrimeSpectrum R)) ⊆
      ⋃ p, (PrimeSpectrum.basicOpen (s p)).1 := by
    intro p _
    exact Set.mem_iUnion.mpr ⟨p, hs p⟩
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover
    (fun p => (PrimeSpectrum.basicOpen (s p)).1)
    (fun p => (PrimeSpectrum.basicOpen (s p)).2) hcov
  let e : t ≃ Fin (Fintype.card t) := Fintype.equivFin t
  let g : Fin (Fintype.card t) → R := fun i => s (e.symm i)
  have hgcover : ∀ p : PrimeSpectrum R, ∃ i, p ∈ PrimeSpectrum.basicOpen (g i) := by
    intro p
    obtain ⟨q, hq⟩ := Set.mem_iUnion.mp (ht (Set.mem_univ p))
    obtain ⟨hqt, hpq⟩ := Set.mem_iUnion.mp hq
    refine ⟨e ⟨q, hqt⟩, ?_⟩
    change p ∈ PrimeSpectrum.basicOpen (s q) at hpq
    simpa only [g, Equiv.symm_apply_apply] using hpq
  have hg : Ideal.span (Set.range g) = ⊤ := by
    apply PrimeSpectrum.iSup_basicOpen_eq_top_iff.mp
    apply top_unique
    intro p _
    obtain ⟨i, hi⟩ := hgcover p
    exact (le_iSup (fun i => PrimeSpectrum.basicOpen (g i)) i) hi
  refine ⟨_, g, hg, fun i => ⟨hdom (e.symm i), hsm (e.symm i)⟩, ?_⟩
  intro p
  obtain ⟨i, hi⟩ := hgcover p
  obtain ⟨q, hq⟩ := (PrimeSpectrum.localization_away_comap_range
    (Localization.Away (g i)) (g i)).ge hi
  exact ⟨i, q, hq⟩

variable {F : Type v} {L A₀ : Type u} [Field F] [Field L] [Algebra F L]
    [CommRing A₀] [Algebra F A₀]

/-- The LITERAL actual field tensor obtains its own actual smooth integral
principal cover, without assuming the tensor is a domain. -/
theorem exists_fieldTensor_principal_domain_cover [Algebra.Smooth F A₀] :
    ∃ (n : ℕ) (g : Fin n → L ⊗[F] A₀), Ideal.span (Set.range g) = ⊤ ∧
      (∀ i, IsDomain (Localization.Away (g i)) ∧
        Algebra.Smooth L (Localization.Away (g i))) ∧
      (∀ p : PrimeSpectrum (L ⊗[F] A₀), ∃ (i : Fin n)
        (q : PrimeSpectrum (Localization.Away (g i))),
          PrimeSpectrum.comap (algebraMap (L ⊗[F] A₀) (Localization.Away (g i))) q = p) :=
  exists_finite_principal_domain_cover L (L ⊗[F] A₀)

/-- The exact original coefficient map into an actual principal chart of the
LITERAL field tensor. -/
def componentCoefficientMap (g : L ⊗[F] A₀) : A₀ →+* Localization.Away g :=
  (algebraMap (L ⊗[F] A₀) (Localization.Away g)).comp
    Algebra.TensorProduct.includeRight.toRingHom

/-- Every whole original coefficient retains its LITERAL tensor/localization. -/
theorem componentCoefficientMap_apply (g : L ⊗[F] A₀) (a : A₀) :
    componentCoefficientMap g a = algebraMap (L ⊗[F] A₀) (Localization.Away g)
      (1 ⊗ₜ[F] a) := rfl

/-- The WHOLE original ideal image is exactly its actual field extension
followed by the SAME literal component-chart localization. -/
theorem map_original_ideal (g : L ⊗[F] A₀) (I : Ideal A₀) :
    I.map (componentCoefficientMap g) =
      (I.map (Algebra.TensorProduct.includeRight (R := F) (A := L)).toRingHom).map
        (algebraMap (L ⊗[F] A₀) (Localization.Away g)) :=
  (Ideal.map_map _ _).symm

/-- WHOLE original product ideals read back as the product of the SAME whole
original chart ideals under the LITERAL tensor/localization coefficient map. -/
theorem map_original_product (g : L ⊗[F] A₀) (I J : Ideal A₀) :
    (I * J).map (componentCoefficientMap g) =
      I.map (componentCoefficientMap g) * J.map (componentCoefficientMap g) :=
  Ideal.map_mul _ _ _

/-- The SAME actual component coefficient map is injective: field extension
and localization are flat, and the actual domain chart is nonzero. -/
theorem componentCoefficientMap_injective [IsDomain A₀] (g : L ⊗[F] A₀)
    [IsDomain (Localization.Away g)] : Function.Injective (componentCoefficientMap g) := by
  let : Algebra A₀ (L ⊗[F] A₀) := Algebra.TensorProduct.rightAlgebra
  let : Module.Flat A₀ (L ⊗[F] A₀) := Module.Flat.of_linearEquiv
    (Algebra.TensorProduct.commRight F A₀ L).symm.toLinearEquiv
  let : Module.Flat A₀ (Localization.Away g) :=
    Module.Flat.trans A₀ (L ⊗[F] A₀) (Localization.Away g)
  change Function.Injective (algebraMap A₀ (Localization.Away g))
  exact Module.isTorsionFree_iff_algebraMap_injective.mp inferInstance

/-- Every NONZERO whole original ideal remains nonzero in each SAME actual
integral principal chart, without geometric-integrality assumptions. -/
theorem map_original_ideal_ne_bot [IsDomain A₀] (g : L ⊗[F] A₀)
    [IsDomain (Localization.Away g)] (I : Ideal A₀) (hI : I ≠ ⊥) :
    I.map (componentCoefficientMap g) ≠ ⊥ :=
  (Ideal.map_eq_bot_iff_of_injective (componentCoefficientMap_injective g)).mp.mt hI

end EnvelopeProperty.Char0.SmoothAffineDomainCover
