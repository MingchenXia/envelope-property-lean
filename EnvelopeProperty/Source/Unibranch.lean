/-
Copyright (c) 2026 Mingchen Xia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia
-/
import EnvelopeProperty.Berkovich.SchemeIntegralNormalization
import EnvelopeProperty.Global.Unibranch
import EnvelopeProperty.Alterations.Algebra.IntegralClosureFiniteType
import Hironaka.Algebra.RegularSmooth.SmoothAt

/-!
# Unibranch integral schemes

FHX §1.1 defines an integral scheme to be unibranch when every local ring has
one branch. This is equivalent to bijectivity of its normalization
(Stacks `0C37`, `0C3B`). Over an algebraically closed field, for schemes locally
of finite type, it is also equivalent to the normalization being a universal
homeomorphism (FHX Lemma 8.1).

`Variety.IsUnibranch` uses bijectivity of the normalization
`ν : X^ν → X` in the function field of `X`. This module proves its equivalence
with the local-ring definition for every integral scheme, and relates it to
geometric unibranchness and universal injectivity over an algebraically closed
field.

## Main definitions and results

* `EnvelopeProperty.Variety.IsUnibranch X` (blueprint `def:var-unibranch`): `ν` is bijective.
  Surjectivity always holds (`IntegralSchemeNormalization.projection_surjective`, lying over), so
  this is injectivity of `ν` (`Variety.isUnibranch_iff_injective`).
* `Variety.isUnibranch_iff_isUnibranchLocalRing_stalk` (`lem:var-unibranch-stalks`, no hypothesis
  on `X` beyond integrality): `X` is unibranch iff every local ring `𝒪_{X,x}` is unibranch in the
  sense of Stacks `0BPZ` / EGA IV₀ (23.2.1) (`IsUnibranchLocalRing`: the normalization of the
  reduction is local). On an affine open `U = Spec A`, the points of `X^ν` over `U` are the
  primes of the integral closure `B` of `A` in `Frac A` (`IntegralSchemeNormalization.chartMap`);
  the primes of `B` over `𝔭` correspond to the maximal ideals of the integral closure of `A_𝔭`,
  so there is exactly one iff that ring is local (Stacks `0C37`, `0C3B`).
* `Variety.isUnibranch_tfae` (`thm:var-unibranch-tfae`), for `X` locally of finite type over an
  algebraically closed field `k`: `X` is unibranch iff all stalks are unibranch iff all stalks are
  geometrically unibranch (`IsGeometricallyUnibranchScheme`) iff `ν` is universally injective. As
  `ν` is integral, hence universally closed, and surjective, the last condition says that `ν` is
  a universal homeomorphism: this is FHX's "and … to its being a universal homeomorphism". The
  passage from bijectivity to pure inseparability of the residue field extensions is the
  Nullstellensatz argument of the proof of FHX `lem:unibranch-universal` (FHX §8), in the form
  of `ringHom_ext_of_maxSpec_injective` (`lem:gl-radicial`) for the finite extension `A ⊆ B`
  (finiteness of the normalization of a finitely generated domain:
  `Alterations.Algebra.IntegralClosureFiniteType.finite_integralClosure`).

The ring-level converses `isLocalRing_atPrime_normalization_of_primes_eq` and
`isGeometricallyUnibranchLocalRing_atPrime_of_primes_eq` are those used for multiprojective models
in `EnvelopeProperty.Global.Unibranch` (`MultiModel.isUnibranch_tfae`); the transfer to the model
of a presentation is `EnvelopeProperty.Source.UnibranchPresentation`.
-/

open CategoryTheory AlgebraicGeometry

universe u

noncomputable section

namespace EnvelopeProperty.Variety

open IntegralSchemeNormalization

/-! ### Ring-level comparison -/

section Ring

variable (A : Type u) [CommRing A] [IsDomain A]

/-- **Unique normalization primes versus unibranch localizations.** For a domain `A` with
integral closure `B` in `Frac A`, the map `Spec B → Spec A` is injective iff every localization
`A_𝔭` is unibranch (`IsUnibranchLocalRing`). The forward direction is
`isLocalRing_atPrime_normalization_of_primes_eq` (a unique prime of `B` over `𝔭` makes the
integral closure of `A_𝔭` local), the converse is
`NormalizationLocalization.injective_primeSpectrumComap_of_isUnibranch`. -/
theorem injective_comap_normalization_iff :
    Function.Injective
        (PrimeSpectrum.comap (algebraMap A (integralClosure A (FractionRing A)))) ↔
      ∀ P : PrimeSpectrum A, IsUnibranchLocalRing (Localization.AtPrime P.asIdeal) := by
  refine ⟨fun h P => ?_,
    NormalizationLocalization.injective_primeSpectrumComap_of_isUnibranch⟩
  have := isLocalRing_atPrime_normalization_of_primes_eq P.asIdeal
    fun q q' hq hq' hqP hq'P => congrArg PrimeSpectrum.asIdeal
      (h (a₁ := ⟨q, hq⟩) (a₂ := ⟨q', hq'⟩) (PrimeSpectrum.ext (hqP.trans hq'P.symm)))
  exact ⟨LocalNormalization.reduced_isDomain _,
    (LocalNormalization.domainNormalizationEquiv (Localization.AtPrime P.asIdeal)
      (FractionRing A)).symm.toRingEquiv.isLocalRing⟩

/-- **Geometric unibranchness from unique normalization primes** (`k` algebraically closed, `A`
finitely generated over `k`). If `Spec B → Spec A` is injective, `B` the integral closure of `A`
in `Frac A`, then every localization `A_𝔭` is geometrically unibranch: `B` is finite over `A`,
so two ring maps from `B` into a reduced ring which agree on `A` are equal
(`ringHom_ext_of_maxSpec_injective`, the Nullstellensatz argument), which makes the residue
field extensions purely inseparable (`residueFieldMap_isPurelyInseparable_of_ringHom_ext`). -/
theorem isGeometricallyUnibranchLocalRing_atPrime_of_injective_comap
    (k : Type u) [Field k] [IsAlgClosed k] [Algebra k A] [Algebra.FiniteType k A]
    (h : Function.Injective
      (PrimeSpectrum.comap (algebraMap A (integralClosure A (FractionRing A)))))
    (P : Ideal A) [P.IsPrime] :
    IsGeometricallyUnibranchLocalRing (Localization.AtPrime P) := by
  have : Module.Finite A (integralClosure A (FractionRing A)) :=
    Alterations.Algebra.IntegralClosureFiniteType.finite_integralClosure k A
      (FractionRing A)
  let : Algebra k (integralClosure A (FractionRing A)) :=
    ((algebraMap A (integralClosure A (FractionRing A))).comp (algebraMap k A)).toAlgebra
  have : IsScalarTower k A (integralClosure A (FractionRing A)) := .of_algebraMap_eq' rfl
  have hmax : ∀ m m' : Ideal (integralClosure A (FractionRing A)), m.IsMaximal → m'.IsMaximal →
      m.comap (algebraMap A (integralClosure A (FractionRing A))) =
        m'.comap (algebraMap A (integralClosure A (FractionRing A))) → m = m' :=
    fun m m' hm hm' hmm => congrArg PrimeSpectrum.asIdeal
      (h (a₁ := ⟨m, hm.isPrime⟩) (a₂ := ⟨m', hm'.isPrime⟩) (PrimeSpectrum.ext hmm))
  have hext : ∀ (L : Type u) [CommRing L] [IsReduced L]
      (f g : integralClosure A (FractionRing A) →+* L),
      f.comp (algebraMap A _) = g.comp (algebraMap A _) → f = g := by
    intro L _ _ f g hfg
    exact ringHom_ext_of_maxSpec_injective (k := k) hmax hfg
  refine isGeometricallyUnibranchLocalRing_atPrime_of_primes_eq P
    (fun q q' hq hq' hqP hq'P => congrArg PrimeSpectrum.asIdeal
      (h (a₁ := ⟨q, hq⟩) (a₂ := ⟨q', hq'⟩) (PrimeSpectrum.ext (hqP.trans hq'P.symm)))) ?_
  intro q _ hq
  exact residueFieldMap_isPurelyInseparable_of_ringHom_ext hext P q hq

end Ring

/-! ### Stalks at the points of an affine open -/

section Stalk

variable {X : Scheme.{u}}

set_option backward.isDefEq.respectTransparency.types false in
/-- The stalk of `X` at the point of an affine open `U` given by a prime `𝔭` of `Γ(X, U)` is the
localization `Γ(X, U)_𝔭`: the open immersion `Spec Γ(X, U) → X` is an isomorphism on stalks,
followed by `Spec.stalkIso`. -/
def affineStalkRingEquiv {U : X.Opens} (hU : IsAffineOpen U) (P : PrimeSpectrum Γ(X, U)) :
    X.presheaf.stalk (hU.fromSpec P) ≃+* Localization.AtPrime P.asIdeal :=
  (asIso (hU.fromSpec.stalkMap P)).commRingCatIsoToRingEquiv.trans
    (Spec.stalkIso Γ(X, U) P).commRingCatIsoToRingEquiv

/-- Unibranchness of a stalk at a point of an affine open `U` is unibranchness of the
corresponding localization of `Γ(X, U)`. -/
theorem isUnibranchLocalRing_stalk_fromSpec_iff {U : X.Opens} (hU : IsAffineOpen U)
    (P : PrimeSpectrum Γ(X, U)) :
    IsUnibranchLocalRing (X.presheaf.stalk (hU.fromSpec P)) ↔
      IsUnibranchLocalRing (Localization.AtPrime P.asIdeal) :=
  ⟨fun _ => .of_ringEquiv (affineStalkRingEquiv hU P),
    fun _ => .of_ringEquiv (affineStalkRingEquiv hU P).symm⟩

end Stalk

/-! ### Unibranch integral schemes -/

/-- **Unibranch integral schemes** (FHX §1.1, `def:var-unibranch`): an integral scheme `X` is
*unibranch* if its normalization `ν: X^ν → X` (the normalization of `X` in its function field,
`IntegralSchemeNormalization.normalization`) is bijective. FHX (paper) defines
unibranchness stalk-wise, "every local ring `𝒪_{X,x}` has one branch", and states its equivalence
with bijectivity of `ν`; for every integral scheme this equivalence is
`Variety.isUnibranch_iff_isUnibranchLocalRing_stalk`. Over an algebraically closed field the
definition is also equivalent to geometric unibranchness of the stalks and to `ν` being a
universal homeomorphism (`Variety.isUnibranch_tfae`). -/
def IsUnibranch (X : Scheme.{u}) [IsIntegral X] : Prop :=
  Function.Bijective (IntegralSchemeNormalization.projection X)

variable {X : Scheme.{u}} [IsIntegral X]

/-- The normalization is always surjective, so `X` is unibranch iff `ν` is injective. -/
theorem isUnibranch_iff_injective : IsUnibranch X ↔ Function.Injective (projection X) :=
  ⟨fun h => h.1, fun h => ⟨h, projection_surjective X⟩⟩

/-- The normalization map of the spectrum of a domain is the map of prime spectra. -/
theorem injective_domainNormalization_projection_iff (A : Type u) [CommRing A] :
    Function.Injective (DomainNormalization.projection A) ↔
      Function.Injective
        (PrimeSpectrum.comap (algebraMap A (integralClosure A (FractionRing A)))) :=
  Iff.rfl

/-- **Injectivity of the normalization is affine-local.** `ν` is injective iff for every nonempty
affine open `U`, the normalization `Spec B_U → Spec Γ(X, U)` is injective, where `B_U` is the
integral closure of `Γ(X, U)` in its fraction field: `ν⁻¹(U) ≅ Spec B_U` over `U`
(`IntegralSchemeNormalization.chartMap`). -/
theorem injective_projection_iff_affine :
    Function.Injective (projection X) ↔
      ∀ (U : X.Opens), IsAffineOpen U → ∀ [Nonempty U],
        Function.Injective (DomainNormalization.projection Γ(X, U)) := by
  constructor
  · intro h U hU _ y y' hyy
    have := chartMap_isOpenImmersion X U hU
    apply (chartMap X U hU).isOpenEmbedding.injective
    apply h
    have h1 := congrArg (fun f : _ ⟶ X => f y) (chartMap_comp_projection X U hU)
    have h2 := congrArg (fun f : _ ⟶ X => f y') (chartMap_comp_projection X U hU)
    simp only [Scheme.Hom.comp_apply] at h1 h2
    rw [h1, h2, hyy]
  · intro h y y' hyy
    obtain ⟨U, hU, hx, -⟩ :=
      exists_isAffineOpen_mem_and_subset (show projection X y ∈ (⊤ : X.Opens) from trivial)
    have : Nonempty U := ⟨⟨_, hx⟩⟩
    have := chartMap_isOpenImmersion X U hU
    have hmem : ∀ z, projection X z ∈ U → ∃ w, chartMap X U hU w = z := fun z hz =>
      Scheme.Hom.mem_opensRange.mp (by rw [chartMap_opensRange]; exact hz)
    have hx' : projection X y' ∈ U := by rw [← hyy]; exact hx
    obtain ⟨w, rfl⟩ := hmem y hx
    obtain ⟨w', rfl⟩ := hmem y' hx'
    congr 1
    apply h U hU
    apply hU.fromSpec.isOpenEmbedding.injective
    have h1 := congrArg (fun f : _ ⟶ X => f w) (chartMap_comp_projection X U hU)
    have h2 := congrArg (fun f : _ ⟶ X => f w') (chartMap_comp_projection X U hU)
    simp only [Scheme.Hom.comp_apply] at h1 h2
    exact h1.symm.trans (hyy.trans h2)

/-- `X` is unibranch iff for every nonempty affine open `U`, all localizations of `Γ(X, U)` at
primes are unibranch. -/
theorem isUnibranch_iff_forall_affine :
    IsUnibranch X ↔ ∀ (U : X.Opens), IsAffineOpen U → ∀ [Nonempty U],
      ∀ P : PrimeSpectrum Γ(X, U), IsUnibranchLocalRing (Localization.AtPrime P.asIdeal) := by
  rw [isUnibranch_iff_injective, injective_projection_iff_affine]
  exact ⟨fun h U hU _ => (injective_comap_normalization_iff Γ(X, U)).mp
      ((injective_domainNormalization_projection_iff Γ(X, U)).mp (h U hU)),
    fun h U hU _ => (injective_domainNormalization_projection_iff Γ(X, U)).mpr
      ((injective_comap_normalization_iff Γ(X, U)).mpr (h U hU))⟩

/-- **Unibranch iff all stalks are unibranch** (`lem:var-unibranch-stalks`; Stacks `0C37`,
`0C3B`): the normalization of an integral scheme `X` is bijective iff every local ring
`𝒪_{X,x}` is unibranch in the sense of Stacks `0BPZ` (`IsUnibranchLocalRing`). No hypothesis on
`X` beyond integrality is needed. -/
theorem isUnibranch_iff_isUnibranchLocalRing_stalk :
    IsUnibranch X ↔ ∀ x : X, IsUnibranchLocalRing (X.presheaf.stalk x) := by
  rw [isUnibranch_iff_forall_affine]
  constructor
  · intro h x
    obtain ⟨U, hU, hx, -⟩ :=
      exists_isAffineOpen_mem_and_subset (show x ∈ (⊤ : X.Opens) from trivial)
    have : Nonempty U := ⟨⟨x, hx⟩⟩
    obtain ⟨P, rfl⟩ : ∃ P : PrimeSpectrum Γ(X, U), hU.fromSpec P = x :=
      ⟨_, hU.fromSpec_primeIdealOf ⟨x, hx⟩⟩
    exact (isUnibranchLocalRing_stalk_fromSpec_iff hU P).mpr (h U hU P)
  · intro h U hU _ P
    exact (isUnibranchLocalRing_stalk_fromSpec_iff hU P).mp (h _)

/-- **Unibranch schemes of finite type over an algebraically closed field are geometrically
unibranch**: all residue field extensions of `ν` are purely inseparable
(`isGeometricallyUnibranchLocalRing_atPrime_of_injective_comap` on affine opens). -/
theorem isGeometricallyUnibranchScheme_of_isUnibranch {k : Type u} [Field k] [IsAlgClosed k]
    (p : X ⟶ Spec (.of k)) [LocallyOfFiniteType p] (hX : IsUnibranch X) :
    IsGeometricallyUnibranchScheme X where
  isGeometricallyUnibranch_stalk x := by
    obtain ⟨U, hU, hx, -⟩ :=
      exists_isAffineOpen_mem_and_subset (show x ∈ (⊤ : X.Opens) from trivial)
    have : Nonempty U := ⟨⟨x, hx⟩⟩
    obtain ⟨P, rfl⟩ : ∃ P : PrimeSpectrum Γ(X, U), hU.fromSpec P = x :=
      ⟨_, hU.fromSpec_primeIdealOf ⟨x, hx⟩⟩
    let := p.sectionsAlgebra U
    have := p.finiteType_sectionsAlgebra hU
    have hinj := (injective_domainNormalization_projection_iff Γ(X, U)).mp
      (injective_projection_iff_affine.mp (isUnibranch_iff_injective.mp hX) U hU)
    have := isGeometricallyUnibranchLocalRing_atPrime_of_injective_comap Γ(X, U) k hinj
      P.asIdeal
    exact .of_ringEquiv (affineStalkRingEquiv hU P).symm

/-- Geometrically unibranch integral schemes are unibranch: `ν` is universally injective
(`IntegralSchemeNormalization.projection_universallyInjective`), with no hypothesis on a base. -/
theorem isUnibranch_of_isGeometricallyUnibranchScheme [IsGeometricallyUnibranchScheme X] :
    IsUnibranch X :=
  have := projection_universallyInjective X
  ⟨(projection X).injective, projection_surjective X⟩

/-- **Unibranchness of varieties** (`thm:var-unibranch-tfae`; FHX §1.1 and
`lem:unibranch-universal`; Stacks `0BPZ`, `0C37`, `0C3B`, `0BQ2`). Let `X` be an integral scheme
locally of finite type over an algebraically closed field `k`. The following are equivalent:
1. `X` is unibranch: its normalization `ν` is bijective;
2. every local ring `𝒪_{X,x}` is unibranch;
3. every local ring `𝒪_{X,x}` is geometrically unibranch;
4. `ν` is universally injective (hence, being integral and surjective, a universal
   homeomorphism). -/
theorem isUnibranch_tfae {k : Type u} [Field k] [IsAlgClosed k] (p : X ⟶ Spec (.of k))
    [LocallyOfFiniteType p] :
    List.TFAE [IsUnibranch X,
      ∀ x : X, IsUnibranchLocalRing (X.presheaf.stalk x),
      IsGeometricallyUnibranchScheme X,
      UniversallyInjective (projection X)] := by
  tfae_have 1 ↔ 2 := isUnibranch_iff_isUnibranchLocalRing_stalk
  tfae_have 1 → 3 := isGeometricallyUnibranchScheme_of_isUnibranch p
  tfae_have 3 → 4 := fun _ => projection_universallyInjective X
  tfae_have 4 → 1 := fun _ => ⟨(projection X).injective, projection_surjective X⟩
  tfae_finish

/-- Over an algebraically closed field, unibranch means geometrically unibranch at every
stalk. -/
theorem isUnibranch_iff_isGeometricallyUnibranchScheme {k : Type u} [Field k] [IsAlgClosed k]
    (p : X ⟶ Spec (.of k)) [LocallyOfFiniteType p] :
    IsUnibranch X ↔ IsGeometricallyUnibranchScheme X :=
  (isUnibranch_tfae p).out 0 2

end EnvelopeProperty.Variety
