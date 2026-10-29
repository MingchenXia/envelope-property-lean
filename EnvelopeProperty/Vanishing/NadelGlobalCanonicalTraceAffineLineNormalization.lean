import EnvelopeProperty.Vanishing.NadelGlobalCanonicalTraceAffineLineNormalizationMixed

/-!
# The mixed sheaf candidate normalizes the affine pulled-line trace

Let `A` be a `k`-algebra with étale coordinates `x: Fin n → A`, and let
`B = A[t]/(t_i^{N_i} - d_i)` be the mixed Kummer algebra (`mixedRing x N I σ u`), with
`d_i = u_i x_{σ(i)}` for `i ∈ I` and `d_i = u_i` otherwise; write `β: Spec B → Spec A`.
The *mixed canonical candidate* `τ: Γ(Ω^n_B) → Γ(Ω^n_A)` (`mixedCanonicalCandidate`) is an
`A`-linear map built by adjoining roots of the units `u_i` (the étale unit cover), where the
cover becomes the pure Kummer cover `t^N = x`, and applying Euler's lemma there
(Esnault–Viehweg, *Lectures on vanishing theorems*, §3; Kollár–Mori, Prop. 2.64). Its sheaf
version `mixedCanonicalSheafCandidate: β_* Ω^n_B ⟶ Ω^n_A` is the lift through the affine
quasicoherent equivalence.

The defining property of the trace of differential forms is the normalization
`τ(b · β^* w) = Tr_{B/A}(b) · w` for `b ∈ B` and forms `w` over `A`. We record this property
as the proposition `MixedCanonicalCandidateNormalization k`, quantified over all mixed charts,
and prove under it:

* `mixedCanonicalSheafCandidate_native`: the sheaf candidate has the same normalization on
  top sections;
* `mixedCanonicalSheafCandidate_differential`: the pushed affine canonical differential
  followed by the sheaf candidate is the affine pulled-line trace `T_{Ω^n_A}` of `β`, i.e.
  `β_*(dβ) ≫ τ = T_{Ω^n_A}`.

The first statement is read off the sections of the sheaf candidate
(`mixedCanonicalSheafCandidate_sections`) by the abstract lemma `gammaTop_value_of_sections`;
the second is the chart normalization criterion
`mixedCanonicalSheafCandidate_differential_of_native` applied to the first.

`MixedCanonicalCandidateNormalization k` is a purely algebraic statement about the explicit
map `mixedCanonicalCandidate` on the explicit algebra `mixedRing x N I σ u`; it contains no
global geometry and no cohomology. It is the statement of
`mixedCanonicalCandidate_native` ( of relative Nadel vanishing, "R-mix-2"). Every
theorem of the global trace chain that depends on it takes it as an explicit hypothesis
`hmix`.
-/

noncomputable section
namespace EnvelopeProperty.Vanishing.NadelGlobalCanonicalTrace
open AlgebraicGeometry CategoryTheory CanonicalGeometry Scheme.Modules
open NadelCanonicalMixed
universe u
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- **Normalization of the mixed canonical candidate** (Euler's lemma on mixed Kummer charts).
For every `k`-algebra `A` with étale coordinates `x`, every mixed Kummer algebra
`B = mixedRing x N I σ u` with positive tame degrees, every `b ∈ B` and every form `w` over
`A`, the mixed canonical candidate sends `b · β^* w` to `Tr_{B/A}(b) · w`.

This is the statement of `mixedCanonicalCandidate_native`; the global canonical trace chain
is proved conditionally on it. -/
def MixedCanonicalCandidateNormalization (k : Type u) [Field k] [CharZero k] : Prop :=
  ∀ {A : Type u} [CommRing A] [Algebra k A] [Nontrivial A] {n q : ℕ} (x : Fin n → A)
    (N : Fin q → ℕ) (I : Set (Fin q)) (σ : I ↪ Fin n) (u : Fin q → Aˣ)
    (hx : (MvPolynomial.aeval (R := k) x).toRingHom.Etale)
    (hN : ∀ i, 0 < N i) (htame : ∀ i, IsUnit (N i : A)) (b : mixedRing x N I σ u)
    (w : (moduleSpecΓFunctor (R := .of A)).obj
      (exteriorCotangentSheaf (affineStructuralMap k (.of A)) n)),
    (mixedCanonicalCandidate x N I σ u hx hN htame).hom
        (b • (show mixedCanonicalModule (k := k) x N I σ u from
          mixedNativeCanonicalPullback (k := k) x N I σ u hx w)) =
      Algebra.trace A (mixedRing x N I σ u) b • w

/-- Top-section value of a morphism `T : P ⟶ Q` of modules on `Spec A` whose section map
factors as `Γ(T) = E ≫ c`: if `E` sends the top section `x₀` to `v` and `c` sends `v` to `r`,
then `T` sends `x₀` to `r`. All objects are arbitrary. -/
private theorem gammaTop_value_of_sections {A : CommRingCat.{u}} {P Q : (Spec A).Modules}
    {M : ModuleCat A} (T : P ⟶ Q) (E : (moduleSpecΓFunctor (R := A)).obj P ⟶ M)
    (c : M ⟶ (moduleSpecΓFunctor (R := A)).obj Q)
    (hsec : (moduleSpecΓFunctor (R := A)).map T = E ≫ c)
    (x₀ : Γ(P, ⊤)) (v : M) (r : (moduleSpecΓFunctor (R := A)).obj Q)
    (hE : E (ModuleSpecGammaCarrier.toNative A P x₀) = v) (hc : c.hom v = r) :
    T.app ⊤ x₀ = ModuleSpecGammaCarrier.toRaw A Q r := by
  have h5 := moduleSpecGamma_map_toRaw A P Q T (ModuleSpecGammaCarrier.toNative A P x₀)
  rw [hsec, CategoryTheory.comp_apply] at h5
  rw [← hc, ← hE]
  exact h5.symm

variable {k A : Type u} [Field k] [CharZero k] [CommRing A] [Algebra k A] [Nontrivial A]
    {n q : ℕ} (x : Fin n → A) (N : Fin q → ℕ) (I : Set (Fin q))
    (σ : I ↪ Fin n) (u : Fin q → Aˣ)

local notation "Bₘ" => mixedRing x N I σ u
local notation "φ" => CommRingCat.ofHom (algebraMap A Bₘ)
local notation "β" => Spec.map φ
local notation "ωA" => exteriorCotangentSheaf (affineStructuralMap k (CommRingCat.of A)) n
local notation "ωB" => exteriorCotangentSheaf (mixedStructure (k := k) x N I σ u) n

/-- Under the normalization of the mixed candidate, the regular mixed sheaf candidate sends
the top section `b · β^* w` of `β_* Ω^n_B` to `Tr_{B/A}(b) · w`. -/
theorem mixedCanonicalSheafCandidate_native
    (hx : (MvPolynomial.aeval (R := k) x).toRingHom.Etale)
    (hN : ∀ i, 0 < N i) (htame : ∀ i, IsUnit (N i : A))
    (hmix : MixedCanonicalCandidateNormalization k)
    (b : Bₘ) (w : (moduleSpecΓFunctor (R := CommRingCat.of A)).obj ωA) :
    (mixedCanonicalSheafCandidate x N I σ u hx hN htame).app ⊤
      (affinePushforwardRawSection φ ωB
        (ModuleSpecGammaCarrier.toRaw (.of Bₘ) ωB
          (b • (show mixedCanonicalModule (k := k) x N I σ u from
            mixedNativeCanonicalPullback (k := k) x N I σ u hx w)))) =
      ModuleSpecGammaCarrier.toRaw (.of A) ωA (Algebra.trace A Bₘ b • w) := by
  exact gammaTop_value_of_sections (mixedCanonicalSheafCandidate x N I σ u hx hN htame)
    (SpecPushforwardTilde.sectionsIso φ ωB).hom (mixedCanonicalCandidate x N I σ u hx hN htame)
    (mixedCanonicalSheafCandidate_sections x N I σ u hx hN htame) _ _ _
    (specPushforwardSectionsIso_hom_raw φ ωB _) (hmix x N I σ u hx hN htame b w)

/-- Under the normalization of the mixed candidate, the pushed affine canonical differential
`β_*(dβ)` followed by the regular mixed sheaf candidate is the affine pulled-line trace of
`Ω^n_A` along `β`. -/
theorem mixedCanonicalSheafCandidate_differential
    (hx : (MvPolynomial.aeval (R := k) x).toRingHom.Etale)
    (hN : ∀ i, 0 < N i) (htame : ∀ i, IsUnit (N i : A))
    (hmix : MixedCanonicalCandidateNormalization k) :
    letI : Module.Free A Bₘ :=
      NadelAdaptedChartMatching.VaryingFinite.free N (NadelMixedKummer.mixedCoefficient x I σ u) hN
    letI : Module.Finite A Bₘ :=
      NadelAdaptedChartMatching.VaryingFinite.finite N
          (NadelMixedKummer.mixedCoefficient x I σ u) hN
    letI : SmoothOfRelativeDimension n (affineStructuralMap k (.of A)) :=
      coordinateStructure_smooth x hx
    (pushforward β).map
        (affineAlgebraCanonicalDifferential k (.of A) (.of Bₘ)
          (IsScalarTower.toAlgHom k A Bₘ) n) ≫
      mixedCanonicalSheafCandidate x N I σ u hx hN htame =
    affinePulledLineTrace (.of A) (.of Bₘ) ωA
      (canonicalLineSheaf_isInvertible (affineStructuralMap k (.of A)) n) := by
  exact mixedCanonicalSheafCandidate_differential_of_native x N I σ u hx hN htame
    (fun b w => mixedCanonicalSheafCandidate_native x N I σ u hx hN htame hmix b w)

end EnvelopeProperty.Vanishing.NadelGlobalCanonicalTrace
