import EnvelopeProperty.Vanishing.RelativeNadelGlobalTwists
import EnvelopeProperty.Vanishing.NadelRelativePrincipalizationTwistedMultiplier
import EnvelopeProperty.AlgGeom.SchemeProjectiveAcyclicPushforwardCohomology
import EnvelopeProperty.AlgGeom.AmpleLineTwistGeneration
import EnvelopeProperty.Char0.AmpleNadelInput

/-! # Relative ample Nadel vanishing, conditional only on the cover trace

Let `k` be a field of characteristic zero, `R` a finite-type `k`-algebra, `X`
smooth integral of dimension `n` over `k` and projective over `Spec R`, `I` a
generically nonzero ideal and `c ≥ 0` rational. If `A, B` are invertible,
`I ⊗ B` is finitely globally generated and `A^d ≅ C ⊗ B^t` with `dc = t` and
`C` ample over `R` (i.e. `A - cB` is ample over `R`), then Nadel vanishing holds:
`H^{q+1}(X, ω_X ⊗ A ⊗ 𝒥(c·I)) = 0`, where `𝒥` is the all-DVR multiplier ideal.

Proof (the argument over a projective `k`-scheme, with the field base replaced
by `Spec R`):

1. principalize `I` by `μ : Y → X` (`NadelRelativePrincipalization`, which
   needs `X → Spec k` separated of finite type; both follow from projectivity
   over `R`). The multiplier comparison
   `NadelRelativePrincipalizationTwistedMultiplier.originalTwistedMultiplierIso`
   identifies `ω_X ⊗ A ⊗ 𝒥(c·I)` with `μ_*(Q_c ⊗ μ^*A)`, `Q_c = ω_Y ⊗ 𝒪(-⌊cE⌋)`,
   which is quasicoherent;
2. `H^{q+1}(Y, Q_c ⊗ μ^*A) = 0` by `relativeSourceVanishing_of_coverTrace`;
3. a projective embedding `j : X ↪ ℙ^s_R` from a very ample power of `C` gives
   the ample `H = j^*𝒪(1)`, and `relativeSource_globalTwists_of_coverTrace`
   supplies the vanishing of all positive twists by `(μ^*H)^m`; the projective
   Leray–Čech comparison
   `SchemeProjectiveAcyclicPushforwardCohomology.subsingleton_H_succ_iff_pushforward`
   then transfers the vanishing from `Y` to `μ_*(Q_c ⊗ μ^*A)`.

The final theorem `relativeAmpleNadelVanishingInput_of_coverTrace` produces
`Char0.RelativeAmpleNadelVanishingInput k` from `CoverCanonicalTraceInput k`
(`RelativeNadelCoverTraceInput`), the existence of the canonical trace on every
normalized adapted cover. That input is not proved here, so this file does
**not** prove Nadel vanishing unconditionally. Neither `IsAlgClosed k` nor
properness over `k` is used.
-/
noncomputable section
namespace EnvelopeProperty.Vanishing.RelativeNadelAssembly
open AlgebraicGeometry CategoryTheory CategoryTheory.MonoidalCategory Scheme.Modules
open CanonicalGeometry Char0
universe u
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] Scheme.Modules.monoidalCategory Scheme.Modules.symmetricCategory

section Multiplier
variable {k : Type u} [Field k] [CharZero k] {X : Scheme.{u}} [IsIntegral X]
    (f : X ⟶ Spec (.of k)) [FiniteType f] [IsSeparated f]
    (n : ℕ) [SmoothOfRelativeDimension n f]
    (I : X.IdealSheafData) (hI : I.stalkIdeal (genericPoint X) ≠ ⊥)

local notation "μ" =>
  Scheme.BlowUpSequence.composite (NadelRelativePrincipalization.sequence f n I hI)
local notation "g" =>
  Scheme.BlowUpSequence.composite (NadelRelativePrincipalization.sequence f n I hI) ≫ f
local notation "J₀" => Scheme.IdealSheafData.comap I
  (Scheme.BlowUpSequence.composite (NadelRelativePrincipalization.sequence f n I hI))
local notation "hJ₀" => NadelRelativePrincipalization.totalTransform_isIdealOfSncDivisor f n I hI

/-- **Relative rational-ample multiplier vanishing, from the cover trace.** For
`X` smooth integral over `k` (char. `0`) with `π : X → Spec R` over `k`, `R` of
finite type over `k`, the module `(ω_X ⊗ A) ⊗ 𝒥(q·I)` has no cohomology in
positive degrees whenever `A^d ≅ C ⊗ B^t` with `C` ample over `R`, `dq = t`, and
`I ⊗ B` finitely globally generated. Conditional only on
`CoverCanonicalTraceInput k`. -/
theorem relativeMultiplierVanishing_of_coverTrace
    {R : Type u} [CommRing R] [Algebra k R] [Algebra.FiniteType k R]
    (hT : CoverCanonicalTraceInput k) (π : X ⟶ Spec (.of R))
    (hπ : π ≫ Spec.map (CommRingCat.ofHom (algebraMap k R)) = f)
    (A : X.Modules) (hA : IsInvertible A) (B : X.Modules) (hB : IsInvertible B)
    (C : X.Modules) (hC : SchemeLineAmpleness.IsAmple π C)
    (G : (I.toModules ⊗ B).GeneratingSections) (hG : G.IsFiniteType)
    (q : ℚ) (hq : 0 ≤ q) (d t : ℕ) (hd : 0 < d) (hdt : (d : ℚ) * q = (t : ℚ))
    (e₀ : bundleTensorPower A d ≅ C ⊗ bundleTensorPower B t) (r : ℕ) :
    letI : Smooth f := SmoothOfRelativeDimension.smooth n f
    Subsingleton (CategoryTheory.Sheaf.H
      ((canonicalLineSheaf f n ⊗ A) ⊗
        (schemeMultiplierIdealSheaf f I hI q).toModules).sheaf (r + 1)) := by
  let : Smooth f := SmoothOfRelativeDimension.smooth n f
  let : SmoothOfRelativeDimension n g :=
    NadelRelativePrincipalization.stage_smoothOfRelativeDimension f n I hI (Fin.last _)
  let : IsProper μ := NadelRelativePrincipalization.composite_isProper f n I hI
  let Q := RoundedCanonicalModule.absolute g n J₀ hJ₀ q
  let F := Scheme.Modules.tensorObj Q ((pullback μ).obj A)
  have hF : IsInvertible F :=
    (RoundedCanonicalModule.absolute_isInvertible g n J₀ hJ₀ q).tensorObj (hA.pullback μ)
  let : F.IsQuasicoherent := hF.isQuasicoherent
  let : ((pushforward μ).obj F).IsQuasicoherent :=
    NadelRelativePrincipalizationTwistedMultiplier.originalTwistedMultiplierPushforward_isQuasicoherent
      f n I hI q A hA
  -- A projective embedding over `R` from a very ample power of `C`.
  obtain ⟨_a, _ha, s, j, hj, hjf, _eC⟩ := hC.2
  let : IsClosedImmersion j := hj
  let H := SchemeProjectiveSectionPositiveBasis.embeddingLine j
  have hH : SchemeLineAmpleness.IsAmple π H :=
    AmpleLineTwistGeneration.isAmple_of_isVeryAmple ⟨s, j, hj, hjf, ⟨Iso.refl _⟩⟩
  have hSource := relativeSourceVanishing_of_coverTrace f n I hI hT π hπ
    A hA B hB C hC G hG q hq d t hd hdt e₀ r
  have hGlobal := relativeSource_globalTwists_of_coverTrace f n I hI hT π hπ
    A hA B hB C hC G hG q hq d t hd hdt e₀ H hH
  have hPush : Subsingleton (CategoryTheory.Sheaf.H ((pushforward μ).obj F).sheaf (r + 1)) :=
    (SchemeProjectiveAcyclicPushforwardCohomology.subsingleton_H_succ_iff_pushforward
      j μ F hGlobal r).mp hSource
  let E := NadelRelativePrincipalizationTwistedMultiplier.originalTwistedMultiplierIso
    f n I hI q A hA
  exact AffinePushforwardCohomology.subsingleton_H_of_retract
    E.hom E.inv E.hom_inv_id (r + 1) hPush

end Multiplier

/-- **Relative ample Nadel vanishing from the canonical trace on adapted covers.**
The existence of the canonical trace on every normalized adapted cover
(`CoverCanonicalTraceInput k`) implies the relative ample Nadel input
`Char0.RelativeAmpleNadelVanishingInput k` consumed by the characteristic-zero
smooth envelope theorem. The finite-type and separatedness hypotheses of the
principalization are derived from projectivity over `R`. -/
theorem relativeAmpleNadelVanishingInput_of_coverTrace {k : Type u} [Field k] [CharZero k]
    (hT : CoverCanonicalTraceInput k) : Char0.RelativeAmpleNadelVanishingInput k := by
  intro R _ _ _ X _ p _ π hπ hp n hn I hI A B hA hB hG c hc d t hd hdt C hC e q
  have : SmoothOfRelativeDimension n p := hn
  have : FiniteType p := NadelRelativePrincipalization.structure_finiteType p π hπ hp
  have : IsSeparated p := NadelRelativePrincipalization.structure_isSeparated p π hπ hp
  obtain ⟨G, hGf⟩ := hG
  obtain ⟨e₀⟩ := e
  exact relativeMultiplierVanishing_of_coverTrace p n I hI hT π hπ A hA B hB C hC G hGf
    c hc d t hd hdt e₀ q

end EnvelopeProperty.Vanishing.RelativeNadelAssembly
