import EnvelopeProperty.Vanishing.RelativeNadelConditionalDescent
import EnvelopeProperty.Vanishing.NadelOriginalRationalAmpleTwists
import EnvelopeProperty.Vanishing.NadelOriginalTwistedRoundedSource

/-! # The global twist family of the relative source, from the cover trace

Keep the setting of `RelativeNadelConditionalDescent`: `μ : Y → X` is the
relative principalization of `I`, `Q_q = ω_Y ⊗ 𝒪(-⌊qE⌋)`, and
`M^d ≅ C ⊗ B^t` with `C` ample over `Spec R`. For a second line `H` ample over
`Spec R` and every `m ≥ 1`, the line `M ⊗ H^m` satisfies the same hypotheses,
with numerator `C ⊗ H^{md}` (still ample over `R`) and the same `B, d, t`
(`relativeTwistedSourceData`). The source vanishing theorem applied to it gives
`H^{r+1}(Y, (Q_q ⊗ μ^*M) ⊗ (μ^*H)^m) = 0` for all `r ≥ 0` and `m ≥ 1`.

This eventual family of vanishing twists is the input of the projective
Leray–Čech comparison `SchemeProjectiveAcyclicPushforwardCohomology`, which
replaces local vanishing `R^iμ_*(Q_q ⊗ μ^*M) = 0` in the proof of Nadel
vanishing. The argument is the one over a projective `k`-scheme, with the
field base replaced by `Spec R`; it uses only `CoverCanonicalTraceInput k`
beyond proved results.
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

/-- The twists `M ⊗ H^m` (`m ≥ 1`) of a rational ample source over an arbitrary
affine base `Spec R` keep the source hypotheses: the line is invertible, the
numerator `C ⊗ H^{md}` is ample over `R`, and
`(M ⊗ H^m)^d ≅ (C ⊗ H^{md}) ⊗ B^t` with the same `B, d, t`. This is
`NadelOriginalRationalAmpleTwists.twistedSourceData` with the field base replaced
by an arbitrary commutative ring. -/
theorem relativeTwistedSourceData {R : Type u} [CommRing R] {X : Scheme.{u}} [IsIntegral X]
    (p : X ⟶ Spec (.of R)) (M : X.Modules) (hM : IsInvertible M)
    (B C H : X.Modules) (hC : SchemeLineAmpleness.IsAmple p C)
    (hH : SchemeLineAmpleness.IsAmple p H) (d t : ℕ) (hd : 0 < d)
    (e₀ : bundleTensorPower M d ≅ C ⊗ bundleTensorPower B t)
    (m : ℕ) (hm : 1 ≤ m) :
    IsInvertible (M ⊗ bundleTensorPower H m) ∧
      SchemeLineAmpleness.IsAmple p (C ⊗ bundleTensorPower H (m * d)) ∧
      Nonempty (bundleTensorPower (M ⊗ bundleTensorPower H m) d ≅
        (C ⊗ bundleTensorPower H (m * d)) ⊗ bundleTensorPower B t) := by
  have hHm : IsInvertible (bundleTensorPower H m) :=
    TensorPowerBaseIdealGrading.tensorPower_isInvertible hH.isInvertible m
  have hmd : 0 < m * d := Nat.mul_pos (Nat.zero_lt_one.trans_le hm) hd
  refine ⟨(hM.tensorObj hHm).of_iso (ModularCurves.monoidalTensorObjIso M _), ?_,
    ⟨NadelOriginalRationalAmpleTwists.twistedSourcePowerIso M B C H d t m e₀⟩⟩
  exact AmpleTensorLines.isAmple_tensor p C (bundleTensorPower H (m * d)) hC
    (AmpleLinePositivePowers.isAmple_tensorPower p H hH (m * d) hmd)

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

/-- **The global twist family of the relative source.** Under the hypotheses of
`relativeSourceVanishing_of_coverTrace` and for any line `H` ample over `Spec R`,
`H^{r+1}(Y, (Q_q ⊗ μ^*M) ⊗ (μ^*H)^m) = 0` for every `r` and every `m ≥ 1`
(the bound is `N = 1`). Conditional only on `CoverCanonicalTraceInput k`. -/
theorem relativeSource_globalTwists_of_coverTrace
    {R : Type u} [CommRing R] [Algebra k R] [Algebra.FiniteType k R]
    (hT : CoverCanonicalTraceInput k) (π : X ⟶ Spec (.of R))
    (hπ : π ≫ Spec.map (CommRingCat.ofHom (algebraMap k R)) = f)
    (M : X.Modules) (hM : IsInvertible M) (B : X.Modules) (hB : IsInvertible B)
    (C : X.Modules) (hC : SchemeLineAmpleness.IsAmple π C)
    (G : (I.toModules ⊗ B).GeneratingSections) (hG : G.IsFiniteType)
    (q : ℚ) (hq : 0 ≤ q) (d t : ℕ) (hd : 0 < d) (hdt : (d : ℚ) * q = (t : ℚ))
    (e₀ : bundleTensorPower M d ≅ C ⊗ bundleTensorPower B t)
    (H : X.Modules) (hH : SchemeLineAmpleness.IsAmple π H) :
    ∀ r : ℕ, ∃ N : ℕ, ∀ m : ℕ, N ≤ m →
      Subsingleton (CategoryTheory.Sheaf.H
        (Scheme.Modules.tensorObj (RoundedCanonicalModule.absolute g n J₀ hJ₀ q)
          ((pullback μ).obj M) ⊗ bundleTensorPower ((pullback μ).obj H) m).sheaf (r + 1)) := by
  intro r
  refine ⟨1, fun m hm => ?_⟩
  obtain ⟨hMm, hCm, ⟨eₘ⟩⟩ := relativeTwistedSourceData π M hM B C H hC hH d t hd e₀ m hm
  have hVan := relativeSourceVanishing_of_coverTrace f n I hI hT π hπ
    (M ⊗ bundleTensorPower H m) hMm B hB (C ⊗ bundleTensorPower H (m * d)) hCm
    G hG q hq d t hd hdt eₘ r
  let E := NadelOriginalTwistedRoundedSource.originalTwistedSourceIso μ
    (RoundedCanonicalModule.absolute g n J₀ hJ₀ q) M H m
  exact AffinePushforwardCohomology.subsingleton_H_of_retract
    E.inv E.hom E.inv_hom_id (r + 1) hVan

end EnvelopeProperty.Vanishing.RelativeNadelAssembly
