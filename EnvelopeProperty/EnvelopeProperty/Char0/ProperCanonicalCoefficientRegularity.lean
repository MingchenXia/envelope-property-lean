import EnvelopeProperty.AlgGeom.ValuativeLineCoefficientRegularity
import EnvelopeProperty.Char0.ValuativeCanonicalSection
import EnvelopeProperty.AlgGeom.GenericOpenValuativeLift
import EnvelopeProperty.Algebra.RegularDVRIntersection

/-! # EVERY actual proper relative canonical coefficient belongs to the original regular ring -/
noncomputable section
open AlgebraicGeometry CategoryTheory Opposite
namespace EnvelopeProperty.Char0.ProperCanonicalCoefficientRegularity
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {k R F : Type u} [Field k] [CommRing R] [IsDomain R] [IsRegularRing R]
    [Field F] [Algebra R F] [IsFractionRing R F]
    {Y : Scheme.{u}} [IsIntegral Y]
    (f : Spec (.of R) ⟶ Spec (.of k)) (g : Y ⟶ Spec (.of R)) (n : ℕ)
    [SmoothOfRelativeDimension n f] [SmoothOfRelativeDimension n (g ≫ f)] [UniversallyClosed g]
    (U : (Spec (.of R)).Opens) [Nonempty U] [IsIso (g ∣_ U)]

/-- EVERY original global section of the actual relative canonical line has
its SAME prescribed rational coefficient in the SAME original regular ring.
ALL DVRs, actual lifts, differential-unit maps and local coefficients are derived. -/
theorem exists_originalRing_coefficient
    (bR : let := CanonicalGeometry.affineChartAlgebra f ⊤
      Module.Basis (Fin n) Γ(Spec (.of R), ⊤)
        (KaehlerDifferential k Γ(Spec (.of R), ⊤)))
    (hd : (RoundedCanonicalModule.differentialSection f g n).val.app (.op ⊤)
      (show Γ(Y, ⊤) from 1) ≠ 0)
    (s : Γ(RoundedCanonicalModule.relative f g n, ⊤)) :
    ∃ a : R, algebraMap R F a =
      GenericOpenFunctionField.specFractionFieldEquiv (F := F) g U
        (CanonicalGeometry.sectionRatio (RoundedCanonicalModule.relative f g n)
          (RoundedCanonicalModule.relative_isInvertible f g n)
          ((RoundedCanonicalModule.differentialSection f g n).val.app (.op ⊤)
            (show Γ(Y, ⊤) from 1)) hd ⊤ s) := by
  apply exists_originalRing_of_mem_all_regularDVR_localizations
  intro P
  let V := Localization.subalgebra F P.val.asIdeal.primeCompl
    P.val.asIdeal.primeCompl_le_nonZeroDivisors
  let : P.val.asIdeal.IsPrime := P.val.isPrime
  let : IsDiscreteValuationRing (Localization.AtPrime P.val.asIdeal) := P.property
  let e : Localization.AtPrime P.val.asIdeal ≃ₐ[R] V :=
    IsLocalization.algEquiv P.val.asIdeal.primeCompl (Localization.AtPrime P.val.asIdeal) V
  let : IsDiscreteValuationRing V :=
    IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing e
  obtain ⟨l, hl, hr⟩ := GenericOpenValuativeLift.exists_valuative_lift (V := V) (F := F) g U
  let : IsIso ((Scheme.Modules.pullbackUnitIso l).inv ≫
      (Scheme.Modules.pullback l).map (RoundedCanonicalModule.differentialSection f g n)) :=
    RoundedCanonicalModule.pullback_differentialSection_isIso_of_source_localization
      f g n P.val.asIdeal.primeCompl l hr bR
  obtain ⟨a, ha⟩ :=
    ValuativeLineCoefficientRegularity.fractionCoefficient_mem_range_of_unit_lift
      g U (RoundedCanonicalModule.relative f g n)
      (RoundedCanonicalModule.relative_isInvertible f g n)
      (RoundedCanonicalModule.differentialSection f g n) hd l hl s
  exact ha ▸ a.property

end EnvelopeProperty.Char0.ProperCanonicalCoefficientRegularity
