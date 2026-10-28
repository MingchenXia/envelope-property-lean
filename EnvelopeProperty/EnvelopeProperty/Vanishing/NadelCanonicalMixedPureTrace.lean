import EnvelopeProperty.Vanishing.NadelCanonicalMixedPureCanonical

/-! # The original whole pure quotient has its genuine intrinsic canonical trace

All original root factors are retained. The coefficient ring R is the base
of this original pure algebra; no auxiliary coefficient-cover trace occurs.
-/

noncomputable section
universe u
namespace EnvelopeProperty.Vanishing.NadelCanonicalMixed.Split

open CategoryTheory ModuleCat CanonicalGeometry NadelCanonicalBaseChange
variable {k R : Type u} [CommRing k] [Nontrivial k] [CommRing R] [Algebra k R] [Nontrivial R]
    {n q : ℕ} (N : Fin q → ℕ) (I : Set (Fin q)) (σ : I ↪ Fin n) (hN : ∀ i, 0 < N i)
    (a : MvPolynomial (Fin n) k →ₐ[k] R) (ha : a.toRingHom.FormallyEtale)
    (htame : ∀ i, IsUnit (N i : R))
attribute [local instance] Classical.propDecidable
local notation "x" => originalCoordinates a
local notation "h" => pureCoefficient x I σ
local notation "B₀" => SplitRing N I h
local notation "P₀" => NadelMixedKummer.Ring N h

omit [Nontrivial k] [Nontrivial R] in
/-- The true whole pure/split map preserves the SAME actual original coefficient inclusion. -/
theorem wholePure_R (r : R) :
    wholePureSmallAlgEquiv N I σ a (algebraMap R P₀ r) = algebraMap R B₀ r :=
  (wholeAlgEquiv N I h (fun i hi => by simp only [pureCoefficient, dif_neg hi])).commutes r

omit [Nontrivial k] [Nontrivial R] in
/-- The genuine original whole exterior comparison preserves actual pulled base top generators. -/
theorem pureToSplitExterior_pulled_generator :
    pureToSplitExterior N I σ a
      (topPullback (R := k) (A := R) (B := P₀) n (affineCanonicalGenerator (baseDifferentialBasis a ha))) =
    topPullback (R := k) (A := R) (B := B₀) n (affineCanonicalGenerator (baseDifferentialBasis a ha)) := by
  have hpure : topPullback (R := k) (A := R) (B := P₀) n
      (affineCanonicalGenerator (baseDifferentialBasis a ha)) =
      exteriorPower.ιMulti P₀ n (fun j => KaehlerDifferential.D k P₀ (algebraMap R P₀ (x j))) := by
    rw [baseGenerator_eq_wedge, topPullback_wedge]
    congr 1
    funext j
    exact KaehlerDifferential.map_D k k R P₀ (x j)
  have hsplit : topPullback (R := k) (A := R) (B := B₀) n
      (affineCanonicalGenerator (baseDifferentialBasis a ha)) =
      exteriorPower.ιMulti B₀ n (fun j => KaehlerDifferential.D k B₀ (algebraMap R B₀ (x j))) := by
    rw [baseGenerator_eq_wedge, topPullback_wedge]
    congr 1
    funext j
    exact KaehlerDifferential.map_D k k R B₀ (x j)
  calc
    _ = pureToSplitExterior N I σ a
        (exteriorPower.ιMulti P₀ n (fun j => KaehlerDifferential.D k P₀ (algebraMap R P₀ (x j)))) :=
      congrArg (pureToSplitExterior N I σ a) hpure
    _ = exteriorPower.ιMulti B₀ n (fun j => KaehlerDifferential.D k B₀
        (wholePureSmallAlgEquiv N I σ a (algebraMap R P₀ (x j)))) :=
      NadelKummerTraceBaseChangeUniqueness.algebraExteriorMap_differential_wedge
        (wholePureSmallAlgEquiv N I σ a).toAlgHom n _
    _ = exteriorPower.ιMulti B₀ n (fun j => KaehlerDifferential.D k B₀ (algebraMap R B₀ (x j))) := by
      congr 1
      funext j
      exact congrArg (KaehlerDifferential.D k B₀) (wholePure_R N I σ a (x j))
    _ = _ := hsplit.symm

omit [Nontrivial k] [Nontrivial R] in
include ha in
/-- The SAME true whole exterior map preserves pulled EVERY original base top form. -/
theorem pureToSplitExterior_pulled_topform (w : affineCanonicalModule k R n) :
    pureToSplitExterior N I σ a (topPullback (R := k) (A := R) (B := P₀) n w) =
      topPullback (R := k) (A := R) (B := B₀) n w := by
  let r := affineCanonicalTrivialization (baseDifferentialBasis a ha) w
  let v := affineCanonicalGenerator (baseDifferentialBasis a ha)
  have hpure : topPullback (R := k) (A := R) (B := P₀) n w =
      algebraMap R P₀ r • topPullback (R := k) (A := R) (B := P₀) n v := by
    exact (congrArg (topPullback (R := k) (A := R) (B := P₀) n)
      (affineCanonical_eq_smul_generator (baseDifferentialBasis a ha) w)).trans
        ((topPullback (R := k) (A := R) (B := P₀) n).map_smulₛₗ r v)
  have hsplit : topPullback (R := k) (A := R) (B := B₀) n w =
      algebraMap R B₀ r • topPullback (R := k) (A := R) (B := B₀) n v := by
    exact (congrArg (topPullback (R := k) (A := R) (B := B₀) n)
      (affineCanonical_eq_smul_generator (baseDifferentialBasis a ha) w)).trans
        ((topPullback (R := k) (A := R) (B := B₀) n).map_smulₛₗ r v)
  calc
    _ = pureToSplitExterior N I σ a
        (algebraMap R P₀ r • topPullback (R := k) (A := R) (B := P₀) n v) :=
      congrArg (pureToSplitExterior N I σ a) hpure
    _ = wholePureSmallAlgEquiv N I σ a (algebraMap R P₀ r) •
        pureToSplitExterior N I σ a (topPullback (R := k) (A := R) (B := P₀) n v) :=
      (pureToSplitExterior N I σ a).map_smulₛₗ _ _
    _ = algebraMap R B₀ r • topPullback (R := k) (A := R) (B := B₀) n v :=
      congrArg₂ (fun s : B₀ => fun z : affineCanonicalModule k B₀ n => s • z)
        (wholePure_R N I σ a r) (pureToSplitExterior_pulled_generator N I σ a ha)
    _ = _ := hsplit.symm

/-- The SAME entire original pure canonical trace has intrinsic native-trace normalization on every genuine original base top form. -/
theorem pureCanonicalCounit_pulled_topform (c : P₀) (w : affineCanonicalModule k R n) :
    pureCanonicalCounit N I σ hN a ha htame (c • topPullback (R := k) (A := R) (B := P₀) n w) =
      Algebra.trace R P₀ c • w := by
  have hexterior : pureToSplitExterior N I σ a (c • topPullback (R := k) (A := R) (B := P₀) n w) =
      wholePureSmallAlgEquiv N I σ a c • topPullback (R := k) (A := R) (B := B₀) n w :=
    ((pureToSplitExterior N I σ a).map_smulₛₗ c _).trans
      (congrArg (fun z : affineCanonicalModule k B₀ n => wholePureSmallAlgEquiv N I σ a c • z)
        (pureToSplitExterior_pulled_topform N I σ a ha w))
  have htrace : Algebra.trace R B₀ (wholePureSmallAlgEquiv N I σ a c) = Algebra.trace R P₀ c :=
    Algebra.trace_eq_of_algEquiv
      (wholeAlgEquiv N I h (fun i hi => by simp only [pureCoefficient, dif_neg hi])) c
  calc
    _ = splitCanonicalCounit N I σ hN a ha htame
        (pureToSplitExterior N I σ a (c • topPullback (R := k) (A := R) (B := P₀) n w)) :=
      pureCanonicalCounit_exterior N I σ hN a ha htame _
    _ = splitCanonicalCounit N I σ hN a ha htame
        (wholePureSmallAlgEquiv N I σ a c • topPullback (R := k) (A := R) (B := B₀) n w) :=
      congrArg (fun z : affineCanonicalModule k B₀ n => splitCanonicalCounit N I σ hN a ha htame z) hexterior
    _ = Algebra.trace R B₀ (wholePureSmallAlgEquiv N I σ a c) • w :=
      splitCanonicalCounit_pulled_topform N I σ hN a ha htame _ w
    _ = _ := congrArg (fun r : R => r • w) htrace

end EnvelopeProperty.Vanishing.NadelCanonicalMixed.Split
