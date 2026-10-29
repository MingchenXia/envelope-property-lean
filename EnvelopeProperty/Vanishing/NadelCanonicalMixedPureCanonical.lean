import EnvelopeProperty.Vanishing.NadelCanonicalMixedPureDual
import EnvelopeProperty.Vanishing.NadelCanonicalFrame

/-! # Genuine canonical duality and its actual whole original pure/split exterior comparison -/

noncomputable section
universe u
namespace EnvelopeProperty.Vanishing.NadelCanonicalMixed.Split

open CategoryTheory ModuleCat CanonicalGeometry
variable {k R : Type u} [CommRing k] [Nontrivial k] [CommRing R] [Algebra k R] [Nontrivial R]
    {n q : ℕ} (N : Fin q → ℕ) (I : Set (Fin q)) (σ : I ↪ Fin n) (hN : ∀ i, 0 < N i)
    (a : MvPolynomial (Fin n) k →ₐ[k] R) (ha : a.toRingHom.FormallyEtale)
    (htame : ∀ i, IsUnit (N i : R))
local notation "x" => originalCoordinates a
local notation "h" => pureCoefficient x I σ
local notation "B₀" => SplitRing N I h
local notation "P₀" => NadelMixedKummer.Ring N h

private theorem trivialization_symm {K A : Type u} [CommRing K] [CommRing A] [Algebra K A] {m : ℕ}
    (b : Module.Basis (Fin m) A (KaehlerDifferential K A)) (r : A) :
    (affineCanonicalTrivialization b).symm r = r • affineCanonicalGenerator b :=
  (affineCanonical_eq_smul_generator b ((affineCanonicalTrivialization b).symm r)).trans
    (congrArg (fun s : A => s • affineCanonicalGenerator b)
      ((affineCanonicalTrivialization b).apply_symm_apply r))

private theorem pureDualizingIso_apply (z w : P₀) :
    (pureDualizingIso N I σ hN a ha htame).hom z w =
      pureCoefficientFunctional N I σ hN a ha htame (w * z) := by
  have hF : (pureDualizingIso N I σ hN a ha htame).hom.hom = pureDualizingMap N I σ hN a ha htame := rfl
  have hz := congrArg
    (fun F : P₀ →ₗ[P₀] (coextendScalars (algebraMap R P₀)).obj (ModuleCat.of R R) => F z) hF
  exact (congrArg (fun φ : (coextendScalars (algebraMap R P₀)).obj (ModuleCat.of R R) => φ w) hz).trans
    (pureDualizingMap_apply N I σ hN a ha htame z w)

private theorem pureDualizingIso_one (z : P₀) :
    (pureDualizingIso N I σ hN a ha htame).hom z (1 : P₀) =
      pureCoefficientFunctional N I σ hN a ha htame z := by
  have hvalue := pureDualizingIso_apply N I σ hN a ha htame z (1 : P₀)
  generalize hcoeff : pureCoefficientFunctional N I σ hN a ha htame = l at hvalue ⊢
  simpa only [one_mul] using hvalue

/-- The actual original split coefficient is the genuine base coefficient of its native canonical trace. -/
theorem splitRegularCoefficient_apply (z : B₀) :
    splitRegularCoefficient N I σ hN a ha htame z =
      affineCanonicalTrivialization (baseDifferentialBasis a ha)
        (splitCanonicalCounit N I σ hN a ha htame
          (z • affineCanonicalGenerator (splitDifferentialBasis N I σ hN a ha htame))) := by
  change affineCanonicalTrivialization (baseDifferentialBasis a ha)
      ((splitCanonicalIso N I σ hN a ha htame).hom
        ((affineCanonicalTrivialization (splitDifferentialBasis N I σ hN a ha htame)).symm z) (1 : B₀)) = _
  exact congrArg
    (fun w : affineCanonicalModule k B₀ n =>
      affineCanonicalTrivialization (baseDifferentialBasis a ha)
        ((splitCanonicalIso N I σ hN a ha htame).hom w (1 : B₀)))
    (trivialization_symm (splitDifferentialBasis N I σ hN a ha htame) z)

/-- The entire split canonical trace has its true original coefficient formula on each genuine top-frame multiple. -/
theorem splitCanonicalCounit_generator (z : B₀) :
    splitCanonicalCounit N I σ hN a ha htame
      (z • affineCanonicalGenerator (splitDifferentialBasis N I σ hN a ha htame)) =
      splitRegularCoefficient N I σ hN a ha htame z • affineCanonicalGenerator (baseDifferentialBasis a ha) :=
  (affineCanonical_eq_smul_generator (baseDifferentialBasis a ha) _).trans
    (congrArg (fun r : R => r • affineCanonicalGenerator (baseDifferentialBasis a ha))
      (splitRegularCoefficient_apply N I σ hN a ha htame z).symm)

/-- The SAME entire original pure quotient has actual native canonical duality, with its differential frame internally produced. -/
def pureCanonicalIso : ModuleCat.of P₀ (affineCanonicalModule k P₀ n) ≅
    (coextendScalars (algebraMap R P₀)).obj (ModuleCat.of R (affineCanonicalModule k R n)) :=
  NadelCanonicalFrame.iso (algebraMap R P₀) (baseDifferentialBasis a ha)
    (pureDifferentialBasis N I σ hN a ha htame) (pureDualizingIso N I σ hN a ha htame)

/-- Each actual original canonical functional retains the whole original coefficient and multiplication map. -/
theorem pureCanonicalIso_apply (w : affineCanonicalModule k P₀ n) (c : P₀) :
    (pureCanonicalIso N I σ hN a ha htame).hom w c =
      pureCoefficientFunctional N I σ hN a ha htame
        (c * affineCanonicalTrivialization (pureDifferentialBasis N I σ hN a ha htame) w) •
            affineCanonicalGenerator (baseDifferentialBasis a ha) := by
  have h0 := NadelCanonicalFrame.iso_apply (algebraMap R P₀) (baseDifferentialBasis a ha)
    (pureDifferentialBasis N I σ hN a ha htame) (pureDualizingIso N I σ hN a ha htame) w c
  exact h0.trans ((congrArg (affineCanonicalTrivialization (baseDifferentialBasis a ha)).symm
    (pureDualizingIso_apply N I σ hN a ha htame _ c)).trans (trivialization_symm (baseDifferentialBasis a ha) _))

/-- The original pure canonical trace is the actual native restriction/coextension counit. -/
def pureCanonicalCounit :
    (restrictScalars (algebraMap R P₀)).obj (ModuleCat.of P₀ (affineCanonicalModule k P₀ n)) ⟶
      ModuleCat.of R (affineCanonicalModule k R n) :=
  NadelCanonicalFrame.counit (algebraMap R P₀) (baseDifferentialBasis a ha)
    (pureDifferentialBasis N I σ hN a ha htame) (pureDualizingIso N I σ hN a ha htame)

/-- Every whole actual pure top form has its genuine coefficient formula under the original canonical trace. -/
theorem pureCanonicalCounit_apply (w : affineCanonicalModule k P₀ n) :
    pureCanonicalCounit N I σ hN a ha htame w =
      pureCoefficientFunctional N I σ hN a ha htame
        (affineCanonicalTrivialization (pureDifferentialBasis N I σ hN a ha htame) w) •
            affineCanonicalGenerator (baseDifferentialBasis a ha) := by
  have h0 := NadelCanonicalFrame.counit_apply (algebraMap R P₀) (baseDifferentialBasis a ha)
    (pureDifferentialBasis N I σ hN a ha htame) (pureDualizingIso N I σ hN a ha htame) w
  have h1 := pureDualizingIso_one N I σ hN a ha htame
    (affineCanonicalTrivialization (pureDifferentialBasis N I σ hN a ha htame) w)
  dsimp only [pureCanonicalCounit]
  generalize hbase : baseDifferentialBasis a ha = bA at h0 h1 ⊢
  generalize hsource : pureDifferentialBasis N I σ hN a ha htame = bB at h0 h1 ⊢
  generalize hfinite : pureDualizingIso N I σ hN a ha htame = F at h0 h1 ⊢
  generalize hcoeff : pureCoefficientFunctional N I σ hN a ha htame = l at h1 ⊢
  have h2 := congrArg (affineCanonicalTrivialization bA).symm h1
  exact (h0.trans h2).trans (trivialization_symm bA _)


omit [Nontrivial k] [Nontrivial R] in
/-- Every original top form maps to its actual whole split coefficient times the genuine split frame. -/
theorem pureToSplitExterior_frame (w : affineCanonicalModule k P₀ n) :
    pureToSplitExterior N I σ a w =
      wholePureSmallAlgEquiv N I σ a
        (affineCanonicalTrivialization (pureDifferentialBasis N I σ hN a ha htame) w) •
          affineCanonicalGenerator (splitDifferentialBasis N I σ hN a ha htame) := by
  calc
    _ = pureToSplitExterior N I σ a
        (affineCanonicalTrivialization (pureDifferentialBasis N I σ hN a ha htame) w •
          affineCanonicalGenerator (pureDifferentialBasis N I σ hN a ha htame)) :=
      congrArg (pureToSplitExterior N I σ a)
        (affineCanonical_eq_smul_generator (pureDifferentialBasis N I σ hN a ha htame) w)
    _ = wholePureSmallAlgEquiv N I σ a
        (affineCanonicalTrivialization (pureDifferentialBasis N I σ hN a ha htame) w) •
          pureToSplitExterior N I σ a (affineCanonicalGenerator (pureDifferentialBasis N I σ hN a ha htame)) :=
      (pureToSplitExterior N I σ a).map_smulₛₗ _ _
    _ = _ := congrArg
      (fun z : affineCanonicalModule k B₀ n => wholePureSmallAlgEquiv N I σ a
        (affineCanonicalTrivialization (pureDifferentialBasis N I σ hN a ha htame) w) • z)
      (pureToSplitExterior_generator N I σ hN a ha htame)

/-- The WHOLE original pure canonical trace agrees with the split trace along the genuine native exterior Kähler map. -/
theorem pureCanonicalCounit_exterior (w : affineCanonicalModule k P₀ n) :
    pureCanonicalCounit N I σ hN a ha htame w =
      splitCanonicalCounit N I σ hN a ha htame (pureToSplitExterior N I σ a w) := by
  have hs := congrArg (fun z : affineCanonicalModule k B₀ n => splitCanonicalCounit N I σ hN a ha htame z)
    (pureToSplitExterior_frame N I σ hN a ha htame w)
  have hcoeff := congrArg (fun r : R => r • affineCanonicalGenerator (baseDifferentialBasis a ha))
    (pureCoefficientFunctional_apply N I σ hN a ha htame
      (affineCanonicalTrivialization (pureDifferentialBasis N I σ hN a ha htame) w))
  exact (pureCanonicalCounit_apply N I σ hN a ha htame w).trans
    (hcoeff.trans ((splitCanonicalCounit_generator N I σ hN a ha htame _).symm.trans hs.symm))

end EnvelopeProperty.Vanishing.NadelCanonicalMixed.Split
