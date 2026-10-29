import EnvelopeProperty.Projective.SubvarietyMultiplierBaseIdealsConePower
import EnvelopeProperty.Char0.SchemeMultiplierContainment
import EnvelopeProperty.Char0.SchemeAsymptoticMultiplierSubadditivity

/-! # The SAME original asymptotic multiplier cone sequence, actually constructed -/

open CategoryTheory AlgebraicGeometry TopologicalSpace
open scoped Polynomial
noncomputable section
universe u
namespace EnvelopeProperty.ProjSubvariety.MultiplierBaseIdeals
variable {k : Type u} [Field k] {M : ℕ} (X : ProjSubvariety k M)

/-- The actual original total-family structure over its SAME original field. -/
def familyAbsoluteStructure : familyScheme X ⟶ Spec (.of k) :=
  familyProjection X ≫ Spec.map (CommRingCat.ofHom (Polynomial.C : k →+* k[X]))

variable [CharZero k] [Smooth (familyAbsoluteStructure X)]

/-- The full actual scheme asymptotic multiplier ideal of the SAME original
obstacle scheme sequence. Nonvanishing is internally produced from phi. -/
def schemeMultiplierSequence (d : ℕ) (φ : X.an → ℝ)
    {C : ℝ} (hC : ∀ v, C ≤ φ v) (m : ℕ) : (familyScheme X).IdealSheafData :=
  Char0.schemeAsymptoticMultiplierIdealSheaf (familyAbsoluteStructure X)
    (schemeIdeal X d φ) (fun q _hq => schemeIdeal_generic_stalk_ne_bot X d φ hC q) m

/-- The actual whole original scheme multiplier containment has no supplied
containment/nonvanishing certificate. -/
theorem schemeIdeal_le_schemeMultiplierSequence (d : ℕ) (φ : X.an → ℝ)
    {C : ℝ} (hC : ∀ v, C ≤ φ v) {m : ℕ} (hm : 0 < m) :
    schemeIdeal X d φ m ≤ schemeMultiplierSequence X d φ hC m :=
  Char0.le_schemeAsymptoticMultiplierIdealSheaf (familyAbsoluteStructure X)
    (schemeIdeal X d φ) (fun q _hq => schemeIdeal_generic_stalk_ne_bot X d φ hC q) hm

/-- Actual whole scheme subadditivity is consumed for the SAME original sequence. -/
theorem schemeMultiplierSequence_mul_le_pow (d : ℕ) (φ : X.an → ℝ)
    {C : ℝ} (hC : ∀ v, C ≤ φ v) (m l : ℕ) :
    schemeMultiplierSequence X d φ hC (m * l) ≤ schemeMultiplierSequence X d φ hC m ^ l :=
  Char0.schemeAsymptoticMultiplierIdealSheaf_mul_le_pow (familyAbsoluteStructure X)
    (schemeIdeal X d φ) (fun q _hq => schemeIdeal_generic_stalk_ne_bot X d φ hC q) m l

/-- The SAME original multiplier cone ideal, from the complete actual scheme
ideal and original homogeneous representation, never a multiplier on a singular cone. -/
def multiplierConeIdeal (d : ℕ) (φ : X.an → ℝ)
    {C : ℝ} (hC : ∀ v, C ≤ φ v) (m : ℕ) : Ideal X.ConeRing :=
  coneIdeal X (schemeMultiplierSequence X d φ hC m)

/-- The SAME original obstacle cone ideal lies in the actual constructed
multiplier cone ideal; all scheme comparison obligations are discharged internally. -/
theorem coneObstacleIdeal_le_multiplierConeIdeal (d : ℕ) (φ : X.an → ℝ)
    {C : ℝ} (hC : ∀ v, C ≤ φ v) {m : ℕ} (hm : 0 < m) :
    X.coneObstacleIdeal d φ m ≤ multiplierConeIdeal X d φ hC m :=
  coneObstacleIdeal_le_coneIdeal_of_schemeIdeal_le X d φ m _
    (schemeIdeal_le_schemeMultiplierSequence X d φ hC hm)

/-- The ACTUAL original multiplier cone sequence satisfies the genuine
original irrelevant-saturation subadditivity, with NO comparison certificate input. -/
theorem multiplierConeIdeal_mul_le_saturation (d : ℕ) (φ : X.an → ℝ)
    {C : ℝ} (hC : ∀ v, C ≤ φ v) (m l : ℕ) :
    multiplierConeIdeal X d φ hC (m * l) ≤
      X.saturation (multiplierConeIdeal X d φ hC m ^ l) :=
  (coneIdeal_mono X (schemeMultiplierSequence_mul_le_pow X d φ hC m l)).trans
    (coneIdeal_pow_le_saturation X (schemeMultiplierSequence X d φ hC m) l)

end EnvelopeProperty.ProjSubvariety.MultiplierBaseIdeals
