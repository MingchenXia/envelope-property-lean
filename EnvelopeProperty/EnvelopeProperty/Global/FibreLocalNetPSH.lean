import EnvelopeProperty.Global.FibreLocalPSH
import EnvelopeProperty.Projective.FSSystemDyadicNet
import EnvelopeProperty.Potential.FiniteWeightedDecreasingLimits

/-! # Actual original psh potentials yield directed native-chart PL limits

The genuine dyadic directed regularization replaces the field-countable
sequence extraction. Original sequential local psh predicates are unchanged.
-/

open scoped NNReal Topology Classical
open Topology Filter MvPolynomial
noncomputable section
universe u
namespace EnvelopeProperty

private theorem fc_iInf_eq_of_tendsto_of_antitone_net
    {J : Type u} [Preorder J] [Nonempty J] [IsDirected J (· ≤ ·)]
    {a : J → EReal} {l : EReal} (ha : Antitone a) (h : Tendsto a atTop (𝓝 l)) :
    ⨅ j, a j = l := tendsto_nhds_unique (tendsto_atTop_iInf ha) h

private theorem fc_iInf_max_of_antitone_net
    {J : Type u} [Preorder J] [Nonempty J] [IsDirected J (· ≤ ·)]
    {a b : J → EReal} (ha : Antitone a) (hb : Antitone b) :
    ⨅ j, max (a j) (b j) = max (⨅ j, a j) (⨅ j, b j) :=
  fc_iInf_eq_of_tendsto_of_antitone_net (fun _ _ hij => max_le_max (ha hij) (hb hij))
    ((tendsto_atTop_iInf ha).max (tendsto_atTop_iInf hb))

private theorem fc_iInf_max_truncStd_net
    {k A J : Type u} [Field k] [CommRing A] [Algebra k A] [Algebra.FiniteType k A]
    [Preorder J] [Nonempty J] [IsDirected J (· ≤ ·)]
    (n : J → ℕ) (hnmono : Monotone n) (hntop : Tendsto n atTop atTop)
    {a : J → EReal} (ha : Antitone a) (x : Berk k A) :
    ⨅ j, max (a j) ((FSData.truncStd k A (n j)).eval x) = ⨅ j, a j := by
  have htrunc : (⨅ j, (FSData.truncStd k A (n j)).eval x) = ⊥ := by
    rw [eq_bot_iff, ← FSData.iInf_truncStd k A x]
    apply le_iInf
    intro m
    obtain ⟨j, hj⟩ := (hntop.eventually (eventually_ge_atTop m)).exists
    exact (iInf_le (fun j => (FSData.truncStd k A (n j)).eval x) j).trans
      (FSData.antitone_truncStd k A x hj)
  have hmax := fc_iInf_max_of_antitone_net ha
    (fun i j hij => FSData.antitone_truncStd k A x (hnmono hij))
  rw [htrunc, max_bot_right] at hmax
  exact hmax

namespace ProjSubvariety.BlowupCenter

variable {k : Type u} [Field k] {M M' : ℕ} {V : ProjSubvariety k M}
  {B : V.BlowupCenter M'}

/-- The actual original blowup inherits genuine finite FS dyadic NETS from
its actual compact FS system, without field countability. -/
theorem IsPSH.exists_isFinFS_net_dyadic {a b : ℚ} {φ : B.an → EReal}
    (h : B.IsPSH ![(a : ℝ), (b : ℝ)] φ) :
    ∃ (J : Type u) (_ : Preorder J) (_ : IsDirected J (· ≤ ·)) (_ : Nonempty J)
      (n : J → ℕ) (Φ : J → B.an → EReal), Monotone n ∧ Tendsto n atTop atTop ∧
      (∀ j, B.IsFinFS (a + ((2 : ℚ) ^ n j)⁻¹) (b + ((2 : ℚ) ^ n j)⁻¹) (Φ j)) ∧
      (∀ x, Antitone fun j => Φ j x) ∧ ∀ x, φ x = ⨅ j, Φ j x := by
  rw [← ratCast_vecCons_two] at h
  exact FSSystem.IsPSH.exists_isFinFS_net_dyadic (θ := ![a, b]) h

variable (B) (i : Fin (M + 1))
  [IsDomain (ProjBerk.QuotChartAlg V.ideal (X i) 1)]

/-- The original normalized Rees-chart potential is a genuine directed
convex PL infimum, with all data derived from the actual original B.IsPSH. -/
theorem fc_exists_convexPL_net_chartPotential {a : ℚ}
    {φ : B.an → EReal} (h : B.IsPSH ![(a : ℝ), 0] φ)
    {g : ProjBerk.QuotChartAlg V.ideal (X i) 1} (hg : g ∈ B.centerSet i) (hg0 : g ≠ 0) :
    ∃ (J : Type u) (_ : Preorder J) (_ : IsDirected J (· ≤ ·)) (_ : Nonempty J)
      (w : J → Berk k (blowupChart (B.centerSet i) g) → EReal),
      (∀ j, IsConvexPLOn Set.univ (w j)) ∧
      (∀ y, Antitone fun j => w j y) ∧
      ∀ y, B.fcChartPotential i a φ hg hg0 y = ⨅ j, w j y := by
  have : Algebra.FiniteType k (ProjBerk.QuotChartAlg V.ideal (X i) 1) :=
    ProjBerk.finiteType_quotChartAlg (isHomogeneous_X k i)
  have h' : B.IsPSH ![((a : ℚ) : ℝ), ((0 : ℚ) : ℝ)] φ := by
    rw [Rat.cast_zero]
    exact h
  obtain ⟨J, _, _, _, n, Φ, hnmono, hntop, hΦ, hanti, hlim⟩ :=
    h'.exists_isFinFS_net_dyadic
  choose D hDrat hDne hDeq using fun j => isFinFS_iff.1 (hΦ j)
  have hG : ∀ (j : J) (w : Berk k (blowupChart (B.centerSet i) g)),
      ((B.chartTerms i g (D j)).sup fun t => fsTerm t w) =
        Φ j (B.chartPoint i hg hg0 w) +
          (((((a + ((2 : ℚ) ^ n j)⁻¹ : ℚ) : ℝ)) *
              Real.log (BiProjBerk.scaleX (B.chartHom i g) w : ℝ) +
            ((((0 : ℚ) + ((2 : ℚ) ^ n j)⁻¹ : ℚ) : ℝ)) *
              Real.log (BiProjBerk.scaleY (B.chartHom i g) w : ℝ) : ℝ) : EReal) := fun j w =>
    (B.sup_fsTerm_chartTerms hg hg0 (D j) (hDrat j) w).trans
      (congrArg (· + _) (hDeq j _).symm)
  have hGanti : ∀ w : Berk k (blowupChart (B.centerSet i) g), Antitone fun j =>
      ((B.chartTerms i g (D j)).sup fun t => fsTerm t w) := by
    intro w j j' hjj'
    exact (hG j' w).trans_le ((add_le_add (hanti _ hjj') (EReal.coe_le_coe_iff.2
      (antitone_dyadic_coeff a (B.log_scaleX_chartHom_nonneg g w)
        (B.log_scaleY_chartHom_nonneg hg hg0 w) (hnmono hjj')))).trans_eq (hG j w).symm)
  refine ⟨J, inferInstance, inferInstance, inferInstance, fun j => ((FSData.truncStd k _ (n j)).addTerms (B.chartTerms i g (D j))
    (B.chartTerms_pos g (D j))).eval,
    fun j => ((FSData.truncStd k _ (n j)).addTerms (B.chartTerms i g (D j))
      (B.chartTerms_pos g (D j))).isConvexPLOn_univ,
    fun w j j' hjj' => ?_, fun w => ?_⟩
  · simp only [FSData.eval_addTerms]
    exact max_le_max (FSData.antitone_truncStd k _ w (hnmono hjj')) (hGanti w hjj')
  · show B.fcChartPotential i a φ hg hg0 w =
      ⨅ j, ((FSData.truncStd k _ (n j)).addTerms (B.chartTerms i g (D j))
        (B.chartTerms_pos g (D j))).eval w
    have hlx := B.log_scaleX_chartHom_nonneg g w
    have hly := B.log_scaleY_chartHom_nonneg hg hg0 w
    have hr : ⨅ j : J, (((((a + ((2 : ℚ) ^ n j)⁻¹ : ℚ) : ℝ)) *
          Real.log (BiProjBerk.scaleX (B.chartHom i g) w : ℝ) +
        ((((0 : ℚ) + ((2 : ℚ) ^ n j)⁻¹ : ℚ) : ℝ)) *
          Real.log (BiProjBerk.scaleY (B.chartHom i g) w : ℝ) : ℝ) : EReal) =
        (((a : ℝ) * Real.log (BiProjBerk.scaleX (B.chartHom i g) w : ℝ) : ℝ) : EReal) :=
      fc_iInf_eq_of_tendsto_of_antitone_net
        (fun _ _ hjj' => EReal.coe_le_coe_iff.2 (antitone_dyadic_coeff a hlx hly (hnmono hjj')))
        ((continuous_coe_real_ereal.tendsto _).comp ((tendsto_dyadic_coeff a _ _).comp hntop))
    have hsum := iInf_add_of_antitone_net (hanti (B.chartPoint i hg hg0 w))
      (fun _ _ hjj' => EReal.coe_le_coe_iff.2 (antitone_dyadic_coeff a hlx hly (hnmono hjj')))
      (fun j => (hΦ j).isFS.ne_top _) (fun _ => EReal.coe_ne_top _)
    have e1 : (⨅ j, ((FSData.truncStd k _ (n j)).addTerms (B.chartTerms i g (D j))
        (B.chartTerms_pos g (D j))).eval w) =
        ⨅ j, ((B.chartTerms i g (D j)).sup fun t => fsTerm t w) := by
      rw [← fc_iInf_max_truncStd_net n hnmono hntop (hGanti w) w]
      refine iInf_congr fun j => ?_
      rw [FSData.eval_addTerms, max_comm]
    rw [e1, fcChartPotential, ← hr, hlim, ← hsum]
    exact iInf_congr fun j => (hG j w).symm


end ProjSubvariety.BlowupCenter
end EnvelopeProperty
