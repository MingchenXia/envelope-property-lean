import EnvelopeProperty.Global.Homogeneous

/-!
# Original support-trivial tests and singular decreasing limits

The actual zero scaling stays inside the original model and preserves every
original section's vanishing. Finiteness only on these support-trivial points
therefore forces the original class to be nef. The resulting non-unibranch
PSH2 case allows poles at other original analytic points.

Full singular PSH2 and intrinsic numerical/BJ identification remain open.
Complete mathematical route: the owned audit `support-trivial-route.tex`.
-/

open scoped NNReal Topology
open Set Filter

noncomputable section

namespace EnvelopeProperty.MultiModel

universe u

variable {k K : Type u} [Field k] [Field K] [Algebra k K] {r : ℕ}
  {X : MultiModel k K r}

/-- The actual zero scaling retains original multigradedness. -/
theorem IsMultigraded.zeroScale {x : Berk k X.S} (hx : X.IsMultigraded x) :
    X.IsMultigraded (Berk.zeroScale x) := by
  intro p a
  by_cases hp : x.val p = 0
  · have ha : x.val (X.homComp a p) = 0 := by
      apply le_antisymm
      · simpa only [hp] using hx p a
      · exact zero_le
    rw [Berk.zeroScale_val_of_eq_zero ha, Berk.zeroScale_val_of_eq_zero hp]
  · rw [Berk.zeroScale_val_of_ne_zero hp]
    exact Berk.zeroScale_val_le_one _ _

/-- The actual zero scaling retains normalization in EVERY original coordinate group. -/
theorem IsNormalized.zeroScale {x : Berk k X.S} (hx : X.IsNormalized x) :
    X.IsNormalized (Berk.zeroScale x) := by
  intro c
  refine le_antisymm (Finset.sup_le fun i _ => Berk.zeroScale_val_le_one _ _) ?_
  obtain ⟨j, hj⟩ := hx.exists_val_coordElem_eq_one c
  have hne : x.val (X.coordElem ⟨c, j⟩) ≠ 0 := by rw [hj]; exact one_ne_zero
  calc
    1 = (Berk.zeroScale x).val (X.coordElem ⟨c, j⟩) :=
      (Berk.zeroScale_val_of_ne_zero hne).symm
    _ ≤ Finset.univ.sup (fun i : Fin (X.M c + 1) =>
        (Berk.zeroScale x).val (X.coordElem ⟨c, i⟩)) :=
      Finset.le_sup (f := fun i : Fin (X.M c + 1) =>
        (Berk.zeroScale x).val (X.coordElem ⟨c, i⟩)) (Finset.mem_univ j)

variable (X) in
/-- The trivial residue valuation at the SAME original algebraic support. -/
def supportTrivialPoint (x : X.an) : X.an :=
  ⟨Berk.zeroScale x.1, x.2.1.zeroScale, x.2.2.zeroScale⟩

/-- The ENTIRE original prime valuation kernel is unchanged. -/
theorem supportTrivialPoint_supp (x : X.an) :
    (X.supportTrivialPoint x).1.val.supp = x.1.val.supp := by
  ext p
  change (Berk.zeroScale x.1).val p = 0 ↔ x.1.val p = 0
  exact Berk.zeroScale_val_eq_zero_iff x.1 p

private theorem homNorm_zeroScale_eq_zero_iff (x : Berk k X.S) (d : Fin r →₀ ℕ)
    (f : K) : X.homNorm (Berk.zeroScale x) d f = 0 ↔ X.homNorm x d f = 0 := by
  classical
  unfold homNorm
  split_ifs with hf
  · exact Berk.zeroScale_val_eq_zero_iff x _
  · rfl

/-- Every SAME original model section has exactly the same vanishing condition
at its original analytic point and actual support-trivial point. -/
theorem secAbs_supportTrivialPoint_eq_zero_iff (x : X.an) (d : Fin r → ℤ) (f : K) :
    X.secAbs (X.supportTrivialPoint x).1 d f = 0 ↔ X.secAbs x.1 d f = 0 := by
  classical
  unfold secAbs
  split_ifs with hf
  · simp only [secAbsAt, ← bot_eq_zero, Finset.sup_eq_bot_iff]
    exact forall_congr' fun β => forall_congr' fun _ => homNorm_zeroScale_eq_zero_iff x.1 _ _
  · rfl

/-- The pole locus of the SAME whole original FS datum is detected at its
actual support-trivial points, without changing sections or weights. -/
theorem FSData.eval_supportTrivialPoint_eq_bot_iff {a : Fin r → ℚ} (D : X.FSData a)
    (x : X.an) : D.eval (X.supportTrivialPoint x) = ⊥ ↔ D.eval x = ⊥ := by
  have h : D.eval (X.supportTrivialPoint x) ≠ ⊥ ↔ D.eval x ≠ ⊥ := by
    simp only [D.eval_ne_bot_iff_exists_secAbs_ne_zero]
    exact exists_congr fun t => and_congr_right fun _ =>
      not_congr (secAbs_supportTrivialPoint_eq_zero_iff x D.deg t.1)
  exact not_iff_not.mp h

/-- Finiteness only at the genuine original support-trivial points forces the
original model class to be nef; singular values elsewhere are permitted. -/
theorem IsPSH.mem_nefCone_of_supportTrivialPoint_ne_bot {θ : Fin r → ℝ}
    {u : X.an → EReal} (hu : X.IsPSH θ u)
    (hfin : ∀ x, u (X.supportTrivialPoint x) ≠ ⊥) : θ ∈ X.nefCone := by
  obtain ⟨ι, _, _, _, a, f, hf, ha, -, hlim⟩ := hu.exists_isRatFS_net
  have hfinite (i : ι) : X.IsFinFS (a i) (f i) := by
    obtain ⟨D, hD, -, he⟩ := hf i
    apply X.isFinFS_iff.mpr
    refine ⟨D, hD, fun x => ?_, he⟩
    have hx : f i (X.supportTrivialPoint x) ≠ ⊥ := by
      apply ne_bot_of_le_ne_bot (hfin x)
      rw [hlim]
      exact iInf_le _ i
    rw [he] at hx
    exact fun hbot => hx ((D.eval_supportTrivialPoint_eq_bot_iff x).mpr hbot)
  apply X.isClosed_nefCone.mem_of_tendsto ha
  exact Eventually.of_forall fun i => X.coe_mem_nefCone (hfinite i).mem_semiampleCone

/-- General/non-unibranch PSH2 for limits finite on the actual support-trivial
points, allowing poles elsewhere on the original analytic space. -/
theorem isPSH_of_antitone_of_supportTrivialPoint_ne_bot {ι : Type u} [Preorder ι]
    [IsDirected ι (· ≤ ·)] [Nonempty ι] {θs : ι → Fin r → ℝ} {θ : Fin r → ℝ}
    (hθ : Tendsto θs atTop (𝓝 θ)) {u : ι → X.an → EReal}
    (hu : ∀ i, X.IsPSH (θs i) (u i)) (hanti : ∀ x, Antitone fun i => u i x)
    {w : X.an → EReal} (hw : ∀ x, w x = ⨅ i, u i x)
    (hfin : ∀ x, w (X.supportTrivialPoint x) ≠ ⊥) : X.IsPSH θ w := by
  have hi : ∀ i, θs i ∈ X.nefCone := by
    intro i
    apply (hu i).mem_nefCone_of_supportTrivialPoint_ne_bot
    intro x
    apply ne_bot_of_le_ne_bot (hfin x)
    rw [hw]
    exact iInf_le _ i
  have hn : θ ∈ X.nefCone := X.isClosed_nefCone.mem_of_tendsto hθ
    (Eventually.of_forall hi)
  exact isPSH_of_antitone hn hθ hu hanti hw
    ⟨X.supportTrivialPoint X.triv, hfin X.triv⟩

end EnvelopeProperty.MultiModel

#check @EnvelopeProperty.MultiModel.IsMultigraded.zeroScale
#check @EnvelopeProperty.MultiModel.IsNormalized.zeroScale
#check @EnvelopeProperty.MultiModel.supportTrivialPoint
#check @EnvelopeProperty.MultiModel.supportTrivialPoint_supp
#check @EnvelopeProperty.MultiModel.secAbs_supportTrivialPoint_eq_zero_iff
#check @EnvelopeProperty.MultiModel.FSData.eval_supportTrivialPoint_eq_bot_iff
#check @EnvelopeProperty.MultiModel.IsPSH.mem_nefCone_of_supportTrivialPoint_ne_bot
#check @EnvelopeProperty.MultiModel.isPSH_of_antitone_of_supportTrivialPoint_ne_bot
#print axioms EnvelopeProperty.MultiModel.IsMultigraded.zeroScale
#print axioms EnvelopeProperty.MultiModel.IsNormalized.zeroScale
#print axioms EnvelopeProperty.MultiModel.supportTrivialPoint
#print axioms EnvelopeProperty.MultiModel.supportTrivialPoint_supp
#print axioms EnvelopeProperty.MultiModel.secAbs_supportTrivialPoint_eq_zero_iff
#print axioms EnvelopeProperty.MultiModel.FSData.eval_supportTrivialPoint_eq_bot_iff
#print axioms EnvelopeProperty.MultiModel.IsPSH.mem_nefCone_of_supportTrivialPoint_ne_bot
#print axioms EnvelopeProperty.MultiModel.isPSH_of_antitone_of_supportTrivialPoint_ne_bot
