import EnvelopeProperty.Berkovich.SpectrumDiscComponents

/-!
# Explicit centred inflation on the actual Berkovich line

The point space and its topology are the original relative seminorm spectrum.
The construction works over any coefficient ring with a real-valued valuation.
Every translated linear coordinate has an exact inflation formula. In particular
inflation preserves closed discs and complements of open discs simultaneously.
-/

open scoped NNReal Polynomial Topology
open Polynomial Topology
noncomputable section

namespace EnvelopeProperty.Berkovich.RelativeSpectrum

variable {F : Type*} [CommRing F] {v : Valuation F ℝ≥0}

theorem fcTranslate_val_X_sub_C (a b : F) (x : RelativeSpectrum v F[X]) :
    val (polynomialTranslation a x) (X - C b) = val x (X - C (b-a)) := by
  change val x (Polynomial.algEquivAevalXAddC a (X-C b)) = _
  congr 1
  simp [Polynomial.algEquivAevalXAddC]
  ring

theorem fcTranslate_add (a b : F) (x : RelativeSpectrum v F[X]) :
    polynomialTranslation a (polynomialTranslation b x) = polynomialTranslation (a+b) x := by
  have he : (Polynomial.algEquivAevalXAddC b).toAlgHom.comp
      (Polynomial.algEquivAevalXAddC a).toAlgHom =
        (Polynomial.algEquivAevalXAddC (a+b)).toAlgHom := by
    apply Polynomial.algHom_ext
    simp [Polynomial.algEquivAevalXAddC]
    ring
  apply ext_val
  intro p
  change val x (Polynomial.algEquivAevalXAddC b
    (Polynomial.algEquivAevalXAddC a p)) = _
  exact congrArg (fun f : F[X] →ₐ[F] F[X] => val x (f p)) he

@[simp]
theorem fcTranslate_zero (x : RelativeSpectrum v F[X]) : polynomialTranslation 0 x = x := by
  apply ext_val
  intro p
  change val x (Polynomial.algEquivAevalXAddC 0 p) = val x p
  simp [Polynomial.algEquivAevalXAddC]

/-- The coefficient restriction of an actual line point is the prescribed base point. -/
theorem fc_proj_eq_self (x : RelativeSpectrum v F[X]) : proj x = self v := by
  apply ext_val
  intro c
  exact x.2 c

/-- The exact linear-coordinate formula for the original whole inflation. -/
theorem fc_polynomialGaussInflation_val_X_sub_C
    (x : RelativeSpectrum v F[X]) (r : ℝ≥0) (b : F) :
    val (polynomialGaussInflation x r) (X-C b) = max (val x (X-C b)) r := by
  rw [polynomialGaussInflation_val_apply]
  have he : Polynomial.algEquivAevalXAddC (X : F[X])
      ((X-C b).map (Polynomial.C : F →+* F[X])) = X + C (X-C b) := by
    simp [Polynomial.algEquivAevalXAddC]
    ring
  rw [he]
  apply le_antisymm
  · exact (val (gauss x r)).map_add _ _ |>.trans_eq (by
      rw [gauss_val_X,gauss_val_C,max_comm])
  · apply max_le
    · have hc : ((X : F[X][X])+C (X-C b : F[X])).coeff 0 = (X-C b : F[X]) := by
        simp only [Polynomial.coeff_add,Polynomial.coeff_X_zero,Polynomial.coeff_C_zero,zero_add]
      have h := Spectrum.le_gauss_val x.1 r ((X : F[X][X])+C (X-C b : F[X])) 0
      rw [hc,pow_zero,mul_one] at h
      exact h
    · have hc : ((X : F[X][X])+C (X-C b : F[X])).coeff 1 = (1 : F[X]) := by
        simp only [Polynomial.coeff_add,Polynomial.coeff_X_one,Polynomial.coeff_C_succ,add_zero]
      have h := Spectrum.le_gauss_val x.1 r ((X : F[X][X])+C (X-C b : F[X])) 1
      rw [hc,pow_one,map_one,one_mul] at h
      exact h

/-- Inflation with a fixed centre, defined on the original complete point data. -/
def fcCenteredInflation (a : F) (x : RelativeSpectrum v F[X]) (r : ℝ≥0) :
    RelativeSpectrum v F[X] :=
  polynomialTranslation a (polynomialGaussInflation (polynomialTranslation (-a) x) r)

@[fun_prop]
theorem continuous_fcCenteredInflation_prod (a : F) :
    Continuous fun p : RelativeSpectrum v F[X] × ℝ≥0 =>
      fcCenteredInflation a p.1 p.2 := by
  rw [continuous_iff]
  intro p
  change Continuous fun z : RelativeSpectrum v F[X] × ℝ≥0 =>
    val (polynomialGaussInflation (polynomialTranslation (-a) z.1) z.2)
      (Polynomial.algEquivAevalXAddC a p)
  simp only [polynomialGaussInflation_val_apply,gauss_val_apply]
  apply Continuous.finset_sup_apply
  intro i _
  simpa only [Pi.mul_def,Function.comp_apply,Pi.pow_apply] using
    (((continuous_val_apply _).comp
      ((polynomialTranslation (R := F) (A := F) (v := v) (-a)).continuous.comp continuous_fst)).mul
        (continuous_snd.pow i))

@[fun_prop]
theorem continuous_fcCenteredInflation (a : F) (x : RelativeSpectrum v F[X]) :
    Continuous (fcCenteredInflation a x) := by
  change Continuous ((fun p : RelativeSpectrum v F[X] × ℝ≥0 =>
    fcCenteredInflation a p.1 p.2) ∘ (fun r : ℝ≥0 => (x,r)))
  exact (continuous_fcCenteredInflation_prod a).comp (continuous_const.prodMk continuous_id)

@[simp]
theorem fcCenteredInflation_zero (a : F) (x : RelativeSpectrum v F[X]) :
    fcCenteredInflation a x 0 = x := by
  simp only [fcCenteredInflation, polynomialGaussInflation_zero, fcTranslate_add,
    add_neg_cancel, fcTranslate_zero]

/-- The exact value of every translated coordinate is retained, including all hole coordinates. -/
theorem fcCenteredInflation_val_X_sub_C (a : F) (x : RelativeSpectrum v F[X])
    (r : ℝ≥0) (b : F) :
    val (fcCenteredInflation a x r) (X-C b) = max (val x (X-C b)) r := by
  rw [fcCenteredInflation, fcTranslate_val_X_sub_C,
    fc_polynomialGaussInflation_val_X_sub_C, fcTranslate_val_X_sub_C]
  rw [show (b-a)-(-a) = b by ring]

/-- At the outer radius the entire original point is the centred Gauss point. -/
theorem fcCenteredInflation_eq_gauss (a : F) (x : RelativeSpectrum v F[X])
    (r : ℝ≥0) (hx : val x (X-C a) ≤ r) :
    fcCenteredInflation a x r = centeredGauss (self v) a r := by
  have hx' : val (polynomialTranslation (-a) x) X ≤ r := by
    change val x (Polynomial.algEquivAevalXAddC (-a) X) ≤ r
    simpa [Polynomial.algEquivAevalXAddC, sub_eq_add_neg] using hx
  rw [fcCenteredInflation, polynomialGaussInflation_eq_gauss _ _ hx', fc_proj_eq_self]
  rfl

/-- All translated linear functions have their exact value at a genuine Gauss point. -/
theorem fc_centeredGauss_val_X_sub_C (a b : F) (r : ℝ≥0) :
    val (centeredGauss (self v) a r) (X-C b) = max (v (a-b)) r := by
  rw [centeredGauss_val_apply]
  have he : Polynomial.algEquivAevalXAddC a (X-C b) = X+C (a-b) := by
    simp [Polynomial.algEquivAevalXAddC]
    ring
  rw [he]
  apply le_antisymm
  · exact (val (gauss (self v) r)).map_add _ _ |>.trans_eq (by
      rw [gauss_val_X,gauss_val_C]
      change max r (v (a-b)) = max (v (a-b)) r
      exact max_comm _ _)
  · apply max_le
    · simpa using Spectrum.le_gauss_val (self v).1 r ((X : F[X])+C (a-b)) 0
    · simpa using Spectrum.le_gauss_val (self v).1 r ((X : F[X])+C (a-b)) 1

/-- Centres in one actual closed disc give the same entire Gauss point at its radius. -/
theorem fc_centeredGauss_eq_of_center_dist_le (a b : F) (r : ℝ≥0)
    (hab : v (b-a) ≤ r) : centeredGauss (self v) b r = centeredGauss (self v) a r := by
  have hfix : polynomialTranslation (b-a) (gauss (self v) r) = gauss (self v) r :=
    centeredGauss_eq_gauss_of_val_le (self v) (b-a) r hab
  calc
    centeredGauss (self v) b r =
        polynomialTranslation a (polynomialTranslation (b-a) (gauss (self v) r)) := by
      rw [fcTranslate_add, show a+(b-a) = b by ring]
      rfl
    _ = centeredGauss (self v) a r := by rw [hfix]; rfl

/-- Radius-zero discs consist of the entire original evaluation point, over arbitrary rings. -/
theorem fc_closedDisc_zero (a : F) :
    {x : RelativeSpectrum v F[X] | val x (X-C a) ≤ 0} = {centeredGauss (self v) a 0} := by
  ext x
  simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff]
  constructor
  · intro hx
    simpa only [fcCenteredInflation_zero] using fcCenteredInflation_eq_gauss a x 0 hx
  · intro hx
    rw [hx,centeredGauss_val_X_sub_C]

/-- A translated closed disc is compact in the actual line topology. -/
theorem fc_isCompact_closedDisc (a : F) (r : ℝ≥0) :
    IsCompact {x : RelativeSpectrum v F[X] | val x (X-C a) ≤ r} := by
  have hc : IsCompact {x : RelativeSpectrum v F[X] | val x X ≤ r} := by
    simpa only [fc_proj_eq_self, true_and] using isCompact_fibreDisc (self v) r
  have he : (polynomialTranslation (v := v) a) '' {x : RelativeSpectrum v F[X] | val x X ≤ r} =
      {x : RelativeSpectrum v F[X] | val x (X-C a) ≤ r} := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      change val y X ≤ r at hy
      change val (polynomialTranslation a y) (X-C a) ≤ r
      simpa only [fcTranslate_val_X_sub_C, sub_self, map_zero, sub_zero] using hy
    · intro hx
      refine ⟨polynomialTranslation (-a) x, ?_, ?_⟩
      · change val x (Polynomial.algEquivAevalXAddC (-a) X) ≤ r
        simpa [Polynomial.algEquivAevalXAddC, sub_eq_add_neg] using hx
      · simp only [fcTranslate_add, add_neg_cancel, fcTranslate_zero]
  rw [← he]
  exact hc.image (polynomialTranslation a).continuous

/-- The two actual linear coordinates differ by the original constant. -/
theorem fc_linear_bound (x : RelativeSpectrum v F[X]) (a b : F) :
    val x (X-C b) ≤ max (val x (X-C a)) (v (a-b)) := by
  have he : (X-C b : F[X]) = (X-C a)+C (a-b) := by
    simp only [map_sub]
    ring
  rw [he]
  exact (val x).map_add _ _ |>.trans (by rw [show val x (C (a-b)) = v (a-b) from x.2 _])

theorem fc_center_distance_bound (x : RelativeSpectrum v F[X]) (a b : F) :
    v (a-b) ≤ max (val x (X-C a)) (val x (X-C b)) := by
  have he : (C (a-b) : F[X]) = (X-C b)-(X-C a) := by
    simp only [map_sub]
    ring
  rw [← show val x (C (a-b)) = v (a-b) from x.2 _, he]
  exact ((val x).map_sub _ _).trans_eq (max_comm _ _)

section AlgebraicallyClosed

variable {K : Type*} [Field K] [IsAlgClosed K] {w : Valuation K ℝ≥0}

/-- Over an algebraically closed field all linear coordinate values determine the entire point. -/
theorem fc_ext_linear (x y : RelativeSpectrum w K[X])
    (h : ∀ a : K, val x (X-C a) = val y (X-C a)) : x = y :=
  eq_of_linear_values h

/-- The actual line topology is already determined by its linear coordinate evaluations. -/
theorem fc_continuous_iff_linear {Z : Type*} [TopologicalSpace Z]
    {g : Z → RelativeSpectrum w K[X]} :
    Continuous g ↔ ∀ a : K, Continuous fun z => val (g z) (X-C a) := by
  constructor
  · intro hg a
    exact (continuous_val_apply _).comp hg
  · intro h
    have hp : ∀ s : Multiset K,
        Continuous fun z => val (g z) ((s.map fun a => X-C a).prod) := by
      intro s
      induction s using Multiset.induction_on with
      | empty => simpa using (continuous_const : Continuous fun _ : Z => (1 : ℝ≥0))
      | @cons a s ih =>
        simpa only [Multiset.map_cons, Multiset.prod_cons, map_mul,Pi.mul_def] using (h a).mul ih
    apply continuous_iff.mpr
    intro p
    have he : (fun z => val (g z) p) =
        (fun z => w p.leadingCoeff * val (g z) ((p.roots.map fun a => X-C a).prod)) := by
      funext z
      conv_lhs => rw [(IsAlgClosed.splits p).eq_prod_roots, map_mul]
      rw [show val (g z) (C p.leadingCoeff) = w p.leadingCoeff from (g z).2 _]
    rw [he]
    exact continuous_const.mul (hp p.roots)

/-- A non-Gauss point in a closed disc lies in an actual strict residue-class disc. -/
theorem fc_exists_strict_residue_disc (x : RelativeSpectrum w K[X]) (a : K) (r : ℝ≥0)
    (hx : val x (X-C a) ≤ r) (hne : x ≠ centeredGauss (self w) a r) :
    ∃ b : K, w (a-b) ≤ r ∧ val x (X-C b) < r := by
  let x' := polynomialTranslation (-a) x
  have hx' : val x' X ≤ r := by
    change val x (Polynomial.algEquivAevalXAddC (-a) X) ≤ r
    simpa [Polynomial.algEquivAevalXAddC, sub_eq_add_neg] using hx
  let y : CoordinateDisc (A := K) w r := ⟨x',hx'⟩
  have hne' : y ≠ discGaussPoint w r := by
    intro h
    have hy : x' = gauss (self w) r := congrArg
      (fun z : CoordinateDisc (A := K) w r => z.1) h
    have hh := congrArg (polynomialTranslation a) hy
    change polynomialTranslation a (polynomialTranslation (-a) x) =
      centeredGauss (self w) a r at hh
    rw [fcTranslate_add, add_neg_cancel, fcTranslate_zero] at hh
    exact hne hh
  obtain ⟨b,hb,hby⟩ := exists_mem_discBranch_of_ne_gauss r y hne'
  refine ⟨b+a, ?_, ?_⟩
  · simpa only [show a-(b+a) = -b by ring, Valuation.map_neg] using hb
  · change val (polynomialTranslation (-a) x) (X-C b) < r at hby
    rw [fcTranslate_val_X_sub_C] at hby
    simpa only [sub_neg_eq_add] using hby

/-- Every point of a closed disc other than its original Gauss point is interior. -/
theorem fc_mem_interior_closedDisc (x : RelativeSpectrum w K[X]) (a : K) (r : ℝ≥0)
    (hx : val x (X-C a) ≤ r) (hne : x ≠ centeredGauss (self w) a r) :
    x ∈ interior {z : RelativeSpectrum w K[X] | val z (X-C a) ≤ r} := by
  obtain ⟨b, hb, hxb⟩ := fc_exists_strict_residue_disc x a r hx hne
  have hsym : w (b-a) = w (a-b) := by
    rw [show b-a = -(a-b) by ring, Valuation.map_neg]
  have hsub : {z : RelativeSpectrum w K[X] | val z (X-C b) < r} ⊆
      {z : RelativeSpectrum w K[X] | val z (X-C a) ≤ r} := by
    intro z hz
    exact (fc_linear_bound z b a).trans (max_le hz.le (hsym ▸ hb))
  exact interior_maximal hsub (isOpen_lt (continuous_val_apply _) continuous_const) hxb

end AlgebraicallyClosed

/-- The original outer Gauss point is approached by actual points outside the closed disc. -/
theorem fc_gauss_not_mem_interior_closedDisc (a : F) (r : ℝ≥0) :
    centeredGauss (self v) a r ∉
      interior {z : RelativeSpectrum v F[X] | val z (X-C a) ≤ r} := by
  intro h
  have hr : r ∈ closure (Set.Ioi r) := by
    rw [closure_Ioi]
    exact (le_rfl : r ≤ r)
  have hn := (continuous_centeredGauss (self v) a).continuousAt.eventually
    (isOpen_interior.mem_nhds h)
  obtain ⟨s, hs, hmem⟩ := ((mem_closure_iff_frequently.mp hr).and_eventually hn).exists
  have hval := interior_subset hmem
  change val (centeredGauss (self v) a s) (X-C a) ≤ r at hval
  rw [centeredGauss_val_X_sub_C] at hval
  exact not_le_of_gt hs hval

/-- The inner Gauss point is approached through the actual removed open disc. -/
theorem fc_gauss_not_mem_interior_discExterior (a : F) (r : ℝ≥0) (hr : 0 < r) :
    centeredGauss (self v) a r ∉
      interior {z : RelativeSpectrum v F[X] | r ≤ val z (X-C a)} := by
  intro h
  have hr' : r ∈ closure (Set.Iio r) := by
    rw [closure_Iio' (show (Set.Iio r).Nonempty from ⟨0,hr⟩)]
    exact (le_rfl : r ≤ r)
  have hn := (continuous_centeredGauss (self v) a).continuousAt.eventually
    (isOpen_interior.mem_nhds h)
  obtain ⟨s, hs, hmem⟩ := ((mem_closure_iff_frequently.mp hr').and_eventually hn).exists
  have hval := interior_subset hmem
  change r ≤ val (centeredGauss (self v) a s) (X-C a) at hval
  rw [centeredGauss_val_X_sub_C] at hval
  exact not_le_of_gt hs hval

section AlgebraicallyClosed

variable {K : Type*} [Field K] [IsAlgClosed K] {w : Valuation K ℝ≥0}

/-- The full topological interior of an actual closed disc removes precisely its Gauss point. -/
theorem fc_interior_closedDisc (a : K) (r : ℝ≥0) :
    interior {x : RelativeSpectrum w K[X] | val x (X-C a) ≤ r} =
      {x : RelativeSpectrum w K[X] | val x (X-C a) ≤ r} \ {centeredGauss (self w) a r} := by
  ext x
  simp only [Set.mem_sdiff, Set.mem_ofPred_eq, Set.mem_singleton_iff]
  constructor
  · intro hx
    have hmem : x ∈ {z : RelativeSpectrum w K[X] | val z (X-C a) ≤ r} :=
      interior_subset hx
    refine ⟨hmem, ?_⟩
    intro he
    exact fc_gauss_not_mem_interior_closedDisc a r (he ▸ hx)
  · rintro ⟨hx, hne⟩
    exact fc_mem_interior_closedDisc x a r hx hne

/-- Every other point of the complement of an open disc is interior. -/
theorem fc_mem_interior_discExterior (x : RelativeSpectrum w K[X]) (a : K) (r : ℝ≥0)
    (hx : r ≤ val x (X-C a)) (hne : x ≠ centeredGauss (self w) a r) :
    x ∈ interior {z : RelativeSpectrum w K[X] | r ≤ val z (X-C a)} := by
  by_cases hstrict : r < val x (X-C a)
  · exact interior_maximal (fun _ hz => hz.le)
      (isOpen_lt continuous_const (continuous_val_apply (X-C a))) hstrict
  · have heq : val x (X-C a) = r := le_antisymm (le_of_not_gt hstrict) hx
    obtain ⟨b, hb, hxb⟩ := fc_exists_strict_residue_disc x a r heq.le hne
    have hsym : w (b-a) = w (a-b) := by
      rw [show b-a = -(a-b) by ring, Valuation.map_neg]
    have hbr : r ≤ w (a-b) := by
      have hc := fc_linear_bound x b a
      rw [heq,hsym] at hc
      apply le_of_not_gt
      intro hbad
      exact not_lt_of_ge hc (max_lt hxb hbad)
    have hsub : {z : RelativeSpectrum w K[X] | val z (X-C b) < r} ⊆
        {z : RelativeSpectrum w K[X] | r ≤ val z (X-C a)} := by
      intro z hz
      change val z (X-C b) < r at hz
      change r ≤ val z (X-C a)
      have hc := fc_center_distance_bound z a b
      apply le_of_not_gt
      intro hbad
      exact not_lt_of_ge (hbr.trans hc) (max_lt hbad hz)
    exact interior_maximal hsub (isOpen_lt (continuous_val_apply _) continuous_const) hxb

/-- The full interior of an open-disc complement removes precisely the original inner Gauss point. -/
theorem fc_interior_discExterior (a : K) (r : ℝ≥0) (hr : 0 < r) :
    interior {x : RelativeSpectrum w K[X] | r ≤ val x (X-C a)} =
      {x : RelativeSpectrum w K[X] | r ≤ val x (X-C a)} \ {centeredGauss (self w) a r} := by
  ext x
  simp only [Set.mem_sdiff, Set.mem_ofPred_eq, Set.mem_singleton_iff]
  constructor
  · intro hx
    have hmem : x ∈ {z : RelativeSpectrum w K[X] | r ≤ val z (X-C a)} :=
      interior_subset hx
    refine ⟨hmem, ?_⟩
    intro he
    exact fc_gauss_not_mem_interior_discExterior a r hr (he ▸ hx)
  · rintro ⟨hx, hne⟩
    exact fc_mem_interior_discExterior x a r hx hne

end AlgebraicallyClosed

section NormedField

variable {K : Type*} [NormedField K] [IsUltrametricDist K] [IsAlgClosed K]

/-- Centre and radius jointly vary continuously for the whole genuine Gauss point. -/
theorem fc_continuous_centeredGauss_prod :
    Continuous fun p : K × ℝ≥0 =>
      centeredGauss (self (NormedField.valuation (K := K))) p.1 p.2 := by
  apply fc_continuous_iff_linear.mpr
  intro b
  simp only [fc_centeredGauss_val_X_sub_C]
  change Continuous fun p : K × ℝ≥0 => max ‖p.1-b‖₊ p.2
  exact ((continuous_nnnorm.comp (continuous_fst.sub continuous_const)).max continuous_snd)

end NormedField

end EnvelopeProperty.Berkovich.RelativeSpectrum
