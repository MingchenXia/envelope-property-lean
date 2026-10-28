import EnvelopeProperty.AlgGeom.NativeNumericalPSHComparisonContinuationRayRealizations
import EnvelopeProperty.AlgGeom.NativeNumericalFiniteSpanTopology

/-! # Curve-weak numerical psh functions on an ample ray are fixed-ray psh functions

Let `X` be integral and projective over `k`, `L` an ample invertible sheaf and `a ≥ 0`.  The
fixed-ray class `NativeLineFubiniStudy.IsPSH p L hL a` uses decreasing nets of FS functions
`𝓗(L, a_j)`, `a_j ∈ ℚ`, `a_j → a`; BJ22's class `PSH(X, a[L])` (Definition 4.1,
`bj22-trivval:defi:psh`), formalized as `IsCurveWeakPSH p (a • [L])`, uses varying lines `M_j/m_j`
with classes converging to `a [L]`.  We prove `isCurveWeakPSH_iff_isPSH_ray`: the two classes
agree, under two explicit hypotheses which are standard theorems:

* `[FiniteDimensional ℝ (NativeRealNumericalClasses.Space p)]`: the real numerical space `N¹(X)`
  is finite dimensional (BJ22 works in the finite dimensional `N¹(X)`); it makes the ample cone
  open (`NativeRealNumericalClasses.isOpen_ampleCone_of_finiteDimensional`);
* `NumericalAmplenessCriterion p`: an invertible sheaf whose numerical class lies in the ample cone
  is ample (Kleiman's criterion; Lazarsfeld, *Positivity I*, Theorem 1.4.23 and Corollary 1.4.10).
  It is derived from the nef-plus-ample theorem in
  `EnvelopeProperty.AlgGeom.NativeNumericalPSHComparisonContinuationKleiman`.

Finite dimensionality of `N¹(X)` is not proved in this project.

The proof is that of BJ22 Theorem 4.15 (i) (`bj22-trivval:thm:pshample`): each `φ_{D_j}` lies in
`𝓗(L, b)` as soon as `b[L] - [D_j]` is ample (`FSData.isFS_ray_of_mem_ampleCone`), and the
coefficients `b` can be chosen rational, `≥ a`, and converging to `a` along the product net
`J × ℕ` (`isPSH_ray_of_antitone_net`).  The net argument itself uses only Kleiman's criterion and
the eventual ampleness of `(a + ε)[L] - [D_j]` for every `ε > 0`; finite dimensionality is used
only to deduce the latter from convergence of the classes in the curve-weak topology.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.MonoidalCategory Scheme.Modules
open Filter Topology
open scoped Classical NNReal ENNReal Topology

noncomputable section

universe u

namespace EnvelopeProperty.NativeRealNumericalClasses

variable {k : Type u} [Field k] {X : Scheme.{u}} (p : X ⟶ Spec (.of k)) [IsProjective p]

/-- If the numerical space is finite dimensional, the ample cone is open in it. -/
theorem isOpen_ampleCone_of_finiteDimensional [IsIntegral X] [FiniteDimensional ℝ (Space p)] :
    IsOpen (ampleCone p : Set (Space p)) := by
  let b := Module.finBasis ℝ (Space p)
  choose n L hL c hc using fun i => exists_finite_line_family p (b i)
  let L' : (Σ i, Fin (n i)) → X.Modules := fun x => L x.1 x.2
  let hL' : ∀ x, IsInvertible (L' x) := fun x => hL x.1 x.2
  let F := lineFamilyMap p L' hL'
  have hgen (x : Σ i, Fin (n i)) : lineClass p (L' x) (hL' x) ∈ LinearMap.range F := by
    refine LinearMap.mem_range.mpr ⟨Pi.single x 1, ?_⟩
    change ∑ y, (Pi.single x 1 : (Σ i, Fin (n i)) → ℝ) y • lineClass p (L' y) (hL' y) = _
    rw [Finset.sum_eq_single x]
    · simp
    · intro y _ hy
      simp [hy]
    · intro h
      exact absurd (Finset.mem_univ x) h
  have hbasis (i : Fin (Module.finrank ℝ (Space p))) : b i ∈ LinearMap.range F := by
    rw [hc i, lineFamilyMap_apply]
    exact Submodule.sum_mem _ fun t _ => Submodule.smul_mem _ _ (hgen ⟨i, t⟩)
  have htop : LinearMap.range F = ⊤ := by
    apply top_le_iff.mp
    rw [← b.span_eq]
    exact Submodule.span_le.mpr (by rintro _ ⟨i, rfl⟩; exact hbasis i)
  have hsurj : Function.Surjective F := LinearMap.range_eq_top.mp htop
  have himg : F '' (F ⁻¹' (ampleCone p : Set (Space p))) = ampleCone p :=
    Set.image_preimage_eq _ hsurj
  rw [← himg]
  exact LinearMap.isOpenMap_of_finiteDimensional F hsurj _
    (isOpen_lineFamilyMap_preimage_ampleCone p L' hL')

end EnvelopeProperty.NativeRealNumericalClasses

namespace EnvelopeProperty.NativeNumericalFubiniStudy

open Berkovich CanonicalGeometry

attribute [local instance] Scheme.Modules.monoidalCategory Scheme.Modules.symmetricCategory

variable {k : Type u} [Field k] {X : Scheme.{u}}

private local instance projectiveProper (p : X ⟶ Spec (.of k)) [IsProjective p] : IsProper p :=
  (ProjectiveFactorizationRingIso.of_isProjective p).isProper

variable (p : X ⟶ Spec (.of k)) [IsProjective p]

/-- Kleiman's criterion for `p`: every invertible sheaf whose numerical class lies in the ample
cone is ample.  This is a hypothesis of the comparison theorems below; it is not proved here. -/
def NumericalAmplenessCriterion : Prop :=
  ∀ (T : X.Modules) (hT : IsInvertible T),
    NativeRealNumericalClasses.lineClass p T hT ∈ NativeRealNumericalClasses.ampleCone p →
      SchemeLineAmpleness.IsAmple p T

/-- Under Kleiman's criterion: if `b ≥ 0` is rational and `b [L] - [D]` is ample, then the function
of a nonzero datum `D` lies in `𝓗(L, b)` (BJ22 Proposition 2.19 (iii)). -/
theorem FSData.isFS_ray_of_mem_ampleCone [IsIntegral X] (hK : NumericalAmplenessCriterion p)
    (D : FSData X) (hD : D.Nonzero) (L : X.Modules) (hL : IsInvertible L) (b : ℚ) (hb0 : 0 ≤ b)
    (hb : (b : ℝ) • NativeRealNumericalClasses.lineClass p L hL - D.numericalClass p ∈
      NativeRealNumericalClasses.ampleCone p) :
    NativeLineFubiniStudy.IsFS p L hL b (D.eval p) := by
  have hden : 0 < b.den := b.den_pos
  have hnum : ((b.num.toNat : ℕ) : ℚ) = (b.num : ℚ) := by
    exact_mod_cast Int.toNat_of_nonneg (Rat.num_nonneg.mpr hb0)
  have hm : (D.m : ℚ) ≠ 0 := by exact_mod_cast D.m_pos.ne'
  have hq : ((D.m * b.num.toNat : ℕ) : ℚ) / ((D.m : ℚ) * (b.den : ℚ)) = b := by
    rw [Nat.cast_mul, mul_div_mul_left _ _ hm, hnum, Rat.num_div_den]
  have hqR : ((D.m * b.num.toNat : ℕ) : ℝ) / ((D.m * b.den : ℕ) : ℝ) = (b : ℝ) := by
    have h := congrArg (fun z : ℚ => (z : ℝ)) hq
    simpa only [Rat.cast_div, Rat.cast_mul, Rat.cast_natCast, Nat.cast_mul] using h
  have hA := hK _
    ((TensorPowerBaseIdealGrading.tensorPower_isInvertible hL (D.m * b.num.toNat)).monoidalTensor
      (TensorPowerBaseIdealGrading.tensorPower_isInvertible D.invertible b.den).dual) (by
    rw [D.lineClass_ampleDifference p L hL b.den (D.m * b.num.toNat) hden, hqR]
    exact (NativeRealNumericalClasses.ampleCone p).smul_mem
      (by exact_mod_cast Nat.mul_pos D.m_pos hden) hb)
  have h := D.isFS_ray_of_ample_difference hD p L hL b.den (D.m * b.num.toNat) hden hA
  exact hq ▸ h

/-- For an ample `L` and any varying-line datum `D`, some `t > 0` makes `t [L] - [D]` ample. -/
theorem FSData.exists_ray_coefficient [IsIntegral X] (D : FSData X) (L : X.Modules)
    (hLA : SchemeLineAmpleness.IsAmple p L) :
    ∃ t : ℝ, 0 < t ∧ t • NativeRealNumericalClasses.lineClass p L hLA.isInvertible -
      D.numericalClass p ∈ NativeRealNumericalClasses.ampleCone p := by
  obtain ⟨ε, hε, hrad⟩ := NativeRealNumericalClasses.exists_ampleCone_lineFamily_radius p
    (fun _ : Fin 1 => D.line) (fun _ => D.invertible) _
    (NativeRealNumericalClasses.ampleLineClass_mem_ampleCone p L hLA)
  have hm : (0 : ℝ) < D.m := by exact_mod_cast D.m_pos
  have h := hrad (fun _ => -(ε / 2)) (fun _ => by
    show |-(ε / 2)| < ε
    rw [abs_neg, abs_of_pos (half_pos hε)]
    exact half_lt_self hε)
  simp only [NativeRealNumericalClasses.lineFamilyMap_apply, Fin.sum_univ_one] at h
  have hcpos : 0 < (ε / 2 * (D.m : ℝ))⁻¹ := inv_pos.mpr (mul_pos (half_pos hε) hm)
  have hcalc : (ε / 2 * (D.m : ℝ))⁻¹ * -(ε / 2) = -(D.m : ℝ)⁻¹ := by
    rw [mul_neg, mul_inv, mul_comm (ε / 2)⁻¹, mul_assoc, inv_mul_cancel₀ (half_pos hε).ne',
      mul_one]
  refine ⟨(ε / 2 * (D.m : ℝ))⁻¹, hcpos, ?_⟩
  have h2 := (NativeRealNumericalClasses.ampleCone p).smul_mem hcpos h
  have he : (ε / 2 * (D.m : ℝ))⁻¹ • (NativeRealNumericalClasses.lineClass p L hLA.isInvertible +
      -(ε / 2) • NativeRealNumericalClasses.lineClass p D.line D.invertible) =
      (ε / 2 * (D.m : ℝ))⁻¹ • NativeRealNumericalClasses.lineClass p L hLA.isInvertible -
        D.numericalClass p := by
    rw [smul_add, smul_smul, hcalc, neg_smul, ← sub_eq_add_neg]
    rfl
  rwa [he] at h2

/-- **The net argument of BJ22 Theorem 4.15 (i) on an ample ray.**  Assume Kleiman's criterion.
Let `L` be ample, `a ≥ 0`, and let `φ` be the decreasing limit of the functions of a net of
nonzero varying-line data `D_j` such that, for every `ε > 0`, eventually `(a + ε)[L] - [D_j]` is
ample.  Then `φ` is a fixed-ray psh function of `(L, a)`. -/
theorem isPSH_ray_of_antitone_net [IsIntegral X]
    (hK : NumericalAmplenessCriterion p) (L : X.Modules) (hLA : SchemeLineAmpleness.IsAmple p L)
    {a : ℝ} (ha : 0 ≤ a)
    {φ : RelativeSchemeValuedPoint (1 : _root_.Valuation k ℝ≥0) p → EReal}
    (hfin : ∃ y, φ y ≠ ⊥) (husc : UpperSemicontinuous φ)
    {J : Type u} [Preorder J] [IsDirected J (· ≤ ·)] [Nonempty J]
    (D : J → FSData X) (hD : ∀ j, (D j).Nonzero)
    (hev : ∀ ε : ℝ, 0 < ε → ∀ᶠ j in atTop,
      (a + ε) • NativeRealNumericalClasses.lineClass p L hLA.isInvertible -
        (D j).numericalClass p ∈ NativeRealNumericalClasses.ampleCone p)
    (hanti : ∀ y, Antitone fun j => (D j).eval p y)
    (hinf : ∀ y, φ y = ⨅ j, (D j).eval p y) :
    NativeLineFubiniStudy.IsPSH p L hLA.isInvertible a φ := by
  set ℓ := NativeRealNumericalClasses.lineClass p L hLA.isInvertible
  have hℓA : ℓ ∈ NativeRealNumericalClasses.ampleCone p :=
    NativeRealNumericalClasses.ampleLineClass_mem_ampleCone p L hLA
  -- the admissible coefficients for `D j`
  let T : J → Set ℝ := fun j => {t | a ≤ t ∧
    t • ℓ - (D j).numericalClass p ∈ NativeRealNumericalClasses.ampleCone p}
  have hup (j : J) {s t : ℝ} (hst : s < t)
      (hs : s • ℓ - (D j).numericalClass p ∈ NativeRealNumericalClasses.ampleCone p) :
      t • ℓ - (D j).numericalClass p ∈ NativeRealNumericalClasses.ampleCone p := by
    have h := (NativeRealNumericalClasses.ampleCone p).add_mem hs
      ((NativeRealNumericalClasses.ampleCone p).smul_mem (sub_pos.mpr hst) hℓA)
    have he : s • ℓ - (D j).numericalClass p + (t - s) • ℓ =
        t • ℓ - (D j).numericalClass p := by
      rw [sub_smul]
      abel
    rwa [he] at h
  have hTne (j : J) : (T j).Nonempty := by
    obtain ⟨t, -, ht⟩ := (D j).exists_ray_coefficient p L hLA
    exact ⟨max t a + 1, (le_max_right t a).trans (lt_add_one _).le,
      hup j ((le_max_left t a).trans_lt (lt_add_one _)) ht⟩
  have hTbdd (j : J) : BddBelow (T j) := ⟨a, fun t ht => ht.1⟩
  choose b hb₁ hb₂ using fun x : J × ℕ =>
    exists_rat_btwn (lt_add_of_pos_right (sInf (T x.1)) (Nat.one_div_pos_of_nat (n := x.2)))
  have hbT (x : J × ℕ) : (b x : ℝ) ∈ T x.1 := by
    obtain ⟨t, ht, htb⟩ := exists_lt_of_csInf_lt (hTne x.1) (hb₁ x)
    exact ⟨ht.1.trans htb.le, hup x.1 htb ht.2⟩
  have hdirP : IsDirected (J × ℕ) (· ≤ ·) := ⟨fun x y => by
    obtain ⟨j, hxj, hyj⟩ := directed_of (· ≤ ·) x.1 y.1
    exact ⟨(j, max x.2 y.2), ⟨hxj, le_max_left _ _⟩, ⟨hyj, le_max_right _ _⟩⟩⟩
  refine ⟨hfin, husc, J × ℕ, inferInstance, hdirP, inferInstance, b,
    fun x => (D x.1).eval p, fun x => ?_, ?_, fun y => ?_, fun y => ?_⟩
  · exact (D x.1).isFS_ray_of_mem_ampleCone p hK (hD x.1) L hLA.isInvertible (b x)
      (by exact_mod_cast ha.trans (hbT x).1) (hbT x).2
  · refine tendsto_order.2 ⟨fun c hc => Eventually.of_forall fun x => hc.trans_le (hbT x).1,
      fun c hc => ?_⟩
    have hε : 0 < (c - a) / 2 := half_pos (sub_pos.mpr hc)
    obtain ⟨j₀, hj₀⟩ := eventually_atTop.mp (hev _ hε)
    obtain ⟨n₀, hn₀⟩ := exists_nat_one_div_lt hε
    refine Filter.mem_of_superset (Filter.mem_atTop (j₀, n₀)) fun x hx => ?_
    have hx' : (j₀, n₀) ≤ x := hx
    have hσ : sInf (T x.1) ≤ a + (c - a) / 2 :=
      csInf_le (hTbdd x.1) ⟨le_add_of_nonneg_right hε.le, hj₀ x.1 hx'.1⟩
    have hn : 1 / ((x.2 : ℝ) + 1) ≤ 1 / ((n₀ : ℝ) + 1) := Nat.one_div_le_one_div hx'.2
    have hbx := hb₂ x
    change (b x : ℝ) < c
    linarith
  · intro x x' hxx'
    exact hanti y hxx'.1
  · rw [hinf y, iInf_prod]
    simp only [iInf_const]

/-- **Comparison on an ample ray.**  Assume `N¹(X)` finite dimensional and Kleiman's criterion.
For an ample `L` and `a ≥ 0`, every curve-weak numerical psh function of class `a [L]` is a
fixed-ray psh function of `(L, a)`. -/
theorem isPSH_ray_of_isCurveWeakPSH [IsIntegral X]
    [FiniteDimensional ℝ (NativeRealNumericalClasses.Space p)]
    (hK : NumericalAmplenessCriterion p) (L : X.Modules) (hLA : SchemeLineAmpleness.IsAmple p L)
    {a : ℝ} (ha : 0 ≤ a)
    {φ : RelativeSchemeValuedPoint (1 : _root_.Valuation k ℝ≥0) p → EReal}
    (h : IsCurveWeakPSH p (a • NativeRealNumericalClasses.lineClass p L hLA.isInvertible) φ) :
    NativeLineFubiniStudy.IsPSH p L hLA.isInvertible a φ := by
  obtain ⟨hfin, husc, J, hJ, hdir, hne, D, hD, hconv, hanti, hinf⟩ := h
  have hopen := NativeRealNumericalClasses.isOpen_ampleCone_of_finiteDimensional p
  have hℓA := NativeRealNumericalClasses.ampleLineClass_mem_ampleCone p L hLA
  refine isPSH_ray_of_antitone_net p hK L hLA ha hfin husc D hD (fun ε hε => ?_) hanti hinf
  have hlim : Tendsto (fun j => (a + ε) •
      NativeRealNumericalClasses.lineClass p L hLA.isInvertible -
      (D j).numericalClass p) atTop
      (𝓝 ((a + ε) • NativeRealNumericalClasses.lineClass p L hLA.isInvertible -
        a • NativeRealNumericalClasses.lineClass p L hLA.isInvertible)) :=
    tendsto_const_nhds.sub hconv
  have hmem : (a + ε) • NativeRealNumericalClasses.lineClass p L hLA.isInvertible -
      a • NativeRealNumericalClasses.lineClass p L hLA.isInvertible ∈
        NativeRealNumericalClasses.ampleCone p := by
    rw [add_smul, add_sub_cancel_left]
    exact (NativeRealNumericalClasses.ampleCone p).smul_mem hε hℓA
  exact hlim.eventually_mem (hopen.mem_nhds hmem)

/-- **Comparison on an ample ray**, both directions: under the finite dimensionality of `N¹(X)`
and Kleiman's criterion, for an ample `L` and `a ≥ 0`, BJ22's `PSH(X, a [L])` (curve-weak
numerical psh functions of class `a [L]`) coincides with the fixed-ray psh class of `(L, a)`. -/
theorem isCurveWeakPSH_iff_isPSH_ray [IsIntegral X]
    [FiniteDimensional ℝ (NativeRealNumericalClasses.Space p)]
    (hK : NumericalAmplenessCriterion p) (L : X.Modules) (hLA : SchemeLineAmpleness.IsAmple p L)
    {a : ℝ} (ha : 0 ≤ a)
    (φ : RelativeSchemeValuedPoint (1 : _root_.Valuation k ℝ≥0) p → EReal) :
    IsCurveWeakPSH p (a • NativeRealNumericalClasses.lineClass p L hLA.isInvertible) φ ↔
      NativeLineFubiniStudy.IsPSH p L hLA.isInvertible a φ :=
  ⟨isPSH_ray_of_isCurveWeakPSH p hK L hLA ha, isCurveWeakPSH_of_ray p L hLA.isInvertible⟩

end EnvelopeProperty.NativeNumericalFubiniStudy
