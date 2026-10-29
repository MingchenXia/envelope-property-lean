import EnvelopeProperty.AlgGeom.GaussRegularSurfaceRealNorms
import EnvelopeProperty.Berkovich.SpecifiedFieldGenericValuedPoints
import EnvelopeProperty.Berkovich.SpectrumBridge
import EnvelopeProperty.Berkovich.SchemeRelativeAtlas
import EnvelopeProperty.Berkovich.SchemeLocalPSH
import EnvelopeProperty.FiniteAffineMax

/-! # Genuine original-stalk fixed-Gauss points and source convex profiles

The field map and coefficient action come from the actual original stalk and
the original structure morphism. No field isomorphism, norm-matching square,
valuation family or affine profile is an input.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace Filter
open scoped Classical NNReal Topology

universe u
namespace EnvelopeProperty.GaussRegularSurfaceConvexProfiles
open Berkovich

variable {k : Type u} [Field k] {X : Scheme.{u}}

/-- The actual ORIGINAL coefficient map through the original whole sections and stalk. -/
def stalkCoefficientMap (f : X ⟶ Spec (CommRingCat.of (Polynomial k))) (p : X) :
    Polynomial k →+* X.presheaf.stalk p :=
  (X.presheaf.germ ⊤ p trivial).hom.comp (SchemeValuedPoint.sectionBaseMap f ⊤)

/-- The actual original parameter, rather than an unrelated local element. -/
def stalkParameter (f : X ⟶ Spec (CommRingCat.of (Polynomial k))) (p : X) :
    X.presheaf.stalk p := stalkCoefficientMap f p Polynomial.X

private abbrev stalkBaseAlgebra (f : X ⟶ Spec (CommRingCat.of (Polynomial k))) (p : X) :
    Algebra k (X.presheaf.stalk p) :=
  ((stalkCoefficientMap f p).comp Polynomial.C).toAlgebra

private theorem stalkCoefficientMap_aeval
    (f : X ⟶ Spec (CommRingCat.of (Polynomial k))) (p : X) (F : Polynomial k) :
    letI : Algebra k (X.presheaf.stalk p) := stalkBaseAlgebra f p
    stalkCoefficientMap f p F = Polynomial.aeval (stalkParameter f p) F := by
  let : Algebra k (X.presheaf.stalk p) := stalkBaseAlgebra f p
  have h : stalkCoefficientMap f p = (Polynomial.aeval (stalkParameter f p)).toRingHom := by
    apply Polynomial.ringHom_ext
    · intro a
      change stalkCoefficientMap f p (Polynomial.C a) = Polynomial.aeval (stalkParameter f p) (Polynomial.C a)
      rw [Polynomial.aeval_C]
      rfl
    · change stalkCoefficientMap f p Polynomial.X = Polynomial.aeval (stalkParameter f p) Polynomial.X
      rw [Polynomial.aeval_X]
      rfl
  exact congrArg (fun h : Polynomial k →+* X.presheaf.stalk p => h F) h

variable [IsIntegral X]

/-- The original stalk's fraction-ring isomorphism INTERNALLY gives this canonical
map from the SAME original global function field into the SAME FractionRing stalk. -/
def genericFieldMap (p : X) : X.functionField →+* FractionRing (X.presheaf.stalk p) :=
  (FractionRing.algEquiv (A := X.presheaf.stalk p) X.functionField).symm.toRingHom

/-- EVERY original section germ keeps its literal original stalk fraction value. -/
theorem genericFieldMap_germ (p : X) (V : X.Opens) [Nonempty V] (hp : p ∈ V)
    (a : Γ(X,V)) :
    genericFieldMap p (X.germToFunctionField V a) =
      algebraMap (X.presheaf.stalk p) (FractionRing (X.presheaf.stalk p))
        (X.presheaf.germ V p hp a) := by
  rw [← X.algebraMap_germ_eq_germToFunctionField hp a]
  exact (FractionRing.algEquiv (A := X.presheaf.stalk p) X.functionField).symm.commutes _

private def nativeFromStalkNorm (p : X)
    (v : Valuation (FractionRing (X.presheaf.stalk p)) ℝ≥0) : SchemeValuedPoint X := by
  let : Algebra X.functionField (FractionRing (X.presheaf.stalk p)) := (genericFieldMap p).toAlgebra
  exact SpecifiedFieldGenericValuedPoints.point X (FractionRing (X.presheaf.stalk p)) (Spectrum.ofValuation v)

private theorem nativeFromStalkNorm_underlying (p : X)
    (v : Valuation (FractionRing (X.presheaf.stalk p)) ℝ≥0) :
    (nativeFromStalkNorm p v).point = genericPoint X := by
  let : Algebra X.functionField (FractionRing (X.presheaf.stalk p)) := (genericFieldMap p).toAlgebra
  exact SpecifiedFieldGenericValuedPoints.point_underlying X (FractionRing (X.presheaf.stalk p)) _

private theorem nativeFromStalkNorm_eval (p : X)
    (v : Valuation (FractionRing (X.presheaf.stalk p)) ℝ≥0) (V : X.Opens) [Nonempty V]
    (a : Γ(X,V)) :
    SchemeValuedPoint.eval (nativeFromStalkNorm p v) V
      (show (nativeFromStalkNorm p v).point ∈ V from by
        let : Algebra X.functionField (FractionRing (X.presheaf.stalk p)) := (genericFieldMap p).toAlgebra
        exact SpecifiedFieldGenericValuedPoints.point_mem X (FractionRing (X.presheaf.stalk p)) _ V) a =
      v (genericFieldMap p (X.germToFunctionField V a)) := by
  let : Algebra X.functionField (FractionRing (X.presheaf.stalk p)) := (genericFieldMap p).toAlgebra
  exact SpecifiedFieldGenericValuedPoints.point_eval X (FractionRing (X.presheaf.stalk p)) _ V a

private theorem nativeFromStalkNorm_memGauss
    (f : X ⟶ Spec (CommRingCat.of (Polynomial k))) (p : X) (r : ℝ≥0)
    (v : Valuation (FractionRing (X.presheaf.stalk p)) ℝ≥0)
    (hv : ∀ F : Polynomial k,
      v (algebraMap (X.presheaf.stalk p) (FractionRing (X.presheaf.stalk p))
        (stalkCoefficientMap f p F)) = gaussValuation (1 : Valuation k ℝ≥0) r F) :
    nativeFromStalkNorm p v ∈ SchemeValuedPoint.relativeLocus
      (gaussValuation (1 : Valuation k ℝ≥0) r) f := by
  let : Nonempty (⊤ : X.Opens) := ⟨⟨p,trivial⟩⟩
  apply (SchemeValuedPoint.mem_relativeLocus_iff_sectionCoefficients _ f _ ⊤ trivial).mpr
  intro F
  rw [nativeFromStalkNorm_eval,genericFieldMap_germ p ⊤ trivial]
  exact hv F

private def weightedNorm (f : X ⟶ Spec (CommRingCat.of (Polynomial k))) (p : X) [IsNoetherianRing (X.presheaf.stalk p)]
    (π z : X.presheaf.stalk p) (hπ : Prime π) (hz : ¬ π ∣ z)
    (hm : IsLocalRing.maximalIdeal (X.presheaf.stalk p) = Ideal.span {π,z})
    (N : ℕ) (hN : 0 < N) (ht : stalkParameter f p ≠ 0) (hπt : π ∣ stalkParameter f p)
    (r : ℝ≥0) (hr0 : 0 < r) (hr1 : r < 1) :
    Valuation (FractionRing (X.presheaf.stalk p)) ℝ≥0 := by
  let : Algebra k (X.presheaf.stalk p) := stalkBaseAlgebra f p
  exact (GaussRegularSurfaceRealNorms.normalizedWeightedPoint (k := k) π z hπ hz hm N hN
    (stalkParameter f p) ht hπt r hr0 hr1).val

private theorem weightedNorm_allPoly (f : X ⟶ Spec (CommRingCat.of (Polynomial k))) (p : X) [IsNoetherianRing (X.presheaf.stalk p)]
    (π z : X.presheaf.stalk p) (hπ : Prime π) (hz : ¬ π ∣ z)
    (hm : IsLocalRing.maximalIdeal (X.presheaf.stalk p) = Ideal.span {π,z})
    (N : ℕ) (hN : 0 < N) (ht : stalkParameter f p ≠ 0) (hπt : π ∣ stalkParameter f p)
    (r : ℝ≥0) (hr0 : 0 < r) (hr1 : r < 1) (F : Polynomial k) :
    weightedNorm f p π z hπ hz hm N hN ht hπt r hr0 hr1
      (algebraMap (X.presheaf.stalk p) (FractionRing (X.presheaf.stalk p)) (stalkCoefficientMap f p F)) =
        gaussValuation (1 : Valuation k ℝ≥0) r F := by
  let : Algebra k (X.presheaf.stalk p) := stalkBaseAlgebra f p
  change (GaussRegularSurfaceRealNorms.normalizedWeightedPoint (k := k) π z hπ hz hm N hN
    (stalkParameter f p) ht hπt r hr0 hr1).val _ = _
  rw [stalkCoefficientMap_aeval]
  have he : algebraMap (X.presheaf.stalk p) (FractionRing (X.presheaf.stalk p))
      (Polynomial.aeval (stalkParameter f p) F) =
      Polynomial.aeval (algebraMap (X.presheaf.stalk p) (FractionRing (X.presheaf.stalk p))
        (stalkParameter f p)) F :=
    (Polynomial.aeval_algHom_apply
      (IsScalarTower.toAlgHom k (X.presheaf.stalk p) (FractionRing (X.presheaf.stalk p)))
      (stalkParameter f p) F).symm
  rw [he]
  exact (GaussRegularSurfaceRealNorms.normalizedWeightedPoint_gauss
    π z hπ hz hm N hN (stalkParameter f p) ht hπt r hr0 hr1).2.2 F

private def verticalNorm (f : X ⟶ Spec (CommRingCat.of (Polynomial k))) (p : X) [IsNoetherianRing (X.presheaf.stalk p)]
    (π : X.presheaf.stalk p) (hπ : Prime π) (ht : stalkParameter f p ≠ 0)
    (hπt : π ∣ stalkParameter f p) (r : ℝ≥0) (hr0 : 0 < r) (hr1 : r < 1) :
    Valuation (FractionRing (X.presheaf.stalk p)) ℝ≥0 := by
  let : Algebra k (X.presheaf.stalk p) := stalkBaseAlgebra f p
  exact (GaussRegularSurfaceRealNorms.normalizedVerticalPoint (k := k) π hπ
    (stalkParameter f p) ht hπt r hr0 hr1).val

private theorem verticalNorm_allPoly (f : X ⟶ Spec (CommRingCat.of (Polynomial k))) (p : X) [IsNoetherianRing (X.presheaf.stalk p)]
    (π : X.presheaf.stalk p) (hπ : Prime π) (ht : stalkParameter f p ≠ 0)
    (hπt : π ∣ stalkParameter f p) (r : ℝ≥0) (hr0 : 0 < r) (hr1 : r < 1) (F : Polynomial k) :
    verticalNorm f p π hπ ht hπt r hr0 hr1
      (algebraMap (X.presheaf.stalk p) (FractionRing (X.presheaf.stalk p)) (stalkCoefficientMap f p F)) =
        gaussValuation (1 : Valuation k ℝ≥0) r F := by
  let : Algebra k (X.presheaf.stalk p) := stalkBaseAlgebra f p
  change (GaussRegularSurfaceRealNorms.normalizedVerticalPoint (k := k) π hπ
    (stalkParameter f p) ht hπt r hr0 hr1).val _ = _
  rw [stalkCoefficientMap_aeval]
  have he : algebraMap (X.presheaf.stalk p) (FractionRing (X.presheaf.stalk p))
      (Polynomial.aeval (stalkParameter f p) F) =
      Polynomial.aeval (algebraMap (X.presheaf.stalk p) (FractionRing (X.presheaf.stalk p))
        (stalkParameter f p)) F :=
    (Polynomial.aeval_algHom_apply
      (IsScalarTower.toAlgHom k (X.presheaf.stalk p) (FractionRing (X.presheaf.stalk p)))
      (stalkParameter f p) F).symm
  rw [he]
  exact (GaussRegularSurfaceRealNorms.normalizedVerticalPoint_gauss
    π hπ (stalkParameter f p) ht hπt r hr0 hr1).2.2 F

/-- An actual fixed-Gauss ORIGINAL native point, internally constructed from the
actual original stalk and its actual weighted DVR; no base certificate is input. -/
def nativeWeightedPoint (f : X ⟶ Spec (CommRingCat.of (Polynomial k))) (p : X) [IsNoetherianRing (X.presheaf.stalk p)]
    (π z : X.presheaf.stalk p) (hπ : Prime π) (hz : ¬ π ∣ z)
    (hm : IsLocalRing.maximalIdeal (X.presheaf.stalk p) = Ideal.span {π,z})
    (N : ℕ) (hN : 0 < N) (ht : stalkParameter f p ≠ 0) (hπt : π ∣ stalkParameter f p)
    (r : ℝ≥0) (hr0 : 0 < r) (hr1 : r < 1) :
    RelativeSchemeValuedPoint (gaussValuation (1 : Valuation k ℝ≥0) r) f :=
  ⟨nativeFromStalkNorm p (weightedNorm f p π z hπ hz hm N hN ht hπt r hr0 hr1),
    nativeFromStalkNorm_memGauss f p r _ (weightedNorm_allPoly f p π z hπ hz hm N hN ht hπt r hr0 hr1)⟩

/-- The distinguished true vertical ORIGINAL native point over the SAME Gauss base. -/
def nativeVerticalPoint (f : X ⟶ Spec (CommRingCat.of (Polynomial k))) (p : X) [IsNoetherianRing (X.presheaf.stalk p)]
    (π : X.presheaf.stalk p) (hπ : Prime π) (ht : stalkParameter f p ≠ 0)
    (hπt : π ∣ stalkParameter f p) (r : ℝ≥0) (hr0 : 0 < r) (hr1 : r < 1) :
    RelativeSchemeValuedPoint (gaussValuation (1 : Valuation k ℝ≥0) r) f :=
  ⟨nativeFromStalkNorm p (verticalNorm f p π hπ ht hπt r hr0 hr1),
    nativeFromStalkNorm_memGauss f p r _ (verticalNorm_allPoly f p π hπ ht hπt r hr0 hr1)⟩

/-- The actual point lies on the SAME original generic scheme point. -/
theorem nativeWeightedPoint_underlying (f : X ⟶ Spec (CommRingCat.of (Polynomial k))) (p : X)
    [IsNoetherianRing (X.presheaf.stalk p)] (π z : X.presheaf.stalk p) (hπ : Prime π) (hz : ¬ π ∣ z)
    (hm : IsLocalRing.maximalIdeal (X.presheaf.stalk p) = Ideal.span {π,z})
    (N : ℕ) (hN : 0 < N) (ht : stalkParameter f p ≠ 0) (hπt : π ∣ stalkParameter f p)
    (r : ℝ≥0) (hr0 : 0 < r) (hr1 : r < 1) :
    (nativeWeightedPoint f p π z hπ hz hm N hN ht hπt r hr0 hr1).1.point = genericPoint X :=
  nativeFromStalkNorm_underlying p _

/-- The actual distinguished vertical point also has the SAME original generic support. -/
theorem nativeVerticalPoint_underlying (f : X ⟶ Spec (CommRingCat.of (Polynomial k))) (p : X)
    [IsNoetherianRing (X.presheaf.stalk p)] (π : X.presheaf.stalk p) (hπ : Prime π)
    (ht : stalkParameter f p ≠ 0) (hπt : π ∣ stalkParameter f p)
    (r : ℝ≥0) (hr0 : 0 < r) (hr1 : r < 1) :
    (nativeVerticalPoint f p π hπ ht hπt r hr0 hr1).1.point = genericPoint X :=
  nativeFromStalkNorm_underlying p _

/-- EVERY original section on EVERY original nonempty open keeps its actual norm value. -/
theorem nativeWeightedPoint_eval (f : X ⟶ Spec (CommRingCat.of (Polynomial k))) (p : X)
    [IsNoetherianRing (X.presheaf.stalk p)] (π z : X.presheaf.stalk p) (hπ : Prime π) (hz : ¬ π ∣ z)
    (hm : IsLocalRing.maximalIdeal (X.presheaf.stalk p) = Ideal.span {π,z})
    (N : ℕ) (hN : 0 < N) (ht : stalkParameter f p ≠ 0) (hπt : π ∣ stalkParameter f p)
    (r : ℝ≥0) (hr0 : 0 < r) (hr1 : r < 1) (V : X.Opens) [Nonempty V]
    (hV : (nativeWeightedPoint f p π z hπ hz hm N hN ht hπt r hr0 hr1).1.point ∈ V)
    (a : Γ(X,V)) :
    SchemeValuedPoint.eval (nativeWeightedPoint f p π z hπ hz hm N hN ht hπt r hr0 hr1).1 V hV a =
      letI : Algebra k (X.presheaf.stalk p) := ((stalkCoefficientMap f p).comp Polynomial.C).toAlgebra
      (GaussRegularSurfaceRealNorms.normalizedWeightedPoint (k := k) π z hπ hz hm N hN
        (stalkParameter f p) ht hπt r hr0 hr1).val (genericFieldMap p (X.germToFunctionField V a)) :=
  nativeFromStalkNorm_eval p _ V a

/-- EVERY original section also keeps its value at the actual distinguished vertical point. -/
theorem nativeVerticalPoint_eval (f : X ⟶ Spec (CommRingCat.of (Polynomial k))) (p : X)
    [IsNoetherianRing (X.presheaf.stalk p)] (π : X.presheaf.stalk p) (hπ : Prime π)
    (ht : stalkParameter f p ≠ 0) (hπt : π ∣ stalkParameter f p)
    (r : ℝ≥0) (hr0 : 0 < r) (hr1 : r < 1) (V : X.Opens) [Nonempty V]
    (hV : (nativeVerticalPoint f p π hπ ht hπt r hr0 hr1).1.point ∈ V) (a : Γ(X,V)) :
    SchemeValuedPoint.eval (nativeVerticalPoint f p π hπ ht hπt r hr0 hr1).1 V hV a =
      letI : Algebra k (X.presheaf.stalk p) := ((stalkCoefficientMap f p).comp Polynomial.C).toAlgebra
      (GaussRegularSurfaceRealNorms.normalizedVerticalPoint (k := k) π hπ
        (stalkParameter f p) ht hπt r hr0 hr1).val (genericFieldMap p (X.germToFunctionField V a)) :=
  nativeFromStalkNorm_eval p _ V a

/-- WHOLE actual original native fixed-Gauss points converge, with no supplied
point topology/field identification or convergence certificate. -/
theorem tendsto_nativeWeightedPoint (f : X ⟶ Spec (CommRingCat.of (Polynomial k))) (p : X)
    [IsNoetherianRing (X.presheaf.stalk p)] (π z : X.presheaf.stalk p) (hπ : Prime π) (hz : ¬ π ∣ z)
    (hm : IsLocalRing.maximalIdeal (X.presheaf.stalk p) = Ideal.span {π,z})
    (ht : stalkParameter f p ≠ 0) (hπt : π ∣ stalkParameter f p)
    (r : ℝ≥0) (hr0 : 0 < r) (hr1 : r < 1) :
    Tendsto (fun n : ℕ => nativeWeightedPoint f p π z hπ hz hm (n+1)
      (Nat.zero_lt_succ n) ht hπt r hr0 hr1) atTop
      (𝓝 (nativeVerticalPoint f p π hπ ht hπt r hr0 hr1)) := by
  let : Algebra k (X.presheaf.stalk p) := stalkBaseAlgebra f p
  let : Algebra X.functionField (FractionRing (X.presheaf.stalk p)) := (genericFieldMap p).toAlgebra
  apply tendsto_subtype_rng.mpr
  exact (SpecifiedFieldGenericValuedPoints.continuous_point X (FractionRing (X.presheaf.stalk p))).continuousAt.tendsto.comp
    (Berk.continuous_toSpectrum.continuousAt.tendsto.comp
      (GaussRegularSurfaceRealNorms.tendsto_normalizedWeightedPoint π z hπ hz hm
        (stalkParameter f p) ht hπt r hr0 hr1))

/-- The SAME actual normalizing scale, using the true order of the ORIGINAL parameter. -/
def nativeScale (f : X ⟶ Spec (CommRingCat.of (Polynomial k))) (p : X)
    [IsNoetherianRing (X.presheaf.stalk p)] (π z : X.presheaf.stalk p) (hπ : Prime π) (hz : ¬ π ∣ z)
    (hm : IsLocalRing.maximalIdeal (X.presheaf.stalk p) = Ideal.span {π,z})
    (r : ℝ≥0) (N : ℕ) (hN : 0 < N) : ℝ :=
  -Real.log (r : ℝ) / (GaussRegularSurfaceRealNorms.weightedParameterOrder π z hπ hz hm N hN
    (stalkParameter f p) : ℝ)

/-- Positivity is a theorem of the actual original parameter, not a scale premise. -/
theorem nativeScale_pos (f : X ⟶ Spec (CommRingCat.of (Polynomial k))) (p : X)
    [IsNoetherianRing (X.presheaf.stalk p)] (π z : X.presheaf.stalk p) (hπ : Prime π) (hz : ¬ π ∣ z)
    (hm : IsLocalRing.maximalIdeal (X.presheaf.stalk p) = Ideal.span {π,z})
    (ht : stalkParameter f p ≠ 0) (hπt : π ∣ stalkParameter f p)
    (r : ℝ≥0) (hr0 : 0 < r) (hr1 : r < 1) (N : ℕ) (hN : 0 < N) :
    0 < nativeScale f p π z hπ hz hm r N hN := by
  apply div_pos
  · exact neg_pos.mpr (Real.log_neg (by exact_mod_cast hr0) (by exact_mod_cast hr1))
  · exact_mod_cast (GaussRegularSurfaceRealNorms.weightedParameterOrder_spec π z hπ hz hm N hN
      (stalkParameter f p) ht hπt).2

/-- The true original parameter scales tend to zero along the SAME actual points. -/
theorem tendsto_nativeScale (f : X ⟶ Spec (CommRingCat.of (Polynomial k))) (p : X)
    [IsNoetherianRing (X.presheaf.stalk p)] (π z : X.presheaf.stalk p) (hπ : Prime π) (hz : ¬ π ∣ z)
    (hm : IsLocalRing.maximalIdeal (X.presheaf.stalk p) = Ideal.span {π,z})
    (ht : stalkParameter f p ≠ 0) (hπt : π ∣ stalkParameter f p) (r : ℝ≥0) :
    Tendsto (fun n : ℕ => nativeScale f p π z hπ hz hm r (n+1) (Nat.zero_lt_succ n)) atTop (𝓝 0) := by
  obtain ⟨e,c,he,_,htail⟩ :=
    GaussRegularSurfaceRealNorms.exists_parameter_orders π z hπ hz hm (stalkParameter f p) ht hπt
  have hN : Tendsto (fun n : ℕ => ((n+1 : ℕ) : ℝ)) atTop atTop := by
    simpa only [Nat.cast_add,Nat.cast_one] using
      tendsto_atTop_add_const_right atTop (1 : ℝ) (tendsto_natCast_atTop_atTop (R := ℝ))
  have hden : Tendsto (fun n : ℕ => (e : ℝ) * (n+1 : ℕ) + (c : ℝ)) atTop atTop :=
    tendsto_atTop_add_const_right atTop (c : ℝ) (Tendsto.const_mul_atTop (by exact_mod_cast he) hN)
  have H : Tendsto (fun n : ℕ => -Real.log (r : ℝ) / ((e : ℝ) * (n+1 : ℕ) + (c : ℝ)))
      atTop (𝓝 0) := tendsto_const_nhds.div_atTop hden
  apply H.congr'
  filter_upwards [eventually_gt_atTop c] with n hn
  have hd : GaussRegularSurfaceRealNorms.weightedParameterOrder π z hπ hz hm (n+1)
      (Nat.zero_lt_succ n) (stalkParameter f p) = e * (n+1) + c := by
    exact_mod_cast (GaussRegularSurfaceRealNorms.weightedParameterOrder_spec π z hπ hz hm (n+1)
      (Nat.zero_lt_succ n) (stalkParameter f p) ht hπt).1.symm.trans
      (htail (n+1) (Nat.zero_lt_succ n) (by omega))
  simp only [nativeScale,hd,Nat.cast_add,Nat.cast_mul,Nat.cast_one]

/-- ACTUAL original units internally give native vertical/leading-residue orders
and simultaneous eventual profiles of their ORIGINAL native section evaluations. -/
theorem exists_unit_profiles (f : X ⟶ Spec (CommRingCat.of (Polynomial k))) (p : X)
    [IsNoetherianRing (X.presheaf.stalk p)] (π z : X.presheaf.stalk p) (hπ : Prime π) (hz : ¬ π ∣ z)
    (hm : IsLocalRing.maximalIdeal (X.presheaf.stalk p) = Ideal.span {π,z})
    (ht : stalkParameter f p ≠ 0) (hπt : π ∣ stalkParameter f p)
    (r : ℝ≥0) (hr0 : 0 < r) (hr1 : r < 1) (V : X.Opens) [Nonempty V]
    (hV0 : (nativeVerticalPoint f p π hπ ht hπt r hr0 hr1).1.point ∈ V)
    (n : ℕ) (a : Fin n → Γ(X,V)ˣ) :
    let F := fun i : Fin n => genericFieldMap p (X.germToFunctionField V (a i : Γ(X,V)))
    ∃ (e c : ℕ) (A B : Fin n → ℤ)
      (v : Fin n → (GaussRegularSurfaceValuationOrders.verticalRing π hπ)ˣ),
      0 < e ∧ e = GaussRegularSurfaceRealNorms.verticalParameterOrder π hπ (stalkParameter f p) ∧
      (∀ i : Fin n,
        F i = GaussRegularSurfaceValuationFractions.verticalFractionEmbedding π hπ (v i) *
          (algebraMap (X.presheaf.stalk p) (FractionRing (X.presheaf.stalk p)) π) ^ (A i) ∧
        GaussRegularSurfaceValuationFractions.verticalOrder π hπ (F i) = WithZero.exp (A i) ∧
        GaussRegularSurfaceValuationFractions.residualOrder π z hπ hz hm
          (GaussRegularSurfaceValuationFractions.verticalResidueEquiv π z hπ hz hm
            (IsLocalRing.residue (GaussRegularSurfaceValuationOrders.verticalRing π hπ) (v i))) =
              WithZero.exp (B i)) ∧
      ∀ᶠ m : ℕ in atTop,
        GaussRegularSurfaceRealNorms.weightedParameterOrder π z hπ hz hm (m+1)
          (Nat.zero_lt_succ m) (stalkParameter f p) = e * (m+1) + c ∧
        ∀ (i : Fin n)
          (hVm : (nativeWeightedPoint f p π z hπ hz hm (m+1) (Nat.zero_lt_succ m) ht hπt r hr0 hr1).1.point ∈ V),
          Real.log (SchemeValuedPoint.eval
            (nativeWeightedPoint f p π z hπ hz hm (m+1) (Nat.zero_lt_succ m) ht hπt r hr0 hr1).1 V hVm
              (a i : Γ(X,V)) : ℝ) =
          Real.log (SchemeValuedPoint.eval (nativeVerticalPoint f p π hπ ht hπt r hr0 hr1).1 V hV0
              (a i : Γ(X,V)) : ℝ) - nativeScale f p π z hπ hz hm r (m+1) (Nat.zero_lt_succ m) *
                ((B i : ℝ) - (A i : ℝ) / (e : ℝ) * (c : ℝ)) := by
  let : Algebra k (X.presheaf.stalk p) := stalkBaseAlgebra f p
  let F := fun i : Fin n => genericFieldMap p (X.germToFunctionField V (a i : Γ(X,V)))
  have hF (i : Fin n) : F i ≠ 0 :=
    (map_ne_zero_iff _ (FractionRing.algEquiv (A := X.presheaf.stalk p) X.functionField).symm.injective).mpr
      ((map_ne_zero_iff _ (X.germToFunctionField_injective V)).mpr (Units.ne_zero (a i)))
  obtain ⟨e,c,he,heq,H⟩ := GaussRegularSurfaceRealNorms.exists_normalized_log_profile
    (k := k) π z hπ hz hm (stalkParameter f p) ht hπt r hr0 hr1
  choose A B v hfactor horder hres hzero htail using fun i : Fin n => H (F i) (hF i)
  obtain ⟨_,_,_,_,_,_,_,hparam⟩ := H 1 one_ne_zero
  refine ⟨e,c,A,B,v,he,heq,fun i => ⟨hfactor i,horder i,hres i⟩,?_⟩
  have hall := (eventually_all_finset (Finset.univ : Finset (Fin n))).mpr (fun i _ => htail i)
  filter_upwards [hall,hparam] with m hm' hp'
  refine ⟨hp'.1,?_⟩
  intro i hVm
  rw [nativeWeightedPoint_eval,nativeVerticalPoint_eval,hzero i]
  have hdR : (GaussRegularSurfaceRealNorms.weightedParameterOrder π z hπ hz hm (m+1)
      (Nat.zero_lt_succ m) (stalkParameter f p) : ℝ) = (e : ℝ) * (m+1 : ℕ) + (c : ℝ) := by
    exact_mod_cast hp'.1
  have hlog := (hm' i (Finset.mem_univ i)).2
  rw [← hdR] at hlog
  exact hlog

/-- The LITERAL original source convexity internally chooses its actual units,
native orders and active set, and gives an exact eventual affine profile and
true quotient of the ORIGINAL function on the SAME original native points. -/
theorem exists_convex_active_profile (f : X ⟶ Spec (CommRingCat.of (Polynomial k))) (p : X)
    [IsNoetherianRing (X.presheaf.stalk p)] (π z : X.presheaf.stalk p) (hπ : Prime π) (hz : ¬ π ∣ z)
    (hm : IsLocalRing.maximalIdeal (X.presheaf.stalk p) = Ideal.span {π,z})
    (ht : stalkParameter f p ≠ 0) (hπt : π ∣ stalkParameter f p)
    (r : ℝ≥0) (hr0 : 0 < r) (hr1 : r < 1)
    {U : Set (RelativeSchemeValuedPoint (gaussValuation (1 : Valuation k ℝ≥0) r) f)}
    {u : RelativeSchemeValuedPoint (gaussValuation (1 : Valuation k ℝ≥0) r) f → EReal}
    (hu : RelativeSchemeValuedPoint.IsConvexPLOn U u)
    (hq0U : nativeVerticalPoint f p π hπ ht hπt r hr0 hr1 ∈ U) :
    let q0 := nativeVerticalPoint f p π hπ ht hπt r hr0 hr1
    let q := fun m : ℕ => nativeWeightedPoint f p π z hπ hz hm (m+1) (Nat.zero_lt_succ m) ht hπt r hr0 hr1
    let ε := fun m : ℕ => nativeScale f p π z hπ hz hm r (m+1) (Nat.zero_lt_succ m)
    ∃ (V : X.Opens) (hV0 : q0.1.point ∈ V) (n : ℕ) (a : Fin n → Γ(X,V)ˣ)
      (I : Finset ((Fin n → ℚ) × ℚ)) (hI : I.Nonempty) (e c : ℕ) (A B : Fin n → ℤ)
      (v : Fin n → (GaussRegularSurfaceValuationOrders.verticalRing π hπ)ˣ),
      letI : Nonempty V := ⟨⟨q0.1.point,hV0⟩⟩
      let F := fun i : Fin n => genericFieldMap p (X.germToFunctionField V (a i : Γ(X,V)))
      let b := fun j : (Fin n → ℚ) × ℚ => RelativeSchemeValuedPoint.unitTropAffine a j q0 hV0
      let s := fun (j : (Fin n → ℚ) × ℚ) (_ : Unit) =>
        -(∑ i : Fin n, (j.1 i : ℝ) * ((B i : ℝ) - (A i : ℝ) / (e : ℝ) * (c : ℝ)))
      let D := FiniteAffineMax.activeSlope I hI b s ()
      0 < e ∧ e = GaussRegularSurfaceRealNorms.verticalParameterOrder π hπ (stalkParameter f p) ∧
      (∀ i : Fin n,
        F i = GaussRegularSurfaceValuationFractions.verticalFractionEmbedding π hπ (v i) *
          (algebraMap (X.presheaf.stalk p) (FractionRing (X.presheaf.stalk p)) π) ^ (A i) ∧
        GaussRegularSurfaceValuationFractions.verticalOrder π hπ (F i) = WithZero.exp (A i) ∧
        GaussRegularSurfaceValuationFractions.residualOrder π z hπ hz hm
          (GaussRegularSurfaceValuationFractions.verticalResidueEquiv π z hπ hz hm
            (IsLocalRing.residue (GaussRegularSurfaceValuationOrders.verticalRing π hπ) (v i))) =
              WithZero.exp (B i)) ∧
      u q0 = ((I.sup' hI b : ℝ) : EReal) ∧
      (∀ᶠ m : ℕ in atTop,
        GaussRegularSurfaceRealNorms.weightedParameterOrder π z hπ hz hm (m+1)
          (Nat.zero_lt_succ m) (stalkParameter f p) = e * (m+1) + c ∧
        u (q m) = ((I.sup' hI b + D * ε m : ℝ) : EReal) ∧
          ((u (q m)).toReal - (u q0).toReal) / ε m = D) ∧
      Tendsto (fun m : ℕ => ((u (q m)).toReal - (u q0).toReal) / ε m) atTop (𝓝 D) := by
  let q0 := nativeVerticalPoint f p π hπ ht hπt r hr0 hr1
  let q := fun m : ℕ => nativeWeightedPoint f p π z hπ hz hm (m+1) (Nat.zero_lt_succ m) ht hπt r hr0 hr1
  let ε := fun m : ℕ => nativeScale f p π z hπ hz hm r (m+1) (Nat.zero_lt_succ m)
  obtain ⟨W,hW,hq0W,_hWU,V,hWV,n,a,I,hI,hform⟩ := hu q0 hq0U
  let hV0 := hWV q0 hq0W
  let : Nonempty V := ⟨⟨q0.1.point,hV0⟩⟩
  obtain ⟨e,c,A,B,v,he,heq,horders,hunit⟩ :=
    exists_unit_profiles f p π z hπ hz hm ht hπt r hr0 hr1 V hV0 n a
  let b := fun j : (Fin n → ℚ) × ℚ => RelativeSchemeValuedPoint.unitTropAffine a j q0 hV0
  let s := fun (j : (Fin n → ℚ) × ℚ) (_ : Unit) =>
    -(∑ i : Fin n, (j.1 i : ℝ) * ((B i : ℝ) - (A i : ℝ) / (e : ℝ) * (c : ℝ)))
  let D := FiniteAffineMax.activeSlope I hI b s ()
  have h0 : u q0 = ((I.sup' hI b : ℝ) : EReal) := hform q0 hq0W
  obtain ⟨δ,hδ,hmax⟩ := FiniteAffineMax.exists_pos_eventual_max I hI {()} b s
  have hWtail : ∀ᶠ m : ℕ in atTop, q m ∈ W :=
    (tendsto_nativeWeightedPoint f p π z hπ hz hm ht hπt r hr0 hr1).eventually (hW.mem_nhds hq0W)
  have hsmall : ∀ᶠ m : ℕ in atTop, ε m < δ :=
    (tendsto_nativeScale f p π z hπ hz hm ht hπt r).eventually (gt_mem_nhds hδ)
  have hprofile : ∀ᶠ m : ℕ in atTop, u (q m) = ((I.sup' hI b + D * ε m : ℝ) : EReal) := by
    filter_upwards [hunit,hWtail,hsmall] with m hmU hmW hmδ
    have hterm (j : (Fin n → ℚ) × ℚ) :
        RelativeSchemeValuedPoint.unitTropAffine a j (q m) (hWV (q m) hmW) = b j + s j () * ε m := by
      have hsum : (∑ i : Fin n, (j.1 i : ℝ) * Real.log
          (SchemeValuedPoint.eval (q m).1 V (hWV (q m) hmW) (a i : Γ(X,V)) : ℝ)) =
          (∑ i : Fin n, (j.1 i : ℝ) * Real.log
            (SchemeValuedPoint.eval q0.1 V hV0 (a i : Γ(X,V)) : ℝ)) -
          (∑ i : Fin n, (j.1 i : ℝ) * ((B i : ℝ) - (A i : ℝ) / (e : ℝ) * (c : ℝ))) * ε m := by
        rw [Finset.sum_mul,← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro i _
        calc
          _ = (j.1 i : ℝ) * (Real.log
              (SchemeValuedPoint.eval q0.1 V hV0 (a i : Γ(X,V)) : ℝ) -
                ε m * ((B i : ℝ) - (A i : ℝ) / (e : ℝ) * (c : ℝ))) :=
            congrArg (fun x : ℝ => (j.1 i : ℝ) * x) (hmU.2 i (hWV (q m) hmW))
          _ = _ := by ring
      change (∑ i : Fin n, (j.1 i : ℝ) * Real.log
        (SchemeValuedPoint.eval (q m).1 V (hWV (q m) hmW) (a i : Γ(X,V)) : ℝ)) + j.2 =
          (∑ i : Fin n, (j.1 i : ℝ) * Real.log
            (SchemeValuedPoint.eval q0.1 V hV0 (a i : Γ(X,V)) : ℝ)) + j.2 +
          (-(∑ i : Fin n, (j.1 i : ℝ) * ((B i : ℝ) - (A i : ℝ) / (e : ℝ) * (c : ℝ)))) * ε m
      rw [hsum]
      ring
    rw [hform (q m) hmW]
    apply congrArg (fun x : ℝ => (x : EReal))
    have hfun : (fun j => RelativeSchemeValuedPoint.unitTropAffine a j (q m) (hWV (q m) hmW)) =
        fun j => b j + s j () * ε m := funext hterm
    rw [hfun,hmax () (Finset.mem_singleton_self ()) (ε m)
      (nativeScale_pos f p π z hπ hz hm ht hπt r hr0 hr1 (m+1) (Nat.zero_lt_succ m)).le hmδ]
  have hquot : ∀ᶠ m : ℕ in atTop, ((u (q m)).toReal - (u q0).toReal) / ε m = D := by
    filter_upwards [hprofile] with m hm'
    rw [hm',h0,EReal.toReal_coe,EReal.toReal_coe,add_sub_cancel_left,
      mul_div_cancel_right₀ _ (nativeScale_pos f p π z hπ hz hm ht hπt r hr0 hr1
        (m+1) (Nat.zero_lt_succ m)).ne']
  refine ⟨V,hV0,n,a,I,hI,e,c,A,B,v,he,heq,horders,h0,?_,?_⟩
  · exact (hunit.and (hprofile.and hquot)).mono fun _ h => ⟨h.1.1,h.2⟩
  · exact tendsto_const_nhds.congr' (hquot.mono fun _ h => h.symm)

end EnvelopeProperty.GaussRegularSurfaceConvexProfiles
