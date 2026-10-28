import SGPT.Okounkov.SchemeAffineNativeFormal
import SGPT.Okounkov.SchemeAffineStalkGerm
import SGPT.Okounkov.SchemeNativeStalkFlatness
import TranscendentalNakamaye.Pending.AnalyticSingularities
import TranscendentalNakamaye.Pending.IdealWeightProducts
import TranscendentalNakamaye.FirstPass.GlobalPotentials

/-!
# Actual native weights of the original affine ideal

Original coefficients are literal global holomorphic functions with whole
algebraic-stalk readback. The half-log squared norm is genuinely quasi-PSH,
including common zeros, and is nondegenerate for nonzero ideals on an integral
source. The canonical native ideal is the extension of the entire original
ideal; coherence, analytic singularity type, bounded generator invariance and
exact product weights are derived from that identity.

TN uses the density exp(-tφ). The normalized half-log weight therefore uses
level 2c, and this module proves the equality of entire multiplier ideals.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace EnvelopeProperty.Char0.NativeAffineIdealWeight
open CategoryTheory AlgebraicGeometry BingWangEntropy Filter Set
open TranscendentalNakamaye TranscendentalNakamaye.FirstPass TranscendentalNakamaye.Pending
open TranscendentalNakamaye.FirstPass.HolomorphicIdealSheaves
open SGPT.Okounkov
open scoped Topology Manifold ContDiff

section NativeSpan
variable {n m : ℕ} {M : Type} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] {p : M}
private theorem mk_sum (g : Fin m → M → ℂ) (hg : ∀ i,HolomorphicAt n (g i) p) :
 NativeHolGerm.mk (fun y=>∑i,g i y) (HolomorphicAt.sum Finset.univ (fun i _=>hg i))=
  ∑i,NativeHolGerm.mk (g i) (hg i) := by
 apply Subtype.ext
 change Germ.ofFun (fun y => ∑ i, g i y) =
   (nativeHolGermSubring n M p).subtype (∑ i, NativeHolGerm.mk (g i) (hg i))
 rw [map_sum]
 have he : (fun y => ∑ i, g i y) = ∑ i, g i := by funext y; simp
 rw [he]
 exact map_sum (Germ.coeRingHom (𝓝 p)) g Finset.univ

/-- Finite holomorphic spans equal ideal spans in the entire native germ ring. -/
theorem mem_native_span_mk_iff (g : Fin m → M → ℂ) (hg : ∀ i,HolomorphicAt n (g i) p)
 (v : M → ℂ) (hv : HolomorphicAt n v p) :
 NativeHolGerm.mk v hv ∈ Ideal.span (Set.range fun i=>NativeHolGerm.mk (g i) (hg i)) ↔
 IsInSpanAt (n := n) (·∈Set.range g) p v := by
 classical
 constructor
 · intro h
   obtain ⟨q,hq⟩:= Ideal.mem_span_range_iff_exists_fun.mp h
   choose b hb hqb using fun i=>NativeHolGerm.exists_eq_mk (n := n) (q i)
   refine ⟨hv,m,g,b,fun i=>Set.mem_range_self i,hb,?_⟩
   apply (NativeHolGerm.mk_eq_mk_iff (n := n) (hf := hv)
     (hg := HolomorphicAt.sum Finset.univ (fun i _ => (hb i).mul (hg i)))).mp
   calc
    NativeHolGerm.mk v hv=∑i,q i * NativeHolGerm.mk (g i) (hg i):=hq.symm
    _=∑i,NativeHolGerm.mk (fun y=>b i y*g i y) ((hb i).mul (hg i)):=by
      apply Finset.sum_congr rfl
      intro i _
      rw [hqb i]
      rfl
    _=NativeHolGerm.mk (fun y=>∑i,b i y*g i y)
      (HolomorphicAt.sum Finset.univ (fun i _=>(hb i).mul (hg i))):=(mk_sum _ (fun i => (hb i).mul (hg i))).symm
 · rintro ⟨_,N,s,b,hs,hb,heq⟩
   choose k hk using hs
   have hsg : ∀i,HolomorphicAt n (s i) p :=fun i=>by rw [←hk i];exact hg (k i)
   have hEq : NativeHolGerm.mk v hv=NativeHolGerm.mk (fun y=>∑i,b i y*s i y)
      (HolomorphicAt.sum Finset.univ (fun i _=>(hb i).mul (hsg i))) :=
       NativeHolGerm.mk_eq_mk_iff.mpr heq
   rw [hEq,mk_sum _ (fun i => (hb i).mul (hsg i))]
   apply Ideal.sum_mem
   intro i _
   have hi : NativeHolGerm.mk (s i) (hsg i) ∈ Ideal.span
      (Set.range fun j=>NativeHolGerm.mk (g j) (hg j)) := by
     apply Ideal.subset_span
     exact ⟨k i,by apply Subtype.ext;exact congrArg Germ.ofFun (hk i)⟩
   exact Ideal.mul_mem_left _ (NativeHolGerm.mk (b i) (hb i)) hi
end NativeSpan

variable {R : Type} [CommRing R] (f : Spec (.of R) ⟶ Spec (.of ℂ)) (n : ℕ)
  [SmoothOfRelativeDimension n f] [IsSeparated f] [QuasiCompact f]

local instance affineWeightTopology : TopologicalSpace (SchemeComplexPoint f) :=
  schemeAnalyticPointTopology f
local instance affineWeightCharts : ChartedSpace (ComplexModel n) (SchemeComplexPoint f) :=
  schemeAnalyticTNChartedSpace f n
local instance affineWeightManifold : IsComplexManifold n (SchemeComplexPoint f) :=
  schemeAnalyticTN_isComplexManifold f n

/-- The literal original affine coefficient, evaluated at the same actual complex point. -/
def originalFunction (r : R) (p : SchemeComplexPoint f) : ℂ := schemeAffineOriginalPoint f p r

private theorem originalFunction_local (r : R) (p : SchemeComplexPoint f) :
    ∃ V : Set (SchemeComplexPoint f), IsOpen V ∧ p ∈ V ∧
      ∃ H : SchemeComplexPoint f → ℂ,
      MDifferentiableOn 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ℂ) H V ∧
      Set.EqOn H (originalFunction f r) V ∧
      ((schemeNativeStalkGerm f n p (schemeAffineOriginalStalk f p r) :
        NativeHolGerm n (SchemeComplexPoint f) p) : Germ (𝓝 p) ℂ) = (H : Germ (𝓝 p) ℂ) := by
  obtain ⟨V,hV,hpV,_,H,hH,hread⟩ := SmoothSchemeGerms.regularSection_locally_holomorphic
    f n ⊤ ((Scheme.ΓSpecIso (.of R)).inv r) p trivial
  refine ⟨V,hV,hpV,H,hH,?_,hread p hpV trivial⟩
  intro q hq
  have he := congrArg (Germ.valueRingHom : Germ (𝓝 q) ℂ →+* ℂ) (hread q hq trivial)
  change NativeHolGerm.eval (schemeNativeStalkGerm f n q
    (schemeAffineOriginalStalk f q r)) = H q at he
  rw [schemeNativeStalkGerm_eval,schemeAffineOriginalStalk_eval] at he
  exact he.symm

/-- Every literal original affine function is holomorphic near each actual native point. -/
theorem originalFunction_holomorphicAt (r : R) (p : SchemeComplexPoint f) :
    HolomorphicAt n (originalFunction f r) p := by
  obtain ⟨V,hV,hp,H,hH,hEq,_⟩ := originalFunction_local f n r p
  apply HolomorphicAt.congr (f := H) ?_ (eventually_of_mem (hV.mem_nhds hp) hEq)
  filter_upwards [hV.mem_nhds hp] with q hq
  exact (hH q hq).mdifferentiableAt (hV.mem_nhds hq)

/-- The whole native germ of the literal function is its actual original algebraic stalk image. -/
theorem originalFunction_germ (r : R) (p : SchemeComplexPoint f) :
    NativeHolGerm.mk (originalFunction f r) (originalFunction_holomorphicAt f n r p) =
      schemeNativeStalkGerm f n p (schemeAffineOriginalStalk f p r) := by
  obtain ⟨V,hV,hp,H,_,hEq,hread⟩ := originalFunction_local f n r p
  apply Subtype.ext
  exact ((Germ.coe_eq.mpr (eventually_of_mem (hV.mem_nhds hp) hEq)).symm).trans hread.symm

/-- The canonical original affine ring map into the whole native holomorphic stalk. -/
def nativeMap (p : SchemeComplexPoint f) : R →+* NativeHolGerm n (SchemeComplexPoint f) p :=
  (schemeNativeStalkGerm f n p).comp (schemeAffineOriginalStalk f p)

/-- Every original coefficient is its literal holomorphic function germ. -/
theorem nativeMap_apply (r : R) (p : SchemeComplexPoint f) :
    nativeMap f n p r =
      NativeHolGerm.mk (originalFunction f r) (originalFunction_holomorphicAt f n r p) :=
  (originalFunction_germ f n r p).symm

/-- Literal functions of a finite original generating tuple. -/
def generators {m : ℕ} (a : Fin m → R) : Fin m → SchemeComplexPoint f → ℂ :=
  fun i => originalFunction f (a i)

/-- The standard multiplier convention uses one half the logarithmic squared norm. -/
def weight {m : ℕ} (a : Fin m → R) (p : SchemeComplexPoint f) : EReal :=
  ((1 / 2 : ℝ) : EReal) * generatorLog (generators f a) p

omit [IsSeparated f] [QuasiCompact f] in
/-- The actual weight retains its literal logarithmic sum, including common zeros. -/
theorem weight_eq_log_sum {m : ℕ} (a : Fin m → R) (p : SchemeComplexPoint f) :
    weight f a p = ((1 / 2 : ℝ) : EReal) *
      ENNReal.log (ENNReal.ofReal (∑ i, ‖schemeAffineOriginalPoint f p (a i)‖ ^ 2)) := by
  rw [weight,generatorLog_eq_log_sum]
  rfl

omit [IsSeparated f] [QuasiCompact f] in
/-- The poles are exactly the common zeros of the original generators. -/
theorem weight_eq_bot_iff {m : ℕ} (a : Fin m → R) (p : SchemeComplexPoint f) :
    weight f a p = ⊥ ↔ ∀ i, schemeAffineOriginalPoint f p (a i) = 0 := by
  have h := scaled_generatorLog_add_eq_bot_iff (generators f a) p
    (show (0 : ℝ) < 1 / 2 by norm_num) 0
  simpa [weight,generators,originalFunction] using h

/-- Quasi-PSH regularity is produced from original affine generator holomorphy. -/
theorem weight_quasiPSH {m : ℕ} (a : Fin m → R) :
    ManifoldQuasiPlurisubharmonic (n := n) (weight f a) := by
  intro e z hz
  let G : Fin m → ComplexModel n → ℂ := fun i w => generators f a i (e.val.symm w)
  have hG : HolomorphicGeneratorsAt G z := by
    refine ⟨e.val.target,e.val.open_target,hz,?_⟩
    intro i w hw
    have hs := (contMDiffAt_symm_of_mem_maximalAtlas (I := 𝓘(ℂ, ComplexModel n)) (n := ∞)
      (IsManifold.subset_maximalAtlas e.property) hw).mdifferentiableAt (by simp)
    exact (mdifferentiableAt_iff_differentiableAt.mp
      ((originalFunction_holomorphicAt f n (a i) (e.val.symm w)).mdifferentiableAt.comp w hs)).differentiableWithinAt
  exact (plurisubharmonicAt_scaled_generatorLog hG
    (show (0 : ℝ) < 1 / 2 by norm_num)).quasiPlurisubharmonicAt

/-- The whole native ideal is the extension of the same original affine ideal. -/
theorem map_ideal_eq_native_span {m : ℕ} (I : Ideal R) (a : Fin m → R)
    (ha : Ideal.span (Set.range a) = I) (p : SchemeComplexPoint f) :
    I.map (nativeMap f n p) = Ideal.span (Set.range fun i =>
      NativeHolGerm.mk (generators f a i) (originalFunction_holomorphicAt f n (a i) p)) := by
  rw [← ha,Ideal.map_span,← Set.range_comp']
  congr 1
  ext g
  simp only [Set.mem_range]
  simp only [nativeMap_apply,generators]

/-- Stalk extension followed by the actual native map gives the same whole native ideal. -/
theorem map_stalk_ideal_eq_native_span {m : ℕ} (I : Ideal R) (a : Fin m → R)
    (ha : Ideal.span (Set.range a) = I) (p : SchemeComplexPoint f) :
    (I.map (schemeAffineOriginalStalk f p)).map (schemeNativeStalkGerm f n p) =
      Ideal.span (Set.range fun i => NativeHolGerm.mk (generators f a i)
        (originalFunction_holomorphicAt f n (a i) p)) := by
  rw [Ideal.map_map]
  exact map_ideal_eq_native_span f n I a ha p

/-- The analytic ideal is the extension of the actual original ideal in each whole native stalk. -/
def analyticIdeal (I : Ideal R) : GermIdeal n (SchemeComplexPoint f) where
  mem p h := ∃ hh : HolomorphicAt n h p,
    NativeHolGerm.mk h hh ∈ I.map (nativeMap f n p)

/-- Its entire original germ membership is precisely the holomorphic span of original generators. -/
theorem analyticIdeal_mem_iff {m : ℕ} (I : Ideal R) (a : Fin m → R)
    (ha : Ideal.span (Set.range a) = I) (p : SchemeComplexPoint f) (h : SchemeComplexPoint f → ℂ) :
    (analyticIdeal f n I).mem p h ↔ IsInSpanAt (n := n) (· ∈ Set.range (generators f a)) p h := by
  constructor
  · rintro ⟨hh,hmem⟩
    rw [map_ideal_eq_native_span f n I a ha p] at hmem
    exact (mem_native_span_mk_iff (generators f a)
      (fun i => originalFunction_holomorphicAt f n (a i) p) h hh).mp hmem
  · intro hh
    refine ⟨hh.1,?_⟩
    rw [map_ideal_eq_native_span f n I a ha p]
    exact (mem_native_span_mk_iff (generators f a)
      (fun i => originalFunction_holomorphicAt f n (a i) p) h hh.1).mpr hh

/-- The actual analytified finite original affine ideal is coherent, with literal global generators. -/
theorem analyticIdeal_isCoherent {m : ℕ} (I : Ideal R) (a : Fin m → R)
    (ha : Ideal.span (Set.range a) = I) : (analyticIdeal f n I).IsCoherent := by
  intro p
  refine ⟨Set.univ,isOpen_univ,Set.mem_univ p,m,generators f a,?_,?_⟩
  · intro i q _
    exact (originalFunction_holomorphicAt f n (a i) q).mdifferentiableAt.mdifferentiableWithinAt
  · intro q _ h
    exact analyticIdeal_mem_iff f n I a ha q h

/-- The genuine half-log weight has analytic singularities of the same whole original ideal. -/
theorem weight_hasAnalyticSingularitiesOfType {m : ℕ} (I : Ideal R) (a : Fin m → R)
    (ha : Ideal.span (Set.range a) = I) :
    GlobalAnalyticSingularities.HasAnalyticSingularitiesOfType (weight f a) (1/2)
      (analyticIdeal f n I) := by
  refine ⟨by norm_num,analyticIdeal_isCoherent f n I a ha,?_⟩
  intro p
  refine ⟨Set.univ,isOpen_univ,Set.mem_univ p,m,generators f a,?_,?_,fun _ => 0,0,?_,?_⟩
  · intro i q _
    exact (originalFunction_holomorphicAt f n (a i) q).mdifferentiableAt.mdifferentiableWithinAt
  · intro q _ h
    exact analyticIdeal_mem_iff f n I a ha q h
  · intro q _
    simp
  · intro q _
    simp [weight]

/-- Inclusion of the same original affine ideals gives inclusion of their entire native analytic ideals. -/
theorem analyticIdeal_mono {I J : Ideal R} (hIJ : I ≤ J) :
    (analyticIdeal f n I).Le (analyticIdeal f n J) := by
  rintro p h ⟨hh,hmem⟩
  exact ⟨hh,Ideal.map_mono hIJ hmem⟩

include n in
/-- Original ideal containment produces the local bounded comparison of genuine normalized weights. -/
theorem weight_moreSingularAt_of_le {m k : ℕ} (I J : Ideal R) (a : Fin m → R) (b : Fin k → R)
    (ha : Ideal.span (Set.range a) = I) (hb : Ideal.span (Set.range b) = J)
    (hIJ : I ≤ J) (p : SchemeComplexPoint f) :
    MoreSingularAt (weight f a) (weight f b) p :=
  IdealWeightComparison.moreSingularAt_of_le
    (weight_hasAnalyticSingularitiesOfType f n I a ha)
    (weight_hasAnalyticSingularitiesOfType f n J b hb) (analyticIdeal_mono f n hIJ) p

include n in
/-- Choice of original generators changes the normalized weight by a locally bounded germ. -/
theorem weight_sameSingularityTypeAt {m k : ℕ} (I : Ideal R) (a : Fin m → R) (b : Fin k → R)
    (ha : Ideal.span (Set.range a) = I) (hb : Ideal.span (Set.range b) = I)
    (p : SchemeComplexPoint f) : SameSingularityTypeAt (weight f a) (weight f b) p :=
  ⟨weight_moreSingularAt_of_le f n I I a b ha hb le_rfl p,
    weight_moreSingularAt_of_le f n I I b a hb ha le_rfl p⟩

/-- Multiplying original generators by an actual original unit preserves the entire original ideal. -/
theorem span_unit_mul {m : ℕ} (a : Fin m → R) (u : Rˣ) :
    Ideal.span (Set.range fun i => (u : R) * a i) = Ideal.span (Set.range a) := by
  apply le_antisymm
  · apply Ideal.span_le.mpr
    rintro r ⟨i,rfl⟩
    exact Ideal.mul_mem_left _ (u : R) (Ideal.subset_span ⟨i,rfl⟩)
  · apply Ideal.span_le.mpr
    rintro r ⟨i,rfl⟩
    have hmem := Ideal.mul_mem_left (Ideal.span (Set.range fun j => (u : R) * a j))
      (↑u⁻¹ : R) (Ideal.subset_span (Set.mem_range_self i))
    simpa [mul_assoc] using hmem

include n in
/-- Actual original units preserve the local bounded singularity type of the normalized weight. -/
theorem weight_unit_mul {m : ℕ} (a : Fin m → R) (u : Rˣ) (p : SchemeComplexPoint f) :
    SameSingularityTypeAt (weight f (fun i => (u : R) * a i)) (weight f a) p :=
  weight_sameSingularityTypeAt f n (Ideal.span (Set.range a)) _ _ (span_unit_mul a u) rfl p

/-- Finite generation gives an actual original tuple with the whole native ideal identity. -/
theorem exists_generators {I : Ideal R} (hI : I.FG) :
    ∃ (m : ℕ) (a : Fin m → R), Ideal.span (Set.range a) = I ∧
      ManifoldQuasiPlurisubharmonic (n := n) (weight f a) ∧
      ∀ p : SchemeComplexPoint f, I.map (nativeMap f n p) = Ideal.span (Set.range fun i =>
        NativeHolGerm.mk (generators f a i) (originalFunction_holomorphicAt f n (a i) p)) := by
  obtain ⟨m,a,ha⟩ := Submodule.fg_iff_exists_fin_generating_family.mp hI
  exact ⟨m,a,ha,weight_quasiPSH f n a,fun p => map_ideal_eq_native_span f n I a ha p⟩

/-- Original coefficients remain distinct as whole native germs on an integral source. -/
theorem nativeMap_injective [IsDomain R] (p : SchemeComplexPoint f) :
    Function.Injective (nativeMap f n p) := by
  have hstalk : Function.Injective (schemeAffineOriginalStalk f p) := by
    have hloc := FaithfulSMul.algebraMap_injective R (SchemeAffineOriginalLocalRing f p)
    have h := (schemeAffineOriginalStalkEquiv f p).injective.comp hloc
    simpa only [Function.comp_def,schemeAffineOriginalStalkEquiv_algebraMap] using h
  exact (schemeNativeStalkGerm_faithfullyFlat f n p).injective.comp hstalk

include n in
/-- The finite locus meets every open neighborhood, derived from a nonzero original ideal. -/
theorem weight_locallyNondegenerate [IsDomain R] {m : ℕ} (a : Fin m → R)
    (ha : Ideal.span (Set.range a) ≠ ⊥) : LocallyNondegenerate (weight f a) := by
  classical
  have hex : ∃ i, a i ≠ 0 := by
    by_contra! h
    apply ha
    apply Ideal.span_eq_bot.mpr
    rintro r ⟨i,rfl⟩
    exact h i
  obtain ⟨i,hi⟩ := hex
  intro p U hU hp
  by_contra! h
  have heq : originalFunction f (a i) =ᶠ[𝓝 p] fun _ => 0 := by
    filter_upwards [hU.mem_nhds hp] with q hq
    exact (weight_eq_bot_iff f a q).mp (h q hq) i
  have hzero : nativeMap f n p (a i) = 0 := by
    rw [nativeMap_apply]
    apply Subtype.ext
    exact Germ.coe_eq.mpr heq
  exact hi ((nativeMap_injective f n p) (hzero.trans (map_zero _).symm))

/-- A nonzero original ideal on an integral source produces a nondegenerate global potential. -/
theorem weight_isGlobalQuasiPshPotential [IsDomain R] {m : ℕ} (a : Fin m → R)
    (ha : Ideal.span (Set.range a) ≠ ⊥) :
    IsGlobalQuasiPshPotential (n := n) (weight f a) :=
  ⟨weight_quasiPSH f n a,weight_locallyNondegenerate f n a ha⟩

/-- Every nonzero finitely generated original ideal yields an actual nondegenerate analytic ideal weight. -/
theorem exists_nonzero_ideal_weight [IsDomain R] (I : Ideal R) (hI : I.FG) (hI0 : I ≠ ⊥) :
    ∃ (m : ℕ) (a : Fin m → R), Ideal.span (Set.range a) = I ∧
      IsGlobalQuasiPshPotential (n := n) (weight f a) ∧
      GlobalAnalyticSingularities.HasAnalyticSingularitiesOfType (weight f a) (1/2)
        (analyticIdeal f n I) := by
  obtain ⟨m,a,ha⟩ := Submodule.fg_iff_exists_fin_generating_family.mp hI
  refine ⟨m,a,ha,weight_isGlobalQuasiPshPotential f n a ?_,
    weight_hasAnalyticSingularitiesOfType f n I a ha⟩
  have ha' : Ideal.span (Set.range a) = I := ha
  rwa [ha']

/-- Pairwise products in the original affine ring, with the existing finite-family indexing. -/
def productGenerators {m k : ℕ} (a : Fin m → R) (b : Fin k → R) : Fin (m*k) → R :=
  fun j => a (finProdFinEquiv.symm j).1 * b (finProdFinEquiv.symm j).2

omit [IsSeparated f] [QuasiCompact f] in
/-- Original evaluation preserves the entire pairwise product tuple. -/
theorem generators_product {m k : ℕ} (a : Fin m → R) (b : Fin k → R) :
    generators f (productGenerators a b) =
      IdealWeightProducts.mulFamily (generators f a) (generators f b) := by
  funext j p
  exact map_mul (schemeAffineOriginalPoint f p) _ _

/-- The pairwise tuple generates the whole original product ideal. -/
theorem span_productGenerators {m k : ℕ} (a : Fin m → R) (b : Fin k → R) :
    Ideal.span (Set.range (productGenerators a b)) =
      Ideal.span (Set.range a) * Ideal.span (Set.range b) := by
  rw [Ideal.span_mul_span]
  congr 1
  ext r
  constructor
  · rintro ⟨j,rfl⟩
    exact ⟨a (finProdFinEquiv.symm j).1,⟨_,rfl⟩,
      b (finProdFinEquiv.symm j).2,⟨_,rfl⟩,rfl⟩
  · rintro ⟨u,⟨i,rfl⟩,v,⟨j,rfl⟩,rfl⟩
    refine ⟨finProdFinEquiv (i,j),?_⟩
    simp [productGenerators]

omit [IsSeparated f] [QuasiCompact f] in
/-- Exact product weight, including all common zeros and zero ideals. -/
theorem weight_product {m k : ℕ} (a : Fin m → R) (b : Fin k → R)
    (p : SchemeComplexPoint f) :
    weight f (productGenerators a b) p = weight f a p + weight f b p := by
  rw [weight,generators_product,IdealWeightProducts.generatorLog_mulFamily]
  exact EReal.left_distrib_of_nonneg_of_ne_top (by norm_num) (EReal.coe_ne_top _) _ _

omit [IsSeparated f] [QuasiCompact f] in
/-- The standard e^{-2cu} convention matches the existing e^{-tφ} convention exactly. -/
theorem multiplierWeight_normalization {m : ℕ} (a : Fin m → R) (c : ℝ)
    (p : SchemeComplexPoint f) :
    multiplierWeight (2*c) (weight f a p) = multiplierWeight c (generatorLog (generators f a) p) := by
  have hcoef : (((2*c : ℝ) : EReal) * ((1/2 : ℝ) : EReal)) = (c : EReal) := by
    rw [← EReal.coe_mul]
    congr 1
    ring
  unfold multiplierWeight weight
  rw [← mul_assoc,hcoef]

omit [IsSeparated f] [QuasiCompact f] in
/-- Normalization is an equality of entire multiplier ideal sheaves, including pole densities. -/
theorem multiplierIdeal_normalization {m : ℕ} (a : Fin m → R) (c : ℝ) :
    multiplierIdeal (n := n) (2*c) (weight f a) =
      multiplierIdeal (n := n) c (generatorLog (generators f a)) := by
  have hc : (0 : ℝ) < 2*c ↔ 0 < c := by constructor <;> intro h <;> linarith
  have hd (e : ComplexChart n (SchemeComplexPoint f)) (v : ComplexModel n → ℂ) :
      multiplierDensity (chartFunction (weight f a) e) (2*c) v =
        multiplierDensity (chartFunction (generatorLog (generators f a)) e) c v := by
    funext z
    simp only [multiplierDensity,chartFunction,multiplierWeight_normalization]
  ext p h
  simp only [multiplierIdeal,MultiplierIntegrableAt,WeightedL2On,hd,hc]

end EnvelopeProperty.Char0.NativeAffineIdealWeight
