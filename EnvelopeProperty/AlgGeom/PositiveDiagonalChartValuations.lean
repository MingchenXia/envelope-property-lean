import EnvelopeProperty.AlgGeom.RankOneSameAlgebraNormComparison
import EnvelopeProperty.Global.SmoothModelEP

/-! # The SAME positive diagonal/native whole homeomorphism retains actual chart values -/
open AlgebraicGeometry CategoryTheory MvPolynomial TopologicalSpace
open scoped Classical NNReal Topology
noncomputable section
universe u
namespace EnvelopeProperty.PositiveDiagonalChartValuations
attribute [local irreducible] MultiModel.veroneseM MultiModel.veronese
variable {k K : Type u} [Field k] [Field K] [Algebra k K] {r : ℕ} [NeZero r]
    (Y : MultiModel k K r) {a : Fin r →₀ ℕ} (ha : ∀ c,0 < a c)
    (Z : MultiModel k K 1) (hS : (Y.veronese ha).S = Z.S)

/-- The SAME actual native same-algebra/positive-diagonal whole analytic homeomorphism. -/
def homeomorph : Z.an ≃ₜ Y.an :=
  (OriginalProjectiveDiagonalNativeComparison.rankOneAnalyticHomeomorph (Y.veronese ha) Z hS).symm.trans
    (Y.veroneseHomeomorph ha).symm

/-- The genuine original whole diagonal point triangle is retained. -/
theorem veronese_homeomorph (z : Z.an) :
    Y.veroneseAnMap ha (homeomorph Y ha Z hS z) =
      (OriginalProjectiveDiagonalNativeComparison.rankOneAnalyticHomeomorph (Y.veronese ha) Z hS).symm z := by
  change Y.veroneseAnMap ha ((Y.veroneseHomeomorph ha).symm _) = _
  rw [← MultiModel.veroneseHomeomorph_apply,Homeomorph.apply_symm_apply]
  rfl

include ha hS in
/-- EVERY literal original positive-diagonal homogeneous piece is the original actual multigraded piece. -/
theorem piece_mem_iff {m : ℕ} {g : K} :
    g ∈ Z.piece (Finsupp.single 0 m) ↔ g ∈ Y.piece (m • a) := by
  change monomial (Finsupp.single 0 m) g ∈ Z.S ↔ _
  rw [← hS]
  exact Y.mem_veronese_piece_iff ha

/-- EVERY actual original homogeneous polynomial value is retained by this SAME whole homeomorphism, at all supports. -/
theorem ofPiece_val (z : Z.an) {m : ℕ} {g : K} (hg : g ∈ Z.piece (Finsupp.single 0 m)) :
    z.1.val (Z.ofPiece hg) =
      (homeomorph Y ha Z hS z).1.val (Y.ofPiece ((piece_mem_iff Y ha Z hS).mp hg)) := by
  have hgD : g ∈ (Y.veronese ha).piece (Finsupp.single 0 m) := by
    change monomial (Finsupp.single 0 m) g ∈ (Y.veronese ha).S
    rw [hS]
    exact hg
  have hsame := RankOneSameAlgebraNormComparison.nativeHomeomorph_symm_val
    (Y.veronese ha) Z hS z ((Y.veronese ha).ofPiece hgD)
  change ((OriginalProjectiveDiagonalNativeComparison.rankOneAnalyticHomeomorph (Y.veronese ha) Z hS).symm z).1.val
    ((Y.veronese ha).ofPiece hgD) = z.1.val (Z.ofPiece hg) at hsame
  have hdiag := Y.veroneseAnMap_val_ofPiece ha (homeomorph Y ha Z hS z) hgD
  have he : (Y.veroneseAnMap ha (homeomorph Y ha Z hS z)).1.val ((Y.veronese ha).ofPiece hgD) =
      ((OriginalProjectiveDiagonalNativeComparison.rankOneAnalyticHomeomorph (Y.veronese ha) Z hS).symm z).1.val
        ((Y.veronese ha).ofPiece hgD) := by
    change ((Y.veroneseHomeomorph ha) ((Y.veroneseHomeomorph ha).symm _)).1.val _ = _
    rw [Homeomorph.apply_symm_apply]
    rfl
  have hp : Y.ofPiece ((Y.mem_veronese_piece_iff' ha).mp hgD) =
      Y.ofPiece ((piece_mem_iff Y ha Z hS).mp hg) :=
    Y.ofPiece_congr _ _ (by rw [Finsupp.single_eq_same]) rfl
  have hv := congrArg (fun p : Y.S => (homeomorph Y ha Z hS z).1.val p) hp
  exact hsame.symm.trans (he.symm.trans (hdiag.trans hv))

private theorem homLocAlg_eq_of_S (D W : MultiModel k K 1) (h : D.S = W.S) (g : K) (b : Fin 1 →₀ ℕ) :
    D.homLocAlg g b = W.homLocAlg g b := by
  cases D
  cases W
  cases h
  rfl

include ha hS in
/-- The ENTIRE corresponding chart algebras are equal inside the SAME actual function field. -/
theorem chartAlg_eq (j : Y.ChartIndex) (hj : ∀ c,Y.coord c (j c) ≠ 0)
    (jZ : Z.ChartIndex) (hcoord : Z.coord 0 (jZ 0) = Y.chartDen j a) :
    Z.chartAlg jZ = Y.chartAlg j := by
  have hZj : ∀ c,Z.coord c (jZ c) ≠ 0 := by
    intro c
    have hc : c = 0 := Subsingleton.elim _ _
    subst c
    rw [hcoord]
    exact MultiModel.chartDen_ne_zero hj a
  have hden : Z.chartDen jZ (Finsupp.single 0 1) = Y.chartDen j a := by
    rw [MultiModel.chartDen,Fin.prod_univ_one]
    simpa only [Finsupp.single_eq_same,pow_one] using hcoord
  rw [Z.chartAlg_eq_homLocAlg hZj (a := Finsupp.single 0 1)
      (by intro c; have hc : c = 0 := Subsingleton.elim _ _; subst c; simp),
    hden,← homLocAlg_eq_of_S (Y.veronese ha) Z hS,MultiModel.homLocAlg_veronese,
    ← Y.chartAlg_eq_homLocAlg hj ha]

/-- The literal original corresponding coordinate has the actual original multigraded chart-monomial value. -/
theorem coordinate_val (z : Z.an) (j : Y.ChartIndex) (jZ : Z.ChartIndex)
    (hcoord : Z.coord 0 (jZ 0) = Y.chartDen j a) :
    z.1.val (Z.coordElem ⟨0,jZ 0⟩) =
      (homeomorph Y ha Z hS z).1.val (Y.chartMono j a) := by
  have h := ofPiece_val Y ha Z hS z (Z.coord_mem_piece 0 (jZ 0))
  change z.1.val (Z.coordElem ⟨0,jZ 0⟩) = _ at h
  have hp : Y.ofPiece ((piece_mem_iff Y ha Z hS).mp (Z.coord_mem_piece 0 (jZ 0))) =
      Y.chartMono j a :=
    Y.ofPiece_congr _ _ (one_smul ℕ a) hcoord
  exact h.trans (congrArg (fun p : Y.S => (homeomorph Y ha Z hS z).1.val p) hp)

omit [NeZero r] in
private theorem coordinates_ne_zero (j : Y.ChartIndex) (hj : ∀ c,Y.coord c (j c) ≠ 0)
    (jZ : Z.ChartIndex) (hcoord : Z.coord 0 (jZ 0) = Y.chartDen j a) :
    ∀ c,Z.coord c (jZ c) ≠ 0 := by
  intro c
  have hc : c = 0 := Subsingleton.elim _ _
  subst c
  rw [hcoord]
  exact MultiModel.chartDen_ne_zero hj a

private theorem point_coordinates_ne_zero (z : Z.an) (j : Y.ChartIndex) (jZ : Z.ChartIndex)
    (hcoord : Z.coord 0 (jZ 0) = Y.chartDen j a)
    (hv : ∀ c,(homeomorph Y ha Z hS z).1.val (Y.coordElem ⟨c,j c⟩) ≠ 0) :
    ∀ c,z.1.val (Z.coordElem ⟨c,jZ c⟩) ≠ 0 := by
  intro c
  have hc : c = 0 := Subsingleton.elim _ _
  subst c
  rw [coordinate_val Y ha Z hS z j jZ hcoord,MultiModel.val_chartMono]
  exact Finset.prod_ne_zero_iff.mpr (fun c _ => pow_ne_zero _ (hv c))

/-- The actual corresponding original rank-one chart point, with its chart-domain facts DERIVED from the same whole homeomorphism. -/
def chartPoint (z : Z.an) (j : Y.ChartIndex) (hj : ∀ c,Y.coord c (j c) ≠ 0)
    (jZ : Z.ChartIndex) (hcoord : Z.coord 0 (jZ 0) = Y.chartDen j a)
    (hv : ∀ c,(homeomorph Y ha Z hS z).1.val (Y.coordElem ⟨c,j c⟩) ≠ 0) :
    Berk k (Z.chartAlg jZ) :=
  Z.chartMap (coordinates_ne_zero Y Z j hj jZ hcoord) z.1
    (point_coordinates_ne_zero Y ha Z hS z j jZ hcoord hv)

/-- EVERY actual original regular chart function retains its value under the SAME whole homeomorphism. -/
theorem chartMap_val (z : Z.an) (j : Y.ChartIndex) (hj : ∀ c,Y.coord c (j c) ≠ 0)
    (jZ : Z.ChartIndex) (hcoord : Z.coord 0 (jZ 0) = Y.chartDen j a)
    (hv : ∀ c,(homeomorph Y ha Z hS z).1.val (Y.coordElem ⟨c,j c⟩) ≠ 0)
    (x : Z.chartAlg jZ) :
    (chartPoint Y ha Z hS z j hj jZ hcoord hv).val x =
      (Y.chartMap hj (homeomorph Y ha Z hS z).1 hv).val
        ((Subalgebra.equivOfEq _ _ (chartAlg_eq Y ha Z hS j hj jZ hcoord)) x) := by
  let xY : Y.chartAlg j := ⟨x.1,(chartAlg_eq Y ha Z hS j hj jZ hcoord) ▸ x.property⟩
  have hxLoc : (x : K) ∈ Y.homLocAlg (Y.chartDen j a) a := by
    rw [← Y.chartAlg_eq_homLocAlg hj ha]
    exact xY.property
  obtain ⟨m,g,hg,hx⟩ := (Y.mem_homLocAlg_iff (Y.chartDen_mem_piece j a)
    (MultiModel.chartDen_ne_zero hj a)).mp hxLoc
  have hgZ : g ∈ Z.piece (Finsupp.single 0 m) := (piece_mem_iff Y ha Z hS).mpr hg
  have hxY : (xY : K) = g / Y.chartDen j (m • a) := by
    rw [MultiModel.chartDen_nsmul]
    exact hx
  have hxZ : (x : K) = g / Z.chartDen jZ (Finsupp.single 0 m) := by
    rw [MultiModel.chartDen,Fin.prod_univ_one,Finsupp.single_eq_same,hcoord]
    exact hx
  have hdenVal : z.1.val (Z.chartMono jZ (Finsupp.single 0 m)) =
      (homeomorph Y ha Z hS z).1.val (Y.chartMono j (m • a)) := by
    have hs : Finsupp.single (0 : Fin 1) m = m • Finsupp.single 0 1 := by
      rw [Finsupp.smul_single]
      simp only [smul_eq_mul,mul_one]
    rw [hs,MultiModel.chartMono_nsmul,MultiModel.chartMono_nsmul,map_pow,map_pow,
      MultiModel.chartMono_single]
    exact congrArg (fun v => v ^ m) (coordinate_val Y ha Z hS z j jZ hcoord)
  change (Z.chartMap (coordinates_ne_zero Y Z j hj jZ hcoord) z.1
    (point_coordinates_ne_zero Y ha Z hS z j jZ hcoord hv)).val x =
      (Y.chartMap hj (homeomorph Y ha Z hS z).1 hv).val xY
  rw [Z.chartMap_val_eq _ _ x hgZ hxZ,Y.chartMap_val_eq _ _ xY hg hxY]
  exact congrArg₂ (fun u v : ℝ≥0 => u / v) (ofPiece_val Y ha Z hS z hgZ) hdenVal

end EnvelopeProperty.PositiveDiagonalChartValuations
