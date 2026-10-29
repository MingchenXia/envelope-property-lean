import EnvelopeProperty.Potential.CurvePieceRefinement
import EnvelopeProperty.Potential.CurvePieceLocalizedFubiniStudy

/-! # Exact literal original weighted norms under genuine finite piece refinement -/

open scoped NNReal ENNReal Polynomial TensorProduct Topology Classical
open Polynomial Topology
noncomputable section
namespace EnvelopeProperty.Berkovich.RelativeSpectrum.FCStandardAffinoid

variable {K B ι : Type*} [Field K] [IsAlgClosed K] {w : Valuation K ℝ≥0} {m n : ℕ}
variable [CommRing B] [Algebra K[X] B] [Algebra K B] [IsScalarTower K K[X] B] [Fintype ι]
variable (U : FCStandardAffinoid w m)

/-- The actual original prescribed-base point of a whole original completed-fibre point. -/
def curveFibreRelativePoint (x : U.carrier) (y : Spectrum.Fibre (B := B) x.1.1) :
    U.CurvePreimage (B := B) :=
  ⟨fcRelativeFibrePoint x.1 y,by rw [fcRelativeFibrePoint_base]; exact x.2⟩

omit [Fintype ι] in
/-- Selected original completed-fibre and whole original curve-point conditions are EXACT. -/
theorem curveFibreRelativePoint_mem_originalPiece (basis : Module.Basis ι K[X] B)
    (e : U.CurveAnalyticAlgebra basis) (x : U.carrier) (y : Spectrum.Fibre (B := B) x.1.1) :
    (Spectrum.fibrePoint y.2).1.val (U.curveIdempotentSpecialization basis e x) = 1 ↔
      U.curveFibreRelativePoint x y ∈ U.curveIdempotentOriginalPiece basis e := by
  have h := U.curveOriginalEvaluation_fibre basis (fcRelativeFibrePoint x.1 y) x
    (fcRelativeFibrePoint_base x.1 y) e
  rw [U.curveOriginalEvaluation_specialization] at h
  exact (congrArg (· = 1) h).symm.to_iff

theorem mem_completedIdempotentFibrePiece_iff_ambient (basis : Module.Basis ι K[X] B)
    (e : U.CurveAnalyticAlgebra basis) (x : U.carrier) (y : Spectrum.Fibre (B := B) x.1.1) :
    let := Module.Finite.of_basis basis
    y ∈ Spectrum.completedIdempotentFibrePiece x.1.1 (U.curveIdempotentSpecialization basis e x) ↔
      (U.curveFibreRelativePoint x y).1 ∈ U.curveIdempotentAmbientPiece basis e := by
  let := Module.Finite.of_basis basis
  rw [U.mem_curveIdempotentAmbientPiece_iff basis e]
  simp only [Spectrum.completedIdempotentFibrePiece,Finset.mem_filter,Finset.mem_univ,true_and]
  exact U.curveFibreRelativePoint_mem_originalPiece basis e x y

omit [Algebra K B] [IsScalarTower K K[X] B] in
/-- Restriction retains the EXACT original finite point set, whole values and full weights. -/
theorem curvePieceNorm_restriction (V : FCStandardAffinoid w n) (hVU : V.carrier ⊆ U.carrier)
    (basis : Module.Basis ι K[X] B) {e : U.CurveAnalyticAlgebra basis} (he : IsIdempotentElem e)
    (u : Spectrum B → EReal) (x : V.carrier) :
    V.curvePieceNorm basis (he.map (U.curveAnalyticNormedRestriction V hVU basis)) u x.1 =
      U.curvePieceNorm basis he u x.1 := by
  let := Module.Finite.of_basis basis
  rw [V.curvePieceNorm_apply basis _ u x,U.curvePieceNorm_apply basis he u ⟨x.1,hVU x.2⟩]
  change (∑ y ∈ Spectrum.completedIdempotentFibrePiece x.1.1
    (V.curveAnalyticSpecialization x (U.curveAnalyticRestriction V hVU (U.curveAnalyticOriginalEquiv basis e))),
      ((Spectrum.fibreNormMult K[X] y.1 : ℝ) : EReal)*u y.1) = _
  rw [U.curveAnalyticRestriction_specialization V hVU]
  rfl

/-- The actual whole original finite weighted norm is additive under a GENUINE
literal finite disjoint partition, retaining ALL original point weights. -/
theorem curvePieceNorm_partition {J : Type*} [Fintype J]
    (basis : Module.Basis ι K[X] B) {e : U.CurveAnalyticAlgebra basis} (he : IsIdempotentElem e)
    (a : J → U.CurveAnalyticAlgebra basis) (ha : ∀ j, IsIdempotentElem (a j))
    (hcover : U.curveIdempotentAmbientPiece basis e = ⋃ j, U.curveIdempotentAmbientPiece basis (a j))
    (hdisj : Pairwise (fun i j => Disjoint (U.curveIdempotentAmbientPiece basis (a i))
      (U.curveIdempotentAmbientPiece basis (a j))))
    (u : Spectrum B → EReal) (x : U.carrier) :
    U.curvePieceNorm basis he u x.1 = ∑ j, U.curvePieceNorm basis (ha j) u x.1 := by
  classical
  let := Module.Finite.of_basis basis
  let S (c : U.CurveAnalyticAlgebra basis) :=
    Spectrum.completedIdempotentFibrePiece x.1.1 (U.curveIdempotentSpecialization basis c x)
  have hS : S e = Finset.univ.biUnion (fun j => S (a j)) := by
    ext y
    simp only [Finset.mem_biUnion,Finset.mem_univ,true_and]
    change y ∈ S e ↔ ∃ j, y ∈ S (a j)
    simp only [S,U.mem_completedIdempotentFibrePiece_iff_ambient,hcover,Set.mem_iUnion]
  have hSpair : (↑(Finset.univ : Finset J) : Set J).PairwiseDisjoint (fun j => S (a j)) := by
    intro i _ j _ hij
    apply Finset.disjoint_left.mpr
    intro y hyi hyj
    have hyi' := (U.mem_completedIdempotentFibrePiece_iff_ambient basis (a i) x y).mp hyi
    have hyj' := (U.mem_completedIdempotentFibrePiece_iff_ambient basis (a j) x y).mp hyj
    exact Set.disjoint_left.mp (hdisj hij) hyi' hyj'
  rw [U.curvePieceNorm_apply basis he u x]
  change (∑ y ∈ S e, ((Spectrum.fibreNormMult K[X] y.1 : ℝ) : EReal)*u y.1) = _
  rw [hS,Finset.sum_biUnion hSpair]
  apply Finset.sum_congr rfl
  intro j _
  exact (U.curvePieceNorm_apply basis (ha j) u x).symm

end EnvelopeProperty.Berkovich.RelativeSpectrum.FCStandardAffinoid
