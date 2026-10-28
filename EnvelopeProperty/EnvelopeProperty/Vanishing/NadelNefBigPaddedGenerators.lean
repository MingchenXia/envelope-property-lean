import EnvelopeProperty.AlgGeom.SchemeGeneratedLineCoefficients
noncomputable section
universe u
namespace EnvelopeProperty.Vanishing.NadelNefBigPaddedGenerators
open EnvelopeProperty.SchemeGeneratedLineCoefficients
variable {A : Type u} [CommRing A] (I : Ideal A) {ι : Type u} [Fintype ι] (g : ι → I)

theorem padded_zero : paddedCoefficients (fun i => (g i : A)) 0 = 0 := rfl

theorem padded_generator (i : ι) :
    paddedCoefficients (fun j => (g j : A)) ((Fintype.equivFin ι) i).succ = g i := by
  simp only [paddedCoefficients, Fin.cases_succ, Equiv.symm_apply_apply]

theorem span_padded (hspan : Ideal.span (Set.range (fun i => (g i : A))) = I) :
    Ideal.span (Set.range (paddedCoefficients (fun i => (g i : A)))) = I := by
  apply le_antisymm
  · apply Ideal.span_le.mpr
    rintro x ⟨j, rfl⟩
    induction j using Fin.cases with
    | zero => exact I.zero_mem
    | succ j => exact (g ((Fintype.equivFin ι).symm j)).property
  · apply hspan.symm.le.trans
    apply Ideal.span_mono
    rintro x ⟨i, rfl⟩
    exact ⟨((Fintype.equivFin ι) i).succ, padded_generator I g i⟩
end EnvelopeProperty.Vanishing.NadelNefBigPaddedGenerators
