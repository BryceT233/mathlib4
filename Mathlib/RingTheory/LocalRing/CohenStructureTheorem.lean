/-
Copyright (c) 2026 Bingyu Xia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan, Bingyu Xia
-/
module

public import Mathlib.RingTheory.AdicCompletion.Completeness
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.RingTheory.MvPowerSeries.Evaluation

public section

open MvPowerSeries IsLocalRing

variable {R : Type*} [CommRing R] [IsLocalRing R]
variable {S : Type*} [CommRing S] [IsLocalRing S]
variable {f : S →+* R}

lemma exists_mvPowerSeries_surjective_of_residueField_map_bijective
    [IsAdicComplete (maximalIdeal R) R] (fg : (maximalIdeal R).FG)
    [IsLocalHom f] (bij : Function.Bijective (ResidueField.map f)) :
    ∃ (n : ℕ) (g : MvPowerSeries (Fin n) S →+* R), Function.Surjective g ∧ g.comp C = f := by
  let : WithIdeal R := { i := maximalIdeal R }
  let : WithIdeal S := { i := maximalIdeal S }
  have f_cont : Continuous f := (WithIdeal.uniformContinuous_of_map_le
    (((IsLocalRing.local_hom_TFAE f).out 0 2).mp (by infer_instance))).continuous
  let : CompleteSpace R := (IsAdic.isPrecomplete_iff (by rfl)).mp (by infer_instance)
  let : T2Space R := (IsAdic.isHausdorff_iff (by rfl)).mp (by infer_instance)
  rcases fg with ⟨s, hs⟩
  have hasEval_equivFin : HasEval (Subtype.val ∘ s.equivFin.symm) := by
    refine ⟨fun i ↦ ?_, by simp [Filter.cofinite_eq_bot]⟩
    have : (Subtype.val ∘ s.equivFin.symm) i ∈ maximalIdeal R := by
      simpa [← hs] using Submodule.mem_span_of_mem (by simp)
    exact WithIdeal.isTopologicallyNilpotent_of_mem this
  let F : MvPowerSeries (Fin s.card) S →+* R := eval₂Hom f_cont hasEval_equivFin
  let : UniformSpace (MvPolynomial (Fin s.card) S) :=
    .comap MvPolynomial.toMvPowerSeries (Pi.uniformSpace _)
  let I : Ideal (MvPowerSeries (Fin s.card) S) := .span (.range X)
  have aux_cont : Continuous (MvPolynomial.eval₂ f (Subtype.val ∘ s.equivFin.symm)) :=
    (MvPolynomial.toMvPowerSeries_uniformContinuous f_cont hasEval_equivFin).continuous
  have map_F_I : I.map F = maximalIdeal R := by
    rw [Ideal.map_span, ← hs]
    congr; ext r
    suffices (∃ a, (s.equivFin.symm a) = r) ↔ r ∈ s by
      simpa [eval₂Hom_eq_extend, F, ← MvPolynomial.coe_X, IsDenseInducing.extend_eq _ aux_cont]
    exact ⟨fun ⟨i, hi⟩ ↦ by simp [← hi], fun h ↦ ⟨s.equivFin ⟨r, h⟩, by simp⟩⟩
  have : IsAdicComplete (I.map F) R := by rwa [map_F_I]
  have F_C (s : S) : F (C s) = f s := by
    simp [eval₂Hom_eq_extend, F, ← MvPolynomial.coe_C, IsDenseInducing.extend_eq _ aux_cont]
  refine ⟨s.card, F, ?_, by ext; exact F_C _⟩
  refine surjective_of_mk_map_comp_surjective (I := I) F fun z ↦ ?_
  rcases bij.surjective (Ideal.quotEquivOfEq map_F_I z) with ⟨w, hw⟩
  revert hw
  refine Submodule.Quotient.induction_on _ w fun s hs ↦ ⟨C s, ?_⟩
  rw [RingHom.coe_comp, Function.comp_apply, F_C,
    ← (Ideal.quotEquivOfEq map_F_I).injective.eq_iff, ← hs]
  rfl

end
