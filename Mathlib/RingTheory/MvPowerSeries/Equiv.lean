/-
Copyright (c) 2026 Bingyu Xia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingyu Xia
-/
module

public import Mathlib.RingTheory.PowerSeries.Trunc
public import Mathlib.RingTheory.MvPowerSeries.Rename

/-!
# Equivalences related to power series rings

This file establishes a number of equivalences related to power series rings and
is patterned after `Mathlib/Algebra/MvPolynomial/Equiv.lean`.

* `MvPowerSeries.isEmptyEquiv` : The isomorphism between multivariable power series
  in no variables and the ground ring.

* `MvPowerSeries.uniqueEquiv` : The isomorphism between multivariable power series
  in a single variable and power series over the ground ring.

* `MvPowerSeries.congrRingEquiv`, `MvPowerSeries.congrAlgEquiv` : The isomorhism between
  multivariable power series induced by an isomorphism between the coefficient rings.

* `MvPowerSeries.sumAlgEquiv` : The isomorphism between multivariable power series
  in a sum of two types, and multivariable power series in one of the types,
  with coefficients in multivariable power series in the other type.

* `MvPowerSeries.commAlgEquiv` : The isomorphism between multivariable power series
  in variables `σ` of multivariable power series in variables `τ` and multivariable power series
  in variables `τ` of multivariable power series in variables `σ`.

* `MvPowerSeries.optionEquivLeft` : The isomorphism between multivariable power series
  in `Option σ` and power series with coefficients in `MvPowerSeries σ R`.

* `MvPowerSeries.optionEquivRight` : The isomorphism between multivariable power series
  in `Option σ` and multivariable power series in `σ` with coefficients in `PowerSeries R`.

* `MvPowerSeries.finSuccEquiv` : The isomorphism between multivariable power series
  in `Fin (n + 1)` and power series over multivariable power series in `Fin n`.

-/

@[expose] public section

noncomputable section

namespace MvPowerSeries

variable {σ τ R S : Type*}

open Finsupp Function

section CommSemiring

variable [CommSemiring R]

section isEmptyEquiv

variable (σ R) in
/-- The isomorphism between multivariable power series in no variables and the ground ring. -/
@[simps!]
def isEmptyEquiv [IsEmpty σ] : MvPowerSeries σ R ≃ₐ[R] R where
  __ := constantCoeff
  invFun := C
  left_inv _ := by
    ext x; rw [Subsingleton.eq_zero x]
    simp
  commutes' _ := rfl

end isEmptyEquiv

section uniqueEquiv

variable (σ R) in
/-- The isomorphism between multivariable power series in a single variable and
power series over the ground ring. -/
abbrev uniqueEquiv [Unique σ] : MvPowerSeries σ R ≃ₐ[R] PowerSeries R :=
  renameEquiv R (Equiv.ofUnique σ Unit)

theorem coeff_uniqueEquiv [Unique σ] (p : MvPowerSeries σ R) (n : ℕ) :
    PowerSeries.coeff n (uniqueEquiv σ R p) = p.coeff (single default n) := by
  simp [PowerSeries.coeff, ← coeff_embDomain_rename (Equiv.ofUnique σ Unit).toEmbedding p]

lemma uniqueEquiv_X [Unique σ] : uniqueEquiv σ R (X default) = .X := by simp [PowerSeries.X]

lemma uniqueEquiv_C [Unique σ] (r : R) : uniqueEquiv σ R (C r) = .C r := by simp [PowerSeries.C]

end uniqueEquiv

section Map

variable [CommSemiring S] {f : R →+* S}

variable (σ) in
/-- If `e : A ≃+* B` is an isomorphism of rings, then so is `map e`. -/
@[simps apply]
def congrRingEquiv (e : R ≃+* S) : MvPowerSeries σ R ≃+* MvPowerSeries σ S where
  __ := map (e : R →+* S)
  invFun := map (e.symm : S →+* R)
  left_inv := map_leftInverse e.left_inv
  right_inv := map_rightInverse e.right_inv

@[simp]
theorem congrRingEquiv_refl : congrRingEquiv σ (RingEquiv.refl R) = RingEquiv.refl _ :=
  RingEquiv.ext (by simp)

@[simp]
theorem congrRingEquiv_symm (e : R ≃+* S) : (congrRingEquiv σ e).symm = congrRingEquiv σ e.symm :=
  rfl

@[simp]
theorem congrRingEquiv_trans {S' : Type*} [CommSemiring S'] (e : R ≃+* S) (f : S ≃+* S') :
    (congrRingEquiv σ e).trans (congrRingEquiv σ f) = congrRingEquiv σ (e.trans f) :=
  RingEquiv.ext fun p => by simp

variable {A₁ A₂ A₃ : Type*} [CommSemiring A₁] [CommSemiring A₂] [CommSemiring A₃]
variable [Algebra R A₁] [Algebra R A₂] [Algebra R A₃]

variable (σ) in
/-- If `e : A ≃ₐ[R] B` is an isomorphism of `R`-algebras, then so is `map e`. -/
@[simps apply]
def congrAlgEquiv (e : A₁ ≃ₐ[R] A₂) : MvPowerSeries σ A₁ ≃ₐ[R] MvPowerSeries σ A₂ := {
  mapAlgHom (e : A₁ →ₐ[R] A₂), congrRingEquiv σ (e : A₁ ≃+* A₂) with toFun := map (e : A₁ →+* A₂) }

@[simp]
theorem congrAlgEquiv_refl : congrAlgEquiv σ (AlgEquiv.refl : A₁ ≃ₐ[R] A₁) = AlgEquiv.refl :=
  AlgEquiv.ext (by simp)

@[simp]
theorem congrAlgEquiv_symm (e : A₁ ≃ₐ[R] A₂) : (congrAlgEquiv σ e).symm = congrAlgEquiv σ e.symm :=
  rfl

@[simp]
theorem congrAlgEquiv_trans (e : A₁ ≃ₐ[R] A₂) (f : A₂ ≃ₐ[R] A₃) :
    (congrAlgEquiv σ e).trans (congrAlgEquiv σ f) = congrAlgEquiv σ (e.trans f) := by
  ext; simp

end Map

end CommSemiring

end MvPowerSeries
