/-
Copyright (c) 2019 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Kenny Lau
-/
module

public import Mathlib.RingTheory.MvPowerSeries.Basic
public import Mathlib.RingTheory.MvPolynomial.Ideal
public import Mathlib.Data.Finsupp.Interval
public import Mathlib.RingTheory.AdicCompletion.Algebra

/-!

# Formal (multivariate) power series - Truncation

* `MvPowerSeries.truncFinset s p` restricts the support of a multivariate power series `p`
  to a finite set of monomials and obtains a multivariate polynomial.

* `MvPowerSeries.trunc n φ` truncates a formal multivariate power series
  to the multivariate polynomial that has the same coefficients as `φ`,
  for all `m < n`, and `0` otherwise.

  Note that here, `m` and `n` have types `σ →₀ ℕ`,
  so that `m < n` means that `m ≠ n` and `m s ≤ n s` for all `s : σ`.

* `MvPowerSeries.trunc_one` : truncation of the unit power series

* `MvPowerSeries.trunc_C` : truncation of a constant

* `MvPowerSeries.trunc_C_mul` : truncation of constant multiple.

* `MvPowerSeries.trunc' n φ` truncates a formal multivariate power series
  to the multivariate polynomial that has the same coefficients as `φ`,
  for all `m ≤ n`, and `0` otherwise.

  Here, `m` and `n`  have types `σ →₀ ℕ` so that `m ≤ n` means that `m s ≤ n s` for all `s : σ`.


* `MvPowerSeries.coeff_mul_eq_coeff_trunc'_mul_trunc'` : compares the coefficients
  of a product with those of the product of truncations.

* `MvPowerSeries.trunc'_one` : truncation of the unit power series.

* `MvPowerSeries.trunc'_C` : truncation of a constant.

* `MvPowerSeries.trunc'_C_mul` : truncation of a constant multiple.

* `MvPowerSeries.trunc'_map` : image of a truncation under a change of rings

* `MvPowerSeries.truncTotal` : the truncation of a multivariate formal power series at
  a total degree `n` when the index `σ` is finite

* `MvPowerSeries.truncTotalAlgHom` : the canonical map induced by `truncTotal` from
  multivariate power series to the quotient ring of multivariate plynomials at
  its `n`-th power of the ideal spanned by all variables.

* `MvPowerSeries.toAdicCompletionAlgEquiv` : the canonical isomorphism from
  multivariate power series to the adic completion of multivariate polynomials at
  the ideal spanned by all variables when the index is finite.

-/

public section

noncomputable section

namespace MvPowerSeries

open Finsupp Finset

variable {σ R S : Type*}

section TruncFinset

variable [CommSemiring R] {s : Finset (σ →₀ ℕ)}

/-- Restrict the support of a multivariate power series to a finite set of monomials and
obtain a multivariate polynomial. -/
def truncFinset (R : Type*) [CommSemiring R] (s : Finset (σ →₀ ℕ)) :
    MvPowerSeries σ R →ₗ[R] MvPolynomial σ R where
  toFun p := ∑ x ∈ s, MvPolynomial.monomial x (p.coeff x)
  map_add' _ _ := by simp [sum_add_distrib]
  map_smul' _ _ := by
    classical
    ext; simp [MvPolynomial.coeff_sum]

theorem truncFinset_apply (p : MvPowerSeries σ R) :
    truncFinset R s p = ∑ x ∈ s, MvPolynomial.monomial x (p.coeff x) := by rfl

@[grind =]
theorem coeff_truncFinset_of_mem {x : σ →₀ ℕ} (p : MvPowerSeries σ R) (h : x ∈ s) :
    (truncFinset R s p).coeff x = p.coeff x := by
  classical
  simp [truncFinset_apply, MvPolynomial.coeff_sum, h]

@[grind =]
theorem coeff_truncFinset_eq_zero {x : σ →₀ ℕ} (p : MvPowerSeries σ R) (h : x ∉ s) :
    (truncFinset R s p).coeff x = 0 := by
  classical
  simp [truncFinset_apply, MvPolynomial.coeff_sum, h]

lemma coeff_truncFinset [DecidableEq σ] {x : σ →₀ ℕ} (p : MvPowerSeries σ R) :
    (truncFinset R s p).coeff x = if x ∈ s then p.coeff x else 0 := by
  simp [truncFinset_apply, MvPolynomial.coeff_sum]

theorem truncFinset_monomial {x : σ →₀ ℕ} (r : R) (h : x ∈ s) :
    truncFinset R s (monomial x r) = MvPolynomial.monomial x r := by
  classical
  ext
  grind [coeff_monomial, MvPolynomial.coeff_monomial]

theorem truncFinset_monomial_eq_zero {x : σ →₀ ℕ} (r : R) (h : x ∉ s) :
    truncFinset R s (monomial x r) = 0 := by
  classical
  ext; simp [truncFinset, MvPolynomial.coeff_sum, coeff_monomial]
  grind

theorem truncFinset_C (h : 0 ∈ s) (r : R) : truncFinset R s (C r) = MvPolynomial.C r :=
  truncFinset_monomial r h

theorem truncFinset_one (h : 0 ∈ s) : truncFinset R s (1 : MvPowerSeries σ R) = 1 :=
  truncFinset_C h 1

theorem truncFinset_truncFinset {t : Finset (σ →₀ ℕ)} (h : s ⊆ t) (p : MvPowerSeries σ R) :
    truncFinset R s (truncFinset R t p) = truncFinset R s p := by
  ext x
  by_cases x ∈ s <;> grind [MvPolynomial.coeff_coe]

theorem truncFinset_map [CommSemiring S] (f : R →+* S) (p : MvPowerSeries σ R) :
    truncFinset S s (map f p) = MvPolynomial.map f (truncFinset R s p) := by
  ext x
  by_cases x ∈ s <;> grind [coeff_map, MvPolynomial.coeff_map]

theorem coeff_truncFinset_mul_truncFinset_eq_coeff_mul (hs : IsLowerSet (s : Set (σ →₀ ℕ)))
    {x : σ →₀ ℕ} (f g : MvPowerSeries σ R) (hx : x ∈ s) :
      (truncFinset R s f * truncFinset R s g).coeff x = coeff x (f * g) := by
  classical
  simp only [MvPowerSeries.coeff_mul, MvPolynomial.coeff_mul]
  apply sum_congr rfl
  rintro ⟨i, j⟩ hij
  simp only [mem_antidiagonal] at hij
  rw [coeff_truncFinset_of_mem _ (hs (show i ≤ x by simp [← hij]) hx),
    coeff_truncFinset_of_mem _ (hs (show j ≤ x by simp [← hij]) hx)]

theorem truncFinset_truncFinset_pow (hs : IsLowerSet (s : Set (σ →₀ ℕ))) {k : ℕ} (hk : 1 ≤ k)
    (p : MvPowerSeries σ R) : truncFinset R s ((truncFinset R s p) ^ k) =
      truncFinset R s (p ^ k) := by
  induction k, hk using Nat.le_induction with
  | base => simp [truncFinset_truncFinset]
  | succ n hmn ih =>
    ext x; by_cases hx : x ∈ s
    · rw [coeff_truncFinset_of_mem _ hx, coeff_truncFinset_of_mem _ hx, pow_succ,
        ← coeff_truncFinset_mul_truncFinset_eq_coeff_mul hs _ _ hx, ih, truncFinset_truncFinset
        (by rfl), pow_succ, coeff_truncFinset_mul_truncFinset_eq_coeff_mul hs _ _ hx]
    simp [coeff_truncFinset_eq_zero _ hx]

theorem support_truncFinset_subset (p : MvPowerSeries σ R) : (truncFinset R s p).support ⊆ s := by
  intro; contrapose!
  simpa using coeff_truncFinset_eq_zero p

lemma totalDegree_truncFinset (p : MvPowerSeries σ R) :
    (truncFinset R s p).totalDegree ≤ s.sup degree := by
  simpa [MvPolynomial.totalDegree] using sup_mono (support_truncFinset_subset p)

lemma truncFinset_coe_eq_self_iff (p : MvPolynomial σ R) :
    truncFinset R s p = p ↔ p.support ⊆ s := by
  refine ⟨fun h ↦ ?_, fun h ↦ MvPolynomial.ext _ _ fun x ↦ ?_⟩
  · rw [← h]
    exact support_truncFinset_subset ..
  by_cases x ∈ s <;> grind [MvPolynomial.coeff_coe]

set_option backward.isDefEq.respectTransparency false in
lemma truncFinset_range_eq_restrictSupport :
    (truncFinset R s).range = MvPolynomial.restrictSupport R s := by
  refine le_antisymm ?_ (fun p h ↦ ⟨p, ?_⟩)
  · rintro _ ⟨p, rfl⟩
    rw [truncFinset_apply]
    refine Submodule.sum_mem _ (fun x hx ↦ ?_)
    simp [MvPolynomial.monomial_mem_restrictSupport, hx]
  rw [MvPolynomial.mem_restrictSupport_iff] at h
  rwa [truncFinset_coe_eq_self_iff]

end TruncFinset

section TruncLT

variable [DecidableEq σ] [CommSemiring R]

/-- The `n`th truncation of a multivariate formal power series to a multivariate polynomial

If `f : MvPowerSeries σ R` and `n : σ →₀ ℕ` is a (finitely-supported) function from `σ`
to the naturals, then `trunc R n f` is the multivariable polynomial obtained from `f`
by keeping only the monomials $c\prod_i X_i^{a_i}$ where `a i ≤ n i` for all `i`
and `a i < n i` for some `i`. -/
def trunc (R : Type*) [CommSemiring R] (n : σ →₀ ℕ) :
    MvPowerSeries σ R →ₗ[R] MvPolynomial σ R := truncFinset R (Iio n)

theorem coeff_trunc (m n : σ →₀ ℕ) (φ : MvPowerSeries σ R) :
    (trunc R n φ).coeff m = if m < n then coeff m φ else 0 := by
  simpa using coeff_truncFinset (s := Iio n) (x := m) φ

@[simp]
theorem trunc_one (n : σ →₀ ℕ) (hnn : n ≠ 0) : trunc R n 1 = 1 :=
  truncFinset_one (by simpa using pos_of_ne_zero hnn)

@[simp]
theorem trunc_C (n : σ →₀ ℕ) (hnn : n ≠ 0) (a : R) : trunc R n (C a) = MvPolynomial.C a :=
  truncFinset_C (by simpa using pos_of_ne_zero hnn) a

@[simp]
theorem trunc_C_mul (n : σ →₀ ℕ) (a : R) (p : MvPowerSeries σ R) :
    trunc R n (C a * p) = MvPolynomial.C a * trunc R n p := by
  ext m; simp [coeff_trunc]

@[simp]
theorem trunc_map [CommSemiring S] (n : σ →₀ ℕ) (f : R →+* S) (p : MvPowerSeries σ R) :
    trunc S n (map f p) = MvPolynomial.map f (trunc R n p) := truncFinset_map f p

end TruncLT

section TruncLE

variable [DecidableEq σ] [CommSemiring R]

/--
The `n`th truncation of a multivariate formal power series to a multivariate polynomial.

If `f : MvPowerSeries σ R` and `n : σ →₀ ℕ` is a (finitely-supported) function from `σ`
to the naturals, then `trunc' R n f` is the multivariable polynomial obtained from `f`
by keeping only the monomials $c\prod_i X_i^{a_i}$ where `a i ≤ n i` for all `i`. -/
def trunc' (R : Type*) [CommSemiring R] (n : σ →₀ ℕ) :
    MvPowerSeries σ R →ₗ[R] MvPolynomial σ R := truncFinset R (Iic n)

/-- Coefficients of the truncation of a multivariate power series. -/
theorem coeff_trunc' (m n : σ →₀ ℕ) (φ : MvPowerSeries σ R) :
    (trunc' R n φ).coeff m = if m ≤ n then coeff m φ else 0 := by
  simpa using coeff_truncFinset (s := Iic n) (x := m) φ

theorem trunc'_trunc' {n m : σ →₀ ℕ} (h : n ≤ m) (φ : MvPowerSeries σ R) :
    trunc' R n (trunc' R m φ) = trunc' R n φ :=
  truncFinset_truncFinset (Iic_subset_Iic.mpr h) φ

/-- Truncation of the multivariate power series `1` -/
@[simp]
theorem trunc'_one (n : σ →₀ ℕ) : trunc' R n 1 = 1 := truncFinset_one (by simp)

@[simp]
theorem trunc'_C (n : σ →₀ ℕ) (a : R) : trunc' R n (C a) = MvPolynomial.C a :=
  truncFinset_C (by simp) a

/-- Coefficients of the truncation of a product of two multivariate power series -/
theorem coeff_trunc'_mul_trunc'_eq_coeff_mul (n : σ →₀ ℕ)
    (f g : MvPowerSeries σ R) {m : σ →₀ ℕ} (h : m ≤ n) :
    (trunc' R n f * trunc' R n g).coeff m = coeff m (f * g) :=
  coeff_truncFinset_mul_truncFinset_eq_coeff_mul (by intro; grind) f g (by simpa)

@[deprecated coeff_trunc'_mul_trunc'_eq_coeff_mul (since := "2026-02-20")]
theorem coeff_mul_eq_coeff_trunc'_mul_trunc' (n : σ →₀ ℕ) (f g : MvPowerSeries σ R) {m : σ →₀ ℕ}
    (h : m ≤ n) : coeff m (f * g) = (trunc' R n f * trunc' R n g).coeff m :=
  (coeff_trunc'_mul_trunc'_eq_coeff_mul n f g h).symm

theorem trunc'_trunc'_pow {n : σ →₀ ℕ} {k : ℕ} (hk : 1 ≤ k) (φ : MvPowerSeries σ R) :
    trunc' R n ((trunc' R n φ) ^ k) = trunc' R n (φ ^ k) :=
  truncFinset_truncFinset_pow (by intro; grind) hk φ

@[simp]
theorem trunc'_C_mul (n : σ →₀ ℕ) (a : R) (p : MvPowerSeries σ R) :
    trunc' R n (C a * p) = MvPolynomial.C a * trunc' R n p := by
  ext m; simp [coeff_trunc']

@[simp]
theorem trunc'_map [CommSemiring S] (n : σ →₀ ℕ) (f : R →+* S) (p : MvPowerSeries σ R) :
    trunc' S n (map f p) = MvPolynomial.map f (trunc' R n p) := truncFinset_map f p

section

theorem totalDegree_trunc' {n : σ →₀ ℕ} (φ : MvPowerSeries σ R) :
    (trunc' R n φ).totalDegree ≤ n.degree := by
  simpa [← sup_Iic_of_monotone degree_mono] using totalDegree_truncFinset φ

theorem ext_trunc' {f g : MvPowerSeries σ R} : f = g ↔ ∀ n, trunc' R n f = trunc' R n g := by
  refine ⟨fun h => by simp [h], fun h => ?_⟩
  ext n
  specialize h n
  have {f' : MvPowerSeries σ R} : f'.coeff n = (trunc' R n f').coeff n := by
    rw [coeff_trunc', if_pos le_rfl]
  simp_rw [this, h]

open Filter in
theorem eq_iff_frequently_trunc'_eq {f g : MvPowerSeries σ R} :
    f = g ↔ ∃ᶠ m in atTop, trunc' R m f = trunc' R m g := by
  refine ⟨fun h => by simp [h, atTop_neBot], fun h => ?_⟩
  ext n
  obtain ⟨m, hm₁, hm₂⟩ := h.forall_exists_of_atTop n
  have {f' : MvPowerSeries σ R} : f'.coeff n = (trunc' R m f').coeff n := by
    rw [coeff_trunc', if_pos hm₁]
  simp [this, hm₂]

end

end TruncLE

section TruncTotal

set_option backward.isDefEq.respectTransparency false

variable {n : ℕ} [Finite σ]

/-- The truncation of a multivariate formal power series at a total degree `n`
when the index `σ` is finite. -/
def truncTotal (R : Type*) [CommSemiring R] (n : ℕ) : MvPowerSeries σ R →ₗ[R] MvPolynomial σ R :=
  truncFinset R (finite_of_degree_lt n).toFinset

theorem coeff_truncTotal [CommSemiring R] (p : MvPowerSeries σ R) {x : σ →₀ ℕ} (h : degree x < n) :
    (truncTotal R n p).coeff x = p.coeff x := coeff_truncFinset_of_mem p (by simpa)

theorem coeff_truncTotal_eq_zero [CommSemiring R] (p : MvPowerSeries σ R) {x : σ →₀ ℕ}
    (h : n ≤ degree x) : (truncTotal R n p).coeff x = 0 := coeff_truncFinset_eq_zero p (by simpa)

lemma truncTotal_one [CommSemiring R] (h : n ≠ 0) : truncTotal R n (1 : MvPowerSeries σ R) = 1 :=
  truncFinset_one (by revert h; contrapose!; simp)

lemma coeff_truncTotal_mul_truncTotal_eq_coeff_mul [CommSemiring R] {x : σ →₀ ℕ}
    (p q : MvPowerSeries σ R) (hx : degree x < n) :
      MvPolynomial.coeff x ((truncTotal R n) p * (truncTotal R n) q) = (coeff x) (p * q) :=
  coeff_truncFinset_mul_truncFinset_eq_coeff_mul (s := (finite_of_degree_lt n).toFinset)
    (fun _ _ h ↦ by simp; grind [degree_mono h]) p q (by simpa)

theorem totalDegree_truncTotal_lt [CommSemiring R] (p : MvPowerSeries σ R) (h : n ≠ 0) :
    (truncTotal R n p).totalDegree < n := by
  apply (totalDegree_truncFinset p).trans_lt
  rw [Finset.sup_lt_iff (by simpa [Nat.pos_iff_ne_zero])]
  simp

variable [CommRing R]

theorem truncTotal_sub_truncTotal_mem_pow_idealOfVars {l m n : ℕ} (h : l ≤ m) (h' : l ≤ n)
    (p : MvPowerSeries σ R) : (truncTotal R m) p - (truncTotal R n) p ∈
      MvPolynomial.idealOfVars σ R ^ l := by
  refine (MvPolynomial.mem_pow_idealOfVars_iff' ..).mpr (fun x hx ↦ ?_)
  rw [MvPolynomial.coeff_sub, sub_eq_zero, coeff_truncTotal _ (by lia),
    coeff_truncTotal _ (by lia)]

theorem truncTotal_mul_sub_mul_truncTotal_mem_pow_idealOfVars (p q : MvPowerSeries σ R) :
    (truncTotal R n) (p * q) - (truncTotal R n) p * (truncTotal R n) q ∈
      MvPolynomial.idealOfVars σ R ^ n := by
  refine (MvPolynomial.mem_pow_idealOfVars_iff' ..).mpr (fun x hx ↦ ?_)
  rw [MvPolynomial.coeff_sub, sub_eq_zero, coeff_truncTotal _ hx,
    coeff_truncTotal_mul_truncTotal_eq_coeff_mul _ _ hx]

/-- The canonical map induced by `truncTotal` from multivariate power series to
the quotient ring of multivariate plynomials at its `n`-th power of
the ideal spanned by all variables. -/
@[simps]
def truncTotalAlgHom (σ R : Type*) [Finite σ] [CommRing R] (n : ℕ) :
    MvPowerSeries σ R →ₐ[MvPolynomial σ R]
      MvPolynomial σ R ⧸ (MvPolynomial.idealOfVars σ R) ^ n where
  toFun p := truncTotal R n p
  map_one' := by
    by_cases! h : n = 0
    · have := Ideal.Quotient.subsingleton_iff.mpr
        (show MvPolynomial.idealOfVars σ R ^ n = ⊤ by simp [h])
      exact Subsingleton.allEq ..
    rw [truncTotal_one h, map_one]
  map_mul' p q := by
    rw [← map_mul, Ideal.Quotient.mk_eq_mk_iff_sub_mem]
    exact truncTotal_mul_sub_mul_truncTotal_mem_pow_idealOfVars p q
  map_zero' := by rw [map_zero, map_zero]
  map_add' _ _ := by simp
  commutes' p := by
    change (Ideal.Quotient.mk (MvPolynomial.idealOfVars σ R ^ n)) (truncTotal R n p) =
      (Ideal.Quotient.mk (MvPolynomial.idealOfVars σ R ^ n)) p
    rw [Ideal.Quotient.eq, MvPolynomial.mem_pow_idealOfVars_iff']
    intro x h
    rw [MvPolynomial.coeff_sub, sub_eq_zero, coeff_truncTotal _ h, MvPolynomial.coeff_coe]

/-- The canonical map from multivariate power series to the adic completion of
multivariate polynomials at the ideal spanned by all variables when the index is finite. -/
def toAdicCompletion (σ R : Type*) [Finite σ] [CommRing R] :
    MvPowerSeries σ R →ₐ[MvPolynomial σ R]
      AdicCompletion (MvPolynomial.idealOfVars σ R) (MvPolynomial σ R) :=
  AdicCompletion.liftAlgHom (MvPolynomial.idealOfVars σ R) (truncTotalAlgHom σ R)
    (fun h ↦ AlgHom.ext fun _ ↦ by
      simpa [Ideal.Quotient.mk_eq_mk_iff_sub_mem] using
        truncTotal_sub_truncTotal_mem_pow_idealOfVars h (le_refl _) _)

lemma toAdicCompletion_apply_eq_mk_truncTotal {n : ℕ} {p : MvPowerSeries σ R} :
    (toAdicCompletion σ R p).val n = truncTotal R n p := by rfl

theorem coeff_toAdicCompletion_val_apply_out {x : σ →₀ ℕ} {p : MvPowerSeries σ R} {n : ℕ}
    (hx : degree x < n) : (Quotient.out (((toAdicCompletion σ R) p).val n)).coeff x =
      (coeff x) p := by
  rw [← coeff_truncTotal _ hx, ← sub_eq_zero, ← MvPolynomial.coeff_sub]
  apply (MvPolynomial.mem_pow_idealOfVars_iff' n _).mp
  · rw [toAdicCompletion_apply_eq_mk_truncTotal, smul_eq_mul]
    nth_rw 1 [← Ideal.mul_top (MvPolynomial.idealOfVars σ R ^ n), ← Ideal.Quotient.eq,
      Ideal.Quotient.mk_out]
  exact hx

theorem toAdicCompletion_coe (p : MvPolynomial σ R) :
    toAdicCompletion σ R p = .of (MvPolynomial.idealOfVars σ R) (MvPolynomial σ R) p := by
  symm; ext n
  suffices p - (truncTotal R n) p ∈ MvPolynomial.idealOfVars σ R ^ n by
    simpa [toAdicCompletion, AdicCompletion.liftAlgHom, AdicCompletion.liftRingHom,
      Ideal.Quotient.mk_eq_mk_iff_sub_mem]
  exact (MvPolynomial.mem_pow_idealOfVars_iff' ..).mpr fun x hx ↦ by simp [coeff_truncTotal _ hx]

/-- An inverse function of `toAdicCompletion`. -/
def toAdicCompletionInv (σ R : Type*) [CommRing R]
    (f : AdicCompletion (MvPolynomial.idealOfVars σ R) (MvPolynomial σ R)) :
      MvPowerSeries σ R := fun x ↦ (f.val (degree x + 1)).out.coeff x

omit [Finite σ] in
lemma coeff_toAdicCompletionInv {x : σ →₀ ℕ}
    {f : AdicCompletion (MvPolynomial.idealOfVars σ R) (MvPolynomial σ R)} :
      coeff x (toAdicCompletionInv σ R f) = (f.val (degree x + 1)).out.coeff x := by rfl

theorem mk_truncTotal_toAdicCompletionInv {n : ℕ}
    {f : AdicCompletion (MvPolynomial.idealOfVars σ R) (MvPolynomial σ R)} :
      Ideal.Quotient.mk (MvPolynomial.idealOfVars σ R ^ n • ⊤)
    ((truncTotal R n) (toAdicCompletionInv σ R f)) = f.val n := by
  rw [← Ideal.Quotient.mk_out (f.val n), Ideal.Quotient.mk_eq_mk_iff_sub_mem]
  simp only [smul_eq_mul, Ideal.mul_top, MvPolynomial.mem_pow_idealOfVars_iff',
    MvPolynomial.coeff_sub]
  intro x h
  rw [coeff_truncTotal _ h, coeff_toAdicCompletionInv, ← MvPolynomial.coeff_sub]
  apply (MvPolynomial.mem_pow_idealOfVars_iff' (degree x + 1) _).mp
  · nth_rw 1 [← Ideal.mul_top (MvPolynomial.idealOfVars σ R ^ (degree x + 1)),
      ← smul_eq_mul, ← Ideal.Quotient.eq]
    simp only [Submodule.mapQ_eq_factor, Submodule.factor_eq_factor, Ideal.Quotient.mk_out]
    rw [← AdicCompletion.transitionMap_ideal_mk _ (Nat.lt_iff_add_one_le.mp h), eq_comm]
    convert f.prop h; simp
  simp

/-- The isomorphism from multivariate power series to the adic completion of
multivariate polynomials at the ideal spanned by all variables when the index is finite. -/
def toAdicCompletionAlgEquiv (σ R : Type*) [Finite σ] [CommRing R] :
    MvPowerSeries σ R ≃ₐ[MvPolynomial σ R]
      AdicCompletion (MvPolynomial.idealOfVars σ R) (MvPolynomial σ R) where
  __ := toAdicCompletion σ R
  invFun := toAdicCompletionInv σ R
  left_inv _ := by
    ext; simp [coeff_toAdicCompletionInv, coeff_toAdicCompletion_val_apply_out]
  right_inv _ := by ext; simpa using mk_truncTotal_toAdicCompletionInv

@[simp]
lemma toAdicCompletionAlgEquiv_apply (p : MvPowerSeries σ R) :
    toAdicCompletionAlgEquiv σ R p = toAdicCompletion σ R p := by rfl

@[simp]
lemma toAdicCompletionAlgEquiv_symm_apply
    (x : AdicCompletion (MvPolynomial.idealOfVars σ R) (MvPolynomial σ R)) :
      (toAdicCompletionAlgEquiv σ R).symm x = toAdicCompletionInv σ R x := by rfl

end TruncTotal

end MvPowerSeries

end
