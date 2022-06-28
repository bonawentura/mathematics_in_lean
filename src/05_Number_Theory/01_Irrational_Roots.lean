import data.nat.gcd
import data.real.irrational

#print nat.coprime

example (m n : nat) (h : m.coprime n) : m.gcd n = 1 := h

example (m n : nat) (h : m.coprime n) : m.gcd n = 1 :=
by { rw nat.coprime at h, exact h }

example : nat.coprime 12 7 := by norm_num
example : nat.gcd 12 8 = 4 := by norm_num

#check @nat.prime_def_lt

example (p : ℕ) (prime_p : nat.prime p) : 2 ≤ p ∧ ∀ (m : ℕ), m < p → m ∣ p → m = 1 :=
by rwa nat.prime_def_lt at prime_p

#check nat.prime.eq_one_or_self_of_dvd

example (p : ℕ) (prime_p : nat.prime p) : ∀ (m : ℕ), m ∣ p → m = 1 ∨ m = p :=
prime_p.eq_one_or_self_of_dvd

example : nat.prime 17 := by norm_num

-- commonly used
example : nat.prime 2 := nat.prime_two
example : nat.prime 3 := nat.prime_three

#check @nat.prime.dvd_mul
#check nat.prime.dvd_mul nat.prime_two
#check nat.prime_two.dvd_mul

lemma even_of_even_sqr {m : ℕ} (h : 2 ∣ m^2) : 2 ∣ m :=
begin
  rw [pow_two, nat.prime_two.dvd_mul] at h,
  cases h; assumption
end

example {m : ℕ} (h : 2 ∣ m^2) : 2 ∣ m :=
nat.prime.dvd_of_dvd_pow nat.prime_two h

example (a b c : nat) (h : a * b = a * c) (h' : a ≠ 0) :
  b = c :=
begin
  -- library_search suggests the following:
  exact (mul_right_inj' h').mp h
end

example {m n : ℕ} (coprime_mn : m.coprime n) : m^2 ≠ 2 * n^2 :=
begin
  intro sqr_eq,
  have : 2 ∣ m,
    {
      apply even_of_even_sqr,
      rw sqr_eq,
      apply nat.dvd_mul_right
    },
  obtain ⟨k, meq⟩ := dvd_iff_exists_eq_mul_left.mp this,
  have : 2 * (2 * k^2) = 2 * n^2,
  { rw [←sqr_eq, meq], ring },
  have : 2 * k^2 = n^2,
    by linarith,
  have : 2 ∣ n,
    {
      apply even_of_even_sqr,
      rw ←this,
      apply nat.dvd_mul_right,
    },
  have : 2 ∣ m.gcd n,
    {
      obtain ⟨l, neq⟩ := dvd_iff_exists_eq_mul_left.mp this,
      rw [meq, neq, nat.gcd_mul_right],
      exact dvd_mul_left 2 _,
    },
  have : 2 ∣ 1,
    {
     convert this,
     symmetry,
     exact coprime_mn,
    },
  norm_num at this,
end

example {m n p : ℕ} (coprime_mn : m.coprime n) (prime_p : p.prime) : m^2 ≠ p * n^2 :=
    sorry

#check nat.factors
#check nat.prime_of_mem_factors
#check nat.prod_factors
#check nat.factors_unique

-- #check nat.count_factors_mul_of_pos
-- #check @nat.factors_count_pow
#check @nat.factors_prime

-- example (m n p : ℕ) (mpos : 0 < m) (npos : 0 < n) :
--   (m * n).factors.count p = m.factors.count p + n.factors.count p :=
-- nat.count_factors_mul_of_pos mpos npos

-- example (n k p : ℕ) : (n^k).factors.count p = k * n.factors.count p :=
-- nat.factors_count_pow

example (p : ℕ) (prime_p : p.prime) : p.factors.count p = 1 :=
begin
  rw nat.factors_prime prime_p,
  simp
end

example {m n p : ℕ} (nnz : n ≠ 0) (prime_p : p.prime) : m^2 ≠ p * n^2 :=
begin
  intro sqr_eq,
  have nsqr_nez : n^2 ≠ 0,
    by simpa,
  have eq1 : (m^2).factors.count p = 2 * m.factors.count p,
    sorry,
  have eq2 : (p * n^2).factors.count p = 2 * n.factors.count p + 1,
    sorry,
  have : (2 * m.factors.count p) % 2 = (2 * n.factors.count p + 1) % 2,
  { rw [←eq1, sqr_eq, eq2] },
  rw [add_comm, nat.add_mul_mod_self_left, nat.mul_mod_right] at this,
  norm_num at this
end

example {m n k r : ℕ} (nnz : n ≠ 0) (pow_eq : m^k = r * n^k) :
  ∀ p : ℕ, p.prime → k ∣ r.factors.count p :=
begin
  intros p prime_p,
  cases r with r,
  { simp },
  have npow_nz : n^k ≠ 0 := λ npowz, nnz (pow_eq_zero npowz),
  have eq1 : (m^k).factors.count p = k * m.factors.count p,
    sorry,
  have eq2 : (r.succ * n^k).factors.count p =
      k * n.factors.count p + r.succ.factors.count p,
    sorry,
  have : r.succ.factors.count p = k * m.factors.count p - k * n.factors.count p,
  { rw [←eq1, pow_eq, eq2, add_comm, nat.add_sub_cancel] },
  rw this,
  sorry
end

#check multiplicity
#check @irrational_nrt_of_n_not_dvd_multiplicity
#check irrational_sqrt_two

