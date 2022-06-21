import data.real.basic

section
variables {x y : ℝ}

example (h : y > x^2) : y > 0 ∨ y < -1 :=
by { left, linarith [pow_two_nonneg x] }

example (h : -y > x^2 + 1) : y > 0 ∨ y < -1 :=
by { right, linarith [pow_two_nonneg x] }

example (h : y > 0) : y > 0 ∨ y < -1 :=
or.inl h

example (h : y < -1) : y > 0 ∨ y < -1 :=
or.inr h

example : x < abs y → x < y ∨ x < -y :=
begin
  cases le_or_gt 0 y with h h,
  { rw abs_of_nonneg h,
    intro h, left, exact h },
  rw abs_of_neg h,
  intro h, right, exact h
end

namespace my_abs

theorem le_abs_self (x : ℝ) : x ≤ abs x :=
begin
  cases le_or_gt 0 x,
  rw abs_of_nonneg h,

  rw abs_of_neg h,
  linarith, 
end

theorem neg_le_abs_self (x : ℝ) : -x ≤ abs x :=
begin
  cases le_or_gt 0 x,
  rw abs_of_nonneg h,
  linarith,
  rw abs_of_neg h,

end

theorem abs_add (x y : ℝ) : abs (x + y) ≤ abs x + abs y :=
begin
  cases lt_or_ge (x + y) 0,
  rw abs_of_neg h,
  linarith [neg_abs_le_self x, neg_abs_le_self y],
  rw abs_of_nonneg h,
  linarith [le_abs_self x, le_abs_self y],
end

theorem lt_abs : x < abs y ↔ x < y ∨ x < -y :=
begin
  split,
  intros hmp,
    cases lt_or_ge y 0,
      rw [abs_of_neg] at hmp,
      apply or.inr hmp,
      apply h,

      rw abs_of_nonneg at hmp,
      apply or.inl hmp,
      apply h,

  intros hmpr,
    cases hmpr,
      cases lt_or_ge y 0,
        rw abs_of_neg,
        linarith,
        apply h,

        rw abs_of_nonneg,
        apply hmpr,
        apply h,

      cases lt_or_ge y 0,
        rw abs_of_neg,
        apply hmpr,
        apply h,

        rw abs_of_nonneg,
        linarith,
        apply h,
end

theorem abs_lt : abs x < y ↔ - y < x ∧ x < y :=
begin
  split,
  intros hmp,
  {
    cases lt_or_ge x 0,
      { 
        rw [abs_of_neg h] at hmp,
        split,
        linarith,
        linarith,
      },
      {
        rw [abs_of_nonneg h] at hmp,
        split,
        linarith,
        linarith, 
      },
  },
  intros hmpr,
  {
    cases lt_or_ge x 0,
      rw abs_of_neg h,
      linarith,

      rw abs_of_nonneg h,
      linarith,      
  }
end

end my_abs
end

example {x : ℝ} (h : x ≠ 0) : x < 0 ∨ x > 0 :=
begin
  rcases lt_trichotomy x 0 with xlt | xeq | xgt,
  { left, exact xlt },
  { contradiction },
  right, exact xgt
end

example {m n k : ℕ} (h : m ∣ n ∨ m ∣ k) : m ∣ n * k :=
begin
  rcases h with ⟨a, rfl⟩ | ⟨b, rfl⟩,
  { rw [mul_assoc],
    apply dvd_mul_right },
  rw [mul_comm, mul_assoc],
  apply dvd_mul_right
end

example {z : ℝ} (h : ∃ x y, z = x^2 + y^2 ∨ z = x^2 + y^2 + 1) :
  z ≥ 0 :=
begin
  rcases h with ⟨x, y, rfl | rfl⟩; linarith [sq_nonneg x, sq_nonneg y],

end

#check @eq_zero_or_eq_zero_of_mul_eq_zero
#check @no_zero_divisors

example {x : ℝ} (h : x^2 = 1) : x = 1 ∨ x = -1 :=
begin
sorry
end

example {x y : ℝ} (h : x^2 = y^2) : x = y ∨ x = -y :=
sorry

section
variables {R : Type*} [comm_ring R] [is_domain R]
variables (x y : R)

example (h : x^2 = 1) : x = 1 ∨ x = -1 :=
sorry

example (h : x^2 = y^2) : x = y ∨ x = -y :=
sorry

end

example (P : Prop) : ¬ ¬ P → P :=
begin
  intro h,
  cases classical.em P,
  { assumption },
  contradiction
end

section
open_locale classical

example (P : Prop) : ¬ ¬ P → P :=
begin
  intro h,
  by_cases h' : P,
  { assumption },
  contradiction
end

#check @or.elim

example (P Q : Prop) : (P → Q) ↔ ¬ P ∨ Q :=
begin
    split,
      
      intro h,
      by_cases h' : P,
      apply or.inr ( h h' ),
      left,
      apply h',

      rintros (h1 | h2),
      intro h',
      apply absurd h' h1,

      intro h',
      apply h2,

end

end