import data.real.basic
import data.nat.prime
import algebra
set_option trace.linarith true

example {x y : ℝ} (h₀ : x ≤ y) (h₁ : ¬ y ≤ x) : x ≤ y ∧ x ≠ y :=
begin
  split,
  { assumption },
  intro h,
  apply h₁,
  rw h
end

example {x y : ℝ} (h₀ : x ≤ y) (h₁ : ¬ y ≤ x) : x ≤ y ∧ x ≠ y :=
⟨h₀, λ h, h₁ (by rw h)⟩

example {x y : ℝ} (h₀ : x ≤ y) (h₁ : ¬ y ≤ x) : x ≤ y ∧ x ≠ y :=
begin
  have h : x ≠ y,
  { contrapose! h₁,
    rw h₁ },
  exact ⟨h₀, h⟩
end

example {x y : ℝ} (h : x ≤ y ∧ x ≠ y) : ¬ y ≤ x :=
begin
  cases h with h₀ h₁,
  contrapose! h₁,
  exact le_antisymm h₀ h₁
end

example {x y : ℝ} : x ≤ y ∧ x ≠ y → ¬ y ≤ x :=
begin
  rintros ⟨h₀, h₁⟩ h',
  exact h₁ (le_antisymm h₀ h')
end

example {x y : ℝ} : x ≤ y ∧ x ≠ y → ¬ y ≤ x :=
λ ⟨h₀, h₁⟩ h', h₁ (le_antisymm h₀ h')

example {x y : ℝ} (h : x ≤ y ∧ x ≠ y) : ¬ y ≤ x :=
begin
  intro h',
  apply h.right,
  exact le_antisymm h.left h'
end

example {x y : ℝ} (h : x ≤ y ∧ x ≠ y) : ¬ y ≤ x :=
λ h', h.right (le_antisymm h.left h')


example {m n : ℕ} (h : m ∣ n ∧ m ≠ n) :
  m ∣ n ∧ ¬ n ∣ m :=
  ⟨ 
    h.1, 
    λ h2, h.2 $ nat.dvd_antisymm h.1 h2 
  ⟩  
-- begin
--   split,
--   apply h.1,
--   intro h2,
--   apply h.2,
--   apply nat.dvd_antisymm,
--   apply h.1,
--   apply h2,
-- end

example : ∃ x : ℝ, 2 < x ∧ x < 4 :=
⟨5/2, by norm_num, by norm_num⟩

example (x y : ℝ) : (∃ z : ℝ, x < z ∧ z < y) → x < y :=
begin
  rintros ⟨z, xltz, zlty⟩,
  exact lt_trans xltz zlty
  
end

example (x y : ℝ) : (∃ z : ℝ, x < z ∧ z < y) → x < y :=
λ ⟨z, xltz, zlty⟩, lt_trans xltz zlty

example : ∃ x : ℝ, 2 < x ∧ x < 4 :=
begin
  use 5 / 2,
  split; norm_num
end

example : ∃ m n : ℕ,
  4 < m ∧ m < n ∧ n < 10 ∧ nat.prime m ∧ nat.prime n :=
begin
  use [5, 7],
  norm_num
end

example {x y : ℝ} : x ≤ y ∧ x ≠ y → x ≤ y ∧ ¬ y ≤ x :=
begin
  rintros ⟨h₀, h₁⟩,
  use [h₀, λ h', h₁ (le_antisymm h₀ h')]
end

example {x y : ℝ} (h : x ≤ y) : ¬ y ≤ x ↔ x ≠ y :=
begin
  split,
  { contrapose!,
    rintro rfl,
    reflexivity },
  contrapose!,
  exact le_antisymm h
end

example {x y : ℝ} (h : x ≤ y) : ¬ y ≤ x ↔ x ≠ y :=
⟨λ h₀ h₁, h₀ (by rw h₁), λ h₀ h₁, h₀ (le_antisymm h h₁)⟩

#check @le_antisymm_iff


example {x y : ℝ} : x ≤ y ∧ ¬ y ≤ x ↔ x ≤ y ∧ x ≠ y :=
begin
  split,
  rintros ⟨xley, nylex⟩,
    split,
    apply xley,
    nlinarith,
  rintros ⟨xley, xney⟩,
    split,
    assumption,
    by_contra,
    apply xney,
    apply le_antisymm,
    repeat {assumption},
end

#check @add_nonneg

theorem aux {x y : ℝ} (h : x^2 + y^2 = 0) : x = 0 :=
begin
  have h' : x^2 = 0,
  have hx: x^2 >= 0 := by apply pow_two_nonneg,
  have hy: y^2 >= 0 := by apply pow_two_nonneg,
  {
    -- have h1 := by apply add_eq_zero,
    linarith,
    
  },
  exact pow_eq_zero h'
end

example (x y : ℝ) : x^2 + y^2 = 0 ↔ x = 0 ∧ y = 0 :=
begin
  split,
  intro hmp,
    apply and.intro,
    apply aux hmp,
    rw ←add_comm at hmp,
    apply aux hmp,
  intro hmpr,
    nlinarith,
end

section
open nat

example (x y : ℝ) : abs (x + 3) < 5 → -8 < x ∧ x < 2 :=
begin
  rw abs_lt,
  intro h,
  split; linarith
end

example : 3 ∣ gcd 6 15 :=
begin
  rw dvd_gcd_iff,
  split; norm_num
end

end

theorem not_monotone_iff {f : ℝ → ℝ}:
  ¬ monotone f ↔ ∃ x y, x ≤ y ∧ f x > f y :=
by { rw monotone, push_neg }

example : ¬ monotone (λ x : ℝ, -x) :=
begin
  -- intro hmx,
  -- rw monotone at hmx,
  rw not_monotone_iff,
  use [1,2],
  norm_num,
end

section
variables {α : Type*} [partial_order α]
variables a b : α


example : a < b ↔ a ≤ b ∧ a ≠ b :=
begin
  rw lt_iff_le_not_le,
  split,
  rintros ⟨aleb, nblea⟩,
    apply and.intro aleb,
    intro hneq,
    apply nblea,
    apply le_of_eq,
    rw eq_comm,
    apply hneq,
  rintros ⟨aleb, neqab⟩,
    apply and.intro aleb,
    intro hblea,
    apply neqab,
    apply le_antisymm aleb hblea,
end

end

section
variables {α : Type*} [preorder α]
variables a b c : α

example : ¬ a < a :=
begin
  rw lt_iff_le_not_le,
  rintros ⟨alea,nalea⟩,
  apply nalea alea,
end

example : a < b → b < c → a < c :=
begin
  simp only [lt_iff_le_not_le],
  rintros ⟨aleb, nblea⟩,
  rintros ⟨ blec, ncleb⟩,
  split,
  apply le_trans aleb blec,
  intro hclea,
  apply ncleb,
  apply le_trans hclea aleb,
end

end
