import data.real.basic
import algebra.order.with_zero
import algebra.order.monoid

set_option trace.linarith true

section
variables a b : ℝ

example (h : a < b) : ¬ b < a :=
begin
  intro h',
  have : a < a,
    from lt_trans h h',
  apply lt_irrefl a this
end

def fn_ub (f : ℝ → ℝ) (a : ℝ) : Prop := ∀ x, f x ≤ a
def fn_lb (f : ℝ → ℝ) (a : ℝ) : Prop := ∀ x, a ≤ f x

def fn_has_ub (f : ℝ → ℝ) := ∃ a, fn_ub f a
def fn_has_lb (f : ℝ → ℝ) := ∃ a, fn_lb f a

variable f : ℝ → ℝ

example (h : ∀ a, ∃ x, f x > a) : ¬ fn_has_ub f :=
begin
  intros fnub,
  cases fnub with a fnuba,
  cases h a with x hx,
  have : f x ≤ a,
    from fnuba x,
  linarith
end

example (h : ∀ a, ∃ x, f x < a) : ¬ fn_has_lb f :=
begin
  intros hlbf,
  cases hlbf with a' ha',
  cases h a' with a'' ha'',
  have : a' <= f a'', from ha' a'',
  linarith,

end

example : ¬ fn_has_ub (λ x, x) :=
begin
  intros h,
  cases h with x' hub,
  rw [fn_ub] at hub,
  have : x' + 1 <= x', from hub (x' + 1),
  linarith,

end

#check (not_le_of_gt : a > b → ¬ a ≤ b)
#check (not_lt_of_ge : a ≥ b → ¬ a < b)
#check (lt_of_not_ge : ¬ a ≥ b → a < b)
#check (le_of_not_gt : ¬ a > b → a ≤ b)

example (h : monotone f) (h' : f a < f b) : a < b :=
begin
  apply lt_of_not_ge,
  intro h2,
  apply absurd h',

  apply not_lt_of_ge,
  apply h h2,

end

example (h : a ≤ b) (h' : f b < f a) : ¬ monotone f :=
begin
  intros hmf,
  apply absurd h',
  apply not_lt_of_ge,
  apply hmf h,
end

-- #check (<=)
-- #set_option trace.linarith true


example :
  ¬ ∀ {f : ℝ → ℝ}, monotone f → ∀ {a b}, f a ≤ f b → a ≤ b :=
begin
  intro h,
  let f := λ x : ℝ, (0 : ℝ),
  have monof : monotone f,
  { 
    rw monotone,
    intros a' b' hab',
    have hfa0 : f a' = 0 := rfl,
    have hfb0 : f b' = 0 := rfl,
    rw [hfa0],
  },
  have h' : f 1 ≤ f 0,
    from le_refl _,
  have h1: (1: ℝ ) <= 0 := h monof h',
  -- linarith,
  -- rw [le_zero_iff 1] at h1,
  -- rw [] at h1,
  -- rw [ le_iff_exists_add ] at h1
  -- apply 
  -- apply absurd h1,
  -- apply not_le_of_gt h1,
  linarith,
  
  -- apply (not_le 1 0).2,
  -- todo: try step by step
end

example (x : ℝ) (h : ∀ ε > 0, x < ε) : x ≤ 0 :=
begin 
  apply le_of_not_gt,
  intro h1,
  -- apply absurd h1,
  let hx := h _ h1,
  -- linarith [h _ h1]
  apply lt_irrefl x,
  apply hx,
  

end

end
-- @end


section
variables {α : Type*} (P : α → Prop) (Q : Prop)

example (h : ¬ ∃ x, P x) : ∀ x, ¬ P x :=
begin
  intros a hp,
  apply h,
  use a,
  apply hp,
end

example (h : ∀ x, ¬ P x) : ¬ ∃ x, P x :=
begin
  intros hpx,
  cases hpx with a ha,
  apply h a,
  apply ha,
end

#check @exists.elim

example (h : ¬ ∀ x, P x) : ∃ x, ¬ P x :=
begin 
    sorry
    
end

example (h : ∃ x, ¬ P x) : ¬ ∀ x, P x :=
begin 
  intros ha,
  cases h with a' hpa,
  apply hpa,
  apply ha a',
end

open_locale classical

example (h : ¬ ∀ x, P x) : ∃ x, ¬ P x :=
begin
  by_contradiction h',
  apply h,
  intro x,
  show P x,
  by_contradiction h'',
  exact h' ⟨x, h''⟩
end

example (h : ¬ ¬ Q) : Q :=
begin
  by_contra h',
  apply h,
  apply h',
end

example (h : Q) : ¬ ¬ Q :=
begin
  -- by_contra h',
  -- apply h',
  -- apply h,
  rw not_not,
  apply h,
end

end

open_locale classical
section
variable (f : ℝ → ℝ)

example (h : ¬ fn_has_ub f) : ∀ a, ∃ x, f x > a :=
begin
  intros a,
  by_contra h',
  apply h,
  -- rw [fn_has_ub],
  use a,
  intro x,
  apply le_of_not_gt,
  intro h'',
  apply h',
  use x,
  apply h'',
end

example (h : ¬ ∀ a, ∃ x, f x > a) : fn_has_ub f :=
begin
  push_neg at h,
  exact h
end

example (h : ¬ fn_has_ub f) : ∀ a, ∃ x, f x > a :=
begin
  simp only [fn_has_ub, fn_ub] at h,
  push_neg at h,
  exact h
end

example (h : ¬ monotone f) : ∃ x y, x ≤ y ∧ f y < f x :=
begin
  simp only [monotone] at h,
  push_neg at h,
  apply h,
end

example (h : ¬ fn_has_ub f) : ∀ a, ∃ x, f x > a :=
begin
  contrapose! h,
  exact h
end

example (x : ℝ) (h : ∀ ε > 0, x ≤ ε) : x ≤ 0 :=
begin
  contrapose! h,
  use x / 2,
  split; linarith
end

end

section
variable a : ℕ

example (h : 0 < 0) : a > 37 :=
begin
  exfalso,
  apply lt_irrefl 0 h
end

example (h : 0 < 0) : a > 37 :=
absurd h (lt_irrefl 0)

example (h : 0 < 0) : a > 37 :=
begin
  have h' : ¬ 0 < 0,
    from lt_irrefl 0,
  contradiction
end

end

