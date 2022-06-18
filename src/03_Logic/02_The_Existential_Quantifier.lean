import data.real.basic

example : ∃ x : ℝ, 2 < x ∧ x < 3 :=
begin
  use 5 / 2,
  norm_num
end

example : ∃ x : ℝ, 2 < x ∧ x < 3 :=
begin
  have h : 2 < (5 : ℝ) / 2 ∧ (5 : ℝ) / 2 < 3,
    by norm_num,
  exact ⟨5 / 2, h⟩
end

example : ∃ x : ℝ, 2 < x ∧ x < 3 :=
⟨5 / 2, by norm_num⟩

def fn_ub (f : ℝ → ℝ) (a : ℝ) : Prop := ∀ x, f x ≤ a
def fn_lb (f : ℝ → ℝ) (a : ℝ) : Prop := ∀ x, a ≤ f x

def fn_has_ub (f : ℝ → ℝ) := ∃ a, fn_ub f a
def fn_has_lb (f : ℝ → ℝ) := ∃ a, fn_lb f a


theorem fn_ub_add {f g : ℝ → ℝ} {a b : ℝ}
    (hfa : fn_ub f a) (hgb : fn_ub g b) :
  fn_ub (λ x, f x + g x) (a + b) :=
λ x, add_le_add (hfa x) (hgb x)

theorem fn_lb_add {f g: ℝ -> ℝ} { a b : ℝ}
(hfa: fn_lb f a) (hgb: fn_lb g b) :
fn_lb (λ x, f x + g x) (a + b) :=
begin
  intros x,
  dsimp,
  apply add_le_add (hfa x) (hgb x),
end

section
variables {f g : ℝ → ℝ}

example (ubf : fn_has_ub f) (ubg : fn_has_ub g) :
  fn_has_ub (λ x, f x + g x) :=
begin
  cases ubf with a ubfa,
  cases ubg with b ubfb,
  use a + b,
  apply fn_ub_add ubfa ubfb
end

example (lbf : fn_has_lb f) (lbg : fn_has_lb g) :
  fn_has_lb (λ x, f x + g x) :=
begin
  cases lbf with a lbfa,
  cases lbg with b lbgb,
  use a + b,
  apply fn_lb_add lbfa lbgb,
end


example {c : ℝ} (ubf : fn_has_ub f) (h : c ≥ 0):
  fn_has_ub (λ x, c * f x) :=
begin
  
  cases ubf with b ubfb,
  let f' := λ (x: ℝ), c * f x,
  have hubfcb: fn_ub f' (c * b) := 
  begin
    rw fn_ub,
    intro x,
    have hf : f' x = c * (f x ) := by refl,
    rw hf,
    apply mul_le_mul_of_nonneg_left,
    apply ubfb,
    apply h,
  end,
  use (c * b),
  apply hubfcb,
end
-- @ start 

example (ubf : fn_has_ub f) (ubg : fn_has_ub g) :
  fn_has_ub (λ x, f x + g x) :=
begin
  rcases ubf with ⟨a, ubfa⟩,
  rcases ubg with ⟨b, ubfb⟩,
  exact ⟨a + b, fn_ub_add ubfa ubfb⟩
end

example : fn_has_ub f → fn_has_ub g →
  fn_has_ub (λ x, f x + g x) :=
begin
  rintros ⟨a, ubfa⟩ ⟨b, ubfb⟩,
  exact ⟨a + b, fn_ub_add ubfa ubfb⟩
end

example : fn_has_ub f → fn_has_ub g →
  fn_has_ub (λ x, f x + g x) :=
λ ⟨a, ubfa⟩ ⟨b, ubfb⟩, ⟨a + b, fn_ub_add ubfa ubfb⟩

end

section
variables {α : Type*} [comm_ring α]

def sum_of_squares (x : α) := ∃ a b, x = a^2 + b^2

theorem sum_of_squares_mul {x y : α}
    (sosx : sum_of_squares x) (sosy : sum_of_squares y) :
  sum_of_squares (x * y) :=
begin
  rcases sosx with ⟨a, b, xeq⟩,
  rcases sosy with ⟨c, d, yeq⟩,
  rw [xeq, yeq],
  use [a*c - b*d, a*d + b*c],
  ring
end
theorem sum_of_squares_mul' {x y : α}
    (sosx : sum_of_squares x) (sosy : sum_of_squares y) :
  sum_of_squares (x * y) :=
begin
  rcases sosx with ⟨a, b, rfl⟩,
  rcases sosy with ⟨c, d, rfl⟩,
  use [a*c - b*d, a*d + b*c],
  ring
end

end
section
variables {a b c : ℕ}

#check (∣)

example (divab : a ∣ b) (divbc : b ∣ c) : a ∣ c :=
begin
  -- cases divab with d beq,
  -- cases divbc with e ceq,
  -- rw [ceq, beq],
  -- use (d * e), ring
  rcases divab with ⟨d, hdivab, rfl⟩,
  rcases divbc with ⟨e, hdivbc, rfl⟩,
  use (d*e),
  apply mul_assoc,
end

example (divab : a ∣ b) (divac : a ∣ c) : a ∣ (b + c) :=
begin
  cases divab with d hbeq,
  cases divac with e hceq,
  rw [hbeq, hceq],
  rw [←mul_add],
  use (d + e),

end

end

section
open function

example {c : ℝ} : surjective (λ x, x + c) :=
begin
  intro x,
  use x - c,
  dsimp, ring
end

example {c : ℝ} (h : c ≠ 0) : surjective (λ x, c * x) :=
begin
  intros x,
  use (x/c),
  dsimp,
  by calc c * (x/c) = c*x/c : by ring
  ... = (c/c) * x : by ring
  ... = x : by simp [h],
end



example (x y : ℝ) (h : x - y ≠ 0) : (x^2 - y^2) / (x - y) = x + y :=
by { field_simp [h], ring }

example {f : ℝ → ℝ} (h : surjective f) : ∃ x, (f x)^2 = 4 :=
begin
  cases h 2 with x hx,
  use x,
  rw hx,
  norm_num
end

end

section
open function
variables {α : Type*} {β : Type*} {γ : Type*}
variables {g : β → γ} {f : α → β}

example (surjg : surjective g) (surjf : surjective f) :
  surjective (λ x, g (f x)) :=
begin
intros xg,
dsimp,
cases surjg xg with b1 h1,
cases surjf b1 with a1 h2,
use a1,
rw [h2, h1],
end

end
