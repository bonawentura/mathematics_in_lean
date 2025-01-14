import algebra.big_operators.ring
import data.real.basic

@[ext] structure point := (x : ℝ) (y : ℝ) (z : ℝ)

#check point.ext

example (a b : point) (hx : a.x = b.x) (hy : a.y = b.y) (hz : a.z = b.z) :
  a = b :=
begin
  ext,
  repeat { assumption }
end

def my_point1 : point :=
{ x := 2,
  y := -1,
  z := 4 }

def my_point2 :=
{ point .
  x := 2,
  y := -1,
  z := 4 }

def my_point3 : point := ⟨2, -1, 4⟩

def my_point4 := point.mk 2 (-1) 4

structure point' := build :: (x : ℝ) (y : ℝ) (z : ℝ)

#check point'.build 2 (-1) 4

namespace point

def add (a b : point) : point := ⟨a.x + b.x, a.y + b.y, a.z + b.z⟩

def add' (a b : point) : point :=
{ x := a.x + b.x,
  y := a.y + b.y,
  z := a.z + b.z }

#check add my_point1 my_point2
#check my_point1.add my_point2

end point

#check point.add my_point1 my_point2
#check my_point1.add my_point2

namespace point

protected theorem add_comm (a b : point) : add a b = add b a :=
begin
  rw [add, add],
  ext; dsimp,
  repeat { apply add_comm }
end

example (a b : point) : add a b = add b a :=
by simp [add, add_comm]

theorem add_x (a b : point) : (a.add b).x = a.x + b.x := rfl

def add_alt : point → point → point
| (point.mk x₁ y₁ z₁) (point.mk x₂ y₂ z₂) := ⟨x₁ + x₂, y₁ + y₂, z₁ + z₂⟩

def add_alt' : point → point → point
| ⟨x₁, y₁, z₁⟩ ⟨x₂, y₂, z₂⟩ := ⟨x₁ + x₂, y₁ + y₂, z₁ + z₂⟩

theorem add_alt_x (a b : point) : (a.add_alt b).x = a.x + b.x :=
by { cases a, cases b, refl }

theorem add_alt_comm (a b : point) : add_alt a b = add_alt b a :=
begin
  rcases a with ⟨xa, ya, za⟩,
  rcases b with ⟨xb, yb, zb⟩,
  rw [add_alt, add_alt],
  ext; dsimp,
  apply add_comm,
  repeat { apply add_comm },
end

example (a b : point) : add_alt a b = add_alt b a :=
begin
  rcases a with ⟨xa, ya, za⟩,
  rcases b with ⟨xb, yb, zb⟩,
  simp [add_alt, add_comm]
end

example : ∀ a b : point, add_alt a b = add_alt b a :=
begin
  rintros ⟨xa, ya, za⟩ ⟨xb, yb, zb⟩,
  simp [add_alt, add_comm]
end

example : ∀ a b : point, add a b = add b a :=
λ ⟨xa, ya, za⟩ ⟨xb, yb, zb⟩, by simp [add, add_comm]

protected theorem add_assoc (a b c : point) :
  (a.add b).add c = a.add (b.add c) :=
begin
  set p1 := (a.add b).add c,
  set p2 := a.add (b.add c),
  ext,
  repeat {  simp [p1, p2, add, add_comm, add_assoc] },

end

def smul (r : ℝ) (a : point) : point := ⟨ r * a.x, r * a.y, r * a.z ⟩ 


theorem smul_distrib (r : ℝ) (a b : point) :
  (smul r a).add (smul r b) = smul r (a.add b) :=
begin
  simp [add, smul, mul_add],
end

end point

structure standard_two_simplex :=
(x : ℝ)
(y : ℝ)
(z : ℝ)
(x_nonneg : 0 ≤ x)
(y_nonneg : 0 ≤ y)
(z_nonneg : 0 ≤ z)
(sum_eq   : x + y + z = 1)

namespace standard_two_simplex

def swap_xy (a : standard_two_simplex) : standard_two_simplex :=
{ x := a.y,
  y := a.x,
  z := a.z,
  x_nonneg := a.y_nonneg,
  y_nonneg := a.x_nonneg,
  z_nonneg := a.z_nonneg,
  sum_eq   := by rw [add_comm a.y a.x, a.sum_eq] }

noncomputable theory

def midpoint (a b : standard_two_simplex) : standard_two_simplex :=
{ x        := (a.x + b.x) / 2,
  y        := (a.y + b.y) / 2,
  z        := (a.z + b.z) / 2,
  x_nonneg := div_nonneg (add_nonneg a.x_nonneg b.x_nonneg) (by norm_num),
  y_nonneg := div_nonneg (add_nonneg a.y_nonneg b.y_nonneg) (by norm_num),
  z_nonneg := div_nonneg (add_nonneg a.z_nonneg b.z_nonneg) (by norm_num),
  sum_eq   := by { field_simp, linarith [a.sum_eq, b.sum_eq]} }


#check @sub_nonneg

def weighted_average (lambda : real)
    (lambda_nonneg : 0 ≤ lambda) (lambda_le : lambda ≤ 1)
    (a b : standard_two_simplex) :
  standard_two_simplex :=
{
  x := lambda * a.x + (1 - lambda) * b.x,
  y := lambda * a.y + (1 - lambda) * b.y,
  z := lambda * a.z + (1 - lambda) * b.z,
  x_nonneg := begin
    have hx1 : 1 - lambda >= 0 := by simp [lambda_le],
    have ha : lambda * a.x >= 0 := by simp [lambda_nonneg, a.x_nonneg, mul_nonneg],
    have hb : (1 - lambda) * b.x >= 0 := mul_nonneg hx1 b.x_nonneg,
    exact add_nonneg ha hb,
  end,
  y_nonneg := add_nonneg (mul_nonneg lambda_nonneg a.y_nonneg) (mul_nonneg (sub_nonneg.mpr lambda_le) b.y_nonneg),
  z_nonneg := by simp [lambda_nonneg, a.z_nonneg, b.z_nonneg, lambda_le, mul_nonneg, add_nonneg, sub_nonneg],
  sum_eq := begin
    simp [sub_mul, ←add_sub_assoc, ←add_assoc],
    calc 
      lambda * a.x + b.x - lambda * b.x + lambda * a.y + b.y - lambda * b.y + lambda * a.z + b.z - lambda * b.z = lambda * (a.x - b.x + a.y - b.y + a.z - b.z) + b.x + b.y + b.z : by simp
      ... = lambda * ( 1 - 1) + 1 : by simp [a.sum_eq, b.sum_eq]
      ... = lambda * 0 + 1 : by linarith
      ... = 1 : by linarith
  end
}

end standard_two_simplex

open_locale big_operators

structure standard_simplex (n : ℕ) :=
(v          : fin n → ℝ)
(nonneg     : ∀ i : fin n, 0 ≤ v i)
(sum_eq_one : ∑ i, v i = 1)

namespace standard_simplex

def midpoint (n : ℕ) (a b : standard_simplex n) : standard_simplex n :=
{ v := λ i, (a.v i + b.v i) / 2,
  nonneg :=
    begin
      intro i,
      apply div_nonneg,
      { linarith [a.nonneg i, b.nonneg i] },
      norm_num
    end,
  sum_eq_one :=
    begin
      simp [div_eq_mul_inv, ←finset.sum_mul, finset.sum_add_distrib,
        a.sum_eq_one, b.sum_eq_one],
      field_simp
    end  }

end standard_simplex

structure is_linear (f : ℝ → ℝ) :=
(is_additive : ∀ x y, f (x + y) = f x + f y)
(preserves_mul : ∀ x c, f (c * x) = c * f x)

section
variables (f : ℝ → ℝ) (linf : is_linear f)

#check linf.is_additive
#check linf.preserves_mul

end

def point'' := ℝ × ℝ × ℝ

def is_linear' (f : ℝ → ℝ) :=
(∀ x y, f (x + y) = f x + f y) ∧ (∀ x c, f (c * x) = c * f x)

def preal := { y : ℝ // 0 < y }

section
variable x : preal

#check x.val
#check x.property

#check x.1
#check x.2

end

def standard_two_simplex' :=
{ p : ℝ × ℝ × ℝ // 0 ≤ p.1 ∧ 0 ≤ p.2.1 ∧ 0 ≤ p.2.2 ∧ p.1 + p.2.1 + p.2.2 = 1 }

def standard_simplex' (n : ℕ) :=
{ v : fin n → ℝ // (∀ i : fin n, 0 ≤ v i) ∧ (∑ i, v i = 1) }

def std_simplex := Σ n : ℕ, standard_simplex n

variable g : standard_two_simplex'
#check g.val
#check g.property

section
variable s : std_simplex

#check s.fst
#check s.snd

#check s.1
#check s.2

end


