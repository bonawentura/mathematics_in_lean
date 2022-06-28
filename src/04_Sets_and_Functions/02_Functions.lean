import data.set.lattice
import data.set.function
import data.real.basic
import analysis.special_functions.log.base

section

variables {α β : Type*}
variable  f : α → β
variables s t : set α
variables u v : set β
open function
open set

example : f ⁻¹' (u ∩ v) = f ⁻¹' u ∩ f ⁻¹' v :=
by { ext, refl }

example : f '' (s ∪ t) = f '' s ∪ f '' t :=
begin
  ext y, split,
  { rintros ⟨x, xs | xt, rfl⟩,
    { 
      left, 
      -- have := by use [x, xs],
      have := f '' s,
      use [x, xs], 
    },
    right, use [x, xt] },
  rintros (⟨x, xs, rfl⟩ | ⟨x, xt, rfl⟩),
  { use [x, or.inl xs] },
  use [x, or.inr xt]
end

example : s ⊆ f ⁻¹' (f '' s) :=
begin
  intros x xs,
  show f x ∈ f '' s,
  use [x, xs]
end

-- #check ('') 

example : f '' s ⊆ v ↔ s ⊆ f ⁻¹' v :=
begin
  split,
    rintros h x xs,
    have : f x ∈ f '' s := mem_image_of_mem _ xs,
    have : f x ∈ v := by apply h this,
    apply this,

    rintros h y ys,
    rcases ys with ⟨x, xs, xeq⟩,
    have hx : x ∈ preimage f v := h xs,
    rw [←xeq],
    apply hx,
  
end

example (h : injective f) : f ⁻¹' (f '' s) ⊆ s :=
begin
  intros x hx,
  rcases hx with ⟨x', xs, hx⟩,
  -- have : x' = x := h hx,
  -- rw ←this,
  -- apply xs,
  rwa [←(h hx)],

end

example : f '' (f⁻¹' u) ⊆ u :=
begin
  intros y hx,
  rcases hx with ⟨x, xmem, xeq⟩,
  rwa ←xeq,
end

example (h : surjective f) : u ⊆ f '' (f⁻¹' u) :=
begin
  intros y yu,
  have := h y,

  rcases h y with ⟨x, heq⟩,
  rwa [←heq],
  use x,
  split,
  rw [←heq] at yu,
  apply yu,
  refl,
end

example (h : s ⊆ t) : f '' s ⊆ f '' t :=
begin
  intros y hy,
  rcases hy with ⟨x, xs, xeq⟩,
  rw ←xeq,
  have xt : x ∈ t := h xs,
  use [x, xt],
end

example (h : u ⊆ v) : f ⁻¹' u ⊆ f ⁻¹' v :=
begin
  intros x hx,
  have xu : f x ∈ u := hx,
  simp,
  exact h xu,
end

example : f ⁻¹' (u ∪ v) = f ⁻¹' u ∪ f ⁻¹' v :=
sorry

example : f '' (s ∩ t) ⊆ f '' s ∩ f '' t :=
sorry

example (h : injective f) : f '' s ∩ f '' t ⊆ f '' (s ∩ t) :=
sorry

example : f '' s \ f '' t ⊆ f '' (s \ t) :=
sorry

example : f ⁻¹' u \ f ⁻¹' v ⊆ f ⁻¹' (u \ v) :=
sorry

example : f '' s ∩ v = f '' (s ∩ f ⁻¹' v) :=
sorry

example : f '' (s ∩ f ⁻¹' u) ⊆ f '' s ∪ u :=
sorry

example : s ∩ f ⁻¹' u ⊆ f ⁻¹' (f '' s ∩ u) :=
sorry

example : s ∪ f ⁻¹' u ⊆ f ⁻¹' (f '' s ∪ u) :=
sorry

variables {I : Type*} (A : I → set α) (B : I → set β)

example : f '' (⋃ i, A i) = ⋃ i, f '' A i :=
begin
  ext y, simp,
  split,
  { rintros ⟨x, ⟨i, xAi⟩, fxeq⟩,
    use [i, x, xAi, fxeq] },
  rintros ⟨i, x, xAi, fxeq⟩,
  exact ⟨x, ⟨i, xAi⟩, fxeq⟩
end

example : f '' (⋂ i, A i) ⊆ ⋂ i, f '' A i :=
begin
  intro y, simp,
  intros x h fxeq i,
  use [x, h i, fxeq],
end

example (i : I) (injf : injective f) :
  (⋂ i, f '' A i) ⊆ f '' (⋂ i, A i) :=
begin
  intro y, simp,
  intro h,
  rcases h i with ⟨x, xAi, fxeq⟩,
  use x, split,
  { intro i',
    rcases h i' with ⟨x', x'Ai, fx'eq⟩,
    have : f x = f x', by rw [fxeq, fx'eq],
    have : x = x', from injf this,
    rw this,
    exact x'Ai },
  exact fxeq
end

example : f ⁻¹' (⋃ i, B i) = ⋃ i, f ⁻¹' (B i) :=
by { ext x, simp }

example : f ⁻¹' (⋂ i, B i) = ⋂ i, f ⁻¹' (B i) :=
by { ext x, simp }

end

section
open set real


example : inj_on log { x | x > 0 } :=
begin
  intros x xpos y ypos,
  intro e,   -- log x = log y
  calc
    x   = exp (log x) : by rw exp_log xpos
    ... = exp (log y) : by rw e
    ... = y           : by rw exp_log ypos
end

example : range exp = { y | y > 0 } :=
begin
  ext y, split,
  { rintros ⟨x, rfl⟩,
    apply exp_pos },
  intro ypos,
  use log y,
  rw exp_log ypos
end

example : inj_on sqrt { x | x ≥ 0 } :=
begin
  intros x xnneg y ynneg heq,
  have hx : sqrt x ≥ 0 := sqrt_nonneg x,
  have hy : sqrt y ≥ 0 := sqrt_nonneg y,
  have hsqrteq:= (sq_eq_sq hx hy).mpr heq,
  have hxsq: sqrt x ^ 2 = x := sq_sqrt xnneg,
  have hysq := sq_sqrt ynneg,
  rwa [←hysq, ←hxsq],
end

example : inj_on (λ x, x^2) { x : ℝ | x ≥ 0 } :=
begin
  intros x xnneg y ynneg ,
  dsimp,
  intros h,
  calc 
      x = sqrt (x ^ 2) : by rw sqrt_sq xnneg
    ... = sqrt (y ^ 2) : by rw h
    ... = y : by rw sqrt_sq ynneg,
end

example : sqrt '' { x | x ≥ 0 } = {y | y ≥ 0} :=
begin
  ext x,
  split,
    rintros ⟨u, ⟨unneg, squeq⟩⟩, 
    rw ←squeq,
    apply sqrt_nonneg,

    rintros hx,
    use x^2,
    dsimp at *,
    split,
      apply pow_nonneg hx,
      apply sqrt_sq hx,
end

example : range (λ x, x^2) = {y : ℝ  | y ≥ 0} :=
begin
  ext y,
  dsimp,
  split,
    rintros ⟨x, fxeq⟩,
    dsimp at fxeq,
    rw ←fxeq,
    apply sq_nonneg,

    intros ynneg,
    simp,
    use sqrt y,
    apply sq_sqrt ynneg,
end

end

section
variables {α β : Type*} [inhabited α]

#check (default : α)

variables (P : α → Prop) (h : ∃ x, P x)

#check classical.some h

example : P (classical.some h) := classical.some_spec h

noncomputable theory
open_locale classical

def inverse (f : α → β) : β → α :=
λ y : β, if h : ∃ x, f x = y then classical.some h else default

-- #print inverse

-- def tst (a : ℕ) := (λ x, if x > 1 then x else 1) a

-- #eval tst 0

-- #check tst

theorem inverse_spec {f : α → β} (y : β) (h : ∃ x, f x = y) :
  f (inverse f y) = y :=
begin
  rw inverse, dsimp, rw dif_pos h,
  exact classical.some_spec h
end

variable  f : α → β
open function

#print left_inverse 
#print right_inverse 
#print dite

example : injective f ↔ left_inverse (inverse f) f  :=
begin
  split,
  {
    rintros injf x,
    apply injf,
    apply inverse_spec,
    use x,
  },
  {
    rintros h x1 x2 feq,
    have := h x1,
    rw [←h x1, ←h x2],
    rw feq,
  }
  
  
end

example : surjective f ↔ right_inverse (inverse f) f :=
begin
  split,
  {
    rintros h y,
    cases h y with x e,
    apply inverse_spec,
    use [x, e],
  },
  {
    rintros h y,
    use (inverse f y),
    apply h,
  },


end

end

section
variable {α : Type*}
open function

theorem Cantor : ∀ f : α → set α, ¬ surjective f :=
begin
  intros f surjf,
  let S := { i | i ∉ f i},
  rcases surjf S with ⟨j, h⟩,
  have h₁ : j ∉ f j,
  { intro h',
    have : j ∉ f j,
      { by rwa h at h' },
    contradiction },
  have h₂ : j ∈ S,
    {
      contradiction,
    },
  have h₃ : j ∉ S,
    {
      rw h at h₁,
      contradiction,
    },
  contradiction
end

end
