import data.set.lattice
import data.nat.parity
import tactic

section
variable {α : Type*}
variables (s t u : set α)

open set

example (h : s ⊆ t) : s ∩ u ⊆ t ∩ u :=
begin
  rw [subset_def, inter_def, inter_def],
  rw subset_def at h,
  dsimp,
  rintros x ⟨xs, xu⟩,
  exact ⟨h _ xs, xu⟩,
end

example (h : s ⊆ t) : s ∩ u ⊆ t ∩ u :=
begin
  simp only [subset_def, mem_inter_eq] at *,
  rintros x ⟨xs, xu⟩,
  exact ⟨h _ xs, xu⟩,
end

example (h : s ⊆ t) : s ∩ u ⊆ t ∩ u :=
begin
  intros x xsu,
  exact ⟨h xsu.1, xsu.2⟩
end

theorem foo (h : s ⊆ t) : s ∩ u ⊆ t ∩ u :=
λ x ⟨xs, xu⟩, ⟨h xs, xu⟩

example (h : s ⊆ t) : s ∩ u ⊆ t ∩ u :=
by exact λ x ⟨xs, xu⟩, ⟨h xs, xu⟩

example : s ∩ (t ∪ u) ⊆ (s ∩ t) ∪ (s ∩ u) :=
begin
  intros x hx,
  have xs : x ∈ s := hx.1,
  have xtu : x ∈ t ∪ u := hx.2,
  cases xtu with xt xu,
  { left,
    show x ∈ s ∩ t,
    exact ⟨xs, xt⟩ },
  right,
  show x ∈ s ∩ u,
  exact ⟨xs, xu⟩
end

example : s ∩ (t ∪ u) ⊆ (s ∩ t) ∪ (s ∩ u) :=
begin
  rintros x ⟨xs, xt | xu⟩,
  { left, exact ⟨xs, xt⟩ },
  right, exact ⟨xs, xu⟩
end

example : (s ∩ t) ∪ (s ∩ u) ⊆ s ∩ (t ∪ u):=
begin
  rintros x ⟨xs, xt⟩,
  dsimp,
  apply and.intro xs (or.inl xt),
  have l : x ∈ s := by finish, 
  have r : x ∈ u := by finish,
  dsimp,
  exact ⟨l, or.inr r⟩,
end

example : s \ t \ u ⊆ s \ (t ∪ u) :=
begin
  intros x xstu,
  have xs : x ∈ s := xstu.1.1,
  have xnt : x ∉ t := xstu.1.2,
  have xnu : x ∉ u := xstu.2,
  split,
  { exact xs }, dsimp,
  intro xtu, -- x ∈ t ∨ x ∈ u
  cases xtu with xt xu,
  { show false, from xnt xt },
  show false, from xnu xu
end

example : s \ t \ u ⊆ s \ (t ∪ u) :=
begin
  rintros x ⟨⟨xs, xnt⟩, xnu⟩,
  use xs,
  rintros (xt | xu); contradiction
end

example : s \ (t ∪ u) ⊆ s \ t \ u :=
begin
  rintros x ⟨xs, xtu⟩,
  use xs,
  dsimp at xtu,
  intro h,
  apply xtu,
  apply or.inl h,
  intro h,
  apply xtu,
  apply or.inr h,
end

example : s ∩ t = t ∩ s :=
begin
  ext x,
  simp only [mem_inter_eq],
  split,
  { rintros ⟨xs, xt⟩, exact ⟨xt, xs⟩ },
  rintros ⟨xt, xs⟩, exact ⟨xs, xt⟩
end

example : s ∩ t = t ∩ s :=
set.ext $ λ x, ⟨λ ⟨xs, xt⟩, ⟨xt, xs⟩, λ ⟨xt, xs⟩, ⟨xs, xt⟩⟩

example : s ∩ t = t ∩ s :=
by ext x; simp [and.comm]

example : s ∩ t = t ∩ s :=
begin
  apply subset.antisymm,
  { rintros x ⟨xs, xt⟩, exact ⟨xt, xs⟩ },
  rintros x ⟨xt, xs⟩, exact ⟨xs, xt⟩
end

example : s ∩ t = t ∩ s :=
subset.antisymm (λx, λ ⟨xs, xt⟩, ⟨xt, xs⟩) (λx, λ⟨xt, xs⟩, ⟨xs, xt⟩)

example : s ∩ (s ∪ t) = s :=
subset.antisymm (λx, λ⟨xs,xst⟩, xs) (λx, λxs, ⟨xs, or.inl xs⟩)

example : s ∪ (s ∩ t) = s :=
begin
  ext x,
  split,
  rintros (xs | ⟨xs, xt⟩),
  exact xs, exact xs,
  intro xs,
  left, apply xs,
end

example : (s \ t) ∪ t = s ∪ t :=
begin
  ext x,
  split,
  rintros (⟨xs, xnt⟩ | xt),
  left, apply xs,
  right, apply xt,
  rintros (xs|xt),
  dsimp,
  cases em (x ∈ t) with xt xnt,
  right, apply xt,
  left, exact ⟨xs, xnt⟩,
  right, exact xt,
end

example : (s \ t) ∪ (t \ s) = (s ∪ t) \ (s ∩ t) :=
begin
  ext x,
  split,
    rintros (⟨xs, xnt⟩ | ⟨xt, xns⟩),
    apply and.intro,
    apply or.inl xs,
    intro xnst,
    apply xnt,
    apply xnst.2,
    apply and.intro,
    apply or.inr xt,
    intro xnst,
    apply xns,
    apply xnst.1,

    rintros ⟨(xs | xt), xnst⟩,
    have xnt : x ∉ t := by begin 
      intro xnt,
      apply xnst,
      exact ⟨xs, xnt⟩,
    end,
    left, exact ⟨xs, xnt⟩,
    right,
    apply and.intro xt,
    intro xs,
    apply xnst,
    exact ⟨xs, xt⟩,
    
end


def evens : set ℕ := {n | even n}
def odds :  set ℕ := {n | ¬ even n}

example : evens ∪ odds = univ :=
begin
  rw [evens, odds],
  ext n,
  simp,
  apply classical.em
end

example (x : ℕ) (h : x ∈ (∅ : set ℕ)) : false :=
h

example (x : ℕ) : x ∈ (univ : set ℕ) :=
trivial

#check @nat.prime.eq_two_or_odd
#check @nat.even_iff

example : { n | nat.prime n } ∩ { n | n > 2} ⊆ { n | ¬ even n } :=
begin
  intro n,
  simp,
  intros nprime,

  cases nat.prime.eq_two_or_odd nprime with h h,

  intros ngt2 neven,
  linarith,

  intros ngt2 neven,
  rw [nat.even_iff] at neven,
  linarith,
  
end

#print prime
#print nat.prime

example (n : ℕ) : prime n ↔ nat.prime n := nat.prime_iff.symm

example (n : ℕ) (h : prime n) : nat.prime n :=
by { rw nat.prime_iff, exact h }

example (n : ℕ) (h : prime n) : nat.prime n :=
by rwa nat.prime_iff

end
section
variables (s t : set ℕ)

example (h₀ : ∀ x ∈ s, ¬ even x) (h₁ : ∀ x ∈ s, prime x) :
  ∀ x ∈ s, ¬ even x ∧ prime x :=
begin
  intros x xs,
  split,
  { apply h₀ x xs },
  apply h₁ x xs
end

example (h : ∃ x ∈ s, ¬ even x ∧ prime x) :
  ∃ x ∈ s, prime x :=
begin
  rcases h with ⟨x, xs, _, prime_x⟩,
  use [x, xs, prime_x]
end

section
variable (ssubt : s ⊆ t)

include ssubt

example (h₀ : ∀ x ∈ t, ¬ even x) (h₁ : ∀ x ∈ t, prime x) :
  ∀ x ∈ s, ¬ even x ∧ prime x :=
begin
  rintros (n ns),
  have nt : n ∈ t := ssubt ns,
  exact ⟨h₀ n nt, h₁ n nt⟩,
end

example (h : ∃ x ∈ s, ¬ even x ∧ prime x) :
  ∃ x ∈ t, prime x :=
begin
  rcases h with ⟨n, ns, ⟨nneven,nprime⟩⟩,
  have nt : n ∈ t := ssubt ns,
  use [n, nt, nprime],
end

end

end

section
variables {α I : Type*}
variables A B : I → set α
variable  s : set α
open set

example : s ∩ (⋃ i, A i) = ⋃ i, (A i ∩ s) :=
begin
  ext x,
  simp only [mem_inter_eq, mem_Union],
  split,
  { rintros ⟨xs, ⟨i, xAi⟩⟩,
    exact ⟨i, xAi, xs⟩ },
  rintros ⟨i, xAi, xs⟩,
  exact ⟨xs, ⟨i, xAi⟩⟩
end

example : (⋂ i, A i ∩ B i) = (⋂ i, A i) ∩ (⋂ i, B i) :=
begin
  ext x,
  simp only [mem_inter_eq, mem_Inter],
  split,
  { intro h,
    split,
    { intro i,
      exact (h i).1 },
    intro i,
    exact (h i).2 },
  rintros ⟨h1, h2⟩ i,
  split,
  { exact h1 i },
  exact h2 i
end

open_locale classical

example : s ∪ (⋂ i, A i) = ⋂ i, (A i ∪ s) :=
begin
  ext x,
  split,
    rintros (xs | xAi),
      simp,
      intro i,
      right, apply xs,

      simp,
      intro i,
      left,
      simp at xAi,
      apply xAi i,

    simp,
    rintros h,
    cases em (x ∈ s) with xs xns,
      apply or.inl xs,

      right,
      intro i,
      have h' := h i,
      apply or_iff_not_imp_right.mp h' xns,

end

def primes : set ℕ := {x | nat.prime x}

example : (⋃ p ∈ primes, {x | p^2 ∣ x}) = {x | ∃ p ∈ primes, p^2 ∣ x} :=
by { ext, rw mem_Union₂, refl }

example : (⋃ p ∈ primes, {x | p^2 ∣ x}) = {x | ∃ p ∈ primes, p^2 ∣ x} :=
by { ext, simp }

example : (⋂ p ∈ primes, {x | ¬ p ∣ x}) ⊆ {x | x < 2} :=
begin
  intro x,
  contrapose!,
  intros hxgt2 nxprime,
  simp at hxgt2,
  simp at nxprime,
  sorry
end

#check @nat.exists_infinite_primes

example : (⋃ p ∈ primes, {x | x ≤ p}) = univ :=
begin
  rw eq_univ_iff_forall,
  intro n,
  simp,
  have hn' := nat.exists_infinite_primes n,
  cases hn' with n' h',

  use n',
  exact ⟨h'.2, h'.1⟩,

end

end

section
open set

variables {α : Type*} (s : set (set α))

example : ⋃₀ s = ⋃ t ∈ s, t :=
begin
  ext x,
  rw mem_Union₂,
  refl
end

example : ⋂₀ s = ⋂ t ∈ s, t :=
begin
  ext x,
  rw mem_Inter₂,
  refl
end

end

