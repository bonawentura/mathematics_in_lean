import tactic
import data.list.basic
import data.nat.basic
import algebra.order.floor

section sorting

inductive sorted : list ℕ -> Prop 
| nil                     : sorted []
| single {x: ℕ}           : sorted [x]
| two_or_more   { x y : ℕ} {zs : list ℕ} 
                (hle: x <= y) (hsorted : sorted (y :: zs)) 
                          : sorted (x :: y :: zs)
  

example : sorted [1,2,3] := begin
  apply sorted.two_or_more,
  linarith,
  apply sorted.two_or_more,
  linarith,
  apply sorted.single,

end


example : [1,2,3] ~ [2,1,3] := 
begin 
  apply list.perm.swap,
end



structure heap (len : ℕ) (size : ℕ) := 
( items : list ℕ )
( length := items.length)
-- ( parent := λ(i :ℕ ), ⌊ i / 2 ⌋₊ )
( left   := λ(i :ℕ ), 2 * i)
( right  := λ(i :ℕ), 2*i + 1)
( size_cond : size <= len ∧ len = items.length)
-- ( get := λ(i:ℕ), match items.nth i with | none := 0 | (some n) := n end)

namespace heap

variables {len size i : ℕ}
variables {a b : ℕ}

def parent (i:ℕ) := ⌊ i / 2 ⌋₊

def get_item (H : heap a b) (i: ℕ) := match H.items.nth i with
| none := 0
| (some n) := n
end

-- #check get_item 

end heap

variables {a b : ℕ}

lemma parent_le_index (i:ℕ) : heap.parent i <= i :=
begin
  rw [heap.parent],
  have : (⌊i / 2⌋₊ <= i / 2) := by dsimp ; refl,
  have : i / 2 <= i := nat.div_le_self i 2,
  linarith,
end

#check heap.items

lemma parent_le_length {hheap: heap a b} (i:ℕ) (hle : i < hheap.items.length) : heap.parent i < hheap.items.length := by begin 
  have := parent_le_index i,
  linarith,
end

def max_cond {a b :ℕ} {hheap: heap a b} (i:ℕ) (hle : i < hheap.items.length) : Prop := 
hheap.items.nth_le (heap.parent i) (parent_le_length i hle) >= hheap.items.nth_le i hle


structure max_heap (len size :ℕ) extends heap len size :=
(dir : ∀ i < items.length, max_cond i H)


def h4 : heap 5 4 := {
  items := [1,2,3,4,5],
  size_cond := by simp,
}

-- #eval h4.get_item (heap.parent 3)

end sorting