import tactic
import data.list.basic
import data.nat.basic
import data.nat.log
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


-- structure h2 extends 

structure heap := 
( items : list ℕ )
-- ( length := items.length)
-- ( parent := λ(i :ℕ ), ⌊ i / 2 ⌋₊ )
-- ( left   := λ(i :ℕ ), 2 * i)
-- ( right  := λ(i :ℕ), 2*i + 1)
-- ( size_cond : size <= len ∧ len = items.length)
-- ( get := λ(i:ℕ), match items.nth i with | none := 0 | (some n) := n end)

namespace heap

variables {len size i : ℕ}
variables {a b  : ℕ}

def parent (i:ℕ) := ⌊ ( i-1 ) / 2 ⌋₊
def right (i: ℕ) := 2 * (i + 1)
def left (i: ℕ) := 2*i + 1
def length (h: heap) := h.items.length

def get_item (H : heap ) (i: ℕ) := match H.items.nth i with
| none := 0
| (some n) := n
end


def height (h: heap ) := nat.floor $ nat.log 2 h.items.length
-- #eval nat.log 2 8

def height_rec (h: heap) := match h.items with 
| [] := 0
| (x::xs) := 1
end


end heap

variables {a b : ℕ}

lemma parent_le_index (i:ℕ) : heap.parent i <= i :=
begin
  rw [heap.parent],
  have : (⌊(i-1) / 2⌋₊ <= (i-1) / 2) := by dsimp ; refl,
  have : (i-1) / 2 <= (i-1) := nat.div_le_self (i-1) 2,
  have : i - 1 <= i := by norm_num,
  linarith,
end

#check @heap.items

lemma parent_le_length {hheap: heap } (i:ℕ) (hle : i < hheap.items.length) : heap.parent i < hheap.items.length := by begin 
  have := parent_le_index i,
  linarith,
end

def max_cond {hheap: heap } (i:ℕ) (hle : i < hheap.items.length) : Prop := 
let 
  parentItem := hheap.items.nth_le (heap.parent i) (parent_le_length i hle),
  ithItem := hheap.items.nth_le i hle
in parentItem >=ithItem 

structure max_heap (len size :ℕ) extends heap :=
(dir : ∀ i < items.length, max_cond i H)

def min_cond  {h : heap } (i: ℕ) (hle: i < h.items.length) : Prop :=
let 
  parentItem := h.items.nth_le (heap.parent i) (parent_le_length i hle),
  ithItem := h.items.nth_le i hle
in ithItem <= parentItem

structure min_heap (len size : ℕ) extends heap :=
(dir: ∀ i < items.length, min_cond i H)

namespace min_heap
  -- def from_list {a : ℕ} (l : list ℕ ) : heap a a  := { 
  --   items := l, 
  --   size_cond := begin
      
  --    end
  --   }
end min_heap

def h4 : heap := {
  items := [1,2,3,4,5]
}

#eval h4.get_item (heap.parent 3)
-- #eval h4.get_item 
-- #eval h4.height

-- example { l: list ℕ} (hsorted: sorted l) : 

end sorting