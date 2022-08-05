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

inductive heap_btree (α : Type ) : Type
| empty {} : heap_btree
| node (l: heap_btree) (k: ℕ) (a: α) (r: heap_btree): heap_btree

  namespace heap_btree

  variables {α : Type }
  def empty_tree : heap_btree α := heap_btree.empty

  def height : heap_btree α -> ℕ 
  | empty := 0
  | (node l k a r) := 1 + (max (height l) (height r))

  end heap_btree


variables {len size i : ℕ}
variables {a b  : ℕ}
variables {α : Type}

def parent (i:ℕ) := ⌊ ( i-1 ) / 2 ⌋₊
def right (i: ℕ) := 2 * (i + 1)
def left (i: ℕ) := 2*i + 1
def length (h: heap) := h.items.length

def get_item (H : heap ) (i: ℕ) := match H.items.nth i with
| none := 0
| (some n) := n
end



-- def to_tree (lst: list ℕ) (key: ℕ) : heap_btree ℕ := match lst with
-- | [] := heap_btree.empty
-- | [x] := heap_btree.node heap_btree.empty key x heap_btree.empty
-- | (x::xs) := heap_btree.node (left) (key) (x) (right)
-- end
-- def to_tree (hp: heap) : heap_btree ℕ := match hp.items with
-- | []      := heap_btree.empty
-- | [x]     := heap_btree.node heap_btree.empty 0 x heap_btree.empty
-- | [p, ] := heap_btree.node (to_tree) 
-- end

def height (h: heap ) := nat.floor $ nat.log 2 h.items.length
-- #eval nat.log 2 8

def tail_children {α : Type} (l: list α) (k: nat)  := match (l.nth k) with
| none := ([] : list α) 
| (some α) := l.drop k
end

--  h             k
--  [1,2,3,4,5]   0
--  [_,_,3,4,5]   2
--  [_,_,_,_,_]   6

--  h             k
--  [1,2,3,4,5]   0
--  [_,2,3,4,5]   1
--  [_,_,_,4,5]   3
--  [_,_,_,_,_]   7
#eval left 3
def tmpList : list ℕ := [1,2,3,4]
def emptyList : list ℕ := []
#check sizeof_measure (list ℕ) tmpList []
-- #eval sizeof_measure (list ℕ) tmpList tmpList
#eval tmpList.sizeof
#eval (tmpList.drop 1).sizeof

lemma list_sizeof_eq_length (l : list ℕ ) : l.sizeof = l.length :=
begin
  induction l with l' IH,
  {
    
  },
  
  -- { 
  --  -- have : list.nil.sizeof = 0 := sorry,
  -- have : list.nil.length = 0 := by begin
  --   simp,
  -- end,
  -- },
  -- _
end

lemma left_subtree_le {α : Type} [has_sizeof α] (h: list α) (hl : h.length > 0) (k:ℕ ):  (list.drop (left k - k) h).sizeof < h.sizeof := 
begin 
  have left_le : left k - k > 0 := by rw [left] ; simp ; linarith,
  have hsizeof := list.drop_sizeof_le h (left k - k),
  set n := left k - k,
  have hneq :( h.drop (n)).length = h.length - n := list.length_drop n h,
  set ln := list.range n,
  -- have : list.sizeof (ln) = n := by library_search,
  have : h.sizeof = h.length := begin 
    sorry,
  end,
  sorry,
end


def height_rec : list ℕ -> ℕ -> ℕ  
| ([]) :=λk,  0
| h := λ k,
have hL : (list.drop (left k - k) h).sizeof < h.sizeof, from begin
  have : left k > k := sorry,
  have : left k - k > 0 := sorry,
  -- apply list.drop_sizeof_le

  
 end,
have hR : (list.drop (right k - k) h).sizeof < h.sizeof, from sorry,
  let L := left k, 
      Ltree :=  h.drop (L - k),
      R := right k,
      Rtree := h.drop (R - k),
      increment := if k = 0 then 0 else 1
      -- Rh := height_rec h k
      in
      increment + max (height_rec Ltree L ) (height_rec Rtree R)
       



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

#eval h4.items.drop 6
#eval heap.tail_children h4.items 6
#eval h4.get_item (heap.parent 3)
-- #eval h4.get_item 
#eval h4.height
#eval heap.height_rec h4.items 0

-- example { l: list ℕ} (hsorted: sorted l) : 

end sorting