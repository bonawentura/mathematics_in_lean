import data.real.basic
import data.matrix.basic
import data.matrix.notation
import data.matrix.dmatrix
import linear_algebra.matrix
import system.io

-- system.io.print _

open io

def printSht (s: string) : io unit := 
print_ln s

#eval printSht "asdasdasd \n"

inductive ttmp : Type 
| one
| two
| three 

#check @ttmp.rec
#check @ttmp.rec_on 

def ftmp (t: ttmp) : ℕ := t.rec_on 1 2 3

def ftmp2 (t: ttmp) : ℕ := t.rec 1 2 3

#eval ftmp ttmp.one
#eval ftmp2 ttmp.two



namespace tmp

universes u


inductive btree (β : Type u) 
| empty {} : btree 
| node (l: btree) (k: nat) (a : β) (r: btree) : btree

namespace btree

variables {β : Type u}

def empty_tree : btree β := btree.empty

def bound (x : nat) : btree β -> bool 
| empty := ff
| (node l k a r) := x = k ∨ bound l ∨ bound r

def height : btree β -> nat
| empty := 0
| (node l k  a r) := 1 + (max (height l) (height r))



end btree


end tmp

-- namespace sorting

/--------------------------
 - define property `sorted` on ℕ
  - sorted on typeclass? *

 - create a `swap` function on a list
  - prove that it is a permutation
  
-----------------------/

-- end
