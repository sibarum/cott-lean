import CottLean.T.Gaussian

/-!
# Scatter: any schedule gives the same grid

A scatter deposits amounts on nodes. Each deposit `i` goes to one node, `node i`, carrying one amount,
`a i`, and a node's value is the sum of what landed on it:

```
grid n = ∑ i with node i = n, a i
```

This is vexelray-sim-fluid's particle-to-grid transfer (`particle.Scatter`), where the amount is the
conserved pair of mass and momentum and summing is traction's mediant `⊕`: the pair
`(Σ w·m·v, Σ w·m)` of `docs/architecture.md`, *conserved pairs*. Nothing here depends on what the
amounts are, only on the laws of the sum, so every result is stated for an additive commutative
monoid `M`. `⊕` on `T` is one (`GaussianPosition`, whose `+` is `⊕`), so are the triples
`(Σ mu, Σ mv, Σ m)` a grid node holds in two dimensions, and so are the `w`-bit registers of
`Scatter/Wrap.lean`. Nesting does not change this: a pair of pairs under `⊕` is four integers added
coordinatewise.

## What is proved

* `run_eq_grid`: atomic adds, applied one deposit at a time in the order of any list that holds each
  deposit once, leave exactly `grid`. The order is the hardware's to choose, and it cannot matter. This
  is the direct scatter.
* `run_perm`: two such orders give the same grid, to the element.
* `grid_flatten`, `grouped_eq_grid`: summing the deposits in groups first and then adding the groups'
  grids, in any order, is again `grid`. This is the pre-reduced scatter (a group is a workgroup's
  deposits, summed in workgroup memory) and the segmented one (a group is a run of one cell, summed
  across a subgroup), given that the group's own sum is right.
* `gather_eq_grid`: summing, for each node, over the cells that touch it and then over each cell's
  particles, which is the gather, is `grid`.
* `total_grid`, `total_grid_particles`: the grid holds exactly what the deposits did, and when each
  particle's shares sum to its amount, exactly what the particles did. This is conservation.

Commutativity is what the order-free results use. `grid_flatten` needs only associativity, which is
why a segmented sum in a fixed order is exact in any monoid; it is the atomics' arbitrary order on top
that needs the sum to commute. IEEE `f32` addition commutes but does not associate, so on floats these
equalities hold only up to rounding (`Scatter/Rounding.lean`).
-/

namespace Scatter

open Finset

variable {ι N M : Type*} [DecidableEq N]

/-! ## The grid -/

section Grid

variable [AddCommMonoid M]

/-- What node `n` holds once every deposit in `s` has landed: the sum of the amounts sent to it. -/
def grid (node : ι → N) (a : ι → M) (s : Finset ι) (n : N) : M :=
  ∑ i ∈ s with node i = n, a i

/-- One atomic add: deposit `i` adds its amount to its own node and leaves every other node alone. -/
def deposit (node : ι → N) (a : ι → M) (g : N → M) (i : ι) : N → M :=
  Function.update g (node i) (g (node i) + a i)

/-- The grid after the deposits of `l`, applied one at a time in that order, from an empty grid. -/
def run (node : ι → N) (a : ι → M) (l : List ι) : N → M :=
  l.foldl (deposit node a) 0

theorem deposit_apply (node : ι → N) (a : ι → M) (g : N → M) (i : ι) (n : N) :
    deposit node a g i n = g n + if node i = n then a i else 0 := by
  unfold deposit
  by_cases h : node i = n
  · subst h; simp
  · simp [h, Function.update_of_ne (Ne.symm h)]

/-- Deposits applied to a grid add, at each node, what was sent there. -/
theorem foldl_deposit (node : ι → N) (a : ι → M) (l : List ι) (g : N → M) (n : N) :
    l.foldl (deposit node a) g n = g n + (l.map fun i => if node i = n then a i else 0).sum := by
  induction l generalizing g with
  | nil => simp
  | cons i l ih => simp [List.foldl_cons, ih, deposit_apply, add_assoc]

/-- The direct scatter: in any order that applies each deposit once, the atomics leave `grid`. -/
theorem run_eq_grid (node : ι → N) (a : ι → M) [DecidableEq ι] {l : List ι} (hl : l.Nodup) :
    run node a l = grid node a l.toFinset := by
  funext n
  rw [run, foldl_deposit, grid, sum_filter, List.sum_toFinset _ hl]
  simp

/-- Any two orders of the same deposits give the same grid. -/
theorem run_perm (node : ι → N) (a : ι → M) {l l' : List ι} (hl : l.Nodup)
    (h : l.Perm l') : run node a l = run node a l' := by
  classical
  rw [run_eq_grid node a hl, run_eq_grid node a (h.nodup_iff.mp hl), List.toFinset_eq_of_perm _ _ h]

/-- The grid of disjoint groups is the sum of the groups' grids. -/
theorem grid_union (node : ι → N) (a : ι → M) [DecidableEq ι] {s t : Finset ι} (h : Disjoint s t) :
    grid node a (s ∪ t) = grid node a s + grid node a t := by
  funext n
  simp [grid, filter_union, sum_union (disjoint_filter_filter h)]

/-- Grouping: summing each group, then summing the groups, is the grid of all the deposits. The groups
must not share a deposit. -/
theorem grid_biUnion (node : ι → N) (a : ι → M) [DecidableEq ι] {κ : Type*} (G : Finset κ)
    (g : κ → Finset ι) (h : (G : Set κ).PairwiseDisjoint g) :
    grid node a (G.biUnion g) = ∑ k ∈ G, grid node a (g k) := by
  funext n
  simp only [grid, Finset.sum_apply, filter_biUnion]
  exact sum_biUnion (fun x hx y hy hxy => disjoint_filter_filter (h hx hy hxy))

omit [AddCommMonoid M] in
/-- The same, for groups given as lists and summed each in its own order: summing the groups' sums is
summing all the deposits in the flattened order. This needs only associativity, in any additive monoid,
commutative or not. -/
theorem grid_flatten {A : Type*} [AddMonoid A] (node : ι → N) (a : ι → A) (groups : List (List ι))
    (n : N) :
    ((groups.flatten).map fun i => if node i = n then a i else 0).sum =
      (groups.map fun l => (l.map fun i => if node i = n then a i else 0).sum).sum := by
  induction groups with
  | nil => simp
  | cons l gs ih => simp [Function.comp_def]

omit [DecidableEq N] in
/-- A sum of functions, evaluated at a point. -/
theorem list_sum_apply (L : List (N → M)) (n : N) : L.sum n = (L.map fun g => g n).sum := by
  induction L with
  | nil => rfl
  | cons g L ih => simp [ih]

/-- The pre-reduced and segmented scatters: groups summed first, then each group's grid added by
atomics in any order. When the groups together hold each deposit once, the result is `grid`. -/
theorem grouped_eq_grid (node : ι → N) (a : ι → M) [DecidableEq ι] {groups : List (List ι)}
    (hl : groups.flatten.Nodup) (order : List (N → M))
    (horder : order.Perm (groups.map fun l => run node a l)) :
    order.sum = grid node a groups.flatten.toFinset := by
  rw [horder.sum_eq, ← run_eq_grid node a hl]
  funext n
  rw [list_sum_apply, List.map_map]
  simp only [run, Function.comp_def, foldl_deposit, Pi.zero_apply, zero_add]
  exact (grid_flatten node a groups n).symm

/-! ## The gather -/

/-- The gather: particle `p` sits in cell `cell p` and sends its share `share p k` to corner `k` of
that cell, `corner (cell p) k`. Node `n` sums, over every cell and corner that is `n`, the shares of the
particles in that cell. It reads each share once and writes each node once, with no atomics. -/
def gather {P C K : Type*} (cell : P → C) (corner : C → K → N) (share : P → K → M)
    (particles : Finset P) (cells : Finset C) (corners : Finset K) [DecidableEq C] (n : N) : M :=
  ∑ c ∈ cells, ∑ k ∈ corners with corner c k = n, ∑ p ∈ particles with cell p = c, share p k

/-- The gather is the scatter turned around: when every particle's cell is among the cells summed, it
gives exactly the grid of the particles' deposits, a deposit being a particle and one of its corners. -/
theorem gather_eq_grid {P C K : Type*} [DecidableEq C] (cell : P → C) (corner : C → K → N)
    (share : P → K → M) (particles : Finset P) (cells : Finset C) (corners : Finset K)
    (hcell : ∀ p ∈ particles, cell p ∈ cells) (n : N) :
    gather cell corner share particles cells corners n =
      grid (fun d : P × K => corner (cell d.1) d.2) (fun d => share d.1 d.2)
        (particles ×ˢ corners) n := by
  unfold gather grid
  rw [sum_filter, sum_product]
  simp_rw [← sum_filter]
  calc ∑ c ∈ cells, ∑ k ∈ corners with corner c k = n, ∑ p ∈ particles with cell p = c, share p k
      = ∑ c ∈ cells, ∑ p ∈ particles with cell p = c, ∑ k ∈ corners with corner (cell p) k = n,
          share p k := by
        refine sum_congr rfl fun c _ => ?_
        rw [sum_comm']
        · intro k p
          simp only [mem_filter]
          aesop
    _ = _ := sum_fiberwise_of_maps_to hcell _

/-! ## Conservation -/

/-- The grid holds exactly what the deposits held, when every deposit lands on one of the nodes
summed. -/
theorem total_grid (node : ι → N) (a : ι → M) (s : Finset ι) (nodes : Finset N)
    (h : ∀ i ∈ s, node i ∈ nodes) : ∑ n ∈ nodes, grid node a s n = ∑ i ∈ s, a i :=
  sum_fiberwise_of_maps_to h a

/-- Conservation of the transfer: when each particle's shares sum to its amount, the grid holds
exactly what the particles did. -/
theorem total_grid_particles {P K : Type*} (node : P → K → N) (share : P → K → M) (amount : P → M)
    (particles : Finset P) (corners : Finset K) (nodes : Finset N)
    (hnode : ∀ p ∈ particles, ∀ k ∈ corners, node p k ∈ nodes)
    (hshare : ∀ p ∈ particles, ∑ k ∈ corners, share p k = amount p) :
    ∑ n ∈ nodes, grid (fun d : P × K => node d.1 d.2) (fun d => share d.1 d.2)
        (particles ×ˢ corners) n = ∑ p ∈ particles, amount p := by
  rw [total_grid _ _ _ _ fun d hd => hnode d.1 (mem_product.mp hd).1 d.2 (mem_product.mp hd).2,
    sum_product]
  exact sum_congr rfl hshare

end Grid

/-! ## On traction's own pairs -/

/-- The grid of pairs under `⊕`, which is `T` read in the exponent position. Every result above
applies to it as stated. -/
abbrev PairGrid (node : ι → N) (a : ι → T.GaussianPosition) (s : Finset ι) : N → T.GaussianPosition :=
  grid node a s

/-- An empty node is `0ω`, the unit of `⊕`, and not a hazard: a node no deposit reached holds it. -/
theorem pairGrid_empty (node : ι → N) (a : ι → T.GaussianPosition) (s : Finset ι) (n : N)
    (h : ∀ i ∈ s, node i ≠ n) : PairGrid node a s n = T.GaussianPosition.of T.«0ω» := by
  simp only [PairGrid, grid]
  rw [filter_false_of_mem h, sum_empty]
  rfl

end Scatter
