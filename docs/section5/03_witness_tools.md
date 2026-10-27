# 03 — Uniform proof tools (to be added to the visibility library)

These lemmas are stated for an arbitrary simple counter-clockwise polygon `P` (`InteriorLeft`).
They are the only "geometric reasoning" used by the Section 5 proof; everything else is
linear arithmetic.  Names are suggestions for `ArtGallery/Vis/` (new file `Vis/Cones.lean`).

## T1 — blocking (exists: `not_sees_of_proper_cross`)

## T1' — vertex cone lemma (`sees_subset_cone`)
Let `v = vtx i` with predecessor `u` and successor `w`, convex (`det u v w > 0`).  If `P.Sees v p`
then `det v w p ≥ 0` and `det u v p ≥ 0`, i.e. `p ∈ v + cone(w − v, u − v)`.
*Proof.* `local_wedge`: near `v` the region is the closed wedge; a segment `v p` with `p` outside the
wedge has points `v + t(p−v)`, small `t > 0`, outside the region.  (The wedge is a cone, so the whole
ray direction is excluded.)  ∎
Consequence (*witness cone*): `V(v) := {p ∈ filled | Sees v p} ⊆ cone_v`.

## T4 — room lemma (`sees_crosses_door`)
Let `R ⊆ ℝ²` be closed and `D ⊆ ℝ²` (the *door*) with `frontier R ∩ P.filled ⊆ D`.  If
`t ∈ R`, `p ∉ R` and `P.Sees t p`, then `segment t p ∩ D ≠ ∅`.
*Proof.* `segment t p` is connected, meets `R` and its complement, hence meets `frontier R`; that
point is in `filled` (segment ⊆ filled), hence in `D`.  ∎

**Rooms used in the construction.**  A *room* is `R = filled_K` for a sub-polygon `K` formed by a
contiguous chain `v_a, …, v_b` of `P`'s vertices closed by the chord `D = [v_b, v_a]`
(pocket rooms: door = pocket mouth on `y = 1`; unit rooms: door = `c0 d0`).  The hypothesis
`frontier(filled_K) ∩ P.filled ⊆ D` follows from: `K` is simple (chain of `P` plus a chord whose open
interior is disjoint from all other edges — box separation), `frontier(filled_K) = boundary K`
(Jordan library), and points of the chain are in `boundary P`; so it suffices that points of
`boundary K \ D` that are in `P.filled`... are only chain points, and a chain point `y ∉ D` has a
neighbourhood whose intersection with `P.filled` lies in `filled_K` (`local_halfplane` /
`local_wedge` for both `P` and `K`, which have the same incident edges at `y`).  Simplest Lean
form: state T4 with hypothesis `∀ y ∈ frontier R, y ∈ P.filled → y ∈ D` and prove that hypothesis
once per room *type* via the local lemmas.

**Cone-door corollary (the uniform "seen only from A" argument).**  If `v` is a convex vertex in the
room `R` with door `D` and `cone_v ∩ D = ∅`, then `V(v) ⊆ R`.  (Segment `v p` lies in `cone_v`
by convexity of the cone; if `p ∉ R` it meets `D`, contradiction.)  Every such claim in the
construction is a finite set of strict linear inequalities on the cone generators and door
endpoints (two inequalities per door endpoint).

## T2 — convex containment (exists: `closure_subset_filled_of_convex`)
Positive claims ("`g` sees `q`"): exhibit a convex polygon `Q ∋ g, q` with interior in the interior
of `P`; for parametric families (corridor) `Q` is described by linear inequalities and "no edge of
`P` meets `int Q`" is proven by *box separation* (each edge lies in a box disjoint from `Q`) except
for the `O(1)` edges near `Q`, which are checked by sign conditions.

## T3 — counting (exists: `guards_in_region`, paper Lemmas 22/23)
Used in the *two-stage* form (08 §Counting): (1) a family `M` of witnesses, one per required guard
position, with pairwise disjoint visibility sets, gives `|G| ≥ |M| = g`; (2) when `|G| = g`, every
guard sees exactly one `m ∈ M`; for each position `X` the guard seeing `m_X` must also see the rest
`W_X` of `X`'s witnesses provided no *other* guard can see `W_X`; positions are processed in an order
(base segments, corridor stationary guards, receivers, gadget stationary guards, enclosed
receivers) such that at each step the other guards are already pinned to their positions and the
check "pinned positions do not see `W_X`" is a finite set of cone computations.

## Stationary guard (SG) lemma (`sg_unique`)

Let `p` be a convex vertex with interior wedge `W` (directions `[w1, w2]`).  Let `q_a, q_b` be the
tips of two V-slots at directions `θ_a < θ_b` strictly inside `(w1, w2)` such that the line
`q_a p` resp. `q_b p` bounds the cone of `q_a` resp. `q_b`, the cone of `q_a` lying on the side
of its line that contains `w1`, the cone of `q_b` on the side containing `w2`.  Then
`V(q_a) ∩ V(q_b) = {p}`, and `p` sees both slots entirely.
*Proof.* Near `p`, `cone(q_a) ⊆ H_a` with `H_a ∩ (p+W) = p + [w1, θ_a]` and
`cone(q_b) ⊆ H_b` with `H_b ∩ (p+W) = p + [θ_b, w2]`; these meet only in `p`.  A point
`x ≠ p` in `H_a ∩ H_b` is outside `p + W`; the segment from `q_a` to `x` runs along the
cone of `q_a` and leaves `filled` near `p` (T1 against one of the two edges at `p`, explicit sign
conditions), so `x ∉ V(q_a)` unless `x` lies on the near side — which is excluded by `H_b`.
The slots are seen by `p` because their directions are interior to `W` and the triangle
`conv(p, slot)` is checked by T2.  ∎

**Design rule learnt the hard way.** A witness placed on a *boundary* ray of `W` (e.g. a needle
on the extension of an edge at `p`) has its cone on the *outside* of `W`, so the interior of its
needle is seen by no guard at all (`p` sees only inside `W`); such witnesses make the polygon
unguardable.  All witnesses of stationary guards are therefore general-position slots.

Instances: corridor SGs (two floor slots on lines of slopes 2, 4 through `p_k`, 04), gadget SGs
(inversion: two floor slots; addition: two slots in the pillar top; orientation `p`: two slots in
the z-block edge).
