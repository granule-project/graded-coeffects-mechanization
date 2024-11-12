module Semiring where

open import Relation.Binary.PropositionalEquality
open import Relation.Nullary
open import Relation.Nullary.Decidable

-- # Semiring definition
record Semiring : Set₁ where
  field
    grade : Set
    1R      : grade
    0R      : grade
    _+R_    : grade -> grade -> grade
    _*R_    : grade -> grade -> grade
    _≤_     : grade -> grade -> Set

    -- Decideable ordering and equality
    _≤d_  : (r : grade) -> (s : grade) -> Dec (r ≤ s)

    leftUnit+   : {r : grade} -> 0R +R r ≡ r
    rightUnit+  : {r : grade} -> r +R 0R ≡ r
    comm+       : {r s : grade} -> r +R s ≡ s +R r

    leftUnit*    : {r : grade} -> (1R *R r) ≡ r
    rightUnit*   : {r : grade} -> (r *R 1R) ≡ r
    leftAbsorb   : {r : grade} -> (0R *R r) ≡ 0R
    rightAbsorb  : {r : grade} -> (r *R 0R) ≡ 0R

    assoc*     : {r s t : grade} -> (r *R s) *R t ≡ r *R (s *R t)
    assoc+     : {r s t : grade} -> (r +R s) +R t ≡ r +R (s +R t)

    distrib1    : {r s t : grade} -> (r *R (s +R t)) ≡ ((r *R s) +R (r *R t))
    distrib2    : {r s t : grade} -> ((r +R s) *R t) ≡ ((r *R t) +R (s *R t))

    monotone*  : {r1 r2 s1 s2 : grade} -> r1 ≤ r2 -> s1 ≤ s2 -> (r1 *R s1) ≤ (r2 *R s2)
    monotone+  : {r1 r2 s1 s2 : grade} -> r1 ≤ r2 -> s1 ≤ s2 -> (r1 +R s1) ≤ (r2 +R s2)

    reflexive≤ : {r : grade} -> r ≤ r
    transitive≤ : {r s t : grade} -> r ≤ s -> s ≤ t -> r ≤ t

open Semiring {{...}}

variable
  R : Semiring

≡-to-≤ : {{ R : Semiring }} {r s : grade} -> r ≡ s -> r ≤ s
≡-to-≤ refl = reflexive≤

-- # Characterisation of what we need just to get non-interference
-- Not that we don't require 0 ≠ 1 because the NI theorem says that the observer is not equal
-- to the observee grade
record NonInterferingSemiring {{R : Semiring}} : Set₁ where
  field
    oneIsBottom : {r : grade} -> 1R ≤ r
    zeroIsTop   : {r : grade} -> r ≤ 0R

    antisymmetry : {r s : grade} -> r ≤ s -> s ≤ r -> r ≡ s

    idem*lax : {r : grade} -> (r *R r) ≤ r

open NonInterferingSemiring

-- ## Some derived properties
decreasing+ : {{ R : Semiring }} {{ R' : NonInterferingSemiring {{R}} }}
             {r1 r2 s : grade} -> (r1 ≤ s) -> ((r1 +R r2) ≤ s)
decreasing+ {{R}} {{R'}} {r1} {r2} {s} pre =
  subst (\h -> ((r1 +R r2) ≤ h)) (rightUnit+) (monotone+ pre (zeroIsTop R'))

increasing* : {{ R : Semiring }} {{ R' : NonInterferingSemiring {{R}} }}
               {r1 r2 s : grade} -> (s ≤ r1) -> (s ≤ (r1 *R r2))
increasing* {{R}} {{R'}} {r1} {r2} {s} pre =
    subst (\h -> h ≤ (r1 *R r2)) (rightUnit*) (monotone* pre (oneIsBottom R'))

-- Interderivability properties
zeroIsTopFromDecreasing+ : {{ R : Semiring }}
  -> ({r1 r2 s : grade} -> (r1 ≤ s) -> ((r1 +R r2) ≤ s))
  -> ({r : grade} -> r ≤ 0R)
zeroIsTopFromDecreasing+ decreasing {r} =
  subst (\h -> h ≤ 0R) leftUnit+ (decreasing (reflexive≤ {0R}))

bottomIsOneFromIncrease* : {{ R : Semiring }}
  -> ({r1 r2 s : grade} -> (s ≤ r1) -> (s ≤ (r1 *R r2)))
  -> ({r : grade} -> 1R ≤ r)
bottomIsOneFromIncrease* increasy {r} =
  subst (\h -> 1R ≤ h) leftUnit* (increasy (reflexive≤ {1R}))

-- ## Some further derived properties

propInvTimesMonoAsymN : {{ R : Semiring }} {{ R' : NonInterferingSemiring }}
                       {r s adv : grade}
                     -> ¬ ((r *R s) ≤ adv)
                     ->   (r ≤ adv)
                     -> ¬ (s ≤ adv)
propInvTimesMonoAsymN {{R}} {{R'}} {r} {s} {adv} ngoal pre1 pre2 =
 let aux = (monotone* pre1 pre2)
 in ngoal (transitive≤ aux (idem*lax R'))

decreasing+Inv : {{ R : Semiring }} {{ R' : NonInterferingSemiring  }}
              {r1 r2 s : grade} -> ¬ ((r1 +R r2) ≤ s) -> ¬ (r1 ≤ s)
decreasing+Inv {{R}} {{R'}} {r1} {r2} {s} pre pre0 =
  pre (decreasing+ {{R}} {{R'}} {r1} {r2} {s} pre0)

decreasing+Inv' : {{ R : Semiring }} {{R' : NonInterferingSemiring }}
                -> {r1 r2 s : grade}
                -> ¬ ((r1 +R r2) ≤ s) -> ¬ (r2 ≤ s)
decreasing+Inv' {{R}} {{R'}} {r1} {r2} {s} pre =
  decreasing+Inv {{R}} {{R'}} {r2} {r1} {s} (\x -> pre (subst (\h -> h ≤ s) (comm+ {r2} {r1}) x))


-------------------------------------------------------
-- NOTES BELOW HERE

-- From Abel&Bernardy (2021) §4.3
-- The paper has a strong implication of lattice nature around here
-- which would imply having a partial order => having an antisymmetric relation

-- They also have an assumption in 4.3.2. that means everything "above 1 in
-- the lattice is secret" though I don't think this needs codifying here
-- but rather this is part of non-interference

-- "The construction generalises however to any lattice of information
-- modalities as specified above"
record Informational {{R : Semiring}} : Set₁ where
  field
    -- Since * is join
    idem* : {r : grade}     -> r *R r ≡ r
    --
    joinOrderRel : {r s : grade} -> r ≤ s -> s ≡ r *R s
    joinOrderReli : {r s : grade} -> s ≡ r *R s -> r ≤ s

    -- Since + is meet
    idem+ : {r : grade}     -> r +R r ≡ r
    -- relationship between meet and ordering
    -- which is usually part of meet-semilattice definition
    meetOrderRel : {r s : grade} -> r ≤ s -> r ≡ r +R s
    meetOrderReli : {r s : grade} -> r ≡ r +R s -> r ≤ s

    absorb1 : {r s : grade} -> r *R (r +R s) ≡ r
    absorb2 : {r s : grade} -> r +R (r *R s) ≡ r

open Informational

-- Proof that an informational semiring is a non-interfering semiring
informationalImpliesNonInterfering : {{R : Semiring}} -> Informational -> NonInterferingSemiring
informationalImpliesNonInterfering record { idem* = idem* ; joinOrderRel = joinOrderRel
             ; joinOrderReli = joinOrderReli
             ; idem+ = idem+
             ; meetOrderRel = meetOrderRel ; meetOrderReli = meetOrderReli
             ; absorb1 = absorb1 ; absorb2 = absorb2 } =
  record
    { oneIsBottom = one ; zeroIsTop = zero ; antisymmetry = antisym ; idem*lax = idem*laxFromExact idem* }
  where
    idem*laxFromExact : {r : grade} -> r *R r ≡ r -> (r *R r) ≤ r
    idem*laxFromExact {r} eq rewrite eq = reflexive≤

    one : {r : grade} → 1R ≤ r
    one {r} =
      bottomIsOneFromIncrease* increasing*h {r}
        where
          eq : {r s : grade} -> r *R s ≡ r *R (r *R s)
          eq {r} {s} = trans (cong (\h -> h *R s) (sym (idem* {r}))) (assoc* {r} {r} {s})

          joinProp : { r s : grade } -> r ≤ (r *R s)
          joinProp {r} {s} = joinOrderReli eq

          increasing*h : {r1 r2 s : grade} -> (s ≤ r1) -> (s ≤ (r1 *R r2))
          increasing*h {r1} {r2} {s} pre =
            transitive≤ (joinProp {s} {r2}) (monotone* pre (reflexive≤ {r2}))

    zero : {r : grade} -> r ≤ 0R
    zero {r} =
          zeroIsTopFromDecreasing+ decreasing+h {r}
        where
          eq : {r s : grade} -> r +R s ≡ (r +R s) +R r
          eq {r} {s} =
           trans
            (trans
              (trans (cong (\h -> h +R s) (sym (idem+ {r})))
                (assoc+ {r} {r} {s}))
                  (cong (\h -> r +R h) (comm+ {r} {s}))) (sym (assoc+ {r} {s} {r}))


          meetProp : { r s : grade } -> (r +R s) ≤ r
          meetProp {r} {s} = meetOrderReli eq

          decreasing+h : {r1 r2 s : grade} -> (r1 ≤ s) -> ((r1 +R r2) ≤ s)
          decreasing+h {r1} {r2} {s} pre =
            transitive≤ (monotone+ pre (reflexive≤ {r2})) (meetProp {s} {r2})

    antisym : {r s : grade} -> r ≤ s -> s ≤ r -> r ≡ s
    antisym {r} {s} x y =
      let prf1 = meetOrderRel x
          prf2 = meetOrderRel y
      in trans prf1 (trans (comm+ {r} {s}) (sym prf2))

-- Abel et al. (2023) take a semiring with a meet operation
-- to induce a partial order
-- Does antisymmetry come out of this? (see below)

record Meety {{R : Semiring}} : Set₁ where
  field
    _∧R_ : grade -> grade -> grade
    comm : {r s : grade} -> r ∧R s ≡ s ∧R r
    assoc : {r s t : grade} -> (r ∧R s) ∧R t ≡ r ∧R (s ∧R t)
    idem  : {r : grade} -> r ∧R r ≡ r

open Meety {{...}}

_<<=_ : {{  R : Semiring }} {{ m : Meety }} -> grade -> grade -> Set
r <<= s = r ≡ r ∧R s

-- Meet produces antisymmetric ordering
antisym : {{ R : Semiring }} {{ m : Meety }} {r s : grade} ->
          r <<= s -> s <<= r -> r ≡ s
antisym {r} {s} prf1 prf2 = trans prf1 (trans (comm {r} {s}) (sym prf2))
 -- prf1 = r ≡ r /\ s
 -- prf2 = s ≡ s /\ r
