{-# OPTIONS --allow-unsolved-metas #-}

module Semiring where

open import Relation.Binary.PropositionalEquality
open import Data.Bool hiding (_≟_; _≤_)
open import Data.Empty
open import Data.Unit hiding (_≟_; _≤_)
open import Relation.Nullary
open import Relation.Unary
open import Relation.Nullary.Decidable
open import Data.Maybe
open import Data.Maybe.Properties
open import Data.Product
open import Data.Sum


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

{- May not need this anymore
partialJoin : {{ R : Semiring }} -> grade R -> grade R -> Maybe (grade R)
partialJoin {{R}} r s with _≤d_ R r s | _≤d_ R s r
... | yes _ | _     = just s
... | no  _ | yes _ = just r
,... | no _  | no  _ = nothing

partialJoinMono : {{ R : Semiring }} {r1 r2 : grade R} {s1 s2 : grade R} {r r' : grade R}
                -> _≤_ R r1 r2
                -> _≤_ R s1 s2
                -> just r ≡ partialJoin r1 s1
                -> just r' ≡ partialJoin r2 s2
                -> _≤_ R r r'
partialJoinMono {{R}} {r1} {r2} {s1} {s2} {r} {r'} pre1 pre2 eq1 eq2
  with _≤d_ R r1 s1 | _≤d_ R s1 r1 | _≤d_ R r2 s2 | _≤d_ R s2 r2
... | yes p1 | yes p2 | yes p3 | yes p4 rewrite just-injective eq1 | just-injective eq2 = pre2
... | yes p1 | yes p2 | yes p3 | no ¬p4 rewrite just-injective eq1 | just-injective eq2 = pre2
... | yes p1 | yes p2 | no ¬p3 | yes p4 rewrite just-injective eq1 | just-injective eq2 = transitive≤ R p2 pre1
... | yes p1 | no ¬p2 | yes p3 | yes p4 rewrite just-injective eq1 | just-injective eq2 = pre2
... | yes p1 | no ¬p2 | yes p3 | no ¬p4 rewrite just-injective eq1 | just-injective eq2 = pre2
... | yes p1 | no ¬p2 | no ¬p3 | yes p4 rewrite just-injective eq1 | just-injective eq2 = transitive≤ R pre2 p4
... | no ¬p1 | yes p2 | yes p3 | yes p4 rewrite just-injective eq1 | just-injective eq2 = transitive≤ R pre1 p3
... | no ¬p1 | yes p2 | yes p3 | no ¬p4 rewrite just-injective eq1 | just-injective eq2 = transitive≤ R pre1 p3
... | no ¬p1 | yes p2 | no ¬p3 | yes p4 rewrite just-injective eq1 | just-injective eq2 = pre1

partialJoinIdem : {{ R : Semiring }} {r : grade R}
                -> just r ≡ partialJoin r r
partialJoinIdem {{R}} {r} with _≤d_ R r r
... | yes p = refl
... | no ¬p = ⊥-elim (¬p (reflexive≤ R {r}))
-}

-- # Characterisation of what we need just to get non-interference
-- Not that we don't require 0 ≠ 1 because the NI theorem says that the observer is not equal
-- to the observee grade
record NonInterferingSemiring {{R : Semiring}} : Set₁ where
  field
    oneIsBottom : {r : grade} -> 1R ≤ r
    zeroIsTop   : {r : grade} -> r ≤ 0R

    antisymmetry : {r s : grade} -> r ≤ s -> s ≤ r -> r ≡ s

    idem* : {r : grade} -> r *R r ≡ r

open NonInterferingSemiring

-- ## Some derived properties

decreasing+ : {{ R : Semiring }} {{ R' : NonInterferingSemiring {{R}} }}
             {r1 r2 s : grade} -> (r1 ≤ s) -> ((r1 +R r2) ≤ s)
decreasing+ {{R}} {{R'}} {r1} {r2} {s} pre =
  subst (\h -> ((r1 +R r2) ≤ h)) (rightUnit+) (monotone+ pre (zeroIsTop R'))

-- NOT USED
increasing* : {{ R : Semiring }} {{ R' : NonInterferingSemiring {{R}} }}
               {r1 r2 s : grade} -> (s ≤ r1) -> (s ≤ (r1 *R r2))
increasing* {{R}} {{R'}} {r1} {r2} {s} pre =
    subst (\h -> h ≤ (r1 *R r2)) (rightUnit*) (monotone* pre (oneIsBottom R'))


-- TODO: is zeroIsTop deriveable from decreaseing +?
-- Vilem?
zeroIsTopFromDecreasing : {{ R : Semiring }} {{ R' : NonInterferingSemiring {{R}} }}
  -> ({r1 r2 s : grade} -> (r1 ≤ s) -> ((r1 +R r2) ≤ s))
  -> ({r : grade} -> r ≤ 0R)
zeroIsTopFromDecreasing decreasing {r} = {!!}
  -- similar to the `zero` proof in `rel1`
  -- sym (rightUnit+ {r}) = plusMeet2 {r} {0R}

-- aha
bottomIsOneFromIncrease* : {{ R : Semiring }} {{ R' : NonInterferingSemiring {{R}} }}
  ->  ({r1 r2 s : grade} -> (s ≤ r1) -> (s ≤ (r1 *R r2)))
  -> ({r : grade} -> 1R ≤ r)
bottomIsOneFromIncrease* increasy {r} =
  subst (\h -> 1R ≤ h) leftUnit* (increasy (reflexive≤ {1R}))

propInvTimesMonoAsymN : {{ R : Semiring }} {{ R' : NonInterferingSemiring }}
                       {r s adv : grade}
                     -> ¬ ((r *R s) ≤ adv)
                     ->   (r ≤ adv)
                     -> ¬ (s ≤ adv)
propInvTimesMonoAsymN {{R}} {{R'}} {r} {s} {adv} ngoal pre1 pre2 =
  ngoal
    (subst (\h -> ((r *R s) ≤ h)) (idem* R') (monotone* pre1 pre2))

{-
-- can we prove the above without idem*
propInvTimesMonoAsymNALT : {{ R : Semiring }} {{ R' : NonInterferingSemiring }}
                       {r s adv : grade}
                     -> ¬ ((r *R s) ≤ adv)
                     ->   (r ≤ adv)
                     -> ¬ (s ≤ adv)
propInvTimesMonoAsymNALT {{R}} {{R'}} {r} {s} {adv} ngola pre1 pre2 = {!!}
  where
-}

decreasing+Inv : {{ R : Semiring }} {{ R' : NonInterferingSemiring  }}
              {r1 r2 s : grade} -> ¬ ((r1 +R r2) ≤ s) -> ¬ (r1 ≤ s)
decreasing+Inv {{R}} {{R'}} {r1} {r2} {s} pre pre0 =
  pre (decreasing+ {{R}} {{R'}} {r1} {r2} {s} pre0)

decreasing+Inv' : {{ R : Semiring }} {{R' : NonInterferingSemiring }}
                -> {r1 r2 s : grade}
                -> ¬ ((r1 +R r2) ≤ s) -> ¬ (r2 ≤ s)
decreasing+Inv' {{R}} {{R'}} {r1} {r2} {s} pre =
  decreasing+Inv {{R}} {{R'}} {r2} {r1} {s} (\x -> pre (subst (\h -> h ≤ s) (comm+ {r2} {r1}) x))

-- Derived alternate characterisation of antisymmetry
antisymmetryAlt : {{R : Semiring}} {{R' : NonInterferingSemiring}} {r s : grade} -> r ≤ s -> r ≢ s -> ¬ (s ≤ r)
antisymmetryAlt {{R}} {{R'}} {r} {s} pre1 pre2 pre3 = ⊥-elim (pre2 (antisymmetry R' {r} {s} pre1 pre3))

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
    -- note that a lattice has these by default...
    idem* : {r : grade}     -> r *R r ≡ r
    absorb1 : {r s : grade} -> r *R (r +R s) ≡ r
    absorb2 : {r s : grade} -> r +R (r *R s) ≡ r

    -- not made explicit in A&B but implicit in the lattice discusssion
    -- + is meet
    plusMeet1 : {r s : grade} -> (r +R s) ≤ r
    plusMeet2 : {r s : grade} -> (r +R s) ≤ s
    -- * is the join
    multJoin1 : {r s : grade} -> r ≤ (r *R s)
    multJoin2 : {r s : grade} -> s ≤ (r *R s)

    -- relationship between meet and ordering
    -- which is usually part of meet-semilattice definition
    meetOrderRel : {r s : grade} -> r ≤ s -> r ≡ r +R s

open Informational

rel1 : {{R : Semiring}} -> Informational -> NonInterferingSemiring
rel1 record { idem* = idem* ; absorb1 = absorb1 ; absorb2 = absorb2 ; plusMeet1 = plusMeet1 ; plusMeet2 = plusMeet2 ; multJoin1 = multJoin1 ; multJoin2 = multJoin2 ; meetOrderRel = meetOrderRel } =
  record
    { oneIsBottom = one ; zeroIsTop = zero ; antisymmetry = antisym ; idem* = idem* }
  where
    one : {r : grade} → 1R ≤ r
    one {r} rewrite sym (leftUnit* {r}) = multJoin1 {1R} {r}

    zero : {r : grade} -> r ≤ 0R
    zero {r} rewrite sym (rightUnit+ {r}) = plusMeet2 {r} {0R}

    -- maybe a classical proof?
    antisym : {r s : grade} -> r ≤ s -> s ≤ r -> r ≡ s
    antisym {r} {s} x y =
      let prf1 = meetOrderRel x
          prf2 = meetOrderRel y
      in trans prf1 (trans (comm+ {r} {s}) (sym prf2))

-- Looks like Informational semiring is much more general
-- But we should try a bit harder
-- TODO (Vilem) - try to get the Informational semiring from NonInterferingSemiring
-- It looks like antisymmetry is the key to leverage in many cases?
rel2 : {{R : Semiring}} -> NonInterferingSemiring -> Informational
rel2 record { oneIsBottom = oneIsBottom ; zeroIsTop = zeroIsTop ; antisymmetry = antisymmetry ; idem* = idem* } =
  record
    { idem* = idem*
    ; absorb1 = {!!}
    ; absorb2 = {!!}
    ; plusMeet1 = {!!}
    ; plusMeet2 = {!!}
    ; multJoin1 = {!!}
    ; multJoin2 = {!!}
    }
  where
    absorba : {r s : grade} → r *R (r +R s) ≡ r
    absorba = {!!}
    -- r * (r + s)
    -- = r * r + r * s
    -- = r + r * s
    -- = r * s + r


    plusMeeta : {r s : grade} -> (r +R s) ≤ r
    plusMeeta = {!!}

-- Abel et al. (2023) take a semiring with a meet operation
-- to induce a partial order
-- Antisymmetry come out of this? (see below)

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

-- Section 6 of Abel et al. (2023) but also
-- called 'quantitative' in Moon et al. (2021) (where we would collapse
-- + and meet here

record WellBehavedZero {{R : Semiring}} {{R' : Meety}} : Set₁ where
  field
    additionPositive : {p q : grade} -> p +R q ≡ 0R -> (p ≡ 0R) × (q ≡ 0R)
    meetPositive     : {p q : grade} -> p ∧R q ≡ 0R -> (p ≡ 0R) × (q ≡ 0R)
    zeroPositive     : {p q : grade} -> p *R q ≡ 0R -> (p ≡ 0R) ⊎ (q ≡ 0R)
    zeroNoTOne       : ¬ (0R ≡ 1R)

open WellBehavedZero {{...}}


posToNi : {{R : Semiring}} {{R' : Meety}}
       -> WellBehavedZero -> NonInterferingSemiring
posToNi record { additionPositive = additionPositive ; meetPositive = meetPositive; zeroPositive = zeroPositive ; zeroNoTOne = zeroNoTOne } = record {
    oneIsBottom = {!!}
  ; zeroIsTop = {!!}
  ; antisymmetry = {!!}
  ; idem* = {!!} }

niToPos : {{R : Semiring}} {{R' : Meety}}
       -> NonInterferingSemiring -> WellBehavedZero
niToPos record { oneIsBottom = oneIsBottom ; zeroIsTop = zeroIsTop ; antisymmetry = antisymmetry ; idem* = idem* } =
  record
    { additionPositive = {!!}
    ; meetPositive = {!!}
    ; zeroPositive = {!!}
    ; zeroNoTOne = {!!}
    }
  where
   addPos : {{R : Semiring}} {{R' : Meety}}
          -> NonInterferingSemiring
          -> {p q : Semiring.grade R} → (p +R q ≡ 0R) → p ≡ Semiring.0R R × q ≡ Semiring.0R R
   addPos {{R}} {{R'}} (record { oneIsBottom = oneIsBottom ; zeroIsTop = zeroIsTop ; antisymmetry = antisymmetry ; idem* = idem* }) {p} {Q} eq1 = left , {!!}
     where
       left : p ≡ 0R
       left =
         let x = increasing* {{R}} {{(record { oneIsBottom = oneIsBottom ; zeroIsTop = zeroIsTop ; antisymmetry = antisymmetry ; idem* = idem* })}} (oneIsBottom {0R})
         in antisymmetry zeroIsTop {!!}
       -- p + q = 0
       -- 0 <= p + q
       -- ->
       -- -> 0 <= p
