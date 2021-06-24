module Semiring where

open import Relation.Binary.PropositionalEquality
open import Data.Bool hiding (_≟_; _≤_)
open import Data.Empty
open import Data.Unit hiding (_≟_; _≤_)

record Semiring : Set₁ where
  field
    carrier : Set
    1r      : carrier
    0r      : carrier
    _+R_    : carrier -> carrier -> carrier
    _*R_    : carrier -> carrier -> carrier
    _≤_     : carrier -> carrier -> Set

    leftUnit+   : {r : carrier} -> 0r +R r ≡ r
    rightUnit+  : {r : carrier} -> r +R 0r ≡ r
    comm+       : {r s : carrier} -> r +R s ≡ s +R r

    leftUnit*    : {r : carrier} -> 1r *R r ≡ r
    rightUnit*   : {r : carrier} -> r *R r ≡ r
    leftAbsorb   : {r : carrier} -> r *R 0r ≡ 0r
    rightAbsorb  : {r : carrier} -> 0r *R r ≡ 0r

    assoc*     : {r s t : carrier} -> (r *R s) *R t ≡ r *R (s *R t)
    assoc+     : {r s t : carrier} -> (r +R s) +R t ≡ r +R (s +R t)

    distrib1    : {r s t : carrier} -> r *R (s +R t) ≡ (r *R s) +R (r *R t)
    distrib2    : {r s t : carrier} -> (r +R s) *R t ≡ (r *R s) +R (r *R t)

    monotone*  : {r1 r2 s1 s2 : carrier} -> r1 ≤ r2 -> s1 ≤ s2 -> (r1 *R s1) ≤ (r2 *R s2)
    monotone+  : {r1 r2 s1 s2 : carrier} -> r1 ≤ r2 -> s1 ≤ s2 -> (r1 +R s2) ≤ (r2 +R s2)



open Semiring

-- Level elements
data Level : Set where
  Public  : Level
  Private : Level
  Dunno   : Level
  Unused  : Level

-- constructive representation of the ordering
data Order : Level -> Level -> Set where
  -- central 'line' and its transitivity
  0Pub    : Order Unused Public
  0Priv   : Order Unused Private
  PrivPub : Order Private Public
  -- dunno branch
  0Dunno  : Order Unused Dunno
  PrivDunno : Order Private Dunno
  -- reflexive cases
  Refl : (l : Level) -> Order l l


levelSemiring : Semiring
carrier levelSemiring = Level
1r levelSemiring      = Private
0r levelSemiring      = Unused

_≤_ levelSemiring x y = Order x y

-- unit property
_+R_ levelSemiring Unused x = x
_+R_ levelSemiring x Unused = x
-- otherwise dunno acts like another unit
_+R_ levelSemiring Dunno x = x
_+R_ levelSemiring x Dunno = x
-- otherwise join
_+R_ levelSemiring Private Private = Private
_+R_ levelSemiring Public  Public  = Public
_+R_ levelSemiring Private Public  = Public
_+R_ levelSemiring Public Private  = Public

-- absorbing
_*R_ levelSemiring Unused x = Unused
_*R_ levelSemiring x Unused = Unused
-- dunno behaviour
_*R_ levelSemiring Private Dunno = Dunno
_*R_ levelSemiring Dunno Private = Dunno
_*R_ levelSemiring x Dunno = x
_*R_ levelSemiring Dunno x = x
-- otherwise join
_*R_ levelSemiring Private Private = Private
_*R_ levelSemiring Public  Public  = Public
_*R_ levelSemiring Private Public  = Public
_*R_ levelSemiring Public Private  = Public

leftUnit+ levelSemiring {Public}  = refl
leftUnit+ levelSemiring {Private} = refl
leftUnit+ levelSemiring {Dunno}   = refl
leftUnit+ levelSemiring {Unused}  = refl

rightUnit+ levelSemiring {Public}  = refl
rightUnit+ levelSemiring {Private} = refl
rightUnit+ levelSemiring {Dunno}   = refl
rightUnit+ levelSemiring {Unused}  = refl

comm+ levelSemiring {Public} {Public} = refl
comm+ levelSemiring {Public} {Private} = refl
comm+ levelSemiring {Public} {Dunno} = refl
comm+ levelSemiring {Public} {Unused} = refl
comm+ levelSemiring {Private} {Public} = refl
comm+ levelSemiring {Private} {Private} = refl
comm+ levelSemiring {Private} {Dunno} = refl
comm+ levelSemiring {Private} {Unused} = refl
comm+ levelSemiring {Dunno} {Public} = refl
comm+ levelSemiring {Dunno} {Private} = refl
comm+ levelSemiring {Dunno} {Dunno} = refl
comm+ levelSemiring {Dunno} {Unused} = refl
comm+ levelSemiring {Unused} {Public} = refl
comm+ levelSemiring {Unused} {Private} = refl
comm+ levelSemiring {Unused} {Dunno} = refl
comm+ levelSemiring {Unused} {Unused} = refl

leftAbsorb levelSemiring {Public} = refl
leftAbsorb levelSemiring {Private} = refl
leftAbsorb levelSemiring {Dunno} = refl
leftAbsorb levelSemiring {Unused} = refl

rightAbsorb levelSemiring {Public} = refl
rightAbsorb levelSemiring {Private} = refl
rightAbsorb levelSemiring {Dunno} = refl
rightAbsorb levelSemiring {Unused} = refl

leftUnit* levelSemiring {Public}   = refl
leftUnit* levelSemiring {Private}  = refl
leftUnit* levelSemiring {Dunno}    = refl
leftUnit* levelSemiring {Unused}   = refl

rightUnit* levelSemiring {Public}  = refl
rightUnit* levelSemiring {Private} = refl
rightUnit* levelSemiring {Dunno}   = refl
rightUnit* levelSemiring {Unused}  = refl

assoc* levelSemiring {r} {s} {t} = {!!}

assoc+ levelSemiring {r} {s} {t} = {!!}

distrib1 levelSemiring {r} {s} {t} = {!!}

distrib2 levelSemiring {r} {s} {t} = {!!}

monotone* levelSemiring 0Pub 0Pub = 0Pub
monotone* levelSemiring 0Pub 0Priv = 0Pub
monotone* levelSemiring 0Pub PrivPub = 0Pub
monotone* levelSemiring 0Pub 0Dunno = 0Pub
monotone* levelSemiring 0Pub PrivDunno = 0Pub
monotone* levelSemiring 0Pub (Refl Public) = 0Pub
monotone* levelSemiring 0Pub (Refl Private) = 0Pub
monotone* levelSemiring 0Pub (Refl Dunno) = 0Pub
monotone* levelSemiring 0Pub (Refl Unused) = Refl Unused
monotone* levelSemiring 0Priv 0Pub = 0Pub
monotone* levelSemiring 0Priv 0Priv = 0Priv
monotone* levelSemiring 0Priv PrivPub = 0Pub
monotone* levelSemiring 0Priv 0Dunno = 0Dunno
monotone* levelSemiring 0Priv PrivDunno = 0Dunno
monotone* levelSemiring 0Priv (Refl Public) = 0Pub
monotone* levelSemiring 0Priv (Refl Private) = 0Priv
monotone* levelSemiring 0Priv (Refl Dunno) = 0Dunno
monotone* levelSemiring 0Priv (Refl Unused) = Refl Unused
monotone* levelSemiring PrivPub 0Pub = 0Pub
monotone* levelSemiring PrivPub 0Priv = 0Pub
monotone* levelSemiring PrivPub PrivPub = PrivPub
monotone* levelSemiring PrivPub 0Dunno = 0Pub
monotone* levelSemiring PrivPub PrivDunno = PrivPub
monotone* levelSemiring PrivPub (Refl Public) = Refl Public
monotone* levelSemiring PrivPub (Refl Private) = PrivPub
-- Private <= Pub   Dunno <= Dunno
-- --------------------------------------
 --    Private * Dunno <= Pub * Dunno
 --       Dunno        <= Pub    uh oh.
monotone* levelSemiring PrivPub (Refl Dunno) = {!!}
monotone* levelSemiring PrivPub (Refl Unused) = Refl Unused
monotone* levelSemiring 0Dunno 0Pub = 0Pub
monotone* levelSemiring 0Dunno 0Priv = 0Dunno
monotone* levelSemiring 0Dunno PrivPub = 0Pub
monotone* levelSemiring 0Dunno 0Dunno = 0Dunno
monotone* levelSemiring 0Dunno PrivDunno = 0Dunno
monotone* levelSemiring 0Dunno (Refl Public) = 0Pub
monotone* levelSemiring 0Dunno (Refl Private) = 0Dunno
monotone* levelSemiring 0Dunno (Refl Dunno) = 0Dunno
monotone* levelSemiring 0Dunno (Refl Unused) = Refl Unused
monotone* levelSemiring PrivDunno 0Pub = 0Pub
monotone* levelSemiring PrivDunno 0Priv = 0Dunno
monotone* levelSemiring PrivDunno PrivPub = PrivPub
monotone* levelSemiring PrivDunno 0Dunno = 0Dunno
monotone* levelSemiring PrivDunno PrivDunno = PrivDunno
monotone* levelSemiring PrivDunno (Refl Public) = Refl Public
monotone* levelSemiring PrivDunno (Refl Private) = PrivDunno
monotone* levelSemiring PrivDunno (Refl Dunno) = Refl Dunno
monotone* levelSemiring PrivDunno (Refl Unused) = Refl Unused
monotone* levelSemiring (Refl Public) 0Pub = 0Pub
monotone* levelSemiring (Refl Private) 0Pub = 0Pub
monotone* levelSemiring (Refl Dunno) 0Pub = 0Pub
monotone* levelSemiring (Refl Unused) 0Pub = Refl Unused
monotone* levelSemiring (Refl Public) 0Priv = 0Pub
monotone* levelSemiring (Refl Private) 0Priv = 0Priv
monotone* levelSemiring (Refl Dunno) 0Priv = 0Dunno
monotone* levelSemiring (Refl Unused) 0Priv = Refl Unused
monotone* levelSemiring (Refl Public) PrivPub = Refl Public
monotone* levelSemiring (Refl Private) PrivPub = PrivPub
monotone* levelSemiring (Refl Dunno) PrivPub = {!!}
monotone* levelSemiring (Refl Unused) PrivPub = Refl Unused
monotone* levelSemiring (Refl Public) 0Dunno = 0Pub
monotone* levelSemiring (Refl Private) 0Dunno = 0Dunno
monotone* levelSemiring (Refl Dunno) 0Dunno = 0Dunno
monotone* levelSemiring (Refl Unused) 0Dunno = Refl Unused
monotone* levelSemiring (Refl Public) PrivDunno = Refl Public
monotone* levelSemiring (Refl Private) PrivDunno = PrivDunno
monotone* levelSemiring (Refl Dunno) PrivDunno = Refl Dunno
monotone* levelSemiring (Refl Unused) PrivDunno = Refl Unused
monotone* levelSemiring (Refl Public) (Refl Public) = Refl Public
monotone* levelSemiring (Refl Public) (Refl Private) = Refl Public
monotone* levelSemiring (Refl Public) (Refl Dunno) = Refl Public
monotone* levelSemiring (Refl Public) (Refl Unused) = Refl Unused
monotone* levelSemiring (Refl Private) (Refl Public) = Refl Public
monotone* levelSemiring (Refl Private) (Refl Private) = Refl Private
monotone* levelSemiring (Refl Private) (Refl Dunno) = Refl Dunno
monotone* levelSemiring (Refl Private) (Refl Unused) = Refl Unused
monotone* levelSemiring (Refl Dunno) (Refl Public) = Refl Public
monotone* levelSemiring (Refl Dunno) (Refl Private) = Refl Dunno
monotone* levelSemiring (Refl Dunno) (Refl Dunno) = Refl Dunno
monotone* levelSemiring (Refl Dunno) (Refl Unused) = Refl Unused
monotone* levelSemiring (Refl Unused) (Refl r) = Refl Unused

monotone+ levelSemiring {r1} {r2} {s1} {s2} pre1 pre2 = {!!}


{-
-- Additional property which would be super useful but doesn't seem to hold for Level

infFlow : {levelSemiring : Semiring} -> {r s adv : carrier} -> boolToSet ((r *R s) ≤ adv) -> boolToSet (s ≤ adv)
infFlow levelSemiring {Public} {Public} {Public} prop = tt
infFlow levelSemiring {Public} {Public} {Private} ()
infFlow levelSemiring {Public} {Public} {Dunno} ()
infFlow levelSemiring {Public} {Public} {Unused} ()
--      Public * Private <= Public (yes)
-- (as) Public <= Public
-- but Private <= Public (
infFlow levelSemiring {Public} {Private} {Public} tt = tt
infFlow levelSemiring {Public} {Private} {Private} prop = tt
infFlow levelSemiring {Public} {Private} {Dunno} prop = tt
infFlow levelSemiring {Public} {Private} {Unused} ()
--    Public * Dunno <= Public (yes)
--    Public <= Public
-- but Dunno <= Public is false
infFlow levelSemiring {Public} {Dunno} {Public} tt = {!!}
infFlow levelSemiring {Public} {Dunno} {Private} ()
infFlow levelSemiring {Public} {Dunno} {Dunno} prop = tt
infFlow levelSemiring {Public} {Dunno} {Unused} ()
infFlow levelSemiring {Public} {Unused} {Public} prop = tt
infFlow levelSemiring {Public} {Unused} {Private} prop = tt
infFlow levelSemiring {Public} {Unused} {Dunno} prop = tt
infFlow levelSemiring {Public} {Unused} {Unused} prop = tt
infFlow levelSemiring {Private} {Public} {Public} prop = tt
infFlow levelSemiring {Private} {Public} {Private} ()
infFlow levelSemiring {Private} {Public} {Dunno} ()
infFlow levelSemiring {Private} {Public} {Unused} ()
infFlow levelSemiring {Private} {Private} {Public} tt = tt
infFlow levelSemiring {Private} {Private} {Private} prop = tt
infFlow levelSemiring {Private} {Private} {Dunno} prop = tt
infFlow levelSemiring {Private} {Private} {Unused} ()
infFlow levelSemiring {Private} {Dunno} {Public} ()
infFlow levelSemiring {Private} {Dunno} {Private} ()
infFlow levelSemiring {Private} {Dunno} {Dunno} prop = tt
infFlow levelSemiring {Private} {Dunno} {Unused} ()
infFlow levelSemiring {Private} {Unused} {Public} prop = tt
infFlow levelSemiring {Private} {Unused} {Private} prop = tt
infFlow levelSemiring {Private} {Unused} {Dunno} prop = tt
infFlow levelSemiring {Private} {Unused} {Unused} prop = tt
infFlow levelSemiring {Dunno} {Public} {Public} prop = tt
infFlow levelSemiring {Dunno} {Public} {Private} ()
infFlow levelSemiring {Dunno} {Public} {Dunno} ()
infFlow levelSemiring {Dunno} {Public} {Unused} ()
infFlow levelSemiring {Dunno} {Private} {Public} prop = tt
infFlow levelSemiring {Dunno} {Private} {Private} prop = tt
infFlow levelSemiring {Dunno} {Private} {Dunno} prop = tt
infFlow levelSemiring {Dunno} {Private} {Unused} ()
infFlow levelSemiring {Dunno} {Dunno} {Public} ()
infFlow levelSemiring {Dunno} {Dunno} {Private} ()
infFlow levelSemiring {Dunno} {Dunno} {Dunno} prop = tt
infFlow levelSemiring {Dunno} {Dunno} {Unused} ()
infFlow levelSemiring {Dunno} {Unused} {Public} prop = tt
infFlow levelSemiring {Dunno} {Unused} {Private} prop = tt
infFlow levelSemiring {Dunno} {Unused} {Dunno} prop = tt
infFlow levelSemiring {Dunno} {Unused} {Unused} prop = tt
infFlow levelSemiring {Unused} {Public} {Public} prop = tt
infFlow levelSemiring {Unused} {Public} {Private} tt = {!!}
infFlow levelSemiring {Unused} {Public} {Dunno} tt = {!!}
infFlow levelSemiring {Unused} {Public} {Unused} tt = {!!}
infFlow levelSemiring {Unused} {Private} {Public} tt = tt
infFlow levelSemiring {Unused} {Private} {Private} prop = tt
infFlow levelSemiring {Unused} {Private} {Dunno} prop = tt
infFlow levelSemiring {Unused} {Private} {Unused} tt = {!!}
infFlow levelSemiring {Unused} {Dunno} {Public} tt = {!!}
infFlow levelSemiring {Unused} {Dunno} {Private} tt = {!!}
infFlow levelSemiring {Unused} {Dunno} {Dunno} prop = tt
infFlow levelSemiring {Unused} {Dunno} {Unused} tt = {!!}
infFlow levelSemiring {Unused} {Unused} {Public} prop = tt
infFlow levelSemiring {Unused} {Unused} {Private} prop = tt
infFlow levelSemiring {Unused} {Unused} {Dunno} prop = tt
infFlow levelSemiring {Unused} {Unused} {Unused} prop = tt
-}
