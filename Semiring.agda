module Semiring where

open import Relation.Binary.PropositionalEquality
open import Data.Bool hiding (_≟_; _≤_)
open import Data.Empty
open import Data.Unit hiding (_≟_; _≤_)
open import Relation.Nullary

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
    distrib2    : {r s t : carrier} -> (r +R s) *R t ≡ (r *R t) +R (s *R t)

    monotone*  : {r1 r2 s1 s2 : carrier} -> r1 ≤ r2 -> s1 ≤ s2 -> (r1 *R s1) ≤ (r2 *R s2)
    monotone+  : {r1 r2 s1 s2 : carrier} -> r1 ≤ r2 -> s1 ≤ s2 -> (r1 +R s2) ≤ (r2 +R s2)

    reflexive≤ : {r : carrier} -> r ≤ r
    transitive≤ : {r s t : carrier} -> r ≤ s -> s ≤ t -> r ≤ t


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
  DunnoPub  : Order Dunno Public
  -- reflexive cases
  Refl : (l : Level) -> Order l l


levelSemiring : Semiring
carrier levelSemiring = Level
1r levelSemiring      = Private
0r levelSemiring      = Unused

-- remember the ordering in the calculus goes the 'opposite way' to Granule but
-- the above `Order` data type is defined using Granule's direction
-- *so we need to flip here*
_≤_ levelSemiring x y = Order y x

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

assoc* levelSemiring {Public} {Public} {Public} = refl
assoc* levelSemiring {Public} {Public} {Private} = refl
assoc* levelSemiring {Public} {Public} {Dunno} = refl
assoc* levelSemiring {Public} {Public} {Unused} = refl
assoc* levelSemiring {Public} {Private} {Public} = refl
assoc* levelSemiring {Public} {Private} {Private} = refl
assoc* levelSemiring {Public} {Private} {Dunno} = refl
assoc* levelSemiring {Public} {Private} {Unused} = refl
assoc* levelSemiring {Public} {Dunno} {Public} = refl
assoc* levelSemiring {Public} {Dunno} {Private} = refl
assoc* levelSemiring {Public} {Dunno} {Dunno} = refl
assoc* levelSemiring {Public} {Dunno} {Unused} = refl
assoc* levelSemiring {Public} {Unused} {t} = refl
assoc* levelSemiring {Private} {Public} {Public} = refl
assoc* levelSemiring {Private} {Public} {Private} = refl
assoc* levelSemiring {Private} {Public} {Dunno} = refl
assoc* levelSemiring {Private} {Public} {Unused} = refl
assoc* levelSemiring {Private} {Private} {Public} = refl
assoc* levelSemiring {Private} {Private} {Private} = refl
assoc* levelSemiring {Private} {Private} {Dunno} = refl
assoc* levelSemiring {Private} {Private} {Unused} = refl
assoc* levelSemiring {Private} {Dunno} {Public} = refl
assoc* levelSemiring {Private} {Dunno} {Private} = refl
assoc* levelSemiring {Private} {Dunno} {Dunno} = refl
assoc* levelSemiring {Private} {Dunno} {Unused} = refl
assoc* levelSemiring {Private} {Unused} {t} = refl
assoc* levelSemiring {Dunno} {Public} {Public} = refl
assoc* levelSemiring {Dunno} {Public} {Private} = refl
assoc* levelSemiring {Dunno} {Public} {Dunno} = refl
assoc* levelSemiring {Dunno} {Public} {Unused} = refl
assoc* levelSemiring {Dunno} {Private} {Public} = refl
assoc* levelSemiring {Dunno} {Private} {Private} = refl
assoc* levelSemiring {Dunno} {Private} {Dunno} = refl
assoc* levelSemiring {Dunno} {Private} {Unused} = refl
assoc* levelSemiring {Dunno} {Dunno} {Public} = refl
assoc* levelSemiring {Dunno} {Dunno} {Private} = refl
assoc* levelSemiring {Dunno} {Dunno} {Dunno} = refl
assoc* levelSemiring {Dunno} {Dunno} {Unused} = refl
assoc* levelSemiring {Dunno} {Unused} {t} = refl
assoc* levelSemiring {Unused} {s} {t} = refl

assoc+ levelSemiring {Public} {Public} {Public} = refl
assoc+ levelSemiring {Public} {Public} {Private} = refl
assoc+ levelSemiring {Public} {Public} {Dunno} = refl
assoc+ levelSemiring {Public} {Public} {Unused} = refl
assoc+ levelSemiring {Public} {Private} {Public} = refl
assoc+ levelSemiring {Public} {Private} {Private} = refl
assoc+ levelSemiring {Public} {Private} {Dunno} = refl
assoc+ levelSemiring {Public} {Private} {Unused} = refl
assoc+ levelSemiring {Public} {Dunno} {Public} = refl
assoc+ levelSemiring {Public} {Dunno} {Private} = refl
assoc+ levelSemiring {Public} {Dunno} {Dunno} = refl
assoc+ levelSemiring {Public} {Dunno} {Unused} = refl
assoc+ levelSemiring {Public} {Unused} {t} = refl
assoc+ levelSemiring {Private} {Public} {Public} = refl
assoc+ levelSemiring {Private} {Public} {Private} = refl
assoc+ levelSemiring {Private} {Public} {Dunno} = refl
assoc+ levelSemiring {Private} {Public} {Unused} = refl
assoc+ levelSemiring {Private} {Private} {Public} = refl
assoc+ levelSemiring {Private} {Private} {Private} = refl
assoc+ levelSemiring {Private} {Private} {Dunno} = refl
assoc+ levelSemiring {Private} {Private} {Unused} = refl
assoc+ levelSemiring {Private} {Dunno} {Public} = refl
assoc+ levelSemiring {Private} {Dunno} {Private} = refl
assoc+ levelSemiring {Private} {Dunno} {Dunno} = refl
assoc+ levelSemiring {Private} {Dunno} {Unused} = refl
assoc+ levelSemiring {Private} {Unused} {t} = refl
assoc+ levelSemiring {Dunno} {Public} {Public} = refl
assoc+ levelSemiring {Dunno} {Public} {Private} = refl
assoc+ levelSemiring {Dunno} {Public} {Dunno} = refl
assoc+ levelSemiring {Dunno} {Public} {Unused} = refl
assoc+ levelSemiring {Dunno} {Private} {Public} = refl
assoc+ levelSemiring {Dunno} {Private} {Private} = refl
assoc+ levelSemiring {Dunno} {Private} {Dunno} = refl
assoc+ levelSemiring {Dunno} {Private} {Unused} = refl
assoc+ levelSemiring {Dunno} {Dunno} {Public} = refl
assoc+ levelSemiring {Dunno} {Dunno} {Private} = refl
assoc+ levelSemiring {Dunno} {Dunno} {Dunno} = refl
assoc+ levelSemiring {Dunno} {Dunno} {Unused} = refl
assoc+ levelSemiring {Dunno} {Unused} {t} = refl
assoc+ levelSemiring {Unused} {s} {t} = refl

distrib1 levelSemiring {Public} {Public} {Public} = refl
distrib1 levelSemiring {Public} {Public} {Private} = refl
distrib1 levelSemiring {Public} {Public} {Dunno} = refl
distrib1 levelSemiring {Public} {Public} {Unused} = refl
distrib1 levelSemiring {Public} {Private} {Public} = refl
distrib1 levelSemiring {Public} {Private} {Private} = refl
distrib1 levelSemiring {Public} {Private} {Dunno} = refl
distrib1 levelSemiring {Public} {Private} {Unused} = refl
distrib1 levelSemiring {Public} {Dunno} {Public} = refl
distrib1 levelSemiring {Public} {Dunno} {Private} = refl
distrib1 levelSemiring {Public} {Dunno} {Dunno} = refl
distrib1 levelSemiring {Public} {Dunno} {Unused} = refl
distrib1 levelSemiring {Public} {Unused} {t} = refl
distrib1 levelSemiring {Private} {Public} {Public} = refl
distrib1 levelSemiring {Private} {Public} {Private} = refl
distrib1 levelSemiring {Private} {Public} {Dunno} = refl
distrib1 levelSemiring {Private} {Public} {Unused} = refl
distrib1 levelSemiring {Private} {Private} {Public} = refl
distrib1 levelSemiring {Private} {Private} {Private} = refl
distrib1 levelSemiring {Private} {Private} {Dunno} = refl
distrib1 levelSemiring {Private} {Private} {Unused} = refl
distrib1 levelSemiring {Private} {Dunno} {Public} = refl
distrib1 levelSemiring {Private} {Dunno} {Private} = refl
distrib1 levelSemiring {Private} {Dunno} {Dunno} = refl
distrib1 levelSemiring {Private} {Dunno} {Unused} = refl
distrib1 levelSemiring {Private} {Unused} {t} = refl
distrib1 levelSemiring {Dunno} {Public} {Public} = refl
distrib1 levelSemiring {Dunno} {Public} {Private} = refl
distrib1 levelSemiring {Dunno} {Public} {Dunno} = refl
distrib1 levelSemiring {Dunno} {Public} {Unused} = refl
distrib1 levelSemiring {Dunno} {Private} {Public} = refl
distrib1 levelSemiring {Dunno} {Private} {Private} = refl
distrib1 levelSemiring {Dunno} {Private} {Dunno} = refl
distrib1 levelSemiring {Dunno} {Private} {Unused} = refl
distrib1 levelSemiring {Dunno} {Dunno} {Public} = refl
distrib1 levelSemiring {Dunno} {Dunno} {Private} = refl
distrib1 levelSemiring {Dunno} {Dunno} {Dunno} = refl
distrib1 levelSemiring {Dunno} {Dunno} {Unused} = refl
distrib1 levelSemiring {Dunno} {Unused} {t} = refl
distrib1 levelSemiring {Unused} {s} {t} = refl

distrib2 levelSemiring {Public} {Public} {Public} = refl
distrib2 levelSemiring {Public} {Public} {Private} = refl
distrib2 levelSemiring {Public} {Public} {Dunno} = refl
distrib2 levelSemiring {Public} {Public} {Unused} = refl
distrib2 levelSemiring {Public} {Private} {Public} = refl
distrib2 levelSemiring {Public} {Private} {Private} = refl
distrib2 levelSemiring {Public} {Private} {Dunno} = refl
distrib2 levelSemiring {Public} {Private} {Unused} = refl
distrib2 levelSemiring {Public} {Dunno} {Public} = refl
distrib2 levelSemiring {Public} {Dunno} {Private} = refl
distrib2 levelSemiring {Public} {Dunno} {Dunno} = refl
distrib2 levelSemiring {Public} {Dunno} {Unused} = refl
distrib2 levelSemiring {Public} {Unused} {Public} = refl
distrib2 levelSemiring {Public} {Unused} {Private} = refl
distrib2 levelSemiring {Public} {Unused} {Dunno} = refl
distrib2 levelSemiring {Public} {Unused} {Unused} = refl
distrib2 levelSemiring {Private} {Public} {Public} = refl
distrib2 levelSemiring {Private} {Public} {Private} = refl
distrib2 levelSemiring {Private} {Public} {Dunno} = refl
distrib2 levelSemiring {Private} {Public} {Unused} = refl
distrib2 levelSemiring {Private} {Private} {Public} = refl
distrib2 levelSemiring {Private} {Private} {Private} = refl
distrib2 levelSemiring {Private} {Private} {Dunno} = refl
distrib2 levelSemiring {Private} {Private} {Unused} = refl
distrib2 levelSemiring {Private} {Dunno} {Public} = refl
distrib2 levelSemiring {Private} {Dunno} {Private} = refl
distrib2 levelSemiring {Private} {Dunno} {Dunno} = refl
distrib2 levelSemiring {Private} {Dunno} {Unused} = refl
distrib2 levelSemiring {Private} {Unused} {Public} = refl
distrib2 levelSemiring {Private} {Unused} {Private} = refl
distrib2 levelSemiring {Private} {Unused} {Dunno} = refl
distrib2 levelSemiring {Private} {Unused} {Unused} = refl
distrib2 levelSemiring {Dunno} {Public} {Public} = refl
distrib2 levelSemiring {Dunno} {Public} {Private} = refl
distrib2 levelSemiring {Dunno} {Public} {Dunno} = refl
distrib2 levelSemiring {Dunno} {Public} {Unused} = refl
distrib2 levelSemiring {Dunno} {Private} {Public} = refl
distrib2 levelSemiring {Dunno} {Private} {Private} = refl
distrib2 levelSemiring {Dunno} {Private} {Dunno} = refl
distrib2 levelSemiring {Dunno} {Private} {Unused} = refl
distrib2 levelSemiring {Dunno} {Dunno} {Public} = refl
distrib2 levelSemiring {Dunno} {Dunno} {Private} = refl
distrib2 levelSemiring {Dunno} {Dunno} {Dunno} = refl
distrib2 levelSemiring {Dunno} {Dunno} {Unused} = refl
distrib2 levelSemiring {Dunno} {Unused} {Public} = refl
distrib2 levelSemiring {Dunno} {Unused} {Private} = refl
distrib2 levelSemiring {Dunno} {Unused} {Dunno} = refl
distrib2 levelSemiring {Dunno} {Unused} {Unused} = refl
distrib2 levelSemiring {Unused} {Public} {Public} = refl
distrib2 levelSemiring {Unused} {Public} {Private} = refl
distrib2 levelSemiring {Unused} {Public} {Dunno} = refl
distrib2 levelSemiring {Unused} {Public} {Unused} = refl
distrib2 levelSemiring {Unused} {Private} {Public} = refl
distrib2 levelSemiring {Unused} {Private} {Private} = refl
distrib2 levelSemiring {Unused} {Private} {Dunno} = refl
distrib2 levelSemiring {Unused} {Private} {Unused} = refl
distrib2 levelSemiring {Unused} {Dunno} {Public} = refl
distrib2 levelSemiring {Unused} {Dunno} {Private} = refl
distrib2 levelSemiring {Unused} {Dunno} {Dunno} = refl
distrib2 levelSemiring {Unused} {Dunno} {Unused} = refl
distrib2 levelSemiring {Unused} {Unused} {t} = refl

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
 --       Dunno        <= Pub    (didn't have this previously 24/06/2021).
monotone* levelSemiring PrivPub (Refl Dunno) = DunnoPub
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
monotone* levelSemiring (Refl Dunno) PrivPub = DunnoPub
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
monotone* levelSemiring 0Pub DunnoPub = 0Pub
monotone* levelSemiring 0Priv DunnoPub = 0Pub
monotone* levelSemiring PrivPub DunnoPub = DunnoPub
monotone* levelSemiring 0Dunno DunnoPub = 0Pub
monotone* levelSemiring PrivDunno DunnoPub = DunnoPub
monotone* levelSemiring DunnoPub 0Pub = 0Pub
monotone* levelSemiring DunnoPub 0Priv = 0Pub
monotone* levelSemiring DunnoPub PrivPub = DunnoPub
monotone* levelSemiring DunnoPub 0Dunno = 0Pub
monotone* levelSemiring DunnoPub PrivDunno = DunnoPub
monotone* levelSemiring DunnoPub DunnoPub = DunnoPub
monotone* levelSemiring DunnoPub (Refl Public) = Refl Public
monotone* levelSemiring DunnoPub (Refl Private) = DunnoPub
monotone* levelSemiring DunnoPub (Refl Dunno) = DunnoPub
monotone* levelSemiring DunnoPub (Refl Unused) = Refl Unused
monotone* levelSemiring (Refl Public) DunnoPub = Refl Public
monotone* levelSemiring (Refl Private) DunnoPub = DunnoPub
monotone* levelSemiring (Refl Dunno) DunnoPub = DunnoPub
monotone* levelSemiring (Refl Unused) DunnoPub = Refl Unused

monotone+ levelSemiring {r1} {r2} {s1} {s2} pre1 pre2 = {!!}

reflexive≤ levelSemiring {r} = Refl r

transitive≤ levelSemiring {r} {s} {t} = {!!}

-- Additional property which would be super useful but doesn't seem to hold for Level

infFlow : {r s adv : Level} -> _≤_ levelSemiring (_*R_ levelSemiring r s) adv -> _≤_ levelSemiring s adv
infFlow {Public} {Public} {Public} inp = Refl Public
infFlow {Public} {Public} {Private} inp = PrivPub
infFlow {Public} {Public} {Dunno} inp = DunnoPub
infFlow {Public} {Public} {Unused} inp = 0Pub

--      Public <<= Public * Private
--  ==  Public <<= Public

-- BUT

--  -/-> Public <<= Private

infFlow {Public} {Private} {Public} inp = {!!}
infFlow {Public} {Private} {Private} inp = {!!}
infFlow {Public} {Private} {Dunno} inp = {!!}
infFlow {Public} {Private} {Unused} inp = {!!}
infFlow {Public} {Dunno} {Public} inp = {!!}
infFlow {Public} {Dunno} {Private} inp = {!!}
infFlow {Public} {Dunno} {Dunno} inp = {!!}
infFlow {Public} {Dunno} {Unused} inp = {!!}
infFlow {Public} {Unused} {Unused} inp = {!!}
infFlow {Private} {Public} {Public} inp = {!!}
infFlow {Private} {Public} {Private} inp = {!!}
infFlow {Private} {Public} {Dunno} inp = {!!}
infFlow {Private} {Public} {Unused} inp = {!!}
infFlow {Private} {Private} {Private} inp = {!!}
infFlow {Private} {Private} {Unused} inp = {!!}
infFlow {Private} {Dunno} {Private} inp = {!!}
infFlow {Private} {Dunno} {Dunno} inp = {!!}
infFlow {Private} {Dunno} {Unused} inp = {!!}
infFlow {Private} {Unused} {Unused} inp = {!!}
infFlow {Dunno} {Public} {Public} inp = {!!}
infFlow {Dunno} {Public} {Private} inp = {!!}
infFlow {Dunno} {Public} {Dunno} inp = {!!}
infFlow {Dunno} {Public} {Unused} inp = {!!}
infFlow {Dunno} {Private} {Private} inp = {!!}
infFlow {Dunno} {Private} {Dunno} inp = {!!}
infFlow {Dunno} {Private} {Unused} inp = {!!}
infFlow {Dunno} {Dunno} {Private} inp = {!!}
infFlow {Dunno} {Dunno} {Dunno} inp = {!!}
infFlow {Dunno} {Dunno} {Unused} inp = {!!}
infFlow {Dunno} {Unused} {Unused} inp = {!!}
infFlow {Unused} {Public} {Unused} inp = {!!}
infFlow {Unused} {Private} {Unused} inp = {!!}
infFlow {Unused} {Dunno} {Unused} inp = {!!}
infFlow {Unused} {Unused} {Unused} inp = {!!}

--- ALTERNATIVE TRICK

infFlo : {r s adv : Level} -> ¬ (_≤_ levelSemiring (_*R_ levelSemiring r s) adv)
                           -> _≤_ levelSemiring s adv
                           -> ⊥
infFlo {Public} {Public} {Public} negarg (Refl .Public) = negarg (Refl Public)
infFlo {Public} {Public} {Private} negarg arg = negarg arg
infFlo {Public} {Public} {Dunno} negarg arg = negarg arg
infFlo {Public} {Public} {Unused} negarg arg = negarg arg
infFlo {Public} {Private} {Private} negarg (Refl .Private) = negarg PrivPub
infFlo {Public} {Private} {Unused} negarg arg = negarg 0Pub
infFlo {Public} {Dunno} {Private} negarg arg = negarg PrivPub
infFlo {Public} {Dunno} {Dunno} negarg arg = negarg DunnoPub
infFlo {Public} {Dunno} {Unused} negarg arg = negarg 0Pub
infFlo {Public} {Unused} {Unused} negarg arg = negarg arg
infFlo {Private} {Public} {Public} negarg arg = negarg arg
infFlo {Private} {Public} {Private} negarg arg = negarg arg
infFlo {Private} {Public} {Dunno} negarg arg = negarg arg
infFlo {Private} {Public} {Unused} negarg arg = negarg arg
infFlo {Private} {Private} {Private} negarg arg = negarg arg
infFlo {Private} {Private} {Unused} negarg arg = negarg arg
infFlo {Private} {Dunno} {Private} negarg arg = negarg arg
infFlo {Private} {Dunno} {Dunno} negarg arg = negarg arg
infFlo {Private} {Dunno} {Unused} negarg arg = negarg arg
infFlo {Private} {Unused} {Unused} negarg arg = negarg arg
infFlo {Dunno} {Public} {Public} negarg arg = negarg arg
infFlo {Dunno} {Public} {Private} negarg arg = negarg arg
infFlo {Dunno} {Public} {Dunno} negarg arg = negarg arg
infFlo {Dunno} {Public} {Unused} negarg arg = negarg arg
infFlo {Dunno} {Private} {Private} negarg arg = negarg PrivDunno
infFlo {Dunno} {Private} {Unused} negarg arg = negarg 0Dunno
infFlo {Dunno} {Dunno} {Private} negarg arg = negarg arg
infFlo {Dunno} {Dunno} {Dunno} negarg arg = negarg arg
infFlo {Dunno} {Dunno} {Unused} negarg arg = negarg arg
infFlo {Dunno} {Unused} {Unused} negarg arg = negarg arg

-- Public <<= Unused * Public   Public <<= Unused   (false)
-- Public <<= Public (true)

infFlo {Unused} {Public} {Public} negarg (Refl .Public) = {!!}
infFlo {Unused} {Public} {Private} negarg arg = {!!}
infFlo {Unused} {Public} {Dunno} negarg arg = {!!}
infFlo {Unused} {Public} {Unused} negarg arg = {!!}
infFlo {Unused} {Private} {Private} negarg arg = {!!}
infFlo {Unused} {Private} {Unused} negarg arg = {!!}
infFlo {Unused} {Dunno} {Private} negarg arg = {!!}
infFlo {Unused} {Dunno} {Dunno} negarg arg = {!!}
infFlo {Unused} {Dunno} {Unused} negarg arg = {!!}
infFlo {Unused} {Unused} {Unused} negarg arg = {!!}
