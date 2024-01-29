{-# OPTIONS --allow-unsolved-metas #-}

module Levels where

open import Relation.Binary.PropositionalEquality
open import Relation.Nullary
open import Relation.Unary
open import Data.Empty
open import Semiring

open Semiring.Semiring
open Semiring.NonInterferingSemiring
open Semiring.InformationFlowSemiring

open import Data.Maybe
open import Data.Maybe.Properties

-- # Level semiring definition

-- Level elements
data Level : Set where
  Public  : Level
  Private : Level
  Dunno   : Level
  Unused  : Level

-- constructive representation of the ordering (using Granule ordering)
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

-- reify the indexed type ordering
reified : (l : Level) -> (j : Level) -> Dec (Order j l)
reified Public Public   = yes (Refl Public)
reified Public Private  = yes PrivPub
reified Public Dunno    = yes DunnoPub
reified Public Unused   = yes 0Pub
reified Private Public  = no (λ ())
reified Private Private = yes (Refl Private)
reified Private Dunno   = no (λ ())
reified Private Unused  = yes 0Priv
reified Dunno Public    = no (λ ())
reified Dunno Private   = yes PrivDunno
reified Dunno Dunno     = yes (Refl Dunno)
reified Dunno Unused    = yes 0Dunno
reified Unused Public   = no (λ ())
reified Unused Private  = no (λ ())
reified Unused Dunno    = no (λ ())
reified Unused Unused   = yes (Refl Unused)

-- Meet with respect to security ordering
meet : Level -> Level -> Level
meet Unused x        = x
meet x Unused        = x
meet Public x        = Public
meet x Public        = Public
meet Private Private = Private
meet Dunno Private   = Dunno
meet Private Dunno   = Dunno
meet Dunno Dunno     = Dunno

comm* : {r s : Level} -> meet r s ≡ meet s r
comm* {Public} {Public} = refl
comm* {Public} {Private} = refl
comm* {Public} {Dunno} = refl
comm* {Public} {Unused} = refl
comm* {Private} {Public} = refl
comm* {Private} {Private} = refl
comm* {Private} {Dunno} = refl
comm* {Private} {Unused} = refl
comm* {Dunno} {Public} = refl
comm* {Dunno} {Private} = refl
comm* {Dunno} {Dunno} = refl
comm* {Dunno} {Unused} = refl
comm* {Unused} {Public} = refl
comm* {Unused} {Private} = refl
comm* {Unused} {Dunno} = refl
comm* {Unused} {Unused} = refl

-- join with respect to the security ordering
join : Level -> Level -> Level
join Unused x = Unused
join x Unused = Unused
join Private x = Private
join x Private = Private
join Dunno x = Dunno
join x Dunno = Dunno
join Public Public = Public

distrib : {r s t : Level} -> 
         Order (meet (meet r s) (meet r t)) (meet r (meet s t))
distrib {Public} {Public} {Public} = Refl Public
distrib {Public} {Public} {Private} = Refl Public
distrib {Public} {Public} {Dunno} = Refl Public
distrib {Public} {Public} {Unused} = Refl Public
distrib {Public} {Private} {Public} = Refl Public
distrib {Public} {Private} {Private} = Refl Public
distrib {Public} {Private} {Dunno} = Refl Public
distrib {Public} {Private} {Unused} = Refl Public
distrib {Public} {Dunno} {Public} = Refl Public
distrib {Public} {Dunno} {Private} = Refl Public
distrib {Public} {Dunno} {Dunno} = Refl Public
distrib {Public} {Dunno} {Unused} = Refl Public
distrib {Public} {Unused} {Public} = Refl Public
distrib {Public} {Unused} {Private} = Refl Public
distrib {Public} {Unused} {Dunno} = Refl Public
distrib {Public} {Unused} {Unused} = Refl Public
distrib {Private} {Public} {Public} = Refl Public
distrib {Private} {Public} {Private} = Refl Public
distrib {Private} {Public} {Dunno} = Refl Public
distrib {Private} {Public} {Unused} = Refl Public
distrib {Private} {Private} {Public} = Refl Public
distrib {Private} {Private} {Private} = Refl Private
distrib {Private} {Private} {Dunno} = Refl Dunno
distrib {Private} {Private} {Unused} = Refl Private
distrib {Private} {Dunno} {Public} = Refl Public
distrib {Private} {Dunno} {Private} = Refl Dunno
distrib {Private} {Dunno} {Dunno} = Refl Dunno
distrib {Private} {Dunno} {Unused} = Refl Dunno
distrib {Private} {Unused} {Public} = Refl Public
distrib {Private} {Unused} {Private} = Refl Private
distrib {Private} {Unused} {Dunno} = Refl Dunno
distrib {Private} {Unused} {Unused} = Refl Private
distrib {Dunno} {Public} {Public} = Refl Public
distrib {Dunno} {Public} {Private} = Refl Public
distrib {Dunno} {Public} {Dunno} = Refl Public
distrib {Dunno} {Public} {Unused} = Refl Public
distrib {Dunno} {Private} {Public} = Refl Public
distrib {Dunno} {Private} {Private} = Refl Dunno
distrib {Dunno} {Private} {Dunno} = Refl Dunno
distrib {Dunno} {Private} {Unused} = Refl Dunno
distrib {Dunno} {Dunno} {Public} = Refl Public
distrib {Dunno} {Dunno} {Private} = Refl Dunno
distrib {Dunno} {Dunno} {Dunno} = Refl Dunno
distrib {Dunno} {Dunno} {Unused} = Refl Dunno
distrib {Dunno} {Unused} {Public} = Refl Public
distrib {Dunno} {Unused} {Private} = Refl Dunno
distrib {Dunno} {Unused} {Dunno} = Refl Dunno
distrib {Dunno} {Unused} {Unused} = Refl Dunno
distrib {Unused} {Public} {Public} = Refl Public
distrib {Unused} {Public} {Private} = Refl Public
distrib {Unused} {Public} {Dunno} = Refl Public
distrib {Unused} {Public} {Unused} = Refl Public
distrib {Unused} {Private} {Public} = Refl Public
distrib {Unused} {Private} {Private} = Refl Private
distrib {Unused} {Private} {Dunno} = Refl Dunno
distrib {Unused} {Private} {Unused} = Refl Private
distrib {Unused} {Dunno} {Public} = Refl Public
distrib {Unused} {Dunno} {Private} = Refl Dunno
distrib {Unused} {Dunno} {Dunno} = Refl Dunno
distrib {Unused} {Dunno} {Unused} = Refl Dunno
distrib {Unused} {Unused} {Public} = Refl Public
distrib {Unused} {Unused} {Private} = Refl Private
distrib {Unused} {Unused} {Dunno} = Refl Dunno
distrib {Unused} {Unused} {Unused} = Refl Unused

instance
  levelSemiring : Semiring
  grade levelSemiring = Level
  1R levelSemiring    = Private
  0R levelSemiring    = Unused

  -- remember the ordering in the calculus goes the 'opposite way' to Granule but
  -- the above `Order` data type is defined using Granule's direction
  -- *so we need to flip here*
  _≤_ levelSemiring x y = Order y x

  _≤d_ levelSemiring = reified

  _+R_ levelSemiring = meet
  _*R_ levelSemiring = meet


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

  leftAbsorb levelSemiring {Public} = 0Pub
  leftAbsorb levelSemiring {Private} = 0Priv
  leftAbsorb levelSemiring {Dunno} = 0Dunno
  leftAbsorb levelSemiring {Unused} = Refl Unused

  rightAbsorb levelSemiring {Public} = 0Pub
  rightAbsorb levelSemiring {Private} = 0Priv
  rightAbsorb levelSemiring {Dunno} = 0Dunno
  rightAbsorb levelSemiring {Unused} = Refl Unused

  leftUnit* levelSemiring {Public}   = Refl Public
  leftUnit* levelSemiring {Private}  = Refl Private
  leftUnit* levelSemiring {Dunno}    = Refl Dunno
  leftUnit* levelSemiring {Unused}   = 0Priv

  rightUnit* levelSemiring {Public}  = Refl Public
  rightUnit* levelSemiring {Private} = Refl Private
  rightUnit* levelSemiring {Dunno}   = Refl Dunno
  rightUnit* levelSemiring {Unused}  = 0Priv

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

  distrib1 levelSemiring {r} {s} {t} = distrib {r} {s} {t}

  distrib2 levelSemiring {r} {s} {t} 
    rewrite comm* {meet r s} {t} = 
      let x = distrib {t} {r} {s}
          y = subst (\h -> Order (meet h (meet t s)) (meet t (meet r s))) (comm* {t} {r}) x
      in subst (\h -> Order (meet (meet r t) h) (meet t (meet r s))) (comm* {t} {s}) y

  monotone* levelSemiring 0Pub 0Pub = 0Pub
  monotone* levelSemiring 0Pub 0Priv = 0Pub
  monotone* levelSemiring 0Pub PrivPub = PrivPub
  monotone* levelSemiring 0Pub 0Dunno = 0Pub
  monotone* levelSemiring 0Pub PrivDunno = PrivPub
  monotone* levelSemiring 0Pub DunnoPub = DunnoPub
  monotone* levelSemiring 0Pub (Refl Public) = Refl Public
  monotone* levelSemiring 0Pub (Refl Private) = PrivPub
  monotone* levelSemiring 0Pub (Refl Dunno) = DunnoPub
  monotone* levelSemiring 0Pub (Refl Unused) = 0Pub
  monotone* levelSemiring 0Priv 0Pub = 0Pub
  monotone* levelSemiring 0Priv 0Priv = 0Priv
  monotone* levelSemiring 0Priv PrivPub = PrivPub
  monotone* levelSemiring 0Priv 0Dunno = 0Dunno
  monotone* levelSemiring 0Priv PrivDunno = PrivDunno
  monotone* levelSemiring 0Priv DunnoPub = DunnoPub
  monotone* levelSemiring 0Priv (Refl Public) = Refl Public
  monotone* levelSemiring 0Priv (Refl Private) = Refl Private
  monotone* levelSemiring 0Priv (Refl Dunno) = Refl Dunno
  monotone* levelSemiring 0Priv (Refl Unused) = 0Priv
  monotone* levelSemiring PrivPub 0Pub = PrivPub
  monotone* levelSemiring PrivPub 0Priv = PrivPub
  monotone* levelSemiring PrivPub PrivPub = PrivPub
  monotone* levelSemiring PrivPub 0Dunno = PrivPub
  monotone* levelSemiring PrivPub PrivDunno = PrivPub
  monotone* levelSemiring PrivPub DunnoPub = DunnoPub
  monotone* levelSemiring PrivPub (Refl Public) = Refl Public
  monotone* levelSemiring PrivPub (Refl Private) = PrivPub
  monotone* levelSemiring PrivPub (Refl Dunno) = DunnoPub
  monotone* levelSemiring PrivPub (Refl Unused) = PrivPub
  monotone* levelSemiring 0Dunno 0Pub = 0Pub
  monotone* levelSemiring 0Dunno 0Priv = 0Dunno
  monotone* levelSemiring 0Dunno PrivPub = PrivPub
  monotone* levelSemiring 0Dunno 0Dunno = 0Dunno
  monotone* levelSemiring 0Dunno PrivDunno = PrivDunno
  monotone* levelSemiring 0Dunno DunnoPub = DunnoPub
  monotone* levelSemiring 0Dunno (Refl Public) = Refl Public
  monotone* levelSemiring 0Dunno (Refl Private) = PrivDunno
  monotone* levelSemiring 0Dunno (Refl Dunno) = Refl Dunno
  monotone* levelSemiring 0Dunno (Refl Unused) = 0Dunno
  monotone* levelSemiring PrivDunno 0Pub = PrivPub
  monotone* levelSemiring PrivDunno 0Priv = PrivDunno
  monotone* levelSemiring PrivDunno PrivPub = PrivPub
  monotone* levelSemiring PrivDunno 0Dunno = PrivDunno
  monotone* levelSemiring PrivDunno PrivDunno = PrivDunno
  monotone* levelSemiring PrivDunno DunnoPub = DunnoPub
  monotone* levelSemiring PrivDunno (Refl Public) = Refl Public
  monotone* levelSemiring PrivDunno (Refl Private) = PrivDunno
  monotone* levelSemiring PrivDunno (Refl Dunno) = Refl Dunno
  monotone* levelSemiring PrivDunno (Refl Unused) = PrivDunno
  monotone* levelSemiring DunnoPub 0Pub = DunnoPub
  monotone* levelSemiring DunnoPub 0Priv = DunnoPub
  monotone* levelSemiring DunnoPub PrivPub = DunnoPub
  monotone* levelSemiring DunnoPub 0Dunno = DunnoPub
  monotone* levelSemiring DunnoPub PrivDunno = DunnoPub
  monotone* levelSemiring DunnoPub DunnoPub = DunnoPub
  monotone* levelSemiring DunnoPub (Refl Public) = Refl Public
  monotone* levelSemiring DunnoPub (Refl Private) = DunnoPub
  monotone* levelSemiring DunnoPub (Refl Dunno) = DunnoPub
  monotone* levelSemiring DunnoPub (Refl Unused) = DunnoPub
  monotone* levelSemiring (Refl Public) 0Pub = Refl Public
  monotone* levelSemiring (Refl Private) 0Pub = PrivPub
  monotone* levelSemiring (Refl Dunno) 0Pub = DunnoPub
  monotone* levelSemiring (Refl Unused) 0Pub = 0Pub
  monotone* levelSemiring (Refl Public) 0Priv = Refl Public
  monotone* levelSemiring (Refl Private) 0Priv = Refl Private
  monotone* levelSemiring (Refl Dunno) 0Priv = Refl Dunno
  monotone* levelSemiring (Refl Unused) 0Priv = 0Priv
  monotone* levelSemiring (Refl Public) PrivPub = Refl Public
  monotone* levelSemiring (Refl Private) PrivPub = PrivPub
  monotone* levelSemiring (Refl Dunno) PrivPub = DunnoPub
  monotone* levelSemiring (Refl Unused) PrivPub = PrivPub
  monotone* levelSemiring (Refl Public) 0Dunno = Refl Public
  monotone* levelSemiring (Refl Private) 0Dunno = PrivDunno
  monotone* levelSemiring (Refl Dunno) 0Dunno = Refl Dunno
  monotone* levelSemiring (Refl Unused) 0Dunno = 0Dunno
  monotone* levelSemiring (Refl Public) PrivDunno = Refl Public
  monotone* levelSemiring (Refl Private) PrivDunno = PrivDunno
  monotone* levelSemiring (Refl Dunno) PrivDunno = Refl Dunno
  monotone* levelSemiring (Refl Unused) PrivDunno = PrivDunno
  monotone* levelSemiring (Refl Public) DunnoPub = Refl Public
  monotone* levelSemiring (Refl Private) DunnoPub = DunnoPub
  monotone* levelSemiring (Refl Dunno) DunnoPub = DunnoPub
  monotone* levelSemiring (Refl Unused) DunnoPub = DunnoPub
  monotone* levelSemiring (Refl x) (Refl y) = Refl (meet x y)

  monotone+ levelSemiring {Public} {Public} {Public} {Public} pre1 pre2 = Refl Public
  monotone+ levelSemiring {Public} {Public} {Public} {Private} pre1 pre2 = Refl Public
  monotone+ levelSemiring {Public} {Public} {Public} {Dunno} pre1 pre2 = Refl Public
  monotone+ levelSemiring {Public} {Public} {Public} {Unused} pre1 pre2 = Refl Public
  monotone+ levelSemiring {Public} {Public} {Private} {Private} pre1 pre2 = Refl Public
  monotone+ levelSemiring {Public} {Public} {Private} {Unused} pre1 pre2 = Refl Public
  monotone+ levelSemiring {Public} {Public} {Dunno} {Private} pre1 pre2 = Refl Public
  monotone+ levelSemiring {Public} {Public} {Dunno} {Dunno} pre1 pre2 = Refl Public
  monotone+ levelSemiring {Public} {Public} {Dunno} {Unused} pre1 pre2 = Refl Public
  monotone+ levelSemiring {Public} {Public} {Unused} {Unused} pre1 pre2 = Refl Public
  monotone+ levelSemiring {Public} {Private} {Public} {Public} pre1 pre2 = Refl Public
  monotone+ levelSemiring {Public} {Private} {Public} {Private} pre1 pre2 = PrivPub
  monotone+ levelSemiring {Public} {Private} {Public} {Dunno} pre1 pre2 = DunnoPub
  monotone+ levelSemiring {Public} {Private} {Public} {Unused} pre1 pre2 = PrivPub
  monotone+ levelSemiring {Public} {Private} {Private} {Private} pre1 pre2 = PrivPub
  monotone+ levelSemiring {Public} {Private} {Private} {Unused} pre1 pre2 = PrivPub
  monotone+ levelSemiring {Public} {Private} {Dunno} {Private} pre1 pre2 = PrivPub
  monotone+ levelSemiring {Public} {Private} {Dunno} {Dunno} pre1 pre2 = DunnoPub
  monotone+ levelSemiring {Public} {Private} {Dunno} {Unused} pre1 pre2 = PrivPub
  monotone+ levelSemiring {Public} {Private} {Unused} {Unused} pre1 pre2 = PrivPub
  monotone+ levelSemiring {Public} {Dunno} {Public} {Public} pre1 pre2 = Refl Public
  monotone+ levelSemiring {Public} {Dunno} {Public} {Private} pre1 pre2 = DunnoPub
  monotone+ levelSemiring {Public} {Dunno} {Public} {Dunno} pre1 pre2 = DunnoPub
  monotone+ levelSemiring {Public} {Dunno} {Public} {Unused} pre1 pre2 = DunnoPub
  monotone+ levelSemiring {Public} {Dunno} {Private} {Private} pre1 pre2 = DunnoPub
  monotone+ levelSemiring {Public} {Dunno} {Private} {Unused} pre1 pre2 = DunnoPub
  monotone+ levelSemiring {Public} {Dunno} {Dunno} {Private} pre1 pre2 = DunnoPub
  monotone+ levelSemiring {Public} {Dunno} {Dunno} {Dunno} pre1 pre2 = DunnoPub
  monotone+ levelSemiring {Public} {Dunno} {Dunno} {Unused} pre1 pre2 = DunnoPub
  monotone+ levelSemiring {Public} {Dunno} {Unused} {Unused} pre1 pre2 = DunnoPub
  monotone+ levelSemiring {Public} {Unused} {Public} {Public} pre1 pre2 = Refl Public
  monotone+ levelSemiring {Public} {Unused} {Public} {Private} pre1 pre2 = PrivPub
  monotone+ levelSemiring {Public} {Unused} {Public} {Dunno} pre1 pre2 = DunnoPub
  monotone+ levelSemiring {Public} {Unused} {Public} {Unused} pre1 pre2 = 0Pub
  monotone+ levelSemiring {Public} {Unused} {Private} {Private} pre1 pre2 = PrivPub
  monotone+ levelSemiring {Public} {Unused} {Private} {Unused} pre1 pre2 = 0Pub
  monotone+ levelSemiring {Public} {Unused} {Dunno} {Private} pre1 pre2 = PrivPub
  monotone+ levelSemiring {Public} {Unused} {Dunno} {Dunno} pre1 pre2 = DunnoPub
  monotone+ levelSemiring {Public} {Unused} {Dunno} {Unused} pre1 pre2 = 0Pub
  monotone+ levelSemiring {Public} {Unused} {Unused} {Unused} pre1 pre2 = 0Pub
  monotone+ levelSemiring {Private} {Private} {Public} {Public} pre1 pre2 = Refl Public
  monotone+ levelSemiring {Private} {Private} {Public} {Private} pre1 pre2 = PrivPub
  monotone+ levelSemiring {Private} {Private} {Public} {Dunno} pre1 pre2 = DunnoPub
  monotone+ levelSemiring {Private} {Private} {Public} {Unused} pre1 pre2 = PrivPub
  monotone+ levelSemiring {Private} {Private} {Private} {Private} pre1 pre2 = Refl Private
  monotone+ levelSemiring {Private} {Private} {Private} {Unused} pre1 pre2 = Refl Private
  monotone+ levelSemiring {Private} {Private} {Dunno} {Private} pre1 pre2 = PrivDunno
  monotone+ levelSemiring {Private} {Private} {Dunno} {Dunno} pre1 pre2 = Refl Dunno
  monotone+ levelSemiring {Private} {Private} {Dunno} {Unused} pre1 pre2 = PrivDunno
  monotone+ levelSemiring {Private} {Private} {Unused} {Unused} pre1 pre2 = Refl Private
  monotone+ levelSemiring {Private} {Unused} {Public} {Public} pre1 pre2 = Refl Public
  monotone+ levelSemiring {Private} {Unused} {Public} {Private} pre1 pre2 = PrivPub
  monotone+ levelSemiring {Private} {Unused} {Public} {Dunno} pre1 pre2 = DunnoPub
  monotone+ levelSemiring {Private} {Unused} {Public} {Unused} pre1 pre2 = 0Pub
  monotone+ levelSemiring {Private} {Unused} {Private} {Private} pre1 pre2 = Refl Private
  monotone+ levelSemiring {Private} {Unused} {Private} {Unused} pre1 pre2 = 0Priv
  monotone+ levelSemiring {Private} {Unused} {Dunno} {Private} pre1 pre2 = PrivDunno
  monotone+ levelSemiring {Private} {Unused} {Dunno} {Dunno} pre1 pre2 = Refl Dunno
  monotone+ levelSemiring {Private} {Unused} {Dunno} {Unused} pre1 pre2 = 0Dunno
  monotone+ levelSemiring {Private} {Unused} {Unused} {Unused} pre1 pre2 = 0Priv
  monotone+ levelSemiring {Dunno} {Private} {Public} {Public} pre1 pre2 = Refl Public
  monotone+ levelSemiring {Dunno} {Private} {Public} {Private} pre1 pre2 = PrivPub
  monotone+ levelSemiring {Dunno} {Private} {Public} {Dunno} pre1 pre2 = DunnoPub
  monotone+ levelSemiring {Dunno} {Private} {Public} {Unused} pre1 pre2 = PrivPub
  monotone+ levelSemiring {Dunno} {Private} {Private} {Private} pre1 pre2 = PrivDunno
  monotone+ levelSemiring {Dunno} {Private} {Private} {Unused} pre1 pre2 = PrivDunno
  monotone+ levelSemiring {Dunno} {Private} {Dunno} {Private} pre1 pre2 = PrivDunno
  monotone+ levelSemiring {Dunno} {Private} {Dunno} {Dunno} pre1 pre2 = Refl Dunno
  monotone+ levelSemiring {Dunno} {Private} {Dunno} {Unused} pre1 pre2 = PrivDunno
  monotone+ levelSemiring {Dunno} {Private} {Unused} {Unused} pre1 pre2 = PrivDunno
  monotone+ levelSemiring {Dunno} {Dunno} {Public} {Public} pre1 pre2 = Refl Public
  monotone+ levelSemiring {Dunno} {Dunno} {Public} {Private} pre1 pre2 = DunnoPub
  monotone+ levelSemiring {Dunno} {Dunno} {Public} {Dunno} pre1 pre2 = DunnoPub
  monotone+ levelSemiring {Dunno} {Dunno} {Public} {Unused} pre1 pre2 = DunnoPub
  monotone+ levelSemiring {Dunno} {Dunno} {Private} {Private} pre1 pre2 = Refl Dunno
  monotone+ levelSemiring {Dunno} {Dunno} {Private} {Unused} pre1 pre2 = Refl Dunno
  monotone+ levelSemiring {Dunno} {Dunno} {Dunno} {Private} pre1 pre2 = Refl Dunno
  monotone+ levelSemiring {Dunno} {Dunno} {Dunno} {Dunno} pre1 pre2 = Refl Dunno
  monotone+ levelSemiring {Dunno} {Dunno} {Dunno} {Unused} pre1 pre2 = Refl Dunno
  monotone+ levelSemiring {Dunno} {Dunno} {Unused} {Unused} pre1 pre2 = Refl Dunno
  monotone+ levelSemiring {Dunno} {Unused} {Public} {Public} pre1 pre2 = Refl Public
  monotone+ levelSemiring {Dunno} {Unused} {Public} {Private} pre1 pre2 = PrivPub
  monotone+ levelSemiring {Dunno} {Unused} {Public} {Dunno} pre1 pre2 = DunnoPub
  monotone+ levelSemiring {Dunno} {Unused} {Public} {Unused} pre1 pre2 = 0Pub
  monotone+ levelSemiring {Dunno} {Unused} {Private} {Private} pre1 pre2 = PrivDunno
  monotone+ levelSemiring {Dunno} {Unused} {Private} {Unused} pre1 pre2 = 0Dunno
  monotone+ levelSemiring {Dunno} {Unused} {Dunno} {Private} pre1 pre2 = PrivDunno
  monotone+ levelSemiring {Dunno} {Unused} {Dunno} {Dunno} pre1 pre2 = Refl Dunno
  monotone+ levelSemiring {Dunno} {Unused} {Dunno} {Unused} pre1 pre2 = 0Dunno
  monotone+ levelSemiring {Dunno} {Unused} {Unused} {Unused} pre1 pre2 = 0Dunno
  monotone+ levelSemiring {Unused} {Unused} {Public} {Public} pre1 pre2 = Refl Public
  monotone+ levelSemiring {Unused} {Unused} {Public} {Private} pre1 pre2 = PrivPub
  monotone+ levelSemiring {Unused} {Unused} {Public} {Dunno} pre1 pre2 = DunnoPub
  monotone+ levelSemiring {Unused} {Unused} {Public} {Unused} pre1 pre2 = 0Pub
  monotone+ levelSemiring {Unused} {Unused} {Private} {Private} pre1 pre2 = Refl Private
  monotone+ levelSemiring {Unused} {Unused} {Private} {Unused} pre1 pre2 = 0Priv
  monotone+ levelSemiring {Unused} {Unused} {Dunno} {Private} pre1 pre2 = PrivDunno
  monotone+ levelSemiring {Unused} {Unused} {Dunno} {Dunno} pre1 pre2 = Refl Dunno
  monotone+ levelSemiring {Unused} {Unused} {Dunno} {Unused} pre1 pre2 = 0Dunno
  monotone+ levelSemiring {Unused} {Unused} {Unused} {Unused} pre1 pre2 = Refl Unused

  reflexive≤ levelSemiring {r} = Refl r

  transitive≤ levelSemiring {Public} {Public} {Public} inp1 inp2 = Refl Public
  transitive≤ levelSemiring {Public} {Public} {Private} inp1 inp2 = PrivPub
  transitive≤ levelSemiring {Public} {Public} {Dunno} inp1 inp2 = DunnoPub
  transitive≤ levelSemiring {Public} {Public} {Unused} inp1 inp2 = 0Pub
  transitive≤ levelSemiring {Public} {Private} {Public} inp1 inp2 = Refl Public
  transitive≤ levelSemiring {Public} {Private} {Private} inp1 inp2 = PrivPub
  transitive≤ levelSemiring {Public} {Private} {Dunno} inp1 inp2 = DunnoPub
  transitive≤ levelSemiring {Public} {Private} {Unused} inp1 inp2 = 0Pub
  transitive≤ levelSemiring {Public} {Dunno} {Public} inp1 inp2 = Refl Public
  transitive≤ levelSemiring {Public} {Dunno} {Private} inp1 inp2 = PrivPub
  transitive≤ levelSemiring {Public} {Dunno} {Dunno} inp1 inp2 = DunnoPub
  transitive≤ levelSemiring {Public} {Dunno} {Unused} inp1 inp2 = 0Pub
  transitive≤ levelSemiring {Public} {Unused} {Public} inp1 inp2 = Refl Public
  transitive≤ levelSemiring {Public} {Unused} {Private} inp1 inp2 = PrivPub
  transitive≤ levelSemiring {Public} {Unused} {Dunno} inp1 inp2 = DunnoPub
  transitive≤ levelSemiring {Public} {Unused} {Unused} inp1 inp2 = 0Pub
  transitive≤ levelSemiring {Private} {Public} {Public} () inp2
  transitive≤ levelSemiring {Private} {Public} {Private} inp1 inp2 = Refl Private
  transitive≤ levelSemiring {Private} {Public} {Dunno} () inp2
  transitive≤ levelSemiring {Private} {Public} {Unused} inp1 inp2 = 0Priv
  transitive≤ levelSemiring {Private} {Private} {Public} inp1 ()
  transitive≤ levelSemiring {Private} {Private} {Private} inp1 inp2 = Refl Private
  transitive≤ levelSemiring {Private} {Private} {Dunno} inp1 ()
  transitive≤ levelSemiring {Private} {Private} {Unused} inp1 inp2 = 0Priv
  transitive≤ levelSemiring {Private} {Dunno} {Public} inp1 ()
  transitive≤ levelSemiring {Private} {Dunno} {Private} inp1 inp2 = Refl Private
  transitive≤ levelSemiring {Private} {Dunno} {Dunno} () inp2
  transitive≤ levelSemiring {Private} {Dunno} {Unused} inp1 inp2 = 0Priv
  transitive≤ levelSemiring {Private} {Unused} {Public} inp1 ()
  transitive≤ levelSemiring {Private} {Unused} {Private} inp1 inp2 = Refl Private
  transitive≤ levelSemiring {Private} {Unused} {Dunno} inp1 ()
  transitive≤ levelSemiring {Private} {Unused} {Unused} inp1 inp2 = 0Priv
  transitive≤ levelSemiring {Dunno} {Public} {Public} () inp2
  transitive≤ levelSemiring {Dunno} {Public} {Private} () inp2
  transitive≤ levelSemiring {Dunno} {Public} {Dunno} inp1 inp2 = Refl Dunno
  transitive≤ levelSemiring {Dunno} {Public} {Unused} inp1 inp2 = 0Dunno
  transitive≤ levelSemiring {Dunno} {Private} {Public} inp1 ()
  transitive≤ levelSemiring {Dunno} {Private} {Private} inp1 inp2 = PrivDunno
  transitive≤ levelSemiring {Dunno} {Private} {Dunno} inp1 inp2 = Refl Dunno
  transitive≤ levelSemiring {Dunno} {Private} {Unused} inp1 inp2 = 0Dunno
  transitive≤ levelSemiring {Dunno} {Dunno} {Public} inp1 ()
  transitive≤ levelSemiring {Dunno} {Dunno} {Private} inp1 inp2 = PrivDunno
  transitive≤ levelSemiring {Dunno} {Dunno} {Dunno} inp1 inp2 = Refl Dunno
  transitive≤ levelSemiring {Dunno} {Dunno} {Unused} inp1 inp2 = 0Dunno
  transitive≤ levelSemiring {Dunno} {Unused} {Public} inp1 ()
  transitive≤ levelSemiring {Dunno} {Unused} {Private} inp1 inp2 = PrivDunno
  transitive≤ levelSemiring {Dunno} {Unused} {Dunno} inp1 inp2 = Refl Dunno
  transitive≤ levelSemiring {Dunno} {Unused} {Unused} inp1 inp2 = 0Dunno
  transitive≤ levelSemiring {Unused} {Public} {t} () inp2
  transitive≤ levelSemiring {Unused} {Private} {t} () inp2
  transitive≤ levelSemiring {Unused} {Dunno} {t} () inp2
  transitive≤ levelSemiring {Unused} {Unused} {Unused} inp1 inp2 = Refl Unused

instance
  levelIFstructure : InformationFlowSemiring levelSemiring

  default levelIFstructure = Dunno

  _#_ levelIFstructure r s = join r s

  comm# levelIFstructure {Public} {Public} = refl
  comm# levelIFstructure {Public} {Private} = refl
  comm# levelIFstructure {Public} {Dunno} = refl
  comm# levelIFstructure {Public} {Unused} = refl
  comm# levelIFstructure {Private} {Public} = refl
  comm# levelIFstructure {Private} {Private} = refl
  comm# levelIFstructure {Private} {Dunno} = refl
  comm# levelIFstructure {Private} {Unused} = refl
  comm# levelIFstructure {Dunno} {Public} = refl
  comm# levelIFstructure {Dunno} {Private} = refl
  comm# levelIFstructure {Dunno} {Dunno} = refl
  comm# levelIFstructure {Dunno} {Unused} = refl
  comm# levelIFstructure {Unused} {Public} = refl
  comm# levelIFstructure {Unused} {Private} = refl
  comm# levelIFstructure {Unused} {Dunno} = refl
  comm# levelIFstructure {Unused} {Unused} = refl

  assoc# levelIFstructure {Public} {Public} {Public} = refl
  assoc# levelIFstructure {Public} {Public} {Private} = refl
  assoc# levelIFstructure {Public} {Public} {Dunno} = refl
  assoc# levelIFstructure {Public} {Public} {Unused} = refl
  assoc# levelIFstructure {Public} {Private} {t} = {!   !}
  assoc# levelIFstructure {Public} {Dunno} {Public} = refl
  assoc# levelIFstructure {Public} {Dunno} {Private} = refl
  assoc# levelIFstructure {Public} {Dunno} {Dunno} = refl
  assoc# levelIFstructure {Public} {Dunno} {Unused} = refl
  assoc# levelIFstructure {Public} {Unused} {Public} = refl
  assoc# levelIFstructure {Public} {Unused} {Private} = refl
  assoc# levelIFstructure {Public} {Unused} {Dunno} = refl
  assoc# levelIFstructure {Public} {Unused} {Unused} = refl
  assoc# levelIFstructure {Private} {s} {t} = {!   !}
  assoc# levelIFstructure {Dunno} {Public} {Public} = refl
  assoc# levelIFstructure {Dunno} {Public} {Private} = refl
  assoc# levelIFstructure {Dunno} {Public} {Dunno} = refl
  assoc# levelIFstructure {Dunno} {Public} {Unused} = refl
  assoc# levelIFstructure {Dunno} {Private} {t} = {!   !}
  assoc# levelIFstructure {Dunno} {Dunno} {Public} = refl
  assoc# levelIFstructure {Dunno} {Dunno} {Private} = refl
  assoc# levelIFstructure {Dunno} {Dunno} {Dunno} = refl
  assoc# levelIFstructure {Dunno} {Dunno} {Unused} = refl
  assoc# levelIFstructure {Dunno} {Unused} {Public} = refl
  assoc# levelIFstructure {Dunno} {Unused} {Private} = refl
  assoc# levelIFstructure {Dunno} {Unused} {Dunno} = refl
  assoc# levelIFstructure {Dunno} {Unused} {Unused} = refl
  assoc# levelIFstructure {Unused} {Public} {Public} = refl
  assoc# levelIFstructure {Unused} {Public} {Private} = refl
  assoc# levelIFstructure {Unused} {Public} {Dunno} = refl
  assoc# levelIFstructure {Unused} {Public} {Unused} = refl
  assoc# levelIFstructure {Unused} {Private} {t} = refl
  assoc# levelIFstructure {Unused} {Dunno} {Public} = refl
  assoc# levelIFstructure {Unused} {Dunno} {Private} = refl
  assoc# levelIFstructure {Unused} {Dunno} {Dunno} = refl
  assoc# levelIFstructure {Unused} {Dunno} {Unused} = refl
  assoc# levelIFstructure {Unused} {Unused} {Public} = refl
  assoc# levelIFstructure {Unused} {Unused} {Private} = refl
  assoc# levelIFstructure {Unused} {Unused} {Dunno} = refl
  assoc# levelIFstructure {Unused} {Unused} {Unused} = refl

  idem# levelIFstructure {Public}  = refl
  idem# levelIFstructure {Private} = refl
  idem# levelIFstructure {Dunno}   = refl
  idem# levelIFstructure {Unused}  = refl

  idem* levelIFstructure {Public} = refl
  idem* levelIFstructure {Private} = refl
  idem* levelIFstructure {Dunno} = refl
  idem* levelIFstructure {Unused} = refl

  
  timesLeft levelIFstructure {Public} {Public} {Public} (Refl .Public) = Refl Public
  timesLeft levelIFstructure {Public} {Public} {Private} PrivPub = PrivPub
  timesLeft levelIFstructure {Public} {Public} {Dunno} DunnoPub = DunnoPub
  timesLeft levelIFstructure {Public} {Public} {Unused} 0Pub = 0Pub
  timesLeft levelIFstructure {Public} {Private} {Public} (Refl .Public) = Refl Public
  timesLeft levelIFstructure {Public} {Private} {Private} PrivPub = PrivPub
  timesLeft levelIFstructure {Public} {Private} {Dunno} DunnoPub = DunnoPub
  timesLeft levelIFstructure {Public} {Private} {Unused} 0Pub = 0Pub
  timesLeft levelIFstructure {Public} {Dunno} {Public} (Refl .Public) = Refl Public
  timesLeft levelIFstructure {Public} {Dunno} {Private} PrivPub = PrivPub
  timesLeft levelIFstructure {Public} {Dunno} {Dunno} DunnoPub = DunnoPub
  timesLeft levelIFstructure {Public} {Dunno} {Unused} 0Pub = 0Pub
  timesLeft levelIFstructure {Public} {Unused} {Public} (Refl .Public) = Refl Public
  timesLeft levelIFstructure {Public} {Unused} {Private} PrivPub = PrivPub
  timesLeft levelIFstructure {Public} {Unused} {Dunno} DunnoPub = DunnoPub
  timesLeft levelIFstructure {Public} {Unused} {Unused} 0Pub = 0Pub
  timesLeft levelIFstructure {Private} {Public} {Public} ()
  timesLeft levelIFstructure {Private} {Public} {Private} (Refl .Private) = PrivPub
  timesLeft levelIFstructure {Private} {Public} {Dunno} ()
  timesLeft levelIFstructure {Private} {Public} {Unused} 0Priv = 0Pub
  timesLeft levelIFstructure {Private} {Private} {Public} ()
  timesLeft levelIFstructure {Private} {Private} {Private} (Refl .Private) = Refl Private
  timesLeft levelIFstructure {Private} {Private} {Dunno} ()
  timesLeft levelIFstructure {Private} {Private} {Unused} 0Priv = 0Priv
  timesLeft levelIFstructure {Private} {Dunno} {Public} ()
  timesLeft levelIFstructure {Private} {Dunno} {Private} (Refl .Private) = PrivDunno
  timesLeft levelIFstructure {Private} {Dunno} {Dunno} ()
  timesLeft levelIFstructure {Private} {Dunno} {Unused} 0Priv = 0Dunno
  timesLeft levelIFstructure {Private} {Unused} {Public} ()
  timesLeft levelIFstructure {Private} {Unused} {Private} (Refl .Private) = Refl Private
  timesLeft levelIFstructure {Private} {Unused} {Dunno} ()
  timesLeft levelIFstructure {Private} {Unused} {Unused} 0Priv = 0Priv
  timesLeft levelIFstructure {Dunno} {Public} {Public} ()
  timesLeft levelIFstructure {Dunno} {Public} {Private} PrivDunno = PrivPub
  timesLeft levelIFstructure {Dunno} {Public} {Dunno} (Refl .Dunno) = DunnoPub
  timesLeft levelIFstructure {Dunno} {Public} {Unused} 0Dunno = 0Pub
  timesLeft levelIFstructure {Dunno} {Private} {Public} ()
  timesLeft levelIFstructure {Dunno} {Private} {Private} PrivDunno = PrivDunno
  timesLeft levelIFstructure {Dunno} {Private} {Dunno} (Refl .Dunno) = Refl Dunno
  timesLeft levelIFstructure {Dunno} {Private} {Unused} 0Dunno = 0Dunno
  timesLeft levelIFstructure {Dunno} {Dunno} {Public} ()
  timesLeft levelIFstructure {Dunno} {Dunno} {Private} PrivDunno = PrivDunno
  timesLeft levelIFstructure {Dunno} {Dunno} {Dunno} (Refl .Dunno) = Refl Dunno
  timesLeft levelIFstructure {Dunno} {Dunno} {Unused} 0Dunno = 0Dunno
  timesLeft levelIFstructure {Dunno} {Unused} {Public} ()
  timesLeft levelIFstructure {Dunno} {Unused} {Private} PrivDunno = PrivDunno
  timesLeft levelIFstructure {Dunno} {Unused} {Dunno} (Refl .Dunno) = Refl Dunno
  timesLeft levelIFstructure {Dunno} {Unused} {Unused} 0Dunno = 0Dunno
  timesLeft levelIFstructure {Unused} {Public} {Public} ()
  timesLeft levelIFstructure {Unused} {Public} {Private} ()
  timesLeft levelIFstructure {Unused} {Public} {Dunno} ()
  timesLeft levelIFstructure {Unused} {Public} {Unused} (Refl .Unused) = 0Pub
  timesLeft levelIFstructure {Unused} {Private} {Public} ()
  timesLeft levelIFstructure {Unused} {Private} {Private} ()
  timesLeft levelIFstructure {Unused} {Private} {Dunno} ()
  timesLeft levelIFstructure {Unused} {Private} {Unused} (Refl .Unused) = 0Priv
  timesLeft levelIFstructure {Unused} {Dunno} {Public} ()
  timesLeft levelIFstructure {Unused} {Dunno} {Private} ()
  timesLeft levelIFstructure {Unused} {Dunno} {Dunno} ()
  timesLeft levelIFstructure {Unused} {Dunno} {Unused} (Refl .Unused) = 0Dunno
  timesLeft levelIFstructure {Unused} {Unused} {Public} ()
  timesLeft levelIFstructure {Unused} {Unused} {Private} ()
  timesLeft levelIFstructure {Unused} {Unused} {Dunno} ()
  timesLeft levelIFstructure {Unused} {Unused} {Unused} (Refl .Unused) = Refl Unused

  com* levelIFstructure = comm*

  leftAbsorbSub levelIFstructure {r} = {!   !}
  rightAbsorbSub levelIFstructure {r} = {!   !}

{-
Things that do not hold

hm : {s g adv : Level}
   -> _≤_ levelSemiring s adv
   -> _≤_ levelSemiring (_*R_ levelSemiring g s) adv
hm {.Public} {Public} {.Unused} 0Pub = 0Pub
hm {.Public} {Private} {.Unused} 0Pub = 0Pub
hm {.Public} {Dunno} {.Unused} 0Pub = 0Pub
hm {.Public} {Unused} {.Unused} 0Pub = Refl Unused
hm {.Private} {Public} {.Unused} 0Priv = 0Pub
hm {.Private} {Private} {.Unused} 0Priv = 0Priv
hm {.Private} {Dunno} {.Unused} 0Priv = 0Dunno
hm {.Private} {Unused} {.Unused} 0Priv = Refl Unused
hm {.Public} {Public} {.Private} PrivPub = PrivPub
hm {.Public} {Private} {.Private} PrivPub = PrivPub
hm {.Public} {Dunno} {.Private} PrivPub = PrivPub
-- Public <= Private  (Lo <= Hi)
-- but
-- Public * Unused <= Private
-- Unused <= Private (0 <= Hi)
-- is false as this means Hi [= 0


ohah'' : {r g adv : Level}
    -> _≤_ levelSemiring r adv
    -> _≤_ levelSemiring (_*R_ levelSemiring r g) adv
    -> ¬ _≤_ levelSemiring g adv
    -> ⊥
ohah'' {Private} {Public} {Public} () pre2 npre3
ohah'' {Public} {Private} {Public} (Refl .Public) (Refl .Public) npre3 = npre3 {!!}
ohah'' {a} {b} {c} pre1 pre2 npre3 = {!!}


ohah : {r g adv : Level}
    -> _≤_ levelSemiring r adv
    -> _≤_ levelSemiring (_*R_ levelSemiring r g) adv
    -> _≤_ levelSemiring g adv
-}

check : {s1 s2 adv : Level}
      -> _≤_ levelSemiring s1 adv
      -> _≤_ levelSemiring (_+R_ levelSemiring s1 s2) adv
check {Public} {Public} {Public} (Refl .Public) = Refl Public
check {Public} {Public} {Private} PrivPub = PrivPub
check {Public} {Public} {Dunno} DunnoPub = DunnoPub
check {Public} {Public} {Unused} 0Pub = 0Pub
check {Public} {Private} {Public} (Refl .Public) = Refl Public
check {Public} {Private} {Private} PrivPub = PrivPub
check {Public} {Private} {Dunno} DunnoPub = DunnoPub
check {Public} {Private} {Unused} 0Pub = 0Pub
check {Public} {Dunno} {Public} (Refl .Public) = Refl Public
check {Public} {Dunno} {Private} PrivPub = PrivPub
check {Public} {Dunno} {Dunno} DunnoPub = DunnoPub
check {Public} {Dunno} {Unused} 0Pub = 0Pub
check {Public} {Unused} {Public} (Refl .Public) = Refl Public
check {Public} {Unused} {Private} PrivPub = PrivPub
check {Public} {Unused} {Dunno} DunnoPub = DunnoPub
check {Public} {Unused} {Unused} 0Pub = 0Pub
check {Private} {Public} {Public} ()
check {Private} {Public} {Private} (Refl .Private) = PrivPub
check {Private} {Public} {Dunno} ()
check {Private} {Public} {Unused} 0Priv = 0Pub
check {Private} {Private} {Public} ()
check {Private} {Private} {Private} (Refl .Private) = Refl Private
check {Private} {Private} {Dunno} ()
check {Private} {Private} {Unused} 0Priv = 0Priv
check {Private} {Dunno} {Public} ()
check {Private} {Dunno} {Private} (Refl .Private) = PrivDunno
check {Private} {Dunno} {Dunno} ()
check {Private} {Dunno} {Unused} 0Priv = 0Dunno
check {Private} {Unused} {Public} ()
check {Private} {Unused} {Private} (Refl .Private) = Refl Private
check {Private} {Unused} {Dunno} ()
check {Private} {Unused} {Unused} 0Priv = 0Priv
check {Dunno} {Public} {Public} ()
check {Dunno} {Public} {Private} PrivDunno = PrivPub
check {Dunno} {Public} {Dunno} (Refl .Dunno) = DunnoPub
check {Dunno} {Public} {Unused} 0Dunno = 0Pub
check {Dunno} {Private} {Public} ()
check {Dunno} {Private} {Private} PrivDunno = PrivDunno
check {Dunno} {Private} {Dunno} (Refl .Dunno) = Refl Dunno
check {Dunno} {Private} {Unused} 0Dunno = 0Dunno
check {Dunno} {Dunno} {Public} ()
check {Dunno} {Dunno} {Private} PrivDunno = PrivDunno
check {Dunno} {Dunno} {Dunno} (Refl .Dunno) = Refl Dunno
check {Dunno} {Dunno} {Unused} 0Dunno = 0Dunno
check {Dunno} {Unused} {Public} ()
check {Dunno} {Unused} {Private} PrivDunno = PrivDunno
check {Dunno} {Unused} {Dunno} (Refl .Dunno) = Refl Dunno
check {Dunno} {Unused} {Unused} 0Dunno = 0Dunno
check {Unused} {Public} {Public} ()
check {Unused} {Public} {Private} ()
check {Unused} {Public} {Dunno} ()
check {Unused} {Public} {Unused} (Refl .Unused) = 0Pub
check {Unused} {Private} {Public} ()
check {Unused} {Private} {Private} ()
check {Unused} {Private} {Dunno} ()
check {Unused} {Private} {Unused} (Refl .Unused) = 0Priv
check {Unused} {Dunno} {Public} ()
check {Unused} {Dunno} {Private} ()
check {Unused} {Dunno} {Dunno} ()
check {Unused} {Dunno} {Unused} (Refl .Unused) = 0Dunno
check {Unused} {Unused} {Public} ()
check {Unused} {Unused} {Private} ()
check {Unused} {Unused} {Dunno} ()
check {Unused} {Unused} {Unused} (Refl .Unused) = Refl Unused
