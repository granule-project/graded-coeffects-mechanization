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

-- # Level semiring definition

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

instance
  levelSemiring : Semiring
  grade levelSemiring = Level
  1R levelSemiring      = Private
  0R levelSemiring      = Unused

  -- remember the ordering in the calculus goes the 'opposite way' to Granule but
  -- the above `Order` data type is defined using Granule's direction
  -- *so we need to flip here*
  _≤_ levelSemiring x y = Order y x

  _≤d_ levelSemiring = reified

  -- unit property
  _+R_ levelSemiring Unused x = x
  _+R_ levelSemiring x Unused = x
  -- Hack for Private
  _+R_ levelSemiring Dunno Private = Dunno
  _+R_ levelSemiring Private Dunno = Dunno
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
  levelSemiringNonInterfering : NonInterferingSemiring levelSemiring
  oneIsBottom levelSemiringNonInterfering {r} = {!!}

  antisymmetry levelSemiringNonInterfering {Public} {Public} (Refl .Public) pre2 = refl
  antisymmetry levelSemiringNonInterfering {Private} {Public} () pre2
  antisymmetry levelSemiringNonInterfering {Private} {Private} (Refl .Private) pre2 = refl
  antisymmetry levelSemiringNonInterfering {Private} {Dunno} () pre2
  antisymmetry levelSemiringNonInterfering {Dunno} {Public} () pre2
  antisymmetry levelSemiringNonInterfering {Dunno} {Dunno} (Refl .Dunno) pre2 = refl
  antisymmetry levelSemiringNonInterfering {Unused} {Public} () pre2
  antisymmetry levelSemiringNonInterfering {Unused} {Private} () pre2
  antisymmetry levelSemiringNonInterfering {Unused} {Dunno} () pre2
  antisymmetry levelSemiringNonInterfering {Unused} {Unused} (Refl .Unused) pre2 = refl

  plusMono levelSemiringNonInterfering {r1} {Unused} {adv} pre rewrite rightUnit+ levelSemiring {r1} = pre
  plusMono levelSemiringNonInterfering {Public} {Public} {adv}  pre = pre
  plusMono levelSemiringNonInterfering {Private} {Public} {adv} pre = transitive≤ levelSemiring PrivPub pre
  plusMono levelSemiringNonInterfering {Dunno} {Public} {adv}   pre = transitive≤ levelSemiring DunnoPub  pre
  plusMono levelSemiringNonInterfering {Unused} {Public} {Unused} pre = 0Pub
  plusMono levelSemiringNonInterfering {Public} {Private} {adv} pre = pre
  plusMono levelSemiringNonInterfering {Private} {Private} {adv} pre = pre
  plusMono levelSemiringNonInterfering {Dunno} {Private} {adv} pre = pre
  plusMono levelSemiringNonInterfering {Unused} {Private} {Unused} pre = 0Priv
  plusMono levelSemiringNonInterfering {Unused} {Dunno} {Unused} pre = 0Dunno
  plusMono levelSemiringNonInterfering {Public} {Dunno} {adv}  pre = pre
  plusMono levelSemiringNonInterfering {Private} {Dunno} {adv} pre = transitive≤ levelSemiring PrivDunno pre
  plusMono levelSemiringNonInterfering {Dunno} {Dunno} {adv}   pre = pre

  propertyConditionalNI levelSemiringNonInterfering {Public} {Public} {Public} {adv} inp1 inp2 = inp1
  propertyConditionalNI levelSemiringNonInterfering {Public} {Public} {Private} {adv} inp1 inp2 = inp1
  propertyConditionalNI levelSemiringNonInterfering {Public} {Public} {Dunno} {adv} inp1 inp2 = inp1
  propertyConditionalNI levelSemiringNonInterfering {Public} {Private} {Public} {adv} inp1 inp2 = inp1
  propertyConditionalNI levelSemiringNonInterfering {Public} {Private} {Private} {adv} inp1 inp2 = inp1
  propertyConditionalNI levelSemiringNonInterfering {Public} {Private} {Dunno} {adv} inp1 inp2 = inp1
  propertyConditionalNI levelSemiringNonInterfering {Public} {Dunno} {Public} {adv} inp1 inp2 = inp1
  propertyConditionalNI levelSemiringNonInterfering {Public} {Dunno} {Private} {adv} inp1 inp2 = inp1
  propertyConditionalNI levelSemiringNonInterfering {Public} {Dunno} {Dunno} {adv} inp1 inp2 = inp1
  propertyConditionalNI levelSemiringNonInterfering {Public} {Unused} {Public} {adv} inp1 inp2 = inp1
  propertyConditionalNI levelSemiringNonInterfering {Public} {Unused} {Private} {adv} inp1 inp2 = inp1
  propertyConditionalNI levelSemiringNonInterfering {Public} {Unused} {Dunno} {adv} inp1 inp2 = inp1
  propertyConditionalNI levelSemiringNonInterfering {Private} {Public} {Public} {Public} inp1 inp2 = λ _ -> inp1 (Refl Public)
  propertyConditionalNI levelSemiringNonInterfering {Private} {Public} {Public} {Private} inp1 inp2 = λ _ -> inp1 PrivPub
  propertyConditionalNI levelSemiringNonInterfering {Private} {Public} {Public} {Dunno} inp1 inp2 = λ _ -> inp1 DunnoPub
  propertyConditionalNI levelSemiringNonInterfering {Private} {Public} {Public} {Unused} inp1 inp2 = λ _ -> inp1 0Pub
  propertyConditionalNI levelSemiringNonInterfering {Private} {Public} {Private} {Public} inp1 inp2 = λ _ -> inp1 (Refl Public)
  propertyConditionalNI levelSemiringNonInterfering {Private} {Public} {Private} {Private} inp1 inp2 = λ _ -> inp1 PrivPub
  propertyConditionalNI levelSemiringNonInterfering {Private} {Public} {Private} {Dunno} inp1 inp2 = λ _ -> inp1 DunnoPub
  propertyConditionalNI levelSemiringNonInterfering {Private} {Public} {Private} {Unused} inp1 inp2 = λ _ -> inp1 0Pub
  propertyConditionalNI levelSemiringNonInterfering {Private} {Public} {Dunno} {Public} inp1 inp2 = λ _ -> inp1 (Refl Public)
  propertyConditionalNI levelSemiringNonInterfering {Private} {Public} {Dunno} {Private} inp1 inp2 = λ _ -> inp1 PrivPub
  propertyConditionalNI levelSemiringNonInterfering {Private} {Public} {Dunno} {Dunno} inp1 inp2 = λ _ -> inp1 DunnoPub
  propertyConditionalNI levelSemiringNonInterfering {Private} {Public} {Dunno} {Unused} inp1 inp2 = λ _ -> inp1 0Pub
  propertyConditionalNI levelSemiringNonInterfering {Private} {Private} {Public} {Public} inp1 inp2 = λ _ -> inp1 (Refl Public)
  propertyConditionalNI levelSemiringNonInterfering {Private} {Private} {Public} {Private} inp1 inp2 = λ _ -> inp1 PrivPub
  propertyConditionalNI levelSemiringNonInterfering {Private} {Private} {Public} {Dunno} inp1 inp2 = λ _ -> inp1 DunnoPub
  propertyConditionalNI levelSemiringNonInterfering {Private} {Private} {Public} {Unused} inp1 inp2 = λ _ -> inp1 0Pub
  propertyConditionalNI levelSemiringNonInterfering {Private} {Private} {Private} {Public} inp1 inp2 = inp1
  propertyConditionalNI levelSemiringNonInterfering {Private} {Private} {Private} {Private} inp1 inp2 = inp1
  propertyConditionalNI levelSemiringNonInterfering {Private} {Private} {Private} {Dunno} inp1 inp2 = inp1
  propertyConditionalNI levelSemiringNonInterfering {Private} {Private} {Private} {Unused} inp1 inp2 = inp1
  propertyConditionalNI levelSemiringNonInterfering {Private} {Private} {Dunno} {Public} inp1 inp2 ()
  propertyConditionalNI levelSemiringNonInterfering {Private} {Private} {Dunno} {Private} inp1 inp2 = λ _ -> inp1 PrivDunno
  propertyConditionalNI levelSemiringNonInterfering {Private} {Private} {Dunno} {Dunno} inp1 inp2 = λ _ -> inp1 (Refl Dunno)
  propertyConditionalNI levelSemiringNonInterfering {Private} {Private} {Dunno} {Unused} inp1 inp2 = λ _ -> inp1 0Dunno
  propertyConditionalNI levelSemiringNonInterfering {Private} {Dunno} {Public} {Public} inp1 inp2 = λ _ -> inp1 (Refl Public)
  propertyConditionalNI levelSemiringNonInterfering {Private} {Dunno} {Public} {Private} inp1 inp2 = λ _ -> inp1 PrivPub
  propertyConditionalNI levelSemiringNonInterfering {Private} {Dunno} {Public} {Dunno} inp1 inp2 = λ _ -> inp1 DunnoPub
  propertyConditionalNI levelSemiringNonInterfering {Private} {Dunno} {Public} {Unused} inp1 inp2 = λ _ -> inp1 0Pub
  propertyConditionalNI levelSemiringNonInterfering {Private} {Dunno} {Private} {Public} inp1 inp2 ()
  propertyConditionalNI levelSemiringNonInterfering {Private} {Dunno} {Private} {Private} inp1 inp2 = λ _ -> inp1 PrivDunno
  propertyConditionalNI levelSemiringNonInterfering {Private} {Dunno} {Private} {Dunno} inp1 inp2 = λ _ -> inp1 (Refl Dunno)
  propertyConditionalNI levelSemiringNonInterfering {Private} {Dunno} {Private} {Unused} inp1 inp2 = λ _ -> inp1 0Dunno
  propertyConditionalNI levelSemiringNonInterfering {Private} {Dunno} {Dunno} {Public} inp1 inp2 ()
  propertyConditionalNI levelSemiringNonInterfering {Private} {Dunno} {Dunno} {Private} inp1 inp2 = λ _ -> inp1 PrivDunno
  propertyConditionalNI levelSemiringNonInterfering {Private} {Dunno} {Dunno} {Dunno} inp1 inp2 = λ _ -> inp1 (Refl Dunno)
  propertyConditionalNI levelSemiringNonInterfering {Private} {Dunno} {Dunno} {Unused} inp1 inp2 = λ _ -> inp1 0Dunno
  propertyConditionalNI levelSemiringNonInterfering {Private} {Unused} {Public} {Public} inp1 inp2 = λ _ -> inp1 (Refl Public)
  propertyConditionalNI levelSemiringNonInterfering {Private} {Unused} {Public} {Private} inp1 inp2 = λ _ -> inp1 PrivPub
  propertyConditionalNI levelSemiringNonInterfering {Private} {Unused} {Public} {Dunno} inp1 inp2 = λ _ -> inp1 DunnoPub
  propertyConditionalNI levelSemiringNonInterfering {Private} {Unused} {Public} {Unused} inp1 inp2 = λ _ -> inp1 0Pub
  propertyConditionalNI levelSemiringNonInterfering {Private} {Unused} {Private} {adv} inp1 inp2 = inp1
  propertyConditionalNI levelSemiringNonInterfering {Private} {Unused} {Dunno} {Public} inp1 inp2 ()
  propertyConditionalNI levelSemiringNonInterfering {Private} {Unused} {Dunno} {Private} inp1 inp2 = λ _ -> inp1 PrivDunno
  propertyConditionalNI levelSemiringNonInterfering {Private} {Unused} {Dunno} {Dunno} inp1 inp2 = λ _ -> inp1 (Refl Dunno)
  propertyConditionalNI levelSemiringNonInterfering {Private} {Unused} {Dunno} {Unused} inp1 inp2 = λ _ -> inp1 0Dunno
  propertyConditionalNI levelSemiringNonInterfering {Dunno} {Public} {Public} {Public} inp1 inp2 = λ _ -> inp1 (Refl Public)
  propertyConditionalNI levelSemiringNonInterfering {Dunno} {Public} {Public} {Private} inp1 inp2 = λ _ -> inp1 PrivPub
  propertyConditionalNI levelSemiringNonInterfering {Dunno} {Public} {Public} {Dunno} inp1 inp2 = λ _ -> inp1 DunnoPub
  propertyConditionalNI levelSemiringNonInterfering {Dunno} {Public} {Public} {Unused} inp1 inp2 = λ _ -> inp1 0Pub
  propertyConditionalNI levelSemiringNonInterfering {Dunno} {Public} {Private} {Public} inp1 inp2 = λ _ -> inp1 (Refl Public)
  propertyConditionalNI levelSemiringNonInterfering {Dunno} {Public} {Private} {Private} inp1 inp2 = λ _ -> inp1 PrivPub
  propertyConditionalNI levelSemiringNonInterfering {Dunno} {Public} {Private} {Dunno} inp1 inp2 = λ _ -> inp1 DunnoPub
  propertyConditionalNI levelSemiringNonInterfering {Dunno} {Public} {Private} {Unused} inp1 inp2 = λ _ -> inp1 0Pub
  propertyConditionalNI levelSemiringNonInterfering {Dunno} {Public} {Dunno} {Public} inp1 inp2 = λ _ -> inp1 (Refl Public)
  propertyConditionalNI levelSemiringNonInterfering {Dunno} {Public} {Dunno} {Private} inp1 inp2 = λ _ -> inp1 PrivPub
  propertyConditionalNI levelSemiringNonInterfering {Dunno} {Public} {Dunno} {Dunno} inp1 inp2 = λ _ -> inp1 DunnoPub
  propertyConditionalNI levelSemiringNonInterfering {Dunno} {Public} {Dunno} {Unused} inp1 inp2 = λ _ -> inp1 0Pub
  propertyConditionalNI levelSemiringNonInterfering {Dunno} {Private} {Public} {Public} inp1 inp2 = λ _ -> inp1 (Refl Public)
  propertyConditionalNI levelSemiringNonInterfering {Dunno} {Private} {Public} {Private} inp1 inp2 = λ _ -> inp1 PrivPub
  propertyConditionalNI levelSemiringNonInterfering {Dunno} {Private} {Public} {Dunno} inp1 inp2 = λ _ -> inp1 DunnoPub
  propertyConditionalNI levelSemiringNonInterfering {Dunno} {Private} {Public} {Unused} inp1 inp2 = λ _ -> inp1 0Pub
  propertyConditionalNI levelSemiringNonInterfering {Dunno} {Private} {Private} {Public} inp1 inp2 ()
  propertyConditionalNI levelSemiringNonInterfering {Dunno} {Private} {Private} {Private} inp1 inp2 = λ _ -> inp1 PrivDunno
  propertyConditionalNI levelSemiringNonInterfering {Dunno} {Private} {Private} {Dunno} inp1 inp2 = λ _ -> inp1 (Refl Dunno)
  propertyConditionalNI levelSemiringNonInterfering {Dunno} {Private} {Private} {Unused} inp1 inp2 = λ _ -> inp1 0Dunno
  propertyConditionalNI levelSemiringNonInterfering {Dunno} {Private} {Dunno} {Public} inp1 inp2 ()
  propertyConditionalNI levelSemiringNonInterfering {Dunno} {Private} {Dunno} {Private} inp1 inp2 = λ _ -> inp1 PrivDunno
  propertyConditionalNI levelSemiringNonInterfering {Dunno} {Private} {Dunno} {Dunno} inp1 inp2 = λ _ -> inp1 (Refl Dunno)
  propertyConditionalNI levelSemiringNonInterfering {Dunno} {Private} {Dunno} {Unused} inp1 inp2 = λ _ -> inp1 0Dunno
  propertyConditionalNI levelSemiringNonInterfering {Dunno} {Dunno} {Public} {Public} inp1 inp2 = λ _ -> inp1 (Refl Public)
  propertyConditionalNI levelSemiringNonInterfering {Dunno} {Dunno} {Public} {Private} inp1 inp2 = λ _ -> inp1 PrivPub
  propertyConditionalNI levelSemiringNonInterfering {Dunno} {Dunno} {Public} {Dunno} inp1 inp2 = λ _ -> inp1 DunnoPub
  propertyConditionalNI levelSemiringNonInterfering {Dunno} {Dunno} {Public} {Unused} inp1 inp2 = λ _ -> inp1 0Pub
  propertyConditionalNI levelSemiringNonInterfering {Dunno} {Dunno} {Private} {Public} inp1 inp2 ()
  propertyConditionalNI levelSemiringNonInterfering {Dunno} {Dunno} {Private} {Private} inp1 inp2 = λ _ -> inp1 PrivDunno
  propertyConditionalNI levelSemiringNonInterfering {Dunno} {Dunno} {Private} {Dunno} inp1 inp2 = λ _ -> inp1 (Refl Dunno)
  propertyConditionalNI levelSemiringNonInterfering {Dunno} {Dunno} {Private} {Unused} inp1 inp2 = λ _ -> inp1 0Dunno
  propertyConditionalNI levelSemiringNonInterfering {Dunno} {Dunno} {Dunno} {Public} inp1 inp2 ()
  propertyConditionalNI levelSemiringNonInterfering {Dunno} {Dunno} {Dunno} {Private} inp1 inp2 = λ _ -> inp1 PrivDunno
  propertyConditionalNI levelSemiringNonInterfering {Dunno} {Dunno} {Dunno} {Dunno} inp1 inp2 = λ _ -> inp1 (Refl Dunno)
  propertyConditionalNI levelSemiringNonInterfering {Dunno} {Dunno} {Dunno} {Unused} inp1 inp2 = λ _ -> inp1 0Dunno
  propertyConditionalNI levelSemiringNonInterfering {Dunno} {Unused} {Public} {Public} inp1 inp2 = λ _ -> inp1 (Refl Public)
  propertyConditionalNI levelSemiringNonInterfering {Dunno} {Unused} {Public} {Private} inp1 inp2 = λ _ -> inp1 PrivPub
  propertyConditionalNI levelSemiringNonInterfering {Dunno} {Unused} {Public} {Dunno} inp1 inp2 = λ _ -> inp1 DunnoPub
  propertyConditionalNI levelSemiringNonInterfering {Dunno} {Unused} {Public} {Unused} inp1 inp2 = λ _ -> inp1 0Pub
  propertyConditionalNI levelSemiringNonInterfering {Dunno} {Unused} {Private} {Public} inp1 inp2 ()
  propertyConditionalNI levelSemiringNonInterfering {Dunno} {Unused} {Private} {Private} inp1 inp2 = λ _ -> inp1 PrivDunno
  propertyConditionalNI levelSemiringNonInterfering {Dunno} {Unused} {Private} {Dunno} inp1 inp2 = λ _ -> inp1 (Refl Dunno)
  propertyConditionalNI levelSemiringNonInterfering {Dunno} {Unused} {Private} {Unused} inp1 inp2 = λ _ -> inp1 0Dunno
  propertyConditionalNI levelSemiringNonInterfering {Dunno} {Unused} {Dunno} {Public} inp1 inp2 ()
  propertyConditionalNI levelSemiringNonInterfering {Dunno} {Unused} {Dunno} {Private} inp1 inp2 = λ _ -> inp1 PrivDunno
  propertyConditionalNI levelSemiringNonInterfering {Dunno} {Unused} {Dunno} {Dunno} inp1 inp2 = λ _ -> inp1 (Refl Dunno)
  propertyConditionalNI levelSemiringNonInterfering {Dunno} {Unused} {Dunno} {Unused} inp1 inp2 = λ _ -> inp1 0Dunno
  propertyConditionalNI levelSemiringNonInterfering {Unused} {Public} {Public} {Public} inp1 inp2 = λ _ -> inp1 (Refl Public)
  propertyConditionalNI levelSemiringNonInterfering {Unused} {Public} {Public} {Private} inp1 inp2 = λ _ -> inp1 PrivPub
  propertyConditionalNI levelSemiringNonInterfering {Unused} {Public} {Public} {Dunno} inp1 inp2 = λ _ -> inp1 DunnoPub
  propertyConditionalNI levelSemiringNonInterfering {Unused} {Public} {Public} {Unused} inp1 inp2 = λ _ -> inp1 0Pub
  propertyConditionalNI levelSemiringNonInterfering {Unused} {Public} {Private} {Public} inp1 inp2 = λ _ -> inp1 (Refl Public)
  propertyConditionalNI levelSemiringNonInterfering {Unused} {Public} {Private} {Private} inp1 inp2 = λ _ -> inp1 PrivPub
  propertyConditionalNI levelSemiringNonInterfering {Unused} {Public} {Private} {Dunno} inp1 inp2 = λ _ -> inp1 DunnoPub
  propertyConditionalNI levelSemiringNonInterfering {Unused} {Public} {Private} {Unused} inp1 inp2 = λ _ -> inp1 0Pub
  propertyConditionalNI levelSemiringNonInterfering {Unused} {Public} {Dunno} {Public} inp1 inp2 = λ _ -> inp1 (Refl Public)
  propertyConditionalNI levelSemiringNonInterfering {Unused} {Public} {Dunno} {Private} inp1 inp2 = λ _ -> inp1 PrivPub
  propertyConditionalNI levelSemiringNonInterfering {Unused} {Public} {Dunno} {Dunno} inp1 inp2 = λ _ -> inp1 DunnoPub
  propertyConditionalNI levelSemiringNonInterfering {Unused} {Public} {Dunno} {Unused} inp1 inp2 = λ _ -> inp1 0Pub
  propertyConditionalNI levelSemiringNonInterfering {Unused} {Private} {Public} {Public} inp1 inp2 ()
  propertyConditionalNI levelSemiringNonInterfering {Unused} {Private} {Public} {Private} inp1 inp2 = λ _ -> inp1 (Refl Private)
  propertyConditionalNI levelSemiringNonInterfering {Unused} {Private} {Public} {Dunno} inp1 inp2 ()
  propertyConditionalNI levelSemiringNonInterfering {Unused} {Private} {Public} {Unused} inp1 inp2 = λ _ -> inp1 0Priv
  propertyConditionalNI levelSemiringNonInterfering {Unused} {Private} {Private} {Public} inp1 inp2 ()
  propertyConditionalNI levelSemiringNonInterfering {Unused} {Private} {Private} {Private} inp1 inp2 = λ _ -> inp1 (Refl Private)
  propertyConditionalNI levelSemiringNonInterfering {Unused} {Private} {Private} {Dunno} inp1 inp2 ()
  propertyConditionalNI levelSemiringNonInterfering {Unused} {Private} {Private} {Unused} inp1 inp2 = λ _ -> inp1 0Priv
  propertyConditionalNI levelSemiringNonInterfering {Unused} {Private} {Dunno} {Public} inp1 inp2 ()
  propertyConditionalNI levelSemiringNonInterfering {Unused} {Private} {Dunno} {Private} inp1 inp2 = λ _ -> inp1 (Refl Private)
  propertyConditionalNI levelSemiringNonInterfering {Unused} {Private} {Dunno} {Dunno} inp1 inp2 ()
  propertyConditionalNI levelSemiringNonInterfering {Unused} {Private} {Dunno} {Unused} inp1 inp2 = λ _ -> inp1 0Priv
  propertyConditionalNI levelSemiringNonInterfering {Unused} {Dunno} {Public} {Public} inp1 inp2 ()
  propertyConditionalNI levelSemiringNonInterfering {Unused} {Dunno} {Private} {Public} inp1 inp2 ()
  propertyConditionalNI levelSemiringNonInterfering {Unused} {Dunno} {Dunno} {Public} inp1 inp2 ()
  propertyConditionalNI levelSemiringNonInterfering {Unused} {Dunno} {Public} {Private} inp1 inp2 = λ _ -> inp1 PrivDunno
  propertyConditionalNI levelSemiringNonInterfering {Unused} {Dunno} {Private} {Private} inp1 inp2 = λ _ -> inp1 PrivDunno
  propertyConditionalNI levelSemiringNonInterfering {Unused} {Dunno} {Dunno} {Private} inp1 inp2 = λ _ -> inp1 PrivDunno
  propertyConditionalNI levelSemiringNonInterfering {Unused} {Dunno} {Public} {Dunno} inp1 inp2 = λ _ -> inp1 (Refl Dunno)
  propertyConditionalNI levelSemiringNonInterfering {Unused} {Dunno} {Private} {Dunno} inp1 inp2 = λ _ -> inp1 (Refl Dunno)
  propertyConditionalNI levelSemiringNonInterfering {Unused} {Dunno} {Dunno} {Dunno} inp1 inp2 = λ _ -> inp1 (Refl Dunno)
  propertyConditionalNI levelSemiringNonInterfering {Unused} {Dunno} {Public} {Unused} inp1 inp2 = λ _ -> inp1 0Dunno
  propertyConditionalNI levelSemiringNonInterfering {Unused} {Dunno} {Private} {Unused} inp1 inp2 = λ _ -> inp1 0Dunno
  propertyConditionalNI levelSemiringNonInterfering {Unused} {Dunno} {Dunno} {Unused} inp1 inp2 = λ _ -> inp1 0Dunno
  propertyConditionalNI levelSemiringNonInterfering {Unused} {Unused} {Public} {Public} inp1 inp2 ()
  propertyConditionalNI levelSemiringNonInterfering {Unused} {Unused} {Private} {Public} inp1 inp2 ()
  propertyConditionalNI levelSemiringNonInterfering {Unused} {Unused} {Dunno} {Public} inp1 inp2 ()
  propertyConditionalNI levelSemiringNonInterfering {Unused} {Unused} {Public} {Private} inp1 inp2 ()
  propertyConditionalNI levelSemiringNonInterfering {Unused} {Unused} {Private} {Private} inp1 inp2 ()
  propertyConditionalNI levelSemiringNonInterfering {Unused} {Unused} {Dunno} {Private} inp1 inp2 ()
  propertyConditionalNI levelSemiringNonInterfering {Unused} {Unused} {Public} {Dunno} inp1 inp2 ()
  propertyConditionalNI levelSemiringNonInterfering {Unused} {Unused} {Private} {Dunno} inp1 inp2 ()
  propertyConditionalNI levelSemiringNonInterfering {Unused} {Unused} {Dunno} {Dunno} inp1 inp2 ()
  propertyConditionalNI levelSemiringNonInterfering {Unused} {Unused} {Public} {Unused} inp1 inp2 = λ _ -> inp1 (Refl Unused)
  propertyConditionalNI levelSemiringNonInterfering {Unused} {Unused} {Private} {Unused} inp1 inp2 = λ _ -> inp1 (Refl Unused)
  propertyConditionalNI levelSemiringNonInterfering {Unused} {Unused} {Dunno} {Unused} inp1 inp2 = λ _ -> inp1 (Refl Unused)

  propertyConditionalNI2 levelSemiringNonInterfering {Public} {Public} {Public} {adv} inp1 inp2 = inp1
  propertyConditionalNI2 levelSemiringNonInterfering {Public} {Public} {Private} {adv} inp1 inp2 = inp1
  propertyConditionalNI2 levelSemiringNonInterfering {Public} {Public} {Dunno} {adv} inp1 inp2 = inp1
  propertyConditionalNI2 levelSemiringNonInterfering {Public} {Private} {Public} {Public} inp1 inp2 = λ _ -> inp1 (Refl Public)
  propertyConditionalNI2 levelSemiringNonInterfering {Public} {Private} {Public} {Private} inp1 inp2 = λ _ -> inp1 PrivPub
  propertyConditionalNI2 levelSemiringNonInterfering {Public} {Private} {Public} {Dunno} inp1 inp2 = λ _ -> inp1 DunnoPub
  propertyConditionalNI2 levelSemiringNonInterfering {Public} {Private} {Public} {Unused} inp1 inp2 = λ _ -> inp1 0Pub
  propertyConditionalNI2 levelSemiringNonInterfering {Public} {Private} {Private} {Public} inp1 inp2 = λ _ -> inp1 (Refl Public)
  propertyConditionalNI2 levelSemiringNonInterfering {Public} {Private} {Private} {Private} inp1 inp2 = λ _ -> inp1 PrivPub
  propertyConditionalNI2 levelSemiringNonInterfering {Public} {Private} {Private} {Dunno} inp1 inp2 = λ _ -> inp1 DunnoPub
  propertyConditionalNI2 levelSemiringNonInterfering {Public} {Private} {Private} {Unused} inp1 inp2 = λ _ -> inp1 0Pub
  propertyConditionalNI2 levelSemiringNonInterfering {Public} {Private} {Dunno} {Public} inp1 inp2 = λ _ -> inp1 (Refl Public)
  propertyConditionalNI2 levelSemiringNonInterfering {Public} {Private} {Dunno} {Private} inp1 inp2 = λ _ -> inp1 PrivPub
  propertyConditionalNI2 levelSemiringNonInterfering {Public} {Private} {Dunno} {Dunno} inp1 inp2 = λ _ -> inp1 DunnoPub
  propertyConditionalNI2 levelSemiringNonInterfering {Public} {Private} {Dunno} {Unused} inp1 inp2 = λ _ -> inp1 0Pub
  propertyConditionalNI2 levelSemiringNonInterfering {Public} {Dunno} {Public} {Public} inp1 inp2 = λ _ -> inp1 (Refl Public)
  propertyConditionalNI2 levelSemiringNonInterfering {Public} {Dunno} {Public} {Private} inp1 inp2 = λ _ -> inp1 PrivPub
  propertyConditionalNI2 levelSemiringNonInterfering {Public} {Dunno} {Public} {Dunno} inp1 inp2 = λ _ -> inp1 DunnoPub
  propertyConditionalNI2 levelSemiringNonInterfering {Public} {Dunno} {Public} {Unused} inp1 inp2 = λ _ -> inp1 0Pub
  propertyConditionalNI2 levelSemiringNonInterfering {Public} {Dunno} {Private} {Public} inp1 inp2 = λ _ -> inp1 (Refl Public)
  propertyConditionalNI2 levelSemiringNonInterfering {Public} {Dunno} {Private} {Private} inp1 inp2 = λ _ -> inp1 PrivPub
  propertyConditionalNI2 levelSemiringNonInterfering {Public} {Dunno} {Private} {Dunno} inp1 inp2 = λ _ -> inp1 DunnoPub
  propertyConditionalNI2 levelSemiringNonInterfering {Public} {Dunno} {Private} {Unused} inp1 inp2 = λ _ -> inp1 0Pub
  propertyConditionalNI2 levelSemiringNonInterfering {Public} {Dunno} {Dunno} {Public} inp1 inp2 = λ _ -> inp1 (Refl Public)
  propertyConditionalNI2 levelSemiringNonInterfering {Public} {Dunno} {Dunno} {Private} inp1 inp2 = λ _ -> inp1 PrivPub
  propertyConditionalNI2 levelSemiringNonInterfering {Public} {Dunno} {Dunno} {Dunno} inp1 inp2 = λ _ -> inp1 DunnoPub
  propertyConditionalNI2 levelSemiringNonInterfering {Public} {Dunno} {Dunno} {Unused} inp1 inp2 = λ _ -> inp1 0Pub
  propertyConditionalNI2 levelSemiringNonInterfering {Public} {Unused} {Public} {Public} inp1 inp2 = λ _ -> inp1 (Refl Public)
  propertyConditionalNI2 levelSemiringNonInterfering {Public} {Unused} {Public} {Private} inp1 inp2 = λ _ -> inp1 PrivPub
  propertyConditionalNI2 levelSemiringNonInterfering {Public} {Unused} {Public} {Dunno} inp1 inp2 = λ _ -> inp1 DunnoPub
  propertyConditionalNI2 levelSemiringNonInterfering {Public} {Unused} {Public} {Unused} inp1 inp2 = λ _ -> inp1 0Pub
  propertyConditionalNI2 levelSemiringNonInterfering {Public} {Unused} {Private} {Public} inp1 inp2 = λ _ -> inp1 (Refl Public)
  propertyConditionalNI2 levelSemiringNonInterfering {Public} {Unused} {Private} {Private} inp1 inp2 = λ _ -> inp1 PrivPub
  propertyConditionalNI2 levelSemiringNonInterfering {Public} {Unused} {Private} {Dunno} inp1 inp2 = λ _ -> inp1 DunnoPub
  propertyConditionalNI2 levelSemiringNonInterfering {Public} {Unused} {Private} {Unused} inp1 inp2 = λ _ -> inp1 0Pub
  propertyConditionalNI2 levelSemiringNonInterfering {Public} {Unused} {Dunno} {Public} inp1 inp2 = λ _ -> inp1 (Refl Public)
  propertyConditionalNI2 levelSemiringNonInterfering {Public} {Unused} {Dunno} {Private} inp1 inp2 = λ _ -> inp1 PrivPub
  propertyConditionalNI2 levelSemiringNonInterfering {Public} {Unused} {Dunno} {Dunno} inp1 inp2 = λ _ -> inp1 DunnoPub
  propertyConditionalNI2 levelSemiringNonInterfering {Public} {Unused} {Dunno} {Unused} inp1 inp2 = λ _ -> inp1 0Pub
  propertyConditionalNI2 levelSemiringNonInterfering {Private} {Public} {Public} {adv} inp1 inp2 = inp1
  propertyConditionalNI2 levelSemiringNonInterfering {Private} {Public} {Private} {adv} inp1 inp2 = inp1
  propertyConditionalNI2 levelSemiringNonInterfering {Private} {Public} {Dunno} {adv} inp1 inp2 = inp1
  propertyConditionalNI2 levelSemiringNonInterfering {Private} {Private} {Public} {Public} inp1 inp2 = λ _ -> inp1 (Refl Public)
  propertyConditionalNI2 levelSemiringNonInterfering {Private} {Private} {Public} {Private} inp1 inp2 = λ _ -> inp1 PrivPub
  propertyConditionalNI2 levelSemiringNonInterfering {Private} {Private} {Public} {Dunno} inp1 inp2 = λ _ -> inp1 DunnoPub
  propertyConditionalNI2 levelSemiringNonInterfering {Private} {Private} {Public} {Unused} inp1 inp2 = λ _ -> inp1 0Pub
  propertyConditionalNI2 levelSemiringNonInterfering {Private} {Private} {Private} {Public} inp1 inp2 ()
  propertyConditionalNI2 levelSemiringNonInterfering {Private} {Private} {Private} {Private} inp1 inp2 = λ _ -> inp1 (Refl Private)
  propertyConditionalNI2 levelSemiringNonInterfering {Private} {Private} {Private} {Dunno} inp1 inp2 ()
  propertyConditionalNI2 levelSemiringNonInterfering {Private} {Private} {Private} {Unused} inp1 inp2 = λ _ -> inp1 0Priv
  propertyConditionalNI2 levelSemiringNonInterfering {Private} {Private} {Dunno} {Public} inp1 inp2 ()
  propertyConditionalNI2 levelSemiringNonInterfering {Private} {Private} {Dunno} {Private} inp1 inp2 = λ _ -> inp1 PrivDunno
  propertyConditionalNI2 levelSemiringNonInterfering {Private} {Private} {Dunno} {Dunno} inp1 inp2 ()
  propertyConditionalNI2 levelSemiringNonInterfering {Private} {Private} {Dunno} {Unused} inp1 inp2 = λ _ -> inp1 0Dunno
  propertyConditionalNI2 levelSemiringNonInterfering {Private} {Dunno} {Public} {Public} inp1 inp2 = λ _ -> inp1 (Refl Public)
  propertyConditionalNI2 levelSemiringNonInterfering {Private} {Dunno} {Public} {Private} inp1 inp2 = λ _ -> inp1 PrivPub
  propertyConditionalNI2 levelSemiringNonInterfering {Private} {Dunno} {Public} {Dunno} inp1 inp2 = λ _ -> inp1 DunnoPub
  propertyConditionalNI2 levelSemiringNonInterfering {Private} {Dunno} {Public} {Unused} inp1 inp2 = λ _ -> inp1 0Pub
  propertyConditionalNI2 levelSemiringNonInterfering {Private} {Dunno} {Private} {Public} inp1 inp2 ()
  propertyConditionalNI2 levelSemiringNonInterfering {Private} {Dunno} {Private} {Private} inp1 inp2 = λ _ -> inp1 PrivDunno
  propertyConditionalNI2 levelSemiringNonInterfering {Private} {Dunno} {Private} {Dunno} inp1 inp2 = λ _ -> inp1 (Refl Dunno)
  propertyConditionalNI2 levelSemiringNonInterfering {Private} {Dunno} {Private} {Unused} inp1 inp2 = λ _ -> inp1 0Dunno
  propertyConditionalNI2 levelSemiringNonInterfering {Private} {Dunno} {Dunno} {Public} inp1 inp2 ()
  propertyConditionalNI2 levelSemiringNonInterfering {Private} {Dunno} {Dunno} {Private} inp1 inp2 = λ _ -> inp1 PrivDunno
  propertyConditionalNI2 levelSemiringNonInterfering {Private} {Dunno} {Dunno} {Dunno} inp1 inp2 = λ _ -> inp1 (Refl Dunno)
  propertyConditionalNI2 levelSemiringNonInterfering {Private} {Dunno} {Dunno} {Unused} inp1 inp2 = λ _ -> inp1 0Dunno
  propertyConditionalNI2 levelSemiringNonInterfering {Private} {Unused} {Public} {Public} inp1 inp2 = λ _ -> inp1 (Refl Public)
  propertyConditionalNI2 levelSemiringNonInterfering {Private} {Unused} {Public} {Private} inp1 inp2 = λ _ -> inp1 PrivPub
  propertyConditionalNI2 levelSemiringNonInterfering {Private} {Unused} {Public} {Dunno} inp1 inp2 = λ _ -> inp1 DunnoPub
  propertyConditionalNI2 levelSemiringNonInterfering {Private} {Unused} {Public} {Unused} inp1 inp2 = λ _ -> inp1 0Pub
  propertyConditionalNI2 levelSemiringNonInterfering {Private} {Unused} {Private} {Public} inp1 inp2 ()
  propertyConditionalNI2 levelSemiringNonInterfering {Private} {Unused} {Private} {Private} inp1 inp2 = λ _ -> inp1 (Refl Private)
  propertyConditionalNI2 levelSemiringNonInterfering {Private} {Unused} {Private} {Dunno} inp1 inp2 ()
  propertyConditionalNI2 levelSemiringNonInterfering {Private} {Unused} {Private} {Unused} inp1 inp2 = λ _ -> inp1 0Priv
  propertyConditionalNI2 levelSemiringNonInterfering {Private} {Unused} {Dunno} {Public} inp1 inp2 ()
  propertyConditionalNI2 levelSemiringNonInterfering {Private} {Unused} {Dunno} {Private} inp1 inp2 = λ _ -> inp1 PrivDunno
  propertyConditionalNI2 levelSemiringNonInterfering {Private} {Unused} {Dunno} {Dunno} inp1 inp2 = λ _ -> inp1 (Refl Dunno)
  propertyConditionalNI2 levelSemiringNonInterfering {Private} {Unused} {Dunno} {Unused} inp1 inp2 = λ _ -> inp1 0Dunno
  propertyConditionalNI2 levelSemiringNonInterfering {Dunno} {Public} {Public} {adv} inp1 inp2 = inp1
  propertyConditionalNI2 levelSemiringNonInterfering {Dunno} {Public} {Private} {adv} inp1 inp2 = inp1
  propertyConditionalNI2 levelSemiringNonInterfering {Dunno} {Public} {Dunno} {adv} inp1 inp2 = inp1
  propertyConditionalNI2 levelSemiringNonInterfering {Dunno} {Private} {Public} {Public} inp1 inp2 = λ _ -> inp1 (Refl Public)
  propertyConditionalNI2 levelSemiringNonInterfering {Dunno} {Private} {Public} {Private} inp1 inp2 = λ _ -> inp1 PrivPub
  propertyConditionalNI2 levelSemiringNonInterfering {Dunno} {Private} {Public} {Dunno} inp1 inp2 = λ _ -> inp1 DunnoPub
  propertyConditionalNI2 levelSemiringNonInterfering {Dunno} {Private} {Public} {Unused} inp1 inp2 = λ _ -> inp1 0Pub
  propertyConditionalNI2 levelSemiringNonInterfering {Dunno} {Private} {Private} {Public} inp1 inp2 ()
  propertyConditionalNI2 levelSemiringNonInterfering {Dunno} {Private} {Private} {Private} inp1 inp2 = λ _ -> inp1 PrivDunno
  propertyConditionalNI2 levelSemiringNonInterfering {Dunno} {Private} {Private} {Dunno} inp1 inp2 = λ _ -> inp1 (Refl Dunno)
  propertyConditionalNI2 levelSemiringNonInterfering {Dunno} {Private} {Private} {Unused} inp1 inp2 = λ _ -> inp1 0Dunno
  propertyConditionalNI2 levelSemiringNonInterfering {Dunno} {Private} {Dunno} {Public} inp1 inp2 ()
  propertyConditionalNI2 levelSemiringNonInterfering {Dunno} {Private} {Dunno} {Private} inp1 inp2 = λ _ -> inp1 PrivDunno
  propertyConditionalNI2 levelSemiringNonInterfering {Dunno} {Private} {Dunno} {Dunno} inp1 inp2 = λ _ -> inp1 (Refl Dunno)
  propertyConditionalNI2 levelSemiringNonInterfering {Dunno} {Private} {Dunno} {Unused} inp1 inp2 = λ _ -> inp1 0Dunno
  propertyConditionalNI2 levelSemiringNonInterfering {Dunno} {Dunno} {Public} {Public} inp1 inp2 = λ _ -> inp1 (Refl Public)
  propertyConditionalNI2 levelSemiringNonInterfering {Dunno} {Dunno} {Public} {Private} inp1 inp2 = λ _ -> inp1 PrivPub
  propertyConditionalNI2 levelSemiringNonInterfering {Dunno} {Dunno} {Public} {Dunno} inp1 inp2 = λ _ -> inp1 DunnoPub
  propertyConditionalNI2 levelSemiringNonInterfering {Dunno} {Dunno} {Public} {Unused} inp1 inp2 = λ _ -> inp1 0Pub
  propertyConditionalNI2 levelSemiringNonInterfering {Dunno} {Dunno} {Private} {adv} inp1 inp2 = inp1
  propertyConditionalNI2 levelSemiringNonInterfering {Dunno} {Dunno} {Dunno} {adv} inp1 inp2 = inp1
  propertyConditionalNI2 levelSemiringNonInterfering {Dunno} {Unused} {Public} {Public} inp1 inp2 = λ _ -> inp1 (Refl Public)
  propertyConditionalNI2 levelSemiringNonInterfering {Dunno} {Unused} {Public} {Private} inp1 inp2 = λ _ -> inp1 PrivPub
  propertyConditionalNI2 levelSemiringNonInterfering {Dunno} {Unused} {Public} {Dunno} inp1 inp2 = λ _ -> inp1 DunnoPub
  propertyConditionalNI2 levelSemiringNonInterfering {Dunno} {Unused} {Public} {Unused} inp1 inp2 = λ _ -> inp1 0Pub
  propertyConditionalNI2 levelSemiringNonInterfering {Dunno} {Unused} {Private} {Public} inp1 inp2 ()
  propertyConditionalNI2 levelSemiringNonInterfering {Dunno} {Unused} {Private} {Private} inp1 inp2 = λ _ -> inp1 PrivDunno
  propertyConditionalNI2 levelSemiringNonInterfering {Dunno} {Unused} {Private} {Dunno} inp1 inp2 = λ _ -> inp1 (Refl Dunno)
  propertyConditionalNI2 levelSemiringNonInterfering {Dunno} {Unused} {Private} {Unused} inp1 inp2 = λ _ -> inp1 0Dunno
  propertyConditionalNI2 levelSemiringNonInterfering {Dunno} {Unused} {Dunno} {Public} inp1 inp2 ()
  propertyConditionalNI2 levelSemiringNonInterfering {Dunno} {Unused} {Dunno} {Private} inp1 inp2 = λ _ -> inp1 PrivDunno
  propertyConditionalNI2 levelSemiringNonInterfering {Dunno} {Unused} {Dunno} {Dunno} inp1 inp2 = λ _ -> inp1 (Refl Dunno)
  propertyConditionalNI2 levelSemiringNonInterfering {Dunno} {Unused} {Dunno} {Unused} inp1 inp2 = λ _ -> inp1 0Dunno
  propertyConditionalNI2 levelSemiringNonInterfering {Unused} {Public} {Public} {adv} inp1 inp2 = inp1
  propertyConditionalNI2 levelSemiringNonInterfering {Unused} {Public} {Private} {adv} inp1 inp2 = inp1
  propertyConditionalNI2 levelSemiringNonInterfering {Unused} {Public} {Dunno} {adv} inp1 inp2 = inp1
  propertyConditionalNI2 levelSemiringNonInterfering {Unused} {Private} {Public} {adv} inp1 inp2 = inp1
  propertyConditionalNI2 levelSemiringNonInterfering {Unused} {Private} {Private} {adv} inp1 inp2 = inp1
  propertyConditionalNI2 levelSemiringNonInterfering {Unused} {Private} {Dunno} {adv} inp1 inp2 = inp1
  propertyConditionalNI2 levelSemiringNonInterfering {Unused} {Dunno} {Public} {adv} inp1 inp2 = inp1
  propertyConditionalNI2 levelSemiringNonInterfering {Unused} {Dunno} {Private} {adv} inp1 inp2 = inp1
  propertyConditionalNI2 levelSemiringNonInterfering {Unused} {Dunno} {Dunno} {adv} inp1 inp2 = inp1
  propertyConditionalNI2 levelSemiringNonInterfering {Unused} {Unused} {Public} {adv} inp1 inp2 = inp1
  propertyConditionalNI2 levelSemiringNonInterfering {Unused} {Unused} {Private} {adv} inp1 inp2 = inp1
  propertyConditionalNI2 levelSemiringNonInterfering {Unused} {Unused} {Dunno} {adv} inp1 inp2 = inp1

  --propInvTimesMonoAsym : {r s adv : Level}
  --                     -> ¬(_≤_ levelSemiring (_*R_ levelSemiring r s) adv)
  --                     -> (_≤_ levelSemiring r adv)
  --                     -> ¬(_≤_ levelSemiring s adv)
  propInvTimesMonoAsym levelSemiringNonInterfering {Public} {Public} {adv} inp1 inp2 = inp1
  propInvTimesMonoAsym levelSemiringNonInterfering {Public} {Private} {Public} inp1 inp2 = λ _ -> inp1 (Refl Public)
  propInvTimesMonoAsym levelSemiringNonInterfering {Public} {Private} {Private} inp1 inp2 = λ _ -> inp1 PrivPub
  propInvTimesMonoAsym levelSemiringNonInterfering {Public} {Private} {Dunno} inp1 inp2 = λ _ -> inp1 DunnoPub
  propInvTimesMonoAsym levelSemiringNonInterfering {Public} {Private} {Unused} inp1 inp2 = λ _ -> inp1 0Pub
  propInvTimesMonoAsym levelSemiringNonInterfering {Public} {Dunno} {Public} inp1 inp2 = λ _ -> inp1 (Refl Public)
  propInvTimesMonoAsym levelSemiringNonInterfering {Public} {Dunno} {Private} inp1 inp2 = λ _ -> inp1 PrivPub
  propInvTimesMonoAsym levelSemiringNonInterfering {Public} {Dunno} {Dunno} inp1 inp2 = λ _ -> inp1 DunnoPub
  propInvTimesMonoAsym levelSemiringNonInterfering {Public} {Dunno} {Unused} inp1 inp2 = λ _ -> inp1 0Pub
  propInvTimesMonoAsym levelSemiringNonInterfering {Public} {Unused} {adv} inp1 inp2 = inp1
  propInvTimesMonoAsym levelSemiringNonInterfering {Private} {Public} {adv} inp1 inp2 = inp1
  propInvTimesMonoAsym levelSemiringNonInterfering {Private} {Private} {adv} inp1 inp2 = inp1
  propInvTimesMonoAsym levelSemiringNonInterfering {Private} {Dunno} {adv} inp1 inp2 = inp1
  propInvTimesMonoAsym levelSemiringNonInterfering {Private} {Unused} {adv} inp1 inp2 = inp1
  propInvTimesMonoAsym levelSemiringNonInterfering {Dunno} {Public} {adv} inp1 inp2 = inp1
  propInvTimesMonoAsym levelSemiringNonInterfering {Dunno} {Private} {Private} inp1 inp2 = λ _ -> inp1 PrivDunno
  propInvTimesMonoAsym levelSemiringNonInterfering {Dunno} {Private} {Dunno} inp1 inp2 = λ _ -> inp1 (Refl Dunno)
  propInvTimesMonoAsym levelSemiringNonInterfering {Dunno} {Private} {Unused} inp1 inp2 = λ _ -> inp1 0Dunno
  propInvTimesMonoAsym levelSemiringNonInterfering {Dunno} {Dunno} {adv} inp1 inp2 = inp1
  propInvTimesMonoAsym levelSemiringNonInterfering {Dunno} {Unused} {adv} inp1 inp2 = inp1
  propInvTimesMonoAsym levelSemiringNonInterfering {Unused} {Public} {Unused} inp1 inp2 = λ _ -> inp1 (Refl Unused)
  propInvTimesMonoAsym levelSemiringNonInterfering {Unused} {Private} {Unused} inp1 inp2 = λ _ -> inp1 (Refl Unused)
  propInvTimesMonoAsym levelSemiringNonInterfering {Unused} {Dunno} {Unused} inp1 inp2 = λ _ -> inp1 (Refl Unused)
  propInvTimesMonoAsym levelSemiringNonInterfering {Unused} {Unused} {adv} inp1 inp2 = inp1

instance
  levelIFstructure : InformationFlowSemiring levelSemiring

  default levelIFstructure = Dunno

  _#_ levelIFstructure Private s = Private
  _#_ levelIFstructure r Private = Private
  _#_ levelIFstructure r s = _+*_ levelSemiring r s

  --substProp levelIFstructure {Public} = {!!}
  --substProp levelIFstructure {Private} = refl
  --substProp levelIFstructure {Dunno} = {!!}
  --substProp levelIFstructure {Unused} = refl

  unit# levelIFstructure {Public}  = refl
  unit# levelIFstructure {Private} = refl
  unit# levelIFstructure {Dunno}   = refl
  unit# levelIFstructure {Unused}  = {!!}

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

  assoc# levelIFstructure {r} {s} {t} = {!!}
