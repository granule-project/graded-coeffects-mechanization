module LocalGlobal where

open import Semiring
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary.Decidable
open import Agda.Builtin.Bool

data Locality : Set where
  Unused : Locality -- 0
  Local  : Locality -- 1, i.e., we can do `a [Local] -> a`
  Global : Locality

data Ordering : Locality -> Locality -> Set where

  GlobalToLocal : Ordering Global Local -- Global < Local

 -- Discussion: (maybe Local < Unused ?)

{-

x : Local A  |- t : B
-----------------------
x : Global A |- t : B

BUT NOT

x : Global A  /|- t : B
-----------------------
x : Local A /|- t : B

-}

  ReflL         : Ordering Local  Local
  ReflG         : Ordering Global Global
  Refl0         : Ordering Unused Unused

_+l_ : Locality -> Locality -> Locality
Unused +l y      = y
y      +l Unused = y
Local  +l Local  = Local
x      +l Global = Global
Global +l y      = Global

_*l_ : Locality -> Locality -> Locality
Unused *l y      = Unused
y      *l Unused = Unused
Local  *l Local  = Local
x      *l Global = Global
Global *l y      = Global


{-
x : Local |- t : A
--------------------------------------
x : Global |- [Global] t : A [Global]

-}


-- f : (Handle -> a [Global])
-------------------------------
-- withFile s f : a [Global]



--        e : a [Global]
---------------------------------------------
-- region e : a [Global]


-- e1 : a [Local]
-- e2 : b [Local]
-------------------
--- <e1, e2> : (a, b) [Local]

localGlobal : Semiring
localGlobal =
  record
    { grade = Locality
    ; 1R = Local  -- i.e., we can go a [Local] -> a
    ; 0R = Unused
    ; _+R_ = _+l_
    ; _*R_ = _*l_
    ; _≤_ = Ordering
    ; _≤d_ = dec<=
    ; leftUnit+ = refl
    ; rightUnit+ = right+
    ; comm+ = \{r} {s} -> commPlus {r} {s}
    ; leftUnit* = leftUnit*
    ; rightUnit* = rightUnit*
    ; leftAbsorb = refl
    ; rightAbsorb = rightabsorb
    ; assoc* = assoc*
    ; assoc+ = \{r} {s} {t} -> assocPlus {r} {s} {t}
    ; distrib1 = distrib1
    ; distrib2 = \{r} {s} {t} -> distrib2prop {r} {s} {t}
    ; monotone* = mon*
    ; monotone+ = mon+
    ; reflexive≤ = reflexive
    ; transitive≤ = transt
    }
  where
    reflexive : {r : Locality} → Ordering r r
    reflexive {Local} = ReflL
    reflexive {Global} = ReflG
    reflexive {Unused} = Refl0

    transt : {r s t : Locality} →
      Ordering r s → Ordering s t → Ordering r t
    transt {.Global} {.Local} {.Local} GlobalToLocal ReflL = GlobalToLocal
    transt {.Local} {.Local} {.Local} ReflL ReflL = ReflL
    transt {.Global} {.Global} {.Local} ReflG GlobalToLocal = GlobalToLocal
    transt {.Global} {.Global} {.Global} ReflG ReflG = ReflG
    transt {.Unused} {.Unused} {.Unused} Refl0 Refl0 = Refl0

    dec<= :  (r s : Locality) → Dec (Ordering r s)
    dec<= Local Local = yes ReflL
    dec<= Local Global = no (λ ())
    dec<= Local Unused = no (\ ())
    dec<= Global Local = yes GlobalToLocal
    dec<= Global Global = yes ReflG
    dec<= Global Unused = no (\())
    dec<= Unused Local = no (\ ())
    dec<= Unused Global = no (\())
    dec<= Unused Unused = yes Refl0


    right+ : {x : Locality} -> (x +l Unused) ≡ x
    right+ {Local} = refl
    right+ {Global} = refl
    right+ {Unused} = refl

    commPlus : {x y : Locality} -> (x +l y) ≡ (y +l x)
    commPlus {Local} {Local} = refl
    commPlus {Local} {Global} = refl
    commPlus {Local} {Unused} = refl
    commPlus {Global} {Local} = refl
    commPlus {Global} {Global} = refl
    commPlus {Global} {Unused} = refl
    commPlus {Unused} {Local} = refl
    commPlus {Unused} {Global} = refl
    commPlus {Unused} {Unused} = refl

    leftUnit* : {x : Locality} ->  (Local *l x) ≡ x
    leftUnit* {Local} = refl
    leftUnit* {Global} = refl
    leftUnit* {Unused} = refl

    rightUnit* : {x : Locality} ->  (x *l Local) ≡ x
    rightUnit* {Local} = refl
    rightUnit* {Global} = refl
    rightUnit* {Unused} = refl

    rightabsorb : {x : Locality} → (x *l Unused) ≡ Unused
    rightabsorb {Local} = refl
    rightabsorb {Global} = refl
    rightabsorb {Unused} = refl

    mon* : {r1 r2 s1 s2 : Locality} →
      Ordering r1 r2 → Ordering s1 s2 → Ordering (r1 *l s1) (r2 *l s2)
    mon* {.Global} {.Local} {.Global} {.Local} GlobalToLocal GlobalToLocal = GlobalToLocal
    mon* {.Global} {.Local} {.Local} {.Local} GlobalToLocal ReflL = GlobalToLocal
    mon* {.Global} {.Local} {.Global} {.Global} GlobalToLocal ReflG = ReflG
    mon* {.Global} {.Local} {.Unused} {.Unused} GlobalToLocal Refl0 = Refl0
    mon* {.Local} {.Local} {.Global} {.Local} ReflL GlobalToLocal = GlobalToLocal
    mon* {.Local} {.Local} {.Local} {.Local} ReflL ReflL = ReflL
    mon* {.Local} {.Local} {.Global} {.Global} ReflL ReflG = ReflG
    mon* {.Local} {.Local} {.Unused} {.Unused} ReflL Refl0 = Refl0
    mon* {.Global} {.Global} {.Global} {.Local} ReflG GlobalToLocal = ReflG
    mon* {.Global} {.Global} {.Local} {.Local} ReflG ReflL = ReflG
    mon* {.Global} {.Global} {.Global} {.Global} ReflG ReflG = ReflG
    mon* {.Global} {.Global} {.Unused} {.Unused} ReflG Refl0 = Refl0
    mon* {.Unused} {.Unused} {.Global} {.Local} Refl0 GlobalToLocal = Refl0
    mon* {.Unused} {.Unused} {.Local} {.Local} Refl0 ReflL = Refl0
    mon* {.Unused} {.Unused} {.Global} {.Global} Refl0 ReflG = Refl0
    mon* {.Unused} {.Unused} {.Unused} {.Unused} Refl0 Refl0 = Refl0

    mon+ : {r1 r2 s1 s2 : Locality} →
      Ordering r1 r2 → Ordering s1 s2 → Ordering (r1 +l s1) (r2 +l s2)
    mon+ {.Global} {.Local} {.Global} {.Local} GlobalToLocal GlobalToLocal = GlobalToLocal
    mon+ {.Global} {.Local} {.Local} {.Local} GlobalToLocal ReflL = GlobalToLocal
    mon+ {.Global} {.Local} {.Global} {.Global} GlobalToLocal ReflG = ReflG
    mon+ {.Global} {.Local} {.Unused} {.Unused} GlobalToLocal Refl0 = GlobalToLocal
    mon+ {.Local} {.Local} {.Global} {.Local} ReflL GlobalToLocal = GlobalToLocal
    mon+ {.Local} {.Local} {.Local} {.Local} ReflL ReflL = ReflL
    mon+ {.Local} {.Local} {.Global} {.Global} ReflL ReflG = ReflG
    mon+ {.Local} {.Local} {.Unused} {.Unused} ReflL Refl0 = ReflL
    mon+ {.Global} {.Global} {.Global} {.Local} ReflG GlobalToLocal = ReflG
    mon+ {.Global} {.Global} {.Local} {.Local} ReflG ReflL = ReflG
    mon+ {.Global} {.Global} {.Global} {.Global} ReflG ReflG = ReflG
    mon+ {.Global} {.Global} {.Unused} {.Unused} ReflG Refl0 = ReflG
    mon+ {.Unused} {.Unused} {.Global} {.Local} Refl0 GlobalToLocal = GlobalToLocal
    mon+ {.Unused} {.Unused} {.Local} {.Local} Refl0 ReflL = ReflL
    mon+ {.Unused} {.Unused} {.Global} {.Global} Refl0 ReflG = ReflG
    mon+ {.Unused} {.Unused} {.Unused} {.Unused} Refl0 Refl0 = Refl0

    assoc* : {r s t : Locality} → ((r *l s) *l t) ≡ (r *l (s *l t))
    assoc* {Local} {Local} {Local} = refl
    assoc* {Local} {Local} {Global} = refl
    assoc* {Local} {Local} {Unused} = refl
    assoc* {Local} {Global} {Local} = refl
    assoc* {Local} {Global} {Global} = refl
    assoc* {Local} {Global} {Unused} = refl
    assoc* {Local} {Unused} {t} = refl
    assoc* {Global} {Local} {Local} = refl
    assoc* {Global} {Local} {Global} = refl
    assoc* {Global} {Local} {Unused} = refl
    assoc* {Global} {Global} {Local} = refl
    assoc* {Global} {Global} {Global} = refl
    assoc* {Global} {Global} {Unused} = refl
    assoc* {Global} {Unused} {t} = refl
    assoc* {Unused} {s} {t} = refl

    distrib1 : {r s t : Locality} → (r *l (s +l t)) ≡ ((r *l s) +l (r *l t))
    distrib1 {Local} {s} {t} rewrite leftUnit* {s +l t} | leftUnit* {s} | leftUnit* {t} = refl
    distrib1 {Global} {Local} {Local} = refl
    distrib1 {Global} {Local} {Global} = refl
    distrib1 {Global} {Local} {Unused} = refl
    distrib1 {Global} {Global} {Local} = refl
    distrib1 {Global} {Global} {Global} = refl
    distrib1 {Global} {Global} {Unused} = refl
    distrib1 {Global} {Unused} {Local} = refl
    distrib1 {Global} {Unused} {Global} = refl
    distrib1 {Global} {Unused} {Unused} = refl
    distrib1 {Unused} {s} {t} = refl

    -- used by distrib2
    comm* : {x y : Locality} -> x *l y ≡ y *l x
    comm* {Local} {Local} = refl
    comm* {Local} {Global} = refl
    comm* {Local} {Unused} = refl
    comm* {Global} {Local} = refl
    comm* {Global} {Global} = refl
    comm* {Global} {Unused} = refl
    comm* {Unused} {Local} = refl
    comm* {Unused} {Global} = refl
    comm* {Unused} {Unused} = refl

    distrib2prop : {r s t : Locality} → ((r +l s) *l t) ≡ ((r *l t) +l (s *l t))
    distrib2prop {r} {s} {t} rewrite comm* {r +l s} {t} | comm* {r} {t} | comm* {s} {t} = distrib1

    assocPlus : {r s t : Locality} → ((r +l s) +l t) ≡ (r +l (s +l t))
    assocPlus {Local} {Local} {Local} = refl
    assocPlus {Local} {Local} {Global} = refl
    assocPlus {Local} {Local} {Unused} = refl
    assocPlus {Local} {Global} {Local} = refl
    assocPlus {Local} {Global} {Global} = refl
    assocPlus {Local} {Global} {Unused} = refl
    assocPlus {Local} {Unused} {t} = refl
    assocPlus {Global} {Local} {Local} = refl
    assocPlus {Global} {Local} {Global} = refl
    assocPlus {Global} {Local} {Unused} = refl
    assocPlus {Global} {Global} {Local} = refl
    assocPlus {Global} {Global} {Global} = refl
    assocPlus {Global} {Global} {Unused} = refl
    assocPlus {Global} {Unused} {t} = refl
    assocPlus {Unused} {s} {t} = refl
