module LocalGlobal where

open import Semiring
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary.Decidable
open import Agda.Builtin.Bool

data Locality : Set where
  Any    : Locality -- 0
  Local  : Locality -- 1, i.e., we can do `a [Local] -> a`
  Global : Locality

data Ordering : Locality -> Locality -> Set where

  GlobalToLocal  : Ordering Global Local -- Global < Local
  AnyToLocal     : Ordering Any Local    -- Any < Local
  AnyToGlobal    : Ordering Any Global   -- Any < Global

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
  Refl0         : Ordering Any Any


-- changed as otherwise no mon+:
-- mon+ {.Local} {.Local} {.Any} {.Global} ReflL AnyToGlobal =  LocalToGlobal
-- mon+ {.Any} {.Global} {.Local} {.Local} AnyToGlobal ReflL = LocalToGLobal
_+l_ : Locality -> Locality -> Locality
Any +l y      = y
y      +l Any = y
Local  +l Local  = Local
x      +l Global = x
Global +l y      = y

_*l_ : Locality -> Locality -> Locality
Any *l y      = Any
y      *l Any = Any
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
    ; 0R = Any
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
    reflexive {Any} = Refl0

    transt : {r s t : Locality} →
      Ordering r s → Ordering s t → Ordering r t
    transt {.Global} {.Local} {.Local} GlobalToLocal ReflL = GlobalToLocal
    transt {.Local} {.Local} {.Local} ReflL ReflL = ReflL
    transt {.Global} {.Global} {.Local} ReflG GlobalToLocal = GlobalToLocal
    transt {.Global} {.Global} {.Global} ReflG ReflG = ReflG
    transt {.Any} {.Any} {.Any} Refl0 Refl0 = Refl0
    transt {.Any} {.Local} {.Local} AnyToLocal ReflL = AnyToLocal
    transt {.Any} {.Global} {.Global} AnyToGlobal ReflG = AnyToGlobal
    transt {.Any} {.Global} {.Local} AnyToGlobal GlobalToLocal = AnyToLocal
    transt {.Any} {.Any} {.Local} Refl0 AnyToLocal = AnyToLocal
    transt {.Any} {.Any} {.Global} Refl0 AnyToGlobal = AnyToGlobal

    dec<= :  (r s : Locality) → Dec (Ordering r s)
    dec<= Local Local = yes ReflL
    dec<= Local Global = no (λ ())
    dec<= Local Any = no (\ ())
    dec<= Global Local = yes GlobalToLocal
    dec<= Global Global = yes ReflG
    dec<= Global Any = no (\())
    dec<= Any Local = yes AnyToLocal
    dec<= Any Global = yes AnyToGlobal
    dec<= Any Any = yes Refl0


    right+ : {x : Locality} -> (x +l Any) ≡ x
    right+ {Local} = refl
    right+ {Global} = refl
    right+ {Any} = refl

    commPlus : {x y : Locality} -> (x +l y) ≡ (y +l x)
    commPlus {Local} {Local} = refl
    commPlus {Local} {Global} = refl
    commPlus {Local} {Any} = refl
    commPlus {Global} {Local} = refl
    commPlus {Global} {Global} = refl
    commPlus {Global} {Any} = refl
    commPlus {Any} {Local} = refl
    commPlus {Any} {Global} = refl
    commPlus {Any} {Any} = refl

    leftUnit* : {x : Locality} ->  (Local *l x) ≡ x
    leftUnit* {Local} = refl
    leftUnit* {Global} = refl
    leftUnit* {Any} = refl

    rightUnit* : {x : Locality} ->  (x *l Local) ≡ x
    rightUnit* {Local} = refl
    rightUnit* {Global} = refl
    rightUnit* {Any} = refl

    rightabsorb : {x : Locality} → (x *l Any) ≡ Any
    rightabsorb {Local} = refl
    rightabsorb {Global} = refl
    rightabsorb {Any} = refl

    mon* : {r1 r2 s1 s2 : Locality} →
      Ordering r1 r2 → Ordering s1 s2 → Ordering (r1 *l s1) (r2 *l s2)
    mon* {.Global} {.Local} {.Global} {.Local} GlobalToLocal GlobalToLocal = GlobalToLocal
    mon* {.Global} {.Local} {.Any} {.Local} GlobalToLocal AnyToLocal = AnyToLocal
    mon* {.Global} {.Local} {.Any} {.Global} GlobalToLocal AnyToGlobal = AnyToGlobal
    mon* {.Global} {.Local} {.Local} {.Local} GlobalToLocal ReflL = GlobalToLocal
    mon* {.Global} {.Local} {.Global} {.Global} GlobalToLocal ReflG = ReflG
    mon* {.Global} {.Local} {.Any} {.Any} GlobalToLocal Refl0 = Refl0
    mon* {.Any} {.Local} {.Global} {.Local} AnyToLocal GlobalToLocal = AnyToLocal
    mon* {.Any} {.Local} {.Any} {.Local} AnyToLocal AnyToLocal = AnyToLocal
    mon* {.Any} {.Local} {.Any} {.Global} AnyToLocal AnyToGlobal = AnyToGlobal
    mon* {.Any} {.Local} {.Local} {.Local} AnyToLocal ReflL = AnyToLocal
    mon* {.Any} {.Local} {.Global} {.Global} AnyToLocal ReflG = AnyToGlobal
    mon* {.Any} {.Local} {.Any} {.Any} AnyToLocal Refl0 = Refl0
    mon* {.Any} {.Global} {.Global} {.Local} AnyToGlobal GlobalToLocal = AnyToGlobal
    mon* {.Any} {.Global} {.Any} {.Local} AnyToGlobal AnyToLocal = AnyToGlobal
    mon* {.Any} {.Global} {.Any} {.Global} AnyToGlobal AnyToGlobal = AnyToGlobal
    mon* {.Any} {.Global} {.Local} {.Local} AnyToGlobal ReflL = AnyToGlobal
    mon* {.Any} {.Global} {.Global} {.Global} AnyToGlobal ReflG = AnyToGlobal
    mon* {.Any} {.Global} {.Any} {.Any} AnyToGlobal Refl0 = Refl0
    mon* {.Local} {.Local} {.Global} {.Local} ReflL GlobalToLocal = GlobalToLocal
    mon* {.Local} {.Local} {.Any} {.Local} ReflL AnyToLocal = AnyToLocal
    mon* {.Local} {.Local} {.Any} {.Global} ReflL AnyToGlobal = AnyToGlobal
    mon* {.Local} {.Local} {.Local} {.Local} ReflL ReflL = ReflL
    mon* {.Local} {.Local} {.Global} {.Global} ReflL ReflG = ReflG
    mon* {.Local} {.Local} {.Any} {.Any} ReflL Refl0 = Refl0
    mon* {.Global} {.Global} {.Global} {.Local} ReflG GlobalToLocal = ReflG
    mon* {.Global} {.Global} {.Any} {.Local} ReflG AnyToLocal = AnyToGlobal
    mon* {.Global} {.Global} {.Any} {.Global} ReflG AnyToGlobal = AnyToGlobal
    mon* {.Global} {.Global} {.Local} {.Local} ReflG ReflL = ReflG
    mon* {.Global} {.Global} {.Global} {.Global} ReflG ReflG = ReflG
    mon* {.Global} {.Global} {.Any} {.Any} ReflG Refl0 = Refl0
    mon* {.Any} {.Any} {.Global} {.Local} Refl0 GlobalToLocal = Refl0
    mon* {.Any} {.Any} {.Any} {.Local} Refl0 AnyToLocal = Refl0
    mon* {.Any} {.Any} {.Any} {.Global} Refl0 AnyToGlobal = Refl0
    mon* {.Any} {.Any} {.Local} {.Local} Refl0 ReflL = Refl0
    mon* {.Any} {.Any} {.Global} {.Global} Refl0 ReflG = Refl0
    mon* {.Any} {.Any} {.Any} {.Any} Refl0 Refl0 = Refl0

    mon+ : {r1 r2 s1 s2 : Locality} →
      Ordering r1 r2 → Ordering s1 s2 → Ordering (r1 +l s1) (r2 +l s2)
    mon+ {.Global} {.Local} {.Global} {.Local} GlobalToLocal GlobalToLocal = GlobalToLocal
    mon+ {.Global} {.Local} {.Any} {.Local} GlobalToLocal AnyToLocal = GlobalToLocal
    mon+ {.Global} {.Local} {.Any} {.Global} GlobalToLocal AnyToGlobal = GlobalToLocal
    mon+ {.Global} {.Local} {.Local} {.Local} GlobalToLocal ReflL = ReflL
    mon+ {.Global} {.Local} {.Global} {.Global} GlobalToLocal ReflG = GlobalToLocal
    mon+ {.Global} {.Local} {.Any} {.Any} GlobalToLocal Refl0 = GlobalToLocal
    mon+ {.Any} {.Local} {.Global} {.Local} AnyToLocal GlobalToLocal = GlobalToLocal
    mon+ {.Any} {.Local} {.Any} {.Local} AnyToLocal AnyToLocal = AnyToLocal
    mon+ {.Any} {.Local} {.Any} {.Global} AnyToLocal AnyToGlobal = AnyToLocal
    mon+ {.Any} {.Local} {.Local} {.Local} AnyToLocal ReflL = ReflL
    mon+ {.Any} {.Local} {.Global} {.Global} AnyToLocal ReflG = GlobalToLocal
    mon+ {.Any} {.Local} {.Any} {.Any} AnyToLocal Refl0 = AnyToLocal
    mon+ {.Any} {.Global} {.Global} {.Local} AnyToGlobal GlobalToLocal = GlobalToLocal
    mon+ {.Any} {.Global} {.Any} {.Local} AnyToGlobal AnyToLocal = AnyToLocal
    mon+ {.Any} {.Global} {.Any} {.Global} AnyToGlobal AnyToGlobal = AnyToGlobal
    mon+ {.Any} {.Global} {.Local} {.Local} AnyToGlobal ReflL = ReflL
    mon+ {.Any} {.Global} {.Global} {.Global} AnyToGlobal ReflG = ReflG
    mon+ {.Any} {.Global} {.Any} {.Any} AnyToGlobal Refl0 = AnyToGlobal
    mon+ {.Local} {.Local} {.Global} {.Local} ReflL GlobalToLocal = ReflL
    mon+ {.Local} {.Local} {.Any} {.Local} ReflL AnyToLocal = ReflL
    mon+ {.Local} {.Local} {.Any} {.Global} ReflL AnyToGlobal = ReflL
    mon+ {.Local} {.Local} {.Local} {.Local} ReflL ReflL = ReflL
    mon+ {.Local} {.Local} {.Global} {.Global} ReflL ReflG = ReflL
    mon+ {.Local} {.Local} {.Any} {.Any} ReflL Refl0 = ReflL
    mon+ {.Global} {.Global} {.Global} {.Local} ReflG GlobalToLocal = GlobalToLocal
    mon+ {.Global} {.Global} {.Any} {.Local} ReflG AnyToLocal = GlobalToLocal
    mon+ {.Global} {.Global} {.Any} {.Global} ReflG AnyToGlobal = ReflG
    mon+ {.Global} {.Global} {.Local} {.Local} ReflG ReflL = ReflL
    mon+ {.Global} {.Global} {.Global} {.Global} ReflG ReflG = ReflG
    mon+ {.Global} {.Global} {.Any} {.Any} ReflG Refl0 = ReflG
    mon+ {.Any} {.Any} {.Global} {.Local} Refl0 GlobalToLocal = GlobalToLocal
    mon+ {.Any} {.Any} {.Any} {.Local} Refl0 AnyToLocal = AnyToLocal
    mon+ {.Any} {.Any} {.Any} {.Global} Refl0 AnyToGlobal = AnyToGlobal
    mon+ {.Any} {.Any} {.Local} {.Local} Refl0 ReflL = ReflL
    mon+ {.Any} {.Any} {.Global} {.Global} Refl0 ReflG = ReflG
    mon+ {.Any} {.Any} {.Any} {.Any} Refl0 Refl0 = Refl0

    assoc* : {r s t : Locality} → ((r *l s) *l t) ≡ (r *l (s *l t))
    assoc* {Local} {Local} {Local} = refl
    assoc* {Local} {Local} {Global} = refl
    assoc* {Local} {Local} {Any} = refl
    assoc* {Local} {Global} {Local} = refl
    assoc* {Local} {Global} {Global} = refl
    assoc* {Local} {Global} {Any} = refl
    assoc* {Local} {Any} {t} = refl
    assoc* {Global} {Local} {Local} = refl
    assoc* {Global} {Local} {Global} = refl
    assoc* {Global} {Local} {Any} = refl
    assoc* {Global} {Global} {Local} = refl
    assoc* {Global} {Global} {Global} = refl
    assoc* {Global} {Global} {Any} = refl
    assoc* {Global} {Any} {t} = refl
    assoc* {Any} {s} {t} = refl

    distrib1 : {r s t : Locality} → (r *l (s +l t)) ≡ ((r *l s) +l (r *l t))
    distrib1 {Local} {s} {t} rewrite leftUnit* {s +l t} | leftUnit* {s} | leftUnit* {t} = refl
    distrib1 {Global} {Local} {Local} = refl
    distrib1 {Global} {Local} {Global} = refl
    distrib1 {Global} {Local} {Any} = refl
    distrib1 {Global} {Global} {Local} = refl
    distrib1 {Global} {Global} {Global} = refl
    distrib1 {Global} {Global} {Any} = refl
    distrib1 {Global} {Any} {Local} = refl
    distrib1 {Global} {Any} {Global} = refl
    distrib1 {Global} {Any} {Any} = refl
    distrib1 {Any} {s} {t} = refl

    -- used by distrib2
    comm* : {x y : Locality} -> x *l y ≡ y *l x
    comm* {Local} {Local} = refl
    comm* {Local} {Global} = refl
    comm* {Local} {Any} = refl
    comm* {Global} {Local} = refl
    comm* {Global} {Global} = refl
    comm* {Global} {Any} = refl
    comm* {Any} {Local} = refl
    comm* {Any} {Global} = refl
    comm* {Any} {Any} = refl

    distrib2prop : {r s t : Locality} → ((r +l s) *l t) ≡ ((r *l t) +l (s *l t))
    distrib2prop {r} {s} {t} rewrite comm* {r +l s} {t} | comm* {r} {t} | comm* {s} {t} = distrib1

    assocPlus : {r s t : Locality} → ((r +l s) +l t) ≡ (r +l (s +l t))
    assocPlus {Local} {Local} {Local} = refl
    assocPlus {Local} {Local} {Global} = refl
    assocPlus {Local} {Local} {Any} = refl
    assocPlus {Local} {Global} {Local} = refl
    assocPlus {Local} {Global} {Global} = refl
    assocPlus {Local} {Global} {Any} = refl
    assocPlus {Local} {Any} {t} = refl
    assocPlus {Global} {Local} {Local} = refl
    assocPlus {Global} {Local} {Global} = refl
    assocPlus {Global} {Local} {Any} = refl
    assocPlus {Global} {Global} {Local} = refl
    assocPlus {Global} {Global} {Global} = refl
    assocPlus {Global} {Global} {Any} = refl
    assocPlus {Global} {Any} {t} = refl
    assocPlus {Any} {s} {t} = refl
