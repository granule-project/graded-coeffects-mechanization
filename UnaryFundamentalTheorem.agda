{-# OPTIONS --allow-unsolved-metas --rewriting #-}

module UnaryFundamentalTheorem where

open import GrCore
open import Data.Unit hiding (_≤_; _≟_)
open import Data.Empty
open import Relation.Binary.PropositionalEquality
open import Data.Product hiding (map)
open import Data.Bool hiding (_≤_; _≟_)
open import Data.Vec hiding (_++_)
open import Data.Nat hiding (_≤_)
open import Data.Fin hiding (_≤_;_+_)
open import Function
open import Data.Maybe hiding (map)
open import Relation.Nullary
open import Data.Sum hiding (map)

open import Semiring

open import OperationalModel
open import RelationalModel

---------------------------------
-- Unary fundamental theorem

-- Terminating pragma needed because in the (App t1 t2) case we need to recursve with (Promote t2) which doesn't look
-- smaller to Agda
{-# TERMINATING #-}
utheorem : {{R : Semiring}} {s : ℕ} {γ : Vec (Term 0) s}
        -> {Γ : Context s} {e : Term s} {τ : Type}
        -> Γ ⊢ e ∶ τ
        -> [ Γ ]Γ γ
        -> [ τ ]e (multisubst γ e)
utheorem {s} {γ} {Γ} {Var x} {τ} (var {s1} {s2} {.τ} {.Γ} {Γ1} {Γ2} pos) context v substi
-- substi : multiredux (multisubst γ e) = v
  rewrite pos with Γ2 | γ | context
... | Empty | x ∷ gee | argInterp , restInterp = conc
  where
    conc : [ τ ]v v
    conc with argInterp (Promote x) refl
    ... | boxInterpV t inner = inner v (isSimultaneousGen {zero} {s1} {zero} {t} {v} {gee} substi )
-- TOODOMABLE - above does the main thing
... | Ext g x | x₁ ∷ gee | Gee = {!!}

{-
... | Empty | x ∷ g | argInterp , restInterp = conc
  where
    conc : [ τ ]v v
    conc with argInterp (Promote x) refl
    ... | boxInterpV t inner = inner v (isSimultaneous' {v} {t} {g} substi)

... | Ext k x | [] | ()
-- same as above just moves down the context (bit of fiddly non key stuff)
... | Ext k x | x₁ ∷ g | argInterp , sndrestInterp = {!!}
-}

utheorem {sz} {γ} {Γ} {App t1 t2} {τ} (app {s} {Γ} {Γ1} {Γ2} {r} {A} {B} typ1 typ2 {pos}) context v1 v1redux
  rewrite pos =
    let
      (bod1 , (fun1redux , bodTy1)) = reduxTheoremAppTy {_} {multisubst γ t1} {multisubst γ t2} {v1} {Empty} {A} {B} (subst (\r -> multiRedux r ≡ v1) (substPresApp {_} {_} {γ} {t1} {t2}) v1redux) (multiSubstTy {sz} {γ} {Γ1} {FunTy A r B} {t1} typ1)
      fun1 = Abs bod1

      ih1 = utheorem {sz} {γ} {Γ1} {t1} {FunTy A r B} typ1 (unaryPlusElimLeftΓ context)
      ih1applied = ih1 fun1 fun1redux

      -- Join up the reductions
      -- multiRedux (App (multisubst' 0 γ t1) (multisubst' 0 γ t2)) ≡ v1
      aeq1 = trans (cong multiRedux (sym (substPresApp {_} {_} {γ} {t1} {t2}))) v1redux
      -- multiRedux (App (Abs var1 bod1) (multisubst' 0 γ t2)) ≡ v1
      aeq2 = trans (sym (multReduxCongruence {_} {multisubst γ t1} {Abs  bod1} {\t1' -> App t1' (multisubst γ t2)} fun1redux)) aeq1
      --
      v1reduxerFull = trans (sym (betaUnderMultiRedux {_} {bod1} {multisubst γ t2})) aeq2

    in extract ih1applied (multisubst γ t2) argument v1 v1reduxerFull
  where
    extract : {s : ℕ} {e : Term (suc s)} -> [ FunTy A r B ]v (Abs e)
           -> (forall (v : Term s)
                 -> [ Box r A ]e (Promote v)
                 -> [ B ]e (syntacticSubst v Data.Fin.zero e))
    extract {s} {e} pre with pre
    ... | funInterpV .e  inner = inner

    argument : [ Box r A ]e (Promote (multisubst γ t2))
    argument =
      let
        ih2 = utheorem {sz} {γ} {r · Γ2} {Promote t2} {Box r A} (pr {Γ' = r · Γ2} {r} typ2 {refl}) (unaryPlusElimRightΓ context)
      in
        subst (\h -> [ Box r A ]e h) (substPresProm {_} {_} {γ} {t2}) ih2

-- # ABS
utheorem {s} {γ} {Γ'} {Abs t} {FunTy A r B} (abs {s1} {s2} {Γ} {Γ1} {Γ2} {Γ'} pos typing {rel}) context v substi rewrite pos | rel =
    subst (\h -> [ FunTy A r B ]v h) thm
      (funInterpV (multisubst' (Data.Vec.map raiseTerm γ) t) body )

  where
    thm : Abs (multisubst' (Data.Vec.map raiseTerm γ) t) ≡ v
    thm =
      let
        qr = cong multiRedux (substPresAbs {_} {_} {γ} {t})
        qr' = trans qr (valuesDontReduce {zero} (absValue (multisubst' (Data.Vec.map raiseTerm γ) t)))
      in trans (sym qr') substi

    body : (v' : Term 0) →
        [ Box r A ]e (Promote v') → [ B ]e
        (syntacticSubst v' zero (multisubst' (Data.Vec.map raiseTerm γ) t))
    body v' arg v1 v1redux rewrite multiSubstComm {s1 + s2} {0} {γ} {v'} {t} =
     let --
      ih = utheorem {suc (s1 + s2)} {v' ∷ γ}  {Ext (Γ1 ,, Γ2) (Grad A r)} {t} {B} (exchange typing) ( arg  , context)
     in ih v1 v1redux


-- # PROMOTION
utheorem {s} {γ} {Γ'} {Promote t} {Box r A} (pr {_} {Γ} {Γ'} typing {prf}) context v substi rewrite prf =
   let
     ih = utheorem {s} {γ} {Γ} {t} {A} typing (unaryTimesElimRightΓ context)
   in
     subst (\h -> [ Box r A ]v h) thm (boxInterpV (multisubst γ t) ih)
  where

    thm : Promote (multisubst γ t) ≡ v
    thm =
       let qr = cong multiRedux (substPresProm {0} {s} {γ} {t})
           qr' = trans qr (valuesDontReduce {zero} {Promote (multisubst γ t)} (promoteValue (multisubst γ t)))
       in sym (trans (sym substi) qr')

-- # Unit
utheorem {_} {γ} {_} {.unit} {.Unit} unitConstr context v substi =
  subst (\h -> [ Unit ]v h) thm unitInterpV
  where
    thm : unit ≡ v
    thm = trans (sym (cong multiRedux (substPresUnit {_} {_} {γ}))) substi

-- # BoolTy
utheorem {_} {γ} {_} {.vtrue} {.BoolTy} trueConstr context v substi =
 subst (\h -> [ BoolTy ]v h) thm boolInterpTrue
  where
    thm : vtrue ≡ v
    thm = trans (sym (cong multiRedux (substPresTrue {_} {_} {γ}))) substi

utheorem {_} {γ} {_} {.vfalse} {.BoolTy} falseConstr context v substi =
 subst (\h -> [ BoolTy ]v h) thm boolInterpFalse
  where
    thm : vfalse ≡ v
    thm = trans (sym (cong multiRedux (substPresFalse {_} {_} {γ}))) substi

-- # If
utheorem {sz} {γ} {Γ} {If tg t1 t2} {B} (if {.sz} {Γ} {Γ1} {Γ2} {.B} {tg} {t1} {t2} {r} {used} typG typ1 typ2 {res}) context v1 v1redux rewrite sym res =
    let
     -- doesn't seem to be used actually here- but more important in the binary case I think
     ih = utheorem {sz} {γ} {Γ1} {tg} {BoolTy} typG (convert context)
    in caseBody
  where
    v1redux' : multiRedux (If (multisubst γ tg) (multisubst γ t1) (multisubst γ t2))  ≡ v1
    v1redux' = trans (cong multiRedux (sym (substPresIf {0} {sz} {γ} {tg} {t1} {t2}))) v1redux

    convert : {sz t : ℕ} {Γ1 Γ2 : Context sz} {γ : Vec (Term t) sz} -> [ (r · Γ1) ++ Γ2 ]Γ γ -> [ Γ1 ]Γ γ
    convert {.0} {_} {Empty} {Empty} {[]} g = tt
    convert {suc sz} {_} {Ext Γ1 (Grad A r1)} {Ext Γ2 (Grad A' r2)} {x ∷ γ} (hd , tl) =
      convertUnaryBox hd , convert {sz} {_} {Γ1} {Γ2} {γ} tl

    caseBody : [ B ]v v1
    caseBody with reduxTheoremBool {_} {multisubst γ tg} {multisubst γ t1} {multisubst γ t2} {v1} v1redux'
    ... | inj₁ trueEv  =
      utheorem {sz} {γ} {Γ2} {t1} {B} typ1 (unaryPlusElimRightΓ context) v1
         (sym (reduxTheoremBool1 {_} {multisubst γ tg} {multisubst γ t1} {multisubst γ t2} {v1} v1redux' trueEv))
    ... | inj₂ falseEv =
      utheorem {sz} {γ} {Γ2} {t2} {B} typ2 (unaryPlusElimRightΓ context) v1
         (sym (reduxTheoremBool2 {_} {multisubst γ tg} {multisubst γ t1} {multisubst γ t2} {v1} v1redux' falseEv))

-- # Unbox
utheorem {s = sz} {γ1} {Γ} {Let t1 t2} {B} (unbox {_} {Γ1} {Γ2} {_} {r} {A} {_} .t1 .t2 typing1 typing2 {prf}) contextInterp v1 v1redux =
  let
       -- Reason about the decomposition of a multireduction on a let
       (e0 , e0redux , bodyRedux1) =
         reduxTheoremLet {0} {multisubst γ1 t1} {multisubst' (map raiseTerm γ1) t2} {v1} (trans (sym (cong multiRedux (substPresLet {zero} {sz} {γ1} {t1}))) v1redux)

       -- Induct on the argument
       ihArg = utheorem {sz} {γ1} {Γ1} {t1} {Box r A} typing1 leftContext (Promote e0) e0redux

       -- Reason about shape of reductions on the body term
       bodyRedux1' = subst (\h -> multiRedux h ≡ v1)
                        (multiSubstComm {sz} {zero} {γ1} {e0}) bodyRedux1

       -- Glue argument induction onto body induction
       ihBody = utheorem {suc sz} {e0 ∷ γ1} {Ext Γ2 (Grad A r)} {t2} {B} typing2  (lifter ihArg , rightContext) v1 bodyRedux1'

   in ihBody

  where
    -- lift a value interpretation to an expression interpretation on a value term
    lifter : {e1 : Term 0} -> [ Box r A ]v (Promote e1) -> [ Box r A ]e (Promote e1)
    lifter {e1} vmeaning v3 v3redux
      rewrite trans (sym (valuesDontReduce {zero} {Promote e1} (promoteValue e1))) v3redux
        = vmeaning

    -- Split context interpretations
    leftContext : [ Γ1 ]Γ γ1
    leftContext = unaryPlusElimLeftΓ {sz} {zero} {γ1} {Γ1} {Γ2} (subst (\h -> [ h ]Γ γ1) prf contextInterp)

    rightContext : [ Γ2 ]Γ γ1
    rightContext = unaryPlusElimRightΓ {sz} {zero} {γ1} {Γ1} {Γ2} (subst (\h -> [ h ]Γ γ1) prf contextInterp)

-- TOODOMABLE

utheorem {s = sz} {γ} {Γ} {tuple t1 t2} {.(Prod _ _)} (prodIntro deriv1 deriv2) context v1 v1redux = {!!}
utheorem {s = sz} {γ} {Γ} {LetProd t1 t2} {B} (prodElim deriv1 deriv2) context v1 v1redux = {!!}
