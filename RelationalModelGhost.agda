{-# OPTIONS --allow-unsolved-metas #-}

module RelationalModelGhost where

open import GrCore hiding (_⊢_∶_)
open import GrCoreGhost

open import Data.Unit hiding (_≤_; _≟_)
open import Data.Empty
open import Relation.Binary.PropositionalEquality
open import Data.Product
open import Data.Bool hiding (_≤_; _≟_)
open import Data.List hiding (_++_)
open import Data.Nat hiding (_≤_)
open import Function
open import Data.Maybe
open import Relation.Nullary
open import Data.Sum

open import Semiring

-- open Semiring.Semiring {{...}} public
-- open NonInterferingSemiring  {{...}} public
-- open InformationFlowSemiring {{...}} public

open import RelationalModel

data InfoContext {{ R : Semiring }} : (r : grade) (adv : grade) -> Set where
  Visible :   {r adv : grade}  -> r ≤ adv -> InfoContext r adv
  Invisible : {r adv : grade}  -> ¬ (r ≤ adv) -> InfoContext r adv

-- Contexts

-- unary
[_]Γg : {{R : Semiring}} -> {s : ℕ} -> ContextG s -> List Term -> Set
[ (Γ , ghostGrade) ]Γg γ = [ Γ ]Γ γ × ⊤

-- binary
⟦_⟧Γg : {{R : Semiring}} -> {s : ℕ} -> ContextG s -> (adv : grade) -> List Term -> List Term -> Set
⟦ (Γ , ghostGrade)   ⟧Γg adv γ1 γ2 = ⟦ Γ ⟧Γ adv γ1 γ2 × InfoContext ghostGrade adv

injPair1 : {A : Set} {B : Set} {a a' : A} {b b' : B} -> (a , b) ≡ (a' , b') -> a ≡ a'
injPair1 refl = refl

injPair2 : {A : Set} {B : Set} {a a' : A} {b b' : B} -> (a , b) ≡ (a' , b') -> b ≡ b'
injPair2 refl = refl

binaryImpliesUnaryGg : {{R : Semiring}} {sz : ℕ} { Γ : Context sz } {adv : grade} {γ1 γ2 : List Term}
                    -> ⟦ Γ ⟧Γ adv γ1 γ2 -> ([ Γ ]Γ γ1) × ([ Γ ]Γ γ2)
binaryImpliesUnaryGg {.0} {Empty} {adv} {_} {_} pre = tt , tt
binaryImpliesUnaryGg {suc sz} {Ext Γ (Grad A r)} {adv} {v1 ∷ γ1} {v2 ∷ γ2} (arg , rest)
  with binaryImpliesUnary {Box r A} {Promote v1} {Promote v2} {adv} arg | binaryImpliesUnaryG {sz} {Γ} {adv} {γ1} {γ2} rest
... | ( arg1 , arg2 ) | ( rest1 , rest2 ) = ( (arg1 , rest1) , (arg2 , rest2) )

promoteLemma : {t t' t'' : Term} -> Promote t ≡ t' -> Σ Term (\t'' -> Promote t'' ≡ t')
promoteLemma {t} {t'} {t''} pre = {!!}

-- # IDEA 1
{-# TERMINATING #-}
biFundamentalTheoremGhost : {{R : Semiring}} {{R' : NonInterferingSemiring R}} {{R'' : InformationFlowSemiring R}} {sz : ℕ}
          {Γ : Context sz} {ghost : grade} {e : Term} {τ : Type}

        -> (Γ , ghost) ⊢ e ∶ τ
        -> {γ1 : List Term} {γ2 : List Term}
        -> (adv : grade)
        -> ⟦ Γ , ghost ⟧Γg adv γ1 γ2
        -> ⟦ Box ghost τ ⟧e adv (Promote (multisubst γ1 e)) (Promote (multisubst γ2 e))

biFundamentalTheoremGhost {_} {Γ} {ghost} {.(Var (Γlength Γ1))} {τ} (var {_} {_} {.τ} {(.Γ , .ghost)} {Γ1} {Γ2} pos) {γ1} {γ2} adv contextInterp v1 v2 v1redux v2redux
 rewrite injPair1 pos | sym (injPair2 pos) | sym v1redux | sym v2redux with Γ1 | γ1 | γ2 | contextInterp
-- var at head of context (key idea, without out loss of generality as position in context is irrelevant
-- to rest of the proof)
... | Empty | a1 ∷ γ1' | a2 ∷ γ2' | ((argInterp , restInterp) , infoContext) = conc

  where

    conc : ⟦ Box ghost τ ⟧v adv (Promote (multisubst (a1 ∷ γ1') (Var 0))) (Promote (multisubst (a2 ∷ γ2') (Var 0)))
    conc with argInterp (Promote a1) (Promote a2) refl refl
    -- goal : ghost ≤ adv
    -- eq   : 1 ≤ adv
    ... | boxInterpBiobs   eq .a1 .a2 inner
       rewrite injPair2 pos | isSimultaneous'' {a1} {γ1'} | isSimultaneous'' {a2} {γ2'} =
          boxInterpBiobs eq a1 a2 inner

    ... | boxInterpBiunobs eq .a1 .a2 inner
       rewrite injPair2 pos | isSimultaneous'' {a1} {γ1'} | isSimultaneous'' {a2} {γ2'} =
          boxInterpBiunobs eq a1 a2 inner

-- var generalisation here
... | _ | _ | _ | _ = {!!}


biFundamentalTheoremGhost {sz} {Γ} {e} {τ} typ {γ1} {γ2} adv contextInterp v1 v2 v1redux v2redux = {!!}


biFundamentalTheoremGhost' : {{R : Semiring}} {{R' : NonInterferingSemiring R}} {{R'' : InformationFlowSemiring R}} {sz : ℕ}
          {Γ : Context sz} {ghost : grade} {e : Term} {τ : Type}

        -> (Γ , ghost) ⊢ e ∶ τ
        -> {γ1 : List Term} {γ2 : List Term}
        -> (adv : grade)
        -> ⟦ Γ ⟧Γ adv γ1 γ2
        -> ⟦ Box ghost τ ⟧v adv (Promote (multisubst γ1 e)) (Promote (multisubst γ2 e))

biFundamentalTheoremGhost' {_} {Γ} {ghost} {.(Var (Γlength Γ1))} {τ} (var {_} {_} {.τ} {(.Γ , .ghost)} {Γ1} {Γ2} pos) {γ1} {γ2} adv contextInterp
 rewrite injPair1 pos | sym (injPair2 pos) with Γ1 | γ1 | γ2 | contextInterp
-- var at head of context (key idea, without out loss of generality as position in context is irrelevant
-- to rest of the proof)
... | Empty | a1 ∷ γ1' | a2 ∷ γ2' | (argInterp , restInterp) = conc

  where

    conc : ⟦ Box ghost τ ⟧v adv (Promote (multisubst (a1 ∷ γ1') (Var 0))) (Promote (multisubst (a2 ∷ γ2') (Var 0)))
    conc with argInterp (Promote a1) (Promote a2) refl refl
    -- goal : ghost ≤ adv
    -- eq   : 1 ≤ adv
    ... | boxInterpBiobs   eq .a1 .a2 inner
       rewrite injPair2 pos | isSimultaneous'' {a1} {γ1'} | isSimultaneous'' {a2} {γ2'} =
          boxInterpBiobs eq a1 a2 inner

    ... | boxInterpBiunobs eq .a1 .a2 inner
       rewrite injPair2 pos | isSimultaneous'' {a1} {γ1'} | isSimultaneous'' {a2} {γ2'} =
          boxInterpBiunobs eq a1 a2 inner

-- var generalisation here
... | _ | _ | _ | _ = {!!}


biFundamentalTheoremGhost' {_} {_} {ghost} {.unit} {.Unit} unitConstr {γ1} {γ2} adv contextInterp with 1R ≤d adv
... | yes p = boxInterpBiobs p {!!} {!!} ?
 -- (subst₂ (\h1 h2 -> ⟦ Unit ⟧v adv h1 h2) (sym thm1) (sym thm2) (unitInterpBi {adv}))
    where
      thm1 : unit ≡  (multisubst' 0 γ1 unit)
      thm1 = ? --trans (sym (cong multiRedux (substPresUnit {γ1} {0}))) {!!}

      thm2 : unit ≡ (multisubst' 0 γ2 unit)
      thm2 = ? -- trans (sym (cong multiRedux (substPresUnit {γ2} {0}))) {!!}
... | no ¬p = {!!}
{- =
  {!!} --
  --
-}

biFundamentalTheoremGhost' {sz} {Γ} {e} {τ} typ {γ1} {γ2} adv contextInterp = {!!}

-- # IDEA 2
{-# TERMINATING #-}
biFundamentalTheoremGhost2 : {{R : Semiring}} {{R' : NonInterferingSemiring R}} {{R'' : InformationFlowSemiring R}} {sz : ℕ}
          {Γ : Context sz} {ghost : grade} {e : Term} {τ : Type}

        -> (Γ , ghost) ⊢ e ∶ τ
        -> {γ1 : List Term} {γ2 : List Term}
        -> (adv : grade)
        -> ⟦ Γ , ghost ⟧Γg adv γ1 γ2
        -> ⟦ τ ⟧e (ghost *R adv) (multisubst γ1 e) (multisubst γ2 e)

biFundamentalTheoremGhost2 {_} {Γ} {ghost} {.(Var (Γlength Γ1))} {τ} (var {_} {_} {.τ} {(.Γ , .ghost)} {Γ1} {Γ2} pos) {γ1} {γ2} adv contextInterp v1 v2 v1redux v2redux rewrite pos | injPair1 pos | (injPair2 pos) | v1redux | v2redux with Γ1 | γ1 | γ2 | contextInterp
... | Empty | a1 ∷ γ1' | a2 ∷ γ2' | ((argInterp , restInterp) , infoContext) = conc
  where
    conc : ⟦ τ ⟧v (1R *R adv) v1 v2
    conc with argInterp (Promote a1) (Promote a2) refl refl
    ... | boxInterpBiobs   eq .a1 .a2 inner
      rewrite leftUnit* {adv} =
          inner v1 v2 (isSimultaneous' {v1} {a1} {γ1'} v1redux) (isSimultaneous' {v2} {a2} {γ2'} v2redux)
    -- problematic here as we cannot connect the unobservability of the output to the input
    ... | boxInterpBiunobs eq .a1 .a2 inner rewrite leftUnit* {adv} = {!!}


-- gen for any variable
... | _ | _ | _ | _ = {!!}


biFundamentalTheoremGhost2 {sz} {Γ} {ghost} {e} {τ} typ {γ1} {γ2} adv contextInterp v1 v2 v1redux v2redux = {!!}

-- # IDEA 2A
{-# TERMINATING #-}
biFundamentalTheoremGhost2a : {{R : Semiring}} {{R' : NonInterferingSemiring R}} {{R'' : InformationFlowSemiring R}} {sz : ℕ}
          {Γ : Context sz} {ghost : grade} {e : Term} {τ : Type}

        -> (Γ , ghost) ⊢ e ∶ τ
        -> {γ1 : List Term} {γ2 : List Term}
        -> (adv : grade)
        -> ⟦ Γ , ghost ⟧Γg (ghost # adv) γ1 γ2
        -> ⟦ τ ⟧e (ghost *R adv) (multisubst γ1 e) (multisubst γ2 e)

biFundamentalTheoremGhost2a {{R}} {{R'}} {{R''}} {_} {Γ} {ghost} {.(Var (Γlength Γ1))} {τ} (var {_} {_} {.τ} {(.Γ , .ghost)} {Γ1} {Γ2} pos) {γ1} {γ2} adv contextInterp v1 v2 v1redux v2redux rewrite pos | injPair1 pos | (injPair2 pos) | v1redux | v2redux with Γ1 | γ1 | γ2 | contextInterp
... | Empty | a1 ∷ γ1' | a2 ∷ γ2' | ((argInterp , restInterp) , infoContext) = conc
  where
    conc : ⟦ τ ⟧v (1R *R adv) v1 v2
    conc with argInterp (Promote a1) (Promote a2) refl refl
    ... | boxInterpBiobs   eq .a1 .a2 inner
      rewrite leftUnit* {adv} =
          let z = inner v1 v2 (isSimultaneous' {v1} {a1} {γ1'} v1redux) (isSimultaneous' {v2} {a2} {γ2'} v2redux)
          -- I guess we can map ⟦ τ ⟧v 1 -> ⟦ τ ⟧v adv ...? as left could be more restricted than right?
          in {!!}
    -- problematic here as we cannot connect the unobservability of the output to the input
    -- ¬ (1 ≤ (1 # adv)
    --
    ... | boxInterpBiunobs eq .a1 .a2 inner rewrite leftUnit* {adv} =
      ⊥-elim (eq (subst (\h -> 1R ≤ h) (trans (sym (absorb# {R} {adv})) (comm# {R} {adv} {1R})) (reflexive≤ {1R}) ))

-- gen for any variable
... | _ | _ | _ | _ = {!!}


biFundamentalTheoremGhost2a {sz} {Γ} {ghost} {e} {τ} typ {γ1} {γ2} adv contextInterp v1 v2 v1redux v2redux = {!!}

{-# TERMINATING #-}
biFundamentalTheoremGhost2b : {{R : Semiring}} {{R' : NonInterferingSemiring R}} {{R'' : InformationFlowSemiring R}} {sz : ℕ}
          {Γ : Context sz} {ghost : grade} {e : Term} {τ : Type}

        -> (Γ , ghost) ⊢ e ∶ τ
        -> {γ1 : List Term} {γ2 : List Term}
        -> (adv : grade)
        -> ⟦ Γ , ghost ⟧Γg (ghost *R adv) γ1 γ2
        -> ⟦ τ ⟧e (ghost *R adv) (multisubst γ1 e) (multisubst γ2 e)

biFundamentalTheoremGhost2b {{R}} {{R'}} {{R''}} {_} {Γ} {ghost} {.(Var (Γlength Γ1))} {τ} (var {_} {_} {.τ} {(.Γ , .ghost)} {Γ1} {Γ2} pos) {γ1} {γ2} adv contextInterp v1 v2 v1redux v2redux rewrite pos | injPair1 pos | (injPair2 pos) | v1redux | v2redux with Γ1 | γ1 | γ2 | contextInterp
... | Empty | a1 ∷ γ1' | a2 ∷ γ2' | ((argInterp , restInterp) , infoContext) = conc
  where
    conc : ⟦ τ ⟧v (1R *R adv) v1 v2
    conc with argInterp (Promote a1) (Promote a2) refl refl
    ... | boxInterpBiobs   eq .a1 .a2 inner
      rewrite leftUnit* {adv} =
          let z = inner v1 v2 (isSimultaneous' {v1} {a1} {γ1'} v1redux) (isSimultaneous' {v2} {a2} {γ2'} v2redux)
          -- I guess we can map ⟦ τ ⟧v 1 -> ⟦ τ ⟧v adv ...? as left could be more restricted than right?
          in z
    -- problematic here as we cannot connect the unobservability of the output to the input
    -- ¬ (1 ≤ (1 # adv)
    --
    ... | boxInterpBiunobs eq .a1 .a2 inner rewrite leftUnit* {adv} =
    -- NOPE
     {!!}
    --  ⊥-elim (eq (subst (\h -> 1R ≤ h) (trans (sym (absorb# {R} {adv})) (comm# {R} {adv} {1R})) (reflexive≤ {1R}) ))

-- gen for any variable
... | _ | _ | _ | _ = {!!}


biFundamentalTheoremGhost2b {sz} {Γ} {ghost} {e} {τ} typ {γ1} {γ2} adv contextInterp v1 v2 v1redux v2redux = {!!}


-- # IDEA 3
{-# TERMINATING #-}
biFundamentalTheoremGhost3 : {{R : Semiring}} {{R' : NonInterferingSemiring R}} {{R'' : InformationFlowSemiring R}} {sz : ℕ}
          {Γ : Context sz} {ghost : grade} {e : Term} {τ : Type}

        -> (Γ , ghost) ⊢ e ∶ τ
        -> {γ1 : List Term} {γ2 : List Term}
        -> (adv : grade)
        -> ⟦ Γ , ghost ⟧Γg (adv # ghost) γ1 γ2
        -> ⟦ τ ⟧e          (adv # ghost) (multisubst γ1 e) (multisubst γ2 e)

biFundamentalTheoremGhost3 {{R}} {{R'}} {{R''}} {_} {Γ} {ghost} {.(Var (Γlength Γ1))} {τ} (var {_} {_} {.τ} {(.Γ , .ghost)} {Γ1} {Γ2} pos) {γ1} {γ2} adv contextInterp v1 v2 v1redux v2redux rewrite pos | injPair1 pos | injPair2 pos | v1redux | v2redux with Γ1 | γ1 | γ2 | contextInterp
-- var at head of context (key idea, without out loss of generality as p```r`tosition in context is irrelevant
-- to rest of the proof)
... | Empty | a1 ∷ γ1' | a2 ∷ γ2' | ((argInterp , restInterp) , infoContext) = conc

  where

    conc : ⟦ τ ⟧v (adv # 1R) v1 v2
    conc with argInterp (Promote a1) (Promote a2) refl refl
    -- inner     : ⟦ τ ⟧e ((R'' InformationFlowSemiring.# adv) 1R) a1 a2
    -- eq        : ghost ≤ adv # ghost
    -- goal      : ⟦ τ ⟧v adv v1 v2
    ... | boxInterpBiobs   eq .a1 .a2 inner =
        let eqa1 = isSimultaneous' {v1} {a1} {γ1'} v1redux
            eqa2 = isSimultaneous' {v2} {a2} {γ2'} v2redux
        in inner v1 v2 eqa1 eqa2
        -- eq : ¬ (1 ≤ (adv # 1r))
        --ghost = 1
    ... | boxInterpBiunobs eq .a1 .a2 inner =
      ⊥-elim (eq (subst (\h -> 1R ≤ h) (sym (absorb# {R} {adv})) (reflexive≤ {1R})))

-- var generalisation here
... | _ | _ | _ | _ = {!!}

biFundamentalTheoremGhost3 {_} {Γ} {ghost} {e} {τ} typing {γ1} {γ2} adv contextInterp v1 v2 v1redux v2redux = {!!}


-- BAD because it requires 1 # adv = adv which is patently false.
biFundamentalTheoremGhost4 : {{R : Semiring}} {{R' : NonInterferingSemiring R}} {{R'' : InformationFlowSemiring R}} {sz : ℕ}
          {Γ : Context sz} {ghost : grade} {e : Term} {τ : Type}

        -> (Γ , ghost) ⊢ e ∶ τ
        -> {γ1 : List Term} {γ2 : List Term}
        -> (adv : grade)
        -> ⟦ Γ , ghost ⟧Γg (adv # ghost) γ1 γ2
        -> ⟦ τ ⟧e          adv (multisubst γ1 e) (multisubst γ2 e)

biFundamentalTheoremGhost4 {{R}} {{R'}} {{R''}} {_} {Γ} {ghost} {.(Var (Γlength Γ1))} {τ} (var {_} {_} {.τ} {(.Γ , .ghost)} {Γ1} {Γ2} pos) {γ1} {γ2} adv contextInterp v1 v2 v1redux v2redux rewrite pos | injPair1 pos | injPair2 pos | v1redux | v2redux with Γ1 | γ1 | γ2 | contextInterp
-- var at head of context (key idea, without out loss of generality as p```r`tosition in context is irrelevant
-- to rest of the proof)
... | Empty | a1 ∷ γ1' | a2 ∷ γ2' | ((argInterp , restInterp) , infoContext) = conc

  where

    conc : ⟦ τ ⟧v adv v1 v2
    conc with argInterp (Promote a1) (Promote a2) refl refl
    -- inner     : ⟦ τ ⟧e ((R'' InformationFlowSemiring.# adv) 1R) a1 a2
    -- eq        : ghost ≤ adv # ghost
    -- goal      : ⟦ τ ⟧v adv v1 v2
    ... | boxInterpBiobs   eq .a1 .a2 inner =
        let eqa1 = isSimultaneous' {v1} {a1} {γ1'} v1redux
            eqa2 = isSimultaneous' {v2} {a2} {γ2'} v2redux
        in {!!} -- inner v1 v2 eqa1 eqa2 -- UHOH requires 1 # adv = adv  which is false
        -- eq : ¬ (1 ≤ (adv # 1r))
        --ghost = 1
    ... | boxInterpBiunobs eq .a1 .a2 inner =
      ⊥-elim (eq (subst (\h -> 1R ≤ h) (sym (absorb# {R} {adv})) (reflexive≤ {1R})))

-- var generalisation here
... | _ | _ | _ | _ = {!!}

biFundamentalTheoremGhost4 {_} {Γ} {ghost} {e} {τ} typing {γ1} {γ2} adv contextInterp v1 v2 v1redux v2redux = {!!}


biFundamentalTheoremGhost5 : {{R : Semiring}} {{R' : NonInterferingSemiring R}} {{R'' : InformationFlowSemiring R}} {sz : ℕ}
          {Γ : Context sz} {ghost : grade} {e : Term} {τ : Type}

        -> (Γ , ghost) ⊢ e ∶ τ
        -> {γ1 : List Term} {γ2 : List Term}
        -> (adv : grade)
        -> ⟦ Γ , adv # ghost ⟧Γg adv γ1 γ2
        -> ⟦ τ ⟧e                (adv # ghost) (multisubst γ1 e) (multisubst γ2 e)

biFundamentalTheoremGhost5 {{R}} {{R'}} {{R''}} {_} {Γ} {ghost} {.(Var (Γlength Γ1))} {τ} (var {_} {_} {.τ} {(.Γ , .ghost)} {Γ1} {Γ2} pos) {γ1} {γ2} adv contextInterp v1 v2 v1redux v2redux rewrite pos | injPair1 pos | injPair2 pos | v1redux | v2redux with Γ1 | γ1 | γ2 | contextInterp
-- var at head of context (key idea, without out loss of generality as p```r`tosition in context is irrelevant
-- to rest of the proof)
... | Empty | a1 ∷ γ1' | a2 ∷ γ2' | ((argInterp , restInterp) , infoContext) = conc

  where
    convertor : {A : Type} -> ⟦ A ⟧v adv v1 v2 -> ⟦ A ⟧v 1R v1 v2
    convertor {FunTy A r A₁} (funInterpBi e1 e2 x x₁ x₂) = {!!}
    convertor {Unit} unitInterpBi = unitInterpBi
    convertor {Box r A} (boxInterpBiobs preq t1 t2 inner) = {!!}
    convertor {Box r A} (boxInterpBiunobs x t1 t2 x₁) = {!!}
    convertor {BoolTy} boolInterpTrueBi = {!!}
    convertor {BoolTy} boolInterpFalseBi = {!!}

    conc : ⟦ τ ⟧v (adv # 1R) v1 v2
    conc with argInterp (Promote a1) (Promote a2) refl refl
    -- inner     : ⟦ τ ⟧e ((R'' InformationFlowSemiring.# adv) 1R) a1 a2
    -- eq        : ghost ≤ adv # ghost
    -- goal      : ⟦ τ ⟧v adv v1 v2
    ... | boxInterpBiobs   eq .a1 .a2 inner =
        let eqa1 = isSimultaneous' {v1} {a1} {γ1'} v1redux
            eqa2 = isSimultaneous' {v2} {a2} {γ2'} v2redux
        in {!!} -- inner v1 v2 eqa1 eqa2 -- UHOH requires 1 # adv = adv  which is false
        -- eq : ¬ (1 ≤ (adv # 1r))
        --ghost = 1
    ... | boxInterpBiunobs eq .a1 .a2 inner = {!!}
      -- ⊥-elim (eq (subst (\h -> 1R ≤ h) (sym (absorb# {R} {adv})) (reflexive≤ {1R})))

-- var generalisation here
... | _ | _ | _ | _ = {!!}

biFundamentalTheoremGhost5 {_} {Γ} {ghost} {e} {τ} typing {γ1} {γ2} adv contextInterp v1 v2 v1redux v2redux = {!!}

informationContextBuilder : {{R : Semiring}} {{R' : NonInterferingSemiring R}} {{R'' : InformationFlowSemiring R}}
  {r s adv : grade} -> r ≤ s -> r ≢ s -> InfoContext (s *R default) (r # (s *R default))
informationContextBuilder {r} {s} {adv} pre neg with  s ≤d r
informationContextBuilder {r} {s} {adv} pre neg | yes p = ⊥-elim (neg (antisymmetry pre p))
informationContextBuilder {r} {s} {adv} pre neg | no ¬p with (s *R default) ≤d (r # (s *R default))
informationContextBuilder {r = r} {s} {adv} pre neg | no ¬p | yes p = Visible p
informationContextBuilder {r = r} {s} {adv} pre neg | no ¬p | no ¬p₁ = Invisible ¬p₁

informationContextBuilder' : {{R : Semiring}} {{R' : NonInterferingSemiring R}} {{R'' : InformationFlowSemiring R}}
  {r s : grade} -> InfoContext (s *R default) (r # (s *R default))
informationContextBuilder' {r} {s} with (s *R default) ≤d (r # (s *R default))
... | yes p = Visible p
... | no ¬p = Invisible ¬p

-- Non-interference result for the ghost calculus
nonInterferenceGhost :
   {{R : Semiring}} {{R' : NonInterferingSemiring R}} {{R'' : InformationFlowSemiring R}}
   {e : Term} {r s : grade} {pre : r ≤ s} {nonEq : r ≢ s}
        -> (Ext Empty (Grad BoolTy s) , r) ⊢ e ∶ Box r BoolTy

        -> (v1 v2 : Term)
        -> (Empty , default) ⊢ v1 ∶ BoolTy
        -> (Empty , default) ⊢ v2 ∶ BoolTy
        -> Value v1
        -> Value v2

        -> multiRedux (syntacticSubst v1 0 e) == multiRedux (syntacticSubst v2 0 e)

nonInterferenceGhost {{R}} {{R'}} {{R''}} {e} {r} {s} {pre} {nonEq} typing v1 v2 v1typing v2typing isvalv1 isvalv2 with
    -- we can think of r as the adversary

    -- Apply fundamental binary theorem to v1
    biFundamentalTheoremGhost5 {zero} {Empty} {s *R default} {Promote v1} {Box s BoolTy}
    --  Invisible {s *R default} {r} {!trans pre (sym (unit# {s})) !}
    -- InfoContext
    --  ((R Semiring.*R s) (InformationFlowSemiring.default R''))
    --  ((R'' InformationFlowSemiring.# r)
    --   ((R Semiring.*R s) (InformationFlowSemiring.default R''))

-- informationContextBuilder' {r} {s}
                  (pr {_} {(Empty , default)} {Empty , s *R default} {s} {BoolTy} {v1} v1typing {refl}) {[]} {[]} r (tt , {!!}) (Promote v1) (Promote v1)
                  (valuesDontReduce {Promote v1} (promoteValue v1))
                  (valuesDontReduce {Promote v1} (promoteValue v1))
    -- Apply fundamental binary theorem to v2
  | biFundamentalTheoremGhost5 {zero} {Empty} {s *R default} {Promote v2} {Box s BoolTy}
                  (pr {_} {(Empty , default )} {Empty , s *R default} {s} {BoolTy} {v2} v2typing {refl})  {[]} {[]} r (tt , {!!}) (Promote v2) (Promote v2)
                  (valuesDontReduce {Promote v2} (promoteValue v2))
                  (valuesDontReduce {Promote v2} (promoteValue v2))
                  -- goal : s ≤ r
                  -- pre : r ≤ s
                  -- pre1 : s ≤ (r # (s * default))
... | boxInterpBiobs pre1 .v1 .v1 inner1 |  boxInterpBiobs pre2 .v2 .v2 inner2 = ⊥-elim ((nonEq (antisymmetry pre {!!}))) --(nonEq (antisymmetry pre {!!}))
... | boxInterpBiobs pre1 .v1 .v1 inner1 | boxInterpBiunobs pre2 .v2 .v2 inner2 = ⊥-elim (⊥-elim (pre2 pre1))
... | boxInterpBiunobs pre1 .v1 .v1 inner1 | boxInterpBiobs pre2 .v2 .v2 inner2 = ⊥-elim (⊥-elim (pre1 pre2))
... | boxInterpBiunobs pre1 .v1 .v1 (valv1 , valv1') | boxInterpBiunobs pre2 .v2 .v2 (valv2 , valv2') =
 let
   -- Show that substituting v1 and evaluating yields a value
   -- and since it is a graded modal type then this value is necessarily
   -- of the form Promote v1''
   substTy1 = substitutionG {zero} {zero} {Ext Empty (Grad BoolTy s)} {Empty} {Empty} {Empty} {r} {default} {s} typing refl v1typing
   (v1'' , prf1) = promoteValueLemmaG {_} {r} {r +R (s *R default)} {BoolTy} (preservationG {zero} {Empty} {Box r BoolTy} {syntacticSubst v1 0 e} substTy1) (multiReduxProducesValuesG substTy1)

   -- ... same as above but for v2 ... leading to result of Promote v2''
   substTy2  = substitutionG {zero} {zero} {Ext Empty (Grad BoolTy s)} {Empty} {Empty} {Empty} {r} {default} {s} typing refl v2typing
   (v2'' , prf2) = promoteValueLemmaG {_} {r} {r +R (s *R default)} {BoolTy} (preservationG {zero} substTy2) (multiReduxProducesValuesG substTy2)

   -- Apply fundamental binary theorem on the result with the values coming from syntacitcally substituting
   -- then evaluating
   inner' = subst (\h -> ⟦ Box s BoolTy ⟧e h (Promote v1) (Promote v2)) (sym (idem# {R} {r})) (inner valv1' valv2')
--   res = biFundamentalTheoremGhost5 {1} {Ext Empty (Grad BoolTy s)} {r} {e} {Box r BoolTy} typing {v1 ∷ []} {v2 ∷ []} r
--          ((inner' , tt) , Visible {r} {r # r} (subst (\h -> r ≤ h) (sym (idem# {R} {r})) reflexive≤)) (Promote v1'') (Promote v2'') prf1 prf2
   res = biFundamentalTheoremGhost5 {1} {Ext Empty (Grad BoolTy s)} {r} {e} {Box r BoolTy} typing {v1 ∷ []} {v2 ∷ []} r
          ((inner valv1' valv2' , tt) , Visible {r # r} {r} (subst (\h -> h ≤ r) (sym (idem# {R} {r})) reflexive≤)) (Promote v1'') (Promote v2'') prf1 prf2


   -- Boolean typed (low) values are equal inside the binary interepration
   res' = subst (\h -> ⟦ Box r BoolTy ⟧v h (Promote v1'') (Promote v2'')) (idem# {R} {r}) res
   boolTyEq = boolBinaryExprInterpEquality v1'' v2'' (unpack res') -- res

   -- Plug together the equalities
     -- Promote
   eq = PromoteEq {v1''} {v2''} (embedReduxCong {v1''} {v2''} boolTyEq)
   eq2 = transFullBetaEq (embedEq prf1) eq

 in transFullBetaEq eq2 (embedEq (sym prf2))
   where

     inner : [ BoolTy ]e v1 -> [ BoolTy ]e v2 -> ⟦ Box s BoolTy ⟧e r (Promote v1) (Promote v2)
     inner av1 av2 v3 v4 v3redux v4redux
       rewrite trans (sym v3redux) (valuesDontReduce {Promote v1} (promoteValue v1))
             | trans (sym v4redux) (valuesDontReduce {Promote v2} (promoteValue v2)) =
       boxInterpBiunobs (antisymmetryAlt {R} {R'} {r} {s} pre nonEq) v1 v2 (av1 , av2)

     -- Helper to unpack interpretation type
     unpack : {v1 v2 : Term} -> ⟦ Box r BoolTy ⟧v r (Promote v1) (Promote v2) -> ⟦ BoolTy ⟧e r v1 v2
     unpack {v1} {v2} (boxInterpBiobs _ .v1 .v2 innerExprInterp) = innerExprInterp
     unpack {v1} {v2} (boxInterpBiunobs eq .v1 .v2 innerExprInterp) = ⊥-elim (eq (reflexive≤ {r}))

-- Non-interference result for the ghost calculus
nonInterferenceGhost1 :
   {{R : Semiring}} {{R' : NonInterferingSemiring R}} {{R'' : InformationFlowSemiring R}}
   {e : Term} {r s : grade} {pre : r ≤ s} {nonEq : r ≢ s}
        -> (Ext Empty (Grad BoolTy s) , r) ⊢ e ∶ Box r BoolTy

        -> (v1 v2 : Term)
        -> (Empty , default) ⊢ v1 ∶ BoolTy
        -> (Empty , default) ⊢ v2 ∶ BoolTy
        -> Value v1
        -> Value v2

        -> multiRedux (syntacticSubst v1 0 e) == multiRedux (syntacticSubst v2 0 e)

nonInterferenceGhost1 {{R}} {{R'}} {{R''}} {e} {r} {s} {pre} {nonEq} typing v1 v2 v1typing v2typing isvalv1 isvalv2 with
    -- we can think of r as the adversary

    -- Apply fundamental binary theorem to v1
    biFundamentalTheoremGhost' {zero} {Empty} {s *R default} {Promote v1} {Box s BoolTy}
                  (pr {_} {(Empty , default)} {Empty , s *R default} {s} {BoolTy} {v1} v1typing {refl}) {[]} {[]} r tt
    -- Apply fundamental binary theorem to v2
  | biFundamentalTheoremGhost' {zero} {Empty} {s *R default} {Promote v2} {Box s BoolTy}
                  (pr {_} {(Empty , default )} {Empty , s *R default} {s} {BoolTy} {v2} v2typing {refl})  {[]} {[]} r tt
                  -- goal : s ≤ r
                  -- pre : r ≤ s
                  -- pre1 : s ≤ (r # (s * default))

-- Issue appears to be if r = Dunno and s = Private
-- i.e., we want to take
--
--        Empty, default |- v1 : BoolTy
--        -----------------------------------------
--        Empty, s * default |- [v1] : [] s BoolTy
--
--        Private * default = default (of course because Private = 1)
--
--        Empty, default |- v1 : BoolTy
--        -----------------------------------------
--        Empty, default |- [v1] : [] Private BoolTy

--        but biFundamentalTheorem' puts a ghost on the output so when we are really considering
--        (s  * default) <= r here

--        [] (s * default) ([] Private BoolTy)

--        so perhaps we need to unpeel another later...

--        which in this tricky case case is Dunno <= Dunno which is true - but this only means we can see down to the
--        boxing underneath...
--
--         but we have that ¬ (Private <= Dunno) so this should be unobservable here.. what am I missing?


... | boxInterpBiobs pre1 (Promote .v1) (Promote .v1) inner1 | boxInterpBiobs pre2 (Promote .v2) (Promote .v2) inner2 =
  ⊥-elim notPossible
  where
    notPossible : ⊥
    notPossible with inner1 (Promote v1) (Promote v1) refl refl | inner2 (Promote v2) (Promote v2) refl refl
    ... | boxInterpBiobs   prei1 .v1 .v1 inneri1 | _ = ⊥-elim (antisymmetryAlt {R} {R'} pre nonEq prei1)
    ... | boxInterpBiunobs prei1 .v1 .v1 inneri1 | boxInterpBiobs   prei2 .v2 .v2 inneri2 = ⊥-elim (antisymmetryAlt {R} {R'} pre nonEq prei2)

--- maybe this okay though and we can work from here similar to the one below....(a bit like old proof)
    ... | boxInterpBiunobs prei1 .v1 .v1 inneri1 | boxInterpBiunobs prei2 .v2 .v2 inneri2 = {!!}

  -- ⊥-elim ((nonEq (antisymmetry pre {!!}))) --(nonEq (antisymmetry pre {!!}))
... | boxInterpBiobs pre1 (Promote .v1) (Promote .v1) inner1 | boxInterpBiunobs pre2 (Promote .v2) (Promote .v2) inner2 = ⊥-elim (⊥-elim (pre2 pre1))
... | boxInterpBiunobs pre1 (Promote .v1) (Promote .v1) inner1 | boxInterpBiobs pre2 (Promote .v2) (Promote .v2) inner2 = ⊥-elim (⊥-elim (pre1 pre2))
... | boxInterpBiunobs pre1 (Promote .v1) (Promote .v1) (valv1 , valv1') | boxInterpBiunobs pre2 (Promote .v2) (Promote .v2) (valv2 , valv2') =
 let
   -- Show that substituting v1 and evaluating yields a value
   -- and since it is a graded modal type then this value is necessarily
   -- of the form Promote v1''
   substTy1 = substitutionG {zero} {zero} {Ext Empty (Grad BoolTy s)} {Empty} {Empty} {Empty} {r} {default} {s} typing refl v1typing
   (v1'' , prf1) = promoteValueLemmaG {_} {r} {r +R (s *R default)} {BoolTy} (preservationG {zero} {Empty} {Box r BoolTy} {syntacticSubst v1 0 e} substTy1) (multiReduxProducesValuesG substTy1)

   -- ... same as above but for v2 ... leading to result of Promote v2''
   substTy2  = substitutionG {zero} {zero} {Ext Empty (Grad BoolTy s)} {Empty} {Empty} {Empty} {r} {default} {s} typing refl v2typing
   (v2'' , prf2) = promoteValueLemmaG {_} {r} {r +R (s *R default)} {BoolTy} (preservationG {zero} substTy2) (multiReduxProducesValuesG substTy2)

   -- Apply fundamental binary theorem on the result with the values coming from syntacitcally substituting
   -- then evaluating
   res = biFundamentalTheoremGhost' {1} {Ext Empty (Grad BoolTy s)} {r} {e} {Box r BoolTy} typing {v1 ∷ []} {v2 ∷ []} r
          (inner (extr valv1') (extr valv2') , tt)

   -- unpack the result based on the reducability up to promotion
   res' = unpack (unpack res (Promote v1'') (Promote v2'') prf1 prf2)
   boolTyEq = boolBinaryExprInterpEquality v1'' v2'' res'

   -- Plug together the equalities
     -- Promote
   eq = PromoteEq {v1''} {v2''} (embedReduxCong {v1''} {v2''} boolTyEq)
   eq2 = transFullBetaEq (embedEq prf1) eq

 in transFullBetaEq eq2 (embedEq (sym prf2))
   where
     extr : {v1 : Term} -> [ Box s BoolTy ]e (Promote v1) -> [ BoolTy ]e v1
     extr {v1} pre v redux with pre (Promote v1) refl
     ... | boxInterpV .v1 inner' =  let k = inner' v redux in k

     inner : [ BoolTy ]e v1 -> [ BoolTy ]e v2 -> ⟦ Box s BoolTy ⟧e r (Promote v1) (Promote v2)
     inner av1 av2 v3 v4 v3redux v4redux
       rewrite trans (sym v3redux) (valuesDontReduce {Promote v1} (promoteValue v1))
             | trans (sym v4redux) (valuesDontReduce {Promote v2} (promoteValue v2)) =
       boxInterpBiunobs (antisymmetryAlt {R} {R'} {r} {s} pre nonEq) v1 v2 (av1 , av2)

     -- Helper to unpack interpretation type
     unpack : {v1 v2 : Term} {A : Type} -> ⟦ Box r A ⟧v r (Promote v1) (Promote v2) -> ⟦ A ⟧e r v1 v2
     unpack {v1} {v2} (boxInterpBiobs _ .v1 .v2 innerExprInterp) = innerExprInterp
     unpack {v1} {v2} (boxInterpBiunobs eq .v1 .v2 innerExprInterp) = ⊥-elim (eq (reflexive≤ {r}))
