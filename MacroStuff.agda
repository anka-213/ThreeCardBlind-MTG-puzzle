open import Function
open import Data.List
open import Data.Unit
open import Reflection
print-repr : Name → Term → TC ⊤
print-repr trm hole = do
    dfn ← getDefinition trm
    -- qDfn ← {! quoteTC dfn  !}
    typeError $ strErr "The expression\n  " ∷
                    termErr (quoteTerm dfn) ∷
                    []
macro
    get-repr! : Name → Term → TC ⊤
    get-repr! trm hole = do
        dfn ← getDefinition trm
        qDfn ← quoteTC dfn
        unify qDfn hole
    print-repr! : Name → Term → TC ⊤
    print-repr! trm hole = do
        tType ← getType trm
        rawType ← quoteTC tType
        dfn ← getDefinition trm
        qDfn ← quoteTC dfn
        typeError $ strErr "Printing type and definition:\n    " ∷
                    nameErr trm ∷
                    strErr " : " ∷
                    termErr tType ∷
                    strErr "\n    " ∷
                    nameErr trm ∷
                    strErr " = " ∷
                    termErr qDfn ∷
                    strErr "\n\nRaw type:\n    " ∷
                    nameErr trm ∷
                    strErr " : " ∷
                    termErr rawType ∷
                    -- strErr "\nContains\n    " ∷
                    []

private
    data Example (t : ⊤) : Set where
        ex1 : ⊤ → Example tt

    -- useEx : ⊤
    -- useEx = {! print-repr! Example  !}

-- IDEA for how to make a data type enumerator macro:
-- Look at type of data and constructor. Remove the arguments that come from the datatype itself and
-- make a product of the arguments of the constructor

{-
>>> print-repr! Example
Printing type and definition:
    Example : (t : ⊤) → Set₀
    Example = data-type 1 (quote ex1 ∷ [])
Raw type:
    Example : pi
              (arg (arg-info visible (modality relevant quantity-ω))
               (def (quote ⊤) []))
              (abs "t" (agda-sort (Sort.lit 0)))

>>> print-repr! ex1
Printing type and definition:
Printing type and definition:
    ex1 : {@0 t : ⊤} (z : ⊤) → Example tt
    ex1 = data-cons (quote Example)
Raw type:
    ex1 : pi
          (arg (arg-info hidden (modality relevant quantity-0))
           (def (quote ⊤) []))
          (abs "t"
           (pi
            (arg (arg-info visible (modality relevant quantity-ω))
             (def (quote ⊤) []))
            (abs "_"
             (def (quote Example)
              (arg (arg-info visible (modality relevant quantity-ω))
               (con (quote tt) [])
               ∷ [])))))
when checking that the expression unquote (print-repr! (quote ex1))
has type ⊤

-}



-- repr-macro : Nat → Term → TC ⊤
-- repr-macro n hole =
--   withNormalisation false $
--   dontReduceDefs don't-reduce $ do
--   tm ← quoteTC n
--   e , vs ← build-expr empty-vars tm
--   size , env ← environment vs
--   repr ← normalise $ def (quote ↓_) (size h∷ e v∷ [])
--   typeError $ strErr "The expression\n  " ∷
--                 termErr tm ∷
--               strErr "\nIs represented by the expression\n  " ∷
--                 termErr e ∷
--               strErr "\nAnd the polynomial\n  " ∷
--                 termErr repr ∷
--               strErr "\nThe environment is\n  " ∷
--                 termErr env ∷ []

{-
        qAction = {! get-repr! Action  !}
        data-type 1
            (quote ACastWalker1 ∷
            quote ACastWalker2 ∷
            quote ACastElixir ∷
            quote AActivateWalker1 ∷
            quote AActivateWalker2 ∷
            quote AActivateElixir ∷
            quote ADeclareAttackers ∷
            quote ADeclareBlockers ∷ quote ADoNothing ∷ [])
-}

{-
Printing type and definition:
    Action : (@0 s : GameState) (@0 p : Player) → Set₀
    Action = data-type 1
             (quote ACastWalker1 ∷
              quote ACastWalker2 ∷
              quote ACastElixir ∷
              quote AActivateWalker1 ∷
              quote AActivateWalker2 ∷
              quote AActivateElixir ∷
              quote ADeclareAttackers ∷
              quote ADeclareBlockers ∷ quote ADoNothing ∷ [])
Raw type:
    Action : pi
             (arg (arg-info visible (modality relevant quantity-0))
              (def (quote GameState) []))
             (abs "s"
              (pi
               (arg (arg-info visible (modality relevant quantity-0))
                (def (quote Player) []))
               (abs "_" (agda-sort (Sort.lit 0)))))
when checking that the expression
unquote (print-repr! (quote Action)) has type Type
-}

{-
Printing type and definition:
    ACastWalker1 : {@0 s : GameState} {p : Player}
                   (@0 isActive : p ≡ .activePlayer s) (@0 inMain : isMain (.phase s))
                   (@0 hasMana₁ : HasMana (stateOfPlayer s p) Two)
                   (@0 isInHand : .walker1State (stateOfPlayer s p) ≡ InHand) →
                   Action s p
    ACastWalker1 = data-cons (quote Action)
Raw type:
    ACastWalker1 : pi
                   (arg (arg-info hidden (modality relevant quantity-0))
                    (def (quote GameState) []))
                   (abs "s"
                    (pi
                     (arg (arg-info hidden (modality relevant quantity-ω))
                      (def (quote Player) []))
                     (abs "p"
                      (pi
                       (arg (arg-info visible (modality relevant quantity-0))
                        (def (quote _≡_)
                         (arg (arg-info hidden (modality relevant quantity-ω))
                          (def (quote Agda.Primitive.lzero) [])
                          ∷
                          arg (arg-info hidden (modality relevant quantity-ω))
                          (def (quote Player) [])
                          ∷
                          arg (arg-info visible (modality relevant quantity-ω)) (var 0 []) ∷
                          arg (arg-info visible (modality relevant quantity-ω))
                          (def (quote activePlayer)
                           (arg (arg-info visible (modality relevant quantity-ω)) (var 1 []) ∷
                            []))
                          ∷ [])))
                       (abs "isActive"
                        (pi
                         (arg (arg-info visible (modality relevant quantity-0))
                          (def (quote isMain)
                           (arg (arg-info visible (modality relevant quantity-ω))
                            (def (quote phase)
                             (arg (arg-info visible (modality relevant quantity-ω)) (var 2 []) ∷
                              []))
                            ∷ [])))
                         (abs "inMain"
                          (pi
                           (arg (arg-info visible (modality relevant quantity-0))
                            (def (quote HasMana)
                             (arg (arg-info hidden (modality relevant quantity-0)) (var 2 []) ∷
                              arg (arg-info visible (modality relevant quantity-ω))
                              (def (quote stateOfPlayer)
                               (arg (arg-info visible (modality relevant quantity-ω)) (var 3 []) ∷
                                arg (arg-info visible (modality relevant quantity-ω)) (var 2 []) ∷
                                []))
                              ∷
                              arg (arg-info visible (modality relevant quantity-ω))
                              (con (quote Two) [])
                              ∷ [])))
                           (abs "hasMana"
                            (pi
                             (arg (arg-info visible (modality relevant quantity-0))
                              (def (quote _≡_)
                               (arg (arg-info hidden (modality relevant quantity-ω))
                                (def (quote Agda.Primitive.lzero) [])
                                ∷
                                arg (arg-info hidden (modality relevant quantity-ω))
                                (def (quote CardPosition)
                                 (arg (arg-info visible (modality relevant quantity-0))
                                  (con (quote Walker) [])
                                  ∷ []))
                                ∷
                                arg (arg-info visible (modality relevant quantity-ω))
                                (def (quote walker1State)
                                 (arg (arg-info hidden (modality relevant quantity-0)) unknown ∷
                                  arg (arg-info visible (modality relevant quantity-ω))
                                  (def (quote stateOfPlayer)
                                   (arg (arg-info visible (modality relevant quantity-ω)) (var 4 [])
                                    ∷
                                    arg (arg-info visible (modality relevant quantity-ω)) (var 3 [])
                                    ∷ []))
                                  ∷ []))
                                ∷
                                arg (arg-info visible (modality relevant quantity-ω))
                                (con (quote InHand)
                                 (arg (arg-info hidden (modality relevant quantity-0)) unknown ∷
                                  []))
                                ∷ [])))
                             (abs "isInHand"
                              (def (quote Action)
                               (arg (arg-info visible (modality relevant quantity-0)) (var 5 []) ∷
                                arg (arg-info visible (modality relevant quantity-0)) (var 4 []) ∷
                                [])))))))))))))
-}
