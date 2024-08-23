open import Data.Bool
open import Data.Nat
open import Data.Nat.Properties
open import Data.Product
open import Data.Sum.Base
open import Data.Unit
open import Function
open import Relation.Binary.PropositionalEquality

open import HangarbackWalker

open PlayerState

mapPlayer : ∀ p → GameState → (PlayerState p → PlayerState p) → GameState
-- mapPlayer p s f = record s { ozzieState = f (GameState.ozzieState s) }
--   where
--     new-states : PlayerState ozzie × PlayerState brigyeetz
--     new-states with p
mapPlayer ozzie s f = record s { ozzieState = f (GameState.ozzieState s) }
mapPlayer brigyeetz s f = record s { brigyeetzState = f (GameState.brigyeetzState s) }
-- TODO: Figure out some abstraction to avoid having all these cases

-- mb-more-health-is-good-b : ∀ (s : GameState) → winningGame brigyeetz s → winningGame brigyeetz (mapPlayer brigyeetz s λ sp → record sp { healthTotal = suc (healthTotal sp)})
∸-suc : ∀ n m → (suc n ∸ m ≡ n ∸ m) ⊎ (suc n ∸ m ≡ suc (n ∸ m))
∸-suc n zero = inj₂ refl
∸-suc zero (suc m) = inj₁ (0∸n≡0 m)
∸-suc (suc n) (suc m) = ∸-suc n m

mapHealth : ∀ (p : Player) (s : GameState) (f : ℕ → ℕ) → GameState
mapHealth p s f = mapPlayer p s λ sp → record sp { healthTotal = f (healthTotal sp)}

subst-health : ∀ (P : GameState → Set) p (s : GameState) {m} → (GameState.stateOfPlayer s p .healthTotal ≡ m) → P s → P (mapHealth p s λ h → m)
subst-health P ozzie s eq Ps = subst (λ a → P (mapHealth ozzie s (λ hlth → a))) eq Ps
subst-health P brigyeetz s eq Ps = subst (λ a → P (mapHealth brigyeetz s (λ hlth → a))) eq Ps

health-map-action : ∀ (p1 p2 : Player) (s : GameState) (n : ℕ) (act : Action s p2) → Action (mapHealth p1 s (n +_)) p2
health-map-action p1 p2         s n (aCastWalker1 isActive@refl inMain hasMana isInHand     ) = {! (aCastWalker1 refl inMain hasMana isInHand     )  !}
health-map-action p1 .brigyeetz s n (aCastWalker2 isActive inMain hasMana isInHand     ) = {! (aCastWalker2 isActive inMain hasMana isInHand     )  !}
health-map-action p1 .ozzie     s n (aCastElixir isActive inMain hasMana isInHand      ) = {! (aCastElixir isActive inMain hasMana isInHand      )  !}
health-map-action p1 p2         s n (aActivateWalker1 hasMana canActivate              ) = {! (aActivateWalker1 hasMana canActivate              )  !}
health-map-action p1 .brigyeetz s n (aActivateWalker2 hasMana canActivate              ) = {! (aActivateWalker2 hasMana canActivate              )  !}
health-map-action p1 .ozzie     s n (aActivateElixir hasMana canActivate               ) = {! (aActivateElixir hasMana canActivate               )  !}
health-map-action p1 p2         s n (aDeclareAttackers inCombat isActive atcks         ) = {! (aDeclareAttackers inCombat isActive atcks         )  !}
health-map-action p1 p2         s n (aDeclareBlockers atcks inCombat2 isOpponent blcks ) = {! (aDeclareBlockers atcks inCombat2 isOpponent blcks )  !}
health-map-action p1 p2         s n (aDoNothing                                        ) = {! (aDoNothing                                        )  !}

health-ineq-preserved : ∀ (p1 p2 : Player) (s : GameState) (n : ℕ) (act : Action s p2)
    → Σ[ m ∈ ℕ ] performAction (mapHealth p1 s (n +_)) p2 (health-map-action p1 p2 s n act) ≡ mapHealth p1 (performAction s p2 act) (m +_)
health-ineq-preserved p1 p2 s n act = {!   !}

mb-more-health-is-good-b : ∀ (s : GameState) n → winningGame brigyeetz (mapHealth brigyeetz s (_∸ n)) → winningGame brigyeetz (mapHealth brigyeetz s λ hlth → suc hlth ∸ n)
more-health-is-good-b : ∀ (s : GameState) → winningGame brigyeetz s → winningGame brigyeetz (mapHealth brigyeetz s suc)
more-opponent-health-is-bad-o : ∀ (s : GameState) → losingGame ozzie s → losingGame ozzie (mapHealth brigyeetz s suc)
mb-more-health-is-good-b = {!   !}

more-opponent-health-is-bad-o s lg (aCastWalker1 isActive inMain hasMana isInHand)     = more-health-is-good-b _ (lg (aCastWalker1 isActive inMain hasMana isInHand)     )
more-opponent-health-is-bad-o s lg (aCastElixir isActive inMain hasMana isInHand)      = more-health-is-good-b _ (lg (aCastElixir isActive inMain hasMana isInHand)      )
more-opponent-health-is-bad-o s lg (aActivateWalker1 hasMana canActivate)              = more-health-is-good-b _ (lg (aActivateWalker1 hasMana canActivate)              )
more-opponent-health-is-bad-o s lg (aActivateElixir hasMana canActivate)               = more-health-is-good-b _ (lg (aActivateElixir hasMana canActivate)               )
more-opponent-health-is-bad-o s lg (aDeclareAttackers inCombat isActive@refl atcks)    = more-health-is-good-b _ (lg (aDeclareAttackers inCombat isActive atcks)         )
more-opponent-health-is-bad-o s@record{activePlayer = brigyeetz} lg (aDeclareBlockers atcks inCombat2 isOpponent blcks) = more-health-is-good-b _ (lg (aDeclareBlockers atcks inCombat2 isOpponent blcks) )
more-opponent-health-is-bad-o s@record{lastPlayerPassed = false} lg aDoNothing         = more-health-is-good-b _ (lg aDoNothing                                          )
more-opponent-health-is-bad-o s@record{phase = preCombatMain ; lastPlayerPassed = true} lg aDoNothing = more-health-is-good-b _ (lg aDoNothing                           )
more-opponent-health-is-bad-o s@record{phase = combat CombatStart ; lastPlayerPassed = true} lg aDoNothing = more-health-is-good-b _ (lg aDoNothing                            )
more-opponent-health-is-bad-o s@record{activePlayer = ozzie ; phase = combat (DeclaredAttackers _ _) ; lastPlayerPassed = true} lg aDoNothing = more-health-is-good-b _ (lg aDoNothing)
more-opponent-health-is-bad-o s@record{activePlayer = brigyeetz ; phase = combat (DeclaredAttackers _ _) ; lastPlayerPassed = true} lg aDoNothing = more-health-is-good-b _ (lg aDoNothing)
more-opponent-health-is-bad-o s@record{activePlayer = ozzie ; phase = combat (DeclaredBlockers _ a b) ; lastPlayerPassed = true} lg aDoNothing =
    case ∸-suc (s .GameState.brigyeetzState .healthTotal) (calculateDamage a b (s .GameState.ozzieState) (s .GameState.brigyeetzState)) of λ where
        (inj₁ x) → subst-health (winningGame brigyeetz) brigyeetz _ (sym x) (lg aDoNothing)
        (inj₂ y) → subst-health (winningGame brigyeetz) brigyeetz _ (sym y) (more-health-is-good-b _ (lg aDoNothing))
-- more-opponent-health-is-bad-o s@record{activePlayer = ozzie ; phase = combat (DeclaredBlockers _ a b) ; lastPlayerPassed = true} lg aDoNothing = {! s .GameState.brigyeetzState .healthTotal ∸ (calculateDamage a b ? ?)  !}
-- more-opponent-health-is-bad-o s@record{activePlayer = ozzie ; phase = combat (DeclaredBlockers _ _ _) ; lastPlayerPassed = true} lg aDoNothing = {!more-health-is-good-b _ (lg aDoNothing)!}
more-opponent-health-is-bad-o s@record{activePlayer = brigyeetz ; phase = combat (DeclaredBlockers _ _ _) ; lastPlayerPassed = true} lg aDoNothing = more-health-is-good-b _ (lg aDoNothing                            )
more-opponent-health-is-bad-o s@record{activePlayer = ozzie ; phase = postCombatMain ; lastPlayerPassed = true} lg aDoNothing = more-health-is-good-b _ (lg aDoNothing   )
more-opponent-health-is-bad-o s@record{activePlayer = brigyeetz ; phase = postCombatMain ; lastPlayerPassed = true} lg aDoNothing = more-health-is-good-b _ (lg aDoNothing)

more-health-is-good-b s (hasWon x) = hasWon x
more-health-is-good-b s (willWin isAliv (aCastWalker1 isActive inMain hasMana isInHand                , snd)) = willWin tt (aCastWalker1 isActive inMain hasMana isInHand                   , more-opponent-health-is-bad-o _ snd)
more-health-is-good-b s (willWin isAliv (aCastWalker2 isActive inMain hasMana isInHand                , snd)) = willWin tt (aCastWalker2 isActive inMain hasMana isInHand                   , more-opponent-health-is-bad-o _ snd)
more-health-is-good-b s (willWin isAliv (aActivateWalker1 hasMana canActivate                         , snd)) = willWin tt (aActivateWalker1 hasMana canActivate                            , more-opponent-health-is-bad-o _ snd)
more-health-is-good-b s (willWin isAliv (aActivateWalker2 hasMana canActivate                         , snd)) = willWin tt (aActivateWalker2 hasMana canActivate                            , more-opponent-health-is-bad-o _ snd)
more-health-is-good-b s (willWin isAliv (aDeclareAttackers inCombat isActive@refl atcks               , snd)) = willWin tt (aDeclareAttackers inCombat isActive atcks                       , more-opponent-health-is-bad-o _ snd)
more-health-is-good-b s@record{activePlayer = ozzie} (willWin isAliv (aDeclareBlockers atcks inCombat2 isOpponent@refl blcks , snd)) = willWin tt (aDeclareBlockers atcks inCombat2 isOpponent blcks    , more-opponent-health-is-bad-o _ snd)
more-health-is-good-b s@record{lastPlayerPassed = false} (willWin isAliv (aDoNothing , snd)) =
    willWin tt (aDoNothing , more-opponent-health-is-bad-o _ snd                                          )
more-health-is-good-b s@record{phase = preCombatMain ; lastPlayerPassed = true} (willWin isAliv (aDoNothing , snd)) =
    willWin tt (aDoNothing , more-opponent-health-is-bad-o _ snd                           )
more-health-is-good-b s@record{phase = combat CombatStart ; lastPlayerPassed = true} (willWin isAliv (aDoNothing , snd)) =
    willWin tt (aDoNothing , more-opponent-health-is-bad-o _ snd                            )
more-health-is-good-b s@record{activePlayer = ozzie ; phase = combat (DeclaredAttackers _ _) ; lastPlayerPassed = true} (willWin isAliv (aDoNothing , snd)) =
    willWin tt (aDoNothing , more-opponent-health-is-bad-o _ snd)
more-health-is-good-b s@record{activePlayer = brigyeetz ; phase = combat (DeclaredAttackers _ _) ; lastPlayerPassed = true} (willWin isAliv (aDoNothing , snd)) =
    willWin tt (aDoNothing , more-opponent-health-is-bad-o _ snd)
more-health-is-good-b s@record{activePlayer = brigyeetz ; phase = combat (DeclaredBlockers _ _ _) ; lastPlayerPassed = true} (willWin isAliv (aDoNothing , snd)) =
    willWin tt (aDoNothing , more-opponent-health-is-bad-o _ snd                            )
more-health-is-good-b s@record{activePlayer = ozzie ; phase = postCombatMain ; lastPlayerPassed = true} (willWin isAliv (aDoNothing , snd)) =
    willWin tt (aDoNothing , more-opponent-health-is-bad-o _ snd   )
more-health-is-good-b s@record{activePlayer = brigyeetz ; phase = postCombatMain ; lastPlayerPassed = true} (willWin isAliv (aDoNothing , snd)) =
    willWin tt (aDoNothing , more-opponent-health-is-bad-o _ snd)
more-health-is-good-b s@record{activePlayer = ozzie ; phase = combat (DeclaredBlockers _ a b) ; lastPlayerPassed = true} (willWin isAliv (aDoNothing , snd)) =
    willWin tt (aDoNothing , (
        case ∸-suc (s .GameState.brigyeetzState .healthTotal) (calculateDamage a b (s .GameState.ozzieState) (s .GameState.brigyeetzState)) of λ where
            (inj₁ x) → subst-health (losingGame ozzie) brigyeetz _ (sym x) snd
            (inj₂ y) → subst-health (losingGame ozzie) brigyeetz _ (sym y) (more-opponent-health-is-bad-o _ snd)
                ))

more-health-is-good-o : ∀ (s : GameState) → winningGame ozzie s → winningGame ozzie (mapPlayer ozzie s λ sp → record sp { healthTotal = suc (healthTotal sp)})
more-opponent-health-is-bad-b : ∀ (s : GameState) → losingGame brigyeetz s → losingGame brigyeetz (mapPlayer ozzie s λ sp → record sp { healthTotal = suc (healthTotal sp)})
more-opponent-health-is-bad-b = {!   !}
more-health-is-good-o s (hasWon x) = hasWon x
more-health-is-good-o s (willWin isAliv (aCastWalker1 isActive inMain hasMana isInHand                , snd)) = willWin tt (aCastWalker1 isActive inMain hasMana isInHand                   , {! more-opponent-health-is-bad-b _ snd  !})
more-health-is-good-o s (willWin isAliv (aCastElixir isActive inMain hasMana isInHand                 , snd)) = willWin tt (aCastElixir isActive inMain hasMana isInHand                    , {! more-opponent-health-is-bad-b _ snd  !})
more-health-is-good-o s (willWin isAliv (aActivateWalker1 hasMana canActivate                         , snd)) = willWin tt (aActivateWalker1 hasMana canActivate                            , {! more-opponent-health-is-bad-b _ snd  !})
more-health-is-good-o s (willWin isAliv (aActivateElixir hasMana canActivate                          , snd)) = willWin tt (aActivateElixir hasMana canActivate                             , {! more-opponent-health-is-bad-b _ snd  !})
more-health-is-good-o s (willWin isAliv (aDeclareAttackers inCombat isActive@refl atcks               , snd)) = willWin tt (aDeclareAttackers inCombat isActive atcks                       , {! more-opponent-health-is-bad-b _ snd  !})
more-health-is-good-o s@record{activePlayer = brigyeetz} (willWin isAliv (aDeclareBlockers atcks inCombat2 isOpponent@refl blcks , snd)) = willWin tt (aDeclareBlockers atcks inCombat2 isOpponent blcks    , {! more-opponent-health-is-bad-b _ snd  !})
more-health-is-good-o s (willWin isAliv (aDoNothing                                                   , snd)) = willWin tt ({! aDoNothing!}                                               , {! more-opponent-health-is-bad-b _ snd  !})

more-health-is-good : ∀ p (s : GameState) → winningGame p s → winningGame p (mapPlayer p s λ sp → record sp { healthTotal = suc (healthTotal sp)})
more-health-is-good = {!   !}

-- more-health-is-good ozzie      s (willWin isAliv (aCastWalker1 x x₁ hasMana isInHand , snd)) = willWin tt {!   !}
-- more-health-is-good brigyeetz  s (willWin isAliv (aCastWalker1 x x₁ hasMana isInHand , snd)) = willWin tt {!   !}
-- more-health-is-good .brigyeetz s (willWin isAliv (aCastWalker2 x x₁ hasMana isInHand , snd)) = {!   !}
-- more-health-is-good .ozzie     s (willWin isAliv (aCastElixir x x₁ hasMana isInHand , snd)) = {!   !}
-- more-health-is-good p          s (willWin isAliv (aActivateWalker1 hasMana canActivate , snd)) = {!   !}
-- more-health-is-good .brigyeetz s (willWin isAliv (aActivateWalker2 hasMana canActivate , snd)) = {!   !}
-- more-health-is-good .ozzie     s (willWin isAliv (aActivateElixir hasMana canActivate , snd)) = {!   !}
-- more-health-is-good p          s (willWin isAliv (aDeclareAttackers x x₁ atcks x₂ , snd)) = {!   !}
-- more-health-is-good p          s (willWin isAliv (aDeclareBlockers atcks x x₁ blcks , snd)) = {!   !}
-- more-health-is-good p          s (willWin isAliv (aDoNothing , snd)) = {!   !}

-- -}

-- -}

-- TODO: Prove that actions commute over health
-- TODO: Complete the implementation of blocking
-- TODO: Some kind of progress on the actual proof
-- TODO: Dynamic programming to enumerate possibilities
-- TODO: Enumerate possibilities and convert with agda2hs
-- TODO: Prove that an abstraction over an entire turn is equivalent
