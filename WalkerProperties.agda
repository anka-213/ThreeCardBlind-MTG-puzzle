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
mapPlayer p s f = record s { ozzieState = new-states .proj₁ ; brigyeetzState = new-states .proj₂ }
  where
    open GameState
    new-states-for : ∀ p → PlayerState ozzie → PlayerState brigyeetz → (PlayerState p → PlayerState p) → PlayerState ozzie × PlayerState brigyeetz
    new-states-for ozzie     ozSt brSt f = f ozSt , brSt
    new-states-for brigyeetz ozSt brSt f = ozSt , f brSt
    new-states = new-states-for p (ozzieState s) (brigyeetzState s) f
-- mapPlayer ozzie s f = record s { ozzieState = f (GameState.ozzieState s) }
-- mapPlayer brigyeetz s f = record s { brigyeetzState = f (GameState.brigyeetzState s) }
-- TODO: Figure out some abstraction to avoid having all these cases

-- mb-more-health-is-good-b : ∀ (s : GameState) → winningGame brigyeetz s → winningGame brigyeetz (mapPlayer brigyeetz s λ sp → record sp { healthTotal = suc (healthTotal sp)})
∸-suc : ∀ n m → (suc n ∸ m ≡ n ∸ m) ⊎ (suc n ∸ m ≡ suc (n ∸ m))
∸-suc n zero = inj₂ refl
∸-suc zero (suc m) = inj₁ (0∸n≡0 m)
∸-suc (suc n) (suc m) = ∸-suc n m

mapHealth : ∀ (p : Player) (s : GameState) (f : ℕ → ℕ) → GameState
mapHealth p s f = mapPlayer p s λ sp → record sp { healthTotal = f (healthTotal sp)}

setHealth : ∀ (p : Player) (s : GameState) (n : ℕ) → GameState
setHealth p s n = mapHealth p s (λ _ → n)

-- TODO: Split actions into subcategories so entire categories can be handled at once

subst-health : ∀ (P : GameState → Set) p (s : GameState) {m} → (GameState.stateOfPlayer s p .healthTotal ≡ m) → P s → P (mapHealth p s λ h → m)
subst-health P ozzie s eq Ps = subst (λ a → P (mapHealth ozzie s (λ hlth → a))) eq Ps
subst-health P brigyeetz s eq Ps = subst (λ a → P (mapHealth brigyeetz s (λ hlth → a))) eq Ps

mapMana : ∀ p1 p2 s {n} k (hasMana : HasMana (GameState.stateOfPlayer s p2) k)
                                   → HasMana (GameState.stateOfPlayer (mapHealth p1 s (_+ n)) p2) k
mapMana ozzie     brigyeetz s k hM = hM
mapMana brigyeetz ozzie     s k hM = hM
mapMana ozzie     ozzie     s 1 hM = hM
mapMana ozzie     ozzie     s 2 hM = hM
mapMana brigyeetz brigyeetz s 1 hM = hM
mapMana brigyeetz brigyeetz s 2 hM = hM

health-card1-independent : ∀ p1 p2 s {f} → walker1State (GameState.stateOfPlayer s p2) ≡ walker1State (GameState.stateOfPlayer (mapHealth p1 s f) p2)
health-card1-independent ozzie ozzie s = refl
health-card1-independent ozzie brigyeetz s = refl
health-card1-independent brigyeetz ozzie s = refl
health-card1-independent brigyeetz brigyeetz s = refl

health-card2-independent : ∀ p1 p2 s {f} → card2State (GameState.stateOfPlayer s p2) ≡ card2State (GameState.stateOfPlayer (mapHealth p1 s f) p2)
health-card2-independent ozzie ozzie s = refl
health-card2-independent ozzie brigyeetz s = refl
health-card2-independent brigyeetz ozzie s = refl
health-card2-independent brigyeetz brigyeetz s = refl

mapInHand : ∀ p1 p2 s {n} (isInHand : walker1State (GameState.stateOfPlayer s p2) ≡ inHand)
                                    → walker1State (GameState.stateOfPlayer (mapHealth p1 s (_+ n)) p2) ≡ inHand
mapInHand p1 p2 s isInHand = subst (_≡ inHand) (health-card1-independent p1 p2 s) isInHand

mapInHand2 : ∀ p1 p2 s {n} (isInHand : card2State (GameState.stateOfPlayer s p2) ≡ inHand)
                                     → card2State (GameState.stateOfPlayer (mapHealth p1 s (_+ n)) p2) ≡ inHand
mapInHand2 p1 p2 s isInHand = subst (_≡ inHand) (health-card2-independent p1 p2 s) isInHand

mapAttackers : ∀ p1 s {n}
    (atcks : AttackerInfo (attackContextFor (GameState.activePlayerState s))) →
    AttackerInfo (attackContextFor (GameState.activePlayerState (mapHealth p1 s (_+ n))))
mapAttackers ozzie     s@record{activePlayer = ozzie    } atcks = atcks
mapAttackers ozzie     s@record{activePlayer = brigyeetz} atcks = atcks
mapAttackers brigyeetz s@record{activePlayer = ozzie    } atcks = atcks
mapAttackers brigyeetz s@record{activePlayer = brigyeetz} atcks = atcks

mapBlockers : ∀ p1 s {n} {pps} {atcks : AttackerInfo pps}
    (blcks : BlockerInfo pps atcks (blockerContextFor (GameState.opponentState s)))
           → BlockerInfo pps atcks (blockerContextFor (GameState.opponentState (mapHealth p1 s (_+ n))))
mapBlockers ozzie     s@record{activePlayer = ozzie    } blckrs = blckrs
mapBlockers ozzie     s@record{activePlayer = brigyeetz} blckrs = blckrs
mapBlockers brigyeetz s@record{activePlayer = ozzie    } blckrs = blckrs
mapBlockers brigyeetz s@record{activePlayer = brigyeetz} blckrs = blckrs


-- IDEA: Store player data in activePlayerState and index actions based on if you are active
-- That way we automatically dismiss non-active player actions and can skip that proof
-- Downside: how do we implement taking turns to do things in isWinningGame?

health-map-action : ∀ (p1 p2 : Player) (s : GameState) (n : ℕ) (act : Action s p2) → Action (mapHealth p1 s (_+ n)) p2
health-map-action p1 p2         s n (aCastWalker1 isActive inMain hasMana isInHand    ) = aCastWalker1 isActive inMain (mapMana p1 p2 s 2 hasMana) (mapInHand  p1 p2 s isInHand)
health-map-action p1 p2         s n (aCastWalker2 isActive inMain hasMana isInHand    ) = aCastWalker2 isActive inMain (mapMana p1 p2 s 2 hasMana) (mapInHand2 p1 p2 s isInHand)
health-map-action p1 p2         s n (aCastElixir isActive inMain hasMana isInHand     ) = aCastElixir  isActive inMain (mapMana p1 p2 s 1 hasMana) (mapInHand2 p1 p2 s isInHand)
health-map-action p1 p2         s n (aActivateWalker1 hasMana canActivate             ) = aActivateWalker1 (mapMana p1 p2 s 1 hasMana) (subst canActivateWalker (health-card1-independent p1 p2 s) canActivate)
health-map-action p1 p2         s n (aActivateWalker2 hasMana canActivate             ) = aActivateWalker2 (mapMana p1 p2 s 1 hasMana) (subst canActivateWalker (health-card2-independent p1 p2 s) canActivate)
health-map-action p1 p2         s n (aActivateElixir hasMana canActivate              ) = aActivateElixir (mapMana p1 p2 s 2 hasMana) (subst (_≡ onBattlefield elixirState) (health-card2-independent p1 p2 s) canActivate)
health-map-action p1 p2         s n (aDeclareAttackers inCombat isActive atcks        ) = aDeclareAttackers inCombat isActive (mapAttackers p1 s atcks)
health-map-action p1 p2         s n (aDeclareBlockers atcks inCombat2 isOpponent blcks) = aDeclareBlockers atcks inCombat2 isOpponent (mapBlockers p1 s blcks)
health-map-action p1 p2         s n (aDoNothing                                       ) = aDoNothing
-- health-map-action ozzie ozzie      s n (aCastWalker1 isActive inMain hasMana isInHand         ) = (aCastWalker1 isActive inMain hasMana isInHand     )
-- health-map-action ozzie brigyeetz  s n (aCastWalker1 isActive inMain hasMana isInHand         ) = (aCastWalker1 isActive inMain hasMana isInHand     )
-- health-map-action ozzie .brigyeetz s n (aCastWalker2 isActive inMain hasMana isInHand         ) = (aCastWalker2 isActive inMain hasMana isInHand     )
-- health-map-action ozzie .ozzie     s n (aCastElixir isActive inMain hasMana isInHand          ) = (aCastElixir isActive inMain hasMana isInHand      )
-- health-map-action ozzie ozzie      s n (aActivateWalker1 hasMana canActivate                  ) = (aActivateWalker1 hasMana canActivate              )
-- health-map-action ozzie brigyeetz  s n (aActivateWalker1 hasMana canActivate                  ) = (aActivateWalker1 hasMana canActivate              )
-- health-map-action ozzie .brigyeetz s n (aActivateWalker2 hasMana canActivate                  ) = (aActivateWalker2 hasMana canActivate              )
-- health-map-action ozzie .ozzie     s n (aActivateElixir hasMana canActivate                   ) = (aActivateElixir hasMana canActivate               )
-- health-map-action ozzie ozzie      s n (aDeclareAttackers inCombat isActive@refl atcks        ) = (aDeclareAttackers inCombat isActive atcks         )
-- health-map-action ozzie brigyeetz  s n (aDeclareAttackers inCombat isActive@refl atcks        ) = (aDeclareAttackers inCombat isActive atcks         )
-- health-map-action ozzie ozzie      s n (aDeclareBlockers atcks inCombat2 isOpponent@refl blcks) = (aDeclareBlockers atcks inCombat2 isOpponent blcks )
-- health-map-action ozzie brigyeetz  s n (aDeclareBlockers atcks inCombat2 isOpponent@refl blcks) = (aDeclareBlockers atcks inCombat2 isOpponent blcks )
-- health-map-action ozzie p2         s n (aDoNothing                                            ) = (aDoNothing                                        )
-- health-map-action brigyeetz ozzie      s n (aCastWalker1 isActive inMain hasMana isInHand     ) = (aCastWalker1 isActive inMain hasMana isInHand     )
-- health-map-action brigyeetz brigyeetz  s n (aCastWalker1 isActive inMain hasMana isInHand     ) = (aCastWalker1 isActive inMain hasMana isInHand     )
-- health-map-action brigyeetz .brigyeetz s n (aCastWalker2 isActive inMain hasMana isInHand     ) = (aCastWalker2 isActive inMain hasMana isInHand     )
-- health-map-action brigyeetz .ozzie     s n (aCastElixir isActive inMain hasMana isInHand      ) = (aCastElixir isActive inMain hasMana isInHand      )
-- health-map-action brigyeetz ozzie      s n (aActivateWalker1 hasMana canActivate              ) = (aActivateWalker1 hasMana canActivate              )
-- health-map-action brigyeetz brigyeetz  s n (aActivateWalker1 hasMana canActivate              ) = (aActivateWalker1 hasMana canActivate              )
-- health-map-action brigyeetz .brigyeetz s n (aActivateWalker2 hasMana canActivate              ) = (aActivateWalker2 hasMana canActivate              )
-- health-map-action brigyeetz .ozzie     s n (aActivateElixir hasMana canActivate               ) = (aActivateElixir hasMana canActivate               )
-- health-map-action brigyeetz ozzie      s n (aDeclareAttackers inCombat isActive@refl atcks    ) = (aDeclareAttackers inCombat isActive atcks         )
-- health-map-action brigyeetz brigyeetz  s n (aDeclareAttackers inCombat isActive@refl atcks    ) = (aDeclareAttackers inCombat isActive atcks         )
-- health-map-action brigyeetz ozzie      s n (aDeclareBlockers atcks inCombat2 isOpponent@refl blcks) = (aDeclareBlockers atcks inCombat2 isOpponent blcks )
-- health-map-action brigyeetz brigyeetz  s n (aDeclareBlockers atcks inCombat2 isOpponent@refl blcks) = (aDeclareBlockers atcks inCombat2 isOpponent blcks )
-- health-map-action brigyeetz p2         s n (aDoNothing                                        ) = (aDoNothing                                        )


health-ineq-preserved : ∀ (p1 p2 : Player) (s : GameState) (n : ℕ) (act : Action s p2)
    → Σ[ m ∈ ℕ ] performAction (mapHealth p1 s (_+ n)) p2 (health-map-action p1 p2 s n act) ≡ mapHealth p1 (performAction s p2 act) (_+ m)
health-ineq-preserved ozzie ozzie      s n (aCastWalker1 isActive inMain hasMana isInHand         ) = n , refl
health-ineq-preserved ozzie brigyeetz  s n (aCastWalker1 isActive inMain hasMana isInHand         ) = n , refl
health-ineq-preserved ozzie .brigyeetz s n (aCastWalker2 isActive inMain hasMana isInHand         ) = n , refl
health-ineq-preserved ozzie .ozzie     s n (aCastElixir isActive inMain hasMana isInHand          ) = n , refl
health-ineq-preserved ozzie ozzie      s n (aActivateWalker1 hasMana canActivate                  ) = n , refl
health-ineq-preserved ozzie brigyeetz  s n (aActivateWalker1 hasMana canActivate                  ) = n , refl
health-ineq-preserved ozzie .brigyeetz s n (aActivateWalker2 hasMana canActivate                  ) = n , refl
health-ineq-preserved ozzie .ozzie     s n act@(aActivateElixir hasMana canActivate               ) = n , refl -- cong (setHealth ozzie  (performAction s ozzie act)) {!   !}
health-ineq-preserved ozzie ozzie      s n (aDeclareAttackers inCombat isActive@refl atcks        ) = n , refl
health-ineq-preserved ozzie brigyeetz  s n (aDeclareAttackers inCombat isActive@refl atcks        ) = n , refl
health-ineq-preserved ozzie ozzie      s n (aDeclareBlockers atcks inCombat2 isOpponent@refl blcks) = n , refl
health-ineq-preserved ozzie brigyeetz  s n (aDeclareBlockers atcks inCombat2 isOpponent@refl blcks) = n , refl
health-ineq-preserved ozzie ozzie      s@record{lastPlayerPassed = false} n (aDoNothing           ) = n , refl
health-ineq-preserved ozzie brigyeetz  s@record{lastPlayerPassed = false} n (aDoNothing           ) = n , refl
health-ineq-preserved ozzie p2         s@record{lastPlayerPassed = true ; phase = preCombatMain      } n (aDoNothing) = {! n , refl  !}
health-ineq-preserved ozzie p2         s@record{lastPlayerPassed = true ; phase = combat CombatStart } n (aDoNothing) = {! n , refl  !}
health-ineq-preserved ozzie p2         s@record{lastPlayerPassed = true ; activePlayer = ozzie     ; phase = combat (DeclaredAttackers _ _) } n (aDoNothing) = {! n , refl  !}
health-ineq-preserved ozzie p2         s@record{lastPlayerPassed = true ; activePlayer = brigyeetz ; phase = combat (DeclaredAttackers _ _) } n (aDoNothing) = {! n , refl  !}
health-ineq-preserved ozzie p2         s@record{lastPlayerPassed = true ; activePlayer = ozzie     ; phase = combat (DeclaredBlockers _ a b)} n (aDoNothing) = {! n , refl  !}
health-ineq-preserved ozzie p2         s@record{lastPlayerPassed = true ; activePlayer = brigyeetz ; phase = combat (DeclaredBlockers _ _ _)} n (aDoNothing) = {! n , refl  !}
health-ineq-preserved ozzie p2         s@record{lastPlayerPassed = true ; activePlayer = ozzie     ; phase = postCombatMain      } n (aDoNothing           ) = {! n , refl  !}
health-ineq-preserved ozzie p2         s@record{lastPlayerPassed = true ; activePlayer = brigyeetz ; phase = postCombatMain      } n (aDoNothing           ) = {! n , refl  !}
health-ineq-preserved brigyeetz ozzie      s n (aCastWalker1 isActive inMain hasMana isInHand         ) = n , refl
health-ineq-preserved brigyeetz brigyeetz  s n (aCastWalker1 isActive inMain hasMana isInHand         ) = n , refl
health-ineq-preserved brigyeetz .brigyeetz s n (aCastWalker2 isActive inMain hasMana isInHand         ) = n , refl
health-ineq-preserved brigyeetz .ozzie     s n (aCastElixir isActive inMain hasMana isInHand          ) = n , refl
health-ineq-preserved brigyeetz ozzie      s n (aActivateWalker1 hasMana canActivate                  ) = n , refl
health-ineq-preserved brigyeetz brigyeetz  s n (aActivateWalker1 hasMana canActivate                  ) = n , refl
health-ineq-preserved brigyeetz .brigyeetz s n (aActivateWalker2 hasMana canActivate                  ) = n , refl
health-ineq-preserved brigyeetz .ozzie     s n (aActivateElixir hasMana canActivate                   ) = n , refl
health-ineq-preserved brigyeetz ozzie      s n (aDeclareAttackers inCombat isActive@refl atcks        ) = n , refl
health-ineq-preserved brigyeetz brigyeetz  s n (aDeclareAttackers inCombat isActive@refl atcks        ) = n , refl
health-ineq-preserved brigyeetz ozzie      s n (aDeclareBlockers atcks inCombat2 isOpponent@refl blcks) = n , refl
health-ineq-preserved brigyeetz brigyeetz  s n (aDeclareBlockers atcks inCombat2 isOpponent@refl blcks) = n , refl
health-ineq-preserved brigyeetz p2         s n (aDoNothing                                            ) = {!   !}

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
