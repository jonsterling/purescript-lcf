module Test.Main where

import qualified LCF as LC
import LCF.Notation

import Control.Monad.Eff
import Control.Monad.Eff.Exception
import Data.List
import Debug.Trace

data Prop = True | False | Conj Prop Prop

instance showProp :: Show Prop where
  show True = "True"
  show False = "False"
  show (Conj p q) = "(" <> show p <> " & " <> show q <> ")"

data Proof = Ax | Abort Proof | Pair Proof Proof

instance showProof :: Show Proof where
  show Ax = "<>"
  show (Abort r) = "abort(" <> show r <> ")"
  show (Pair m n) = "<" <> show m <> ", " <> show n <> ">"

data Judgement = IsTrue Prop

instance showJudgement :: Show Judgement where
  show (IsTrue p) = show p <> " true"

type Tactic e = LCF.Tactic Judgement Proof e

unitIntroT :: forall e. Tactic e
unitIntroT = LCF.Tactic \j ->
  case j of
    IsTrue True -> pure { subgoals : Nil, validation : \_ -> pure Ax }
    _ -> throwException $ error "unitIntroT"

conjIntroT :: forall e. Tactic e
conjIntroT = LCF.Tactic \j ->
  case j of
    IsTrue (Conj p q) -> pure
      { subgoals : fromArray [IsTrue p, IsTrue q]
      , validation : \ds ->
          case ds of
            Cons m (Cons n Nil) -> pure $ Pair m n
            _ -> throwException $ error "Malformed derivation (conjIntroT)"
      }
    _ -> throwException $ error "conjIntroT"

assert :: forall e. Judgement -> Tactic e -> Eff (err :: Exception | e) Proof
assert j t = do
  state <- t `LCF.runTactic` j
  if null state.subgoals
    then state.validation Nil
    else throwException $ error $ "subgoals remaining: " <> show state.subgoals

main = do
  let goal = IsTrue $ Conj True True
  proof <- assert goal $ conjIntroT <> unitIntroT
  print proof
