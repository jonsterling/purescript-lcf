module LCF
( Validation()
, ProofState()
, Tactic(..)
, runTactic

, lazyThenLT
, lazyThenT
, thenLT
, thenT
) where

import Control.Monad.Eff
import Control.Monad.Eff.Exception
import Data.List
import Data.Monoid
import Data.Tuple
import Data.Lazy

type Validation d e = List d -> Eff (err :: Exception | e) d
type ProofState j d e = { subgoals :: List j, validation :: Validation d e }
newtype Tactic j d e = Tactic (j -> ProofState j d e)

runTactic :: forall j d e. Tactic j d e -> j -> ProofState j d e
runTactic (Tactic t) = t

splitAt :: forall a e. Number -> List a -> Eff (err :: Exception | e) (Tuple (List a) (List a))
splitAt n ls =
  if n < 0
    then throwException $ error "splitAt: negative index"
    else if n == 0
      then return $ Tuple Nil ls
      else return $ go n ls
  where
    go _ Nil = Tuple Nil Nil
    go 1 (Cons x xs) = Tuple (Cons x Nil) xs
    go m (Cons x xs) =
      case go (m - 1) xs of
        Tuple xs' xs'' -> Tuple (Cons x xs') xs''

mapShape :: forall a b e. List Number -> List (List a -> Eff (err :: Exception | e) b) -> List a -> Eff (err :: Exception | e) (List b)
mapShape Nil _ _ = return Nil
mapShape (Cons n ns) (Cons f fs) xs = do
  Tuple ys zs <- splitAt n xs
  Cons <$> f ys <*> mapShape ns fs zs

refine :: forall j d e. Validation d e -> List (List j) -> List (Validation d e) -> ProofState j d e
refine v subgoals vs =
  { subgoals : subgoals >>= id
  , validation : \ds -> mapShape (length <$> subgoals) vs ds >>= v
  }

idT :: forall j d e. Tactic j d e
idT = Tactic \j ->
  { subgoals: Nil
  , validation: \ds ->
      case ds of
        Cons d Nil -> return d
        _ -> throwException $ error "idTac: Wrong number of subderivations"
  }

unzipProofStates :: forall j d e. List (ProofState j d e) -> Tuple (List (List j)) (List (Validation  d e))
unzipProofStates = go $ Tuple Nil Nil
  where
    go r Nil = r
    go (Tuple jss vs) (Cons s ss) = go (Tuple (Cons s.subgoals jss) (Cons s.validation vs)) ss

lazyThenLT :: forall j d e. Tactic j d e -> Lazy (List (Tactic j d e)) -> Tactic j d e
lazyThenLT t1 tsl = Tactic \j ->
  let
    state1 = t1 `runTactic` j
  in
    if null state1.subgoals then state1 else
      case unzipProofStates $ (runTactic <$> force tsl) <*> state1.subgoals of
        Tuple subgoals validations ->
          refine state1.validation subgoals validations

lazyThenT :: forall j d e. Tactic j d e -> Lazy (Tactic j d e) -> Tactic j d e
lazyThenT t1 t2l = Tactic \j ->
  let
    state1 = t1 `runTactic` j
  in
    if null state1.subgoals then state1 else
      case unzipProofStates $ runTactic (force t2l) <$> state1.subgoals of
        Tuple subgoals validations ->
          refine state1.validation subgoals validations

thenLT :: forall j d e. Tactic j d e -> List (Tactic j d e) -> Tactic j d e
thenLT t1 ts = lazyThenLT t1 $ pure ts

thenT :: forall j d e. Tactic j d e -> Tactic j d e -> Tactic j d e
thenT t1 t2 = lazyThenT t1 $ pure t2

instance semigroupTactic :: Semigroup (Tactic j d e) where
  (<>) = thenT

instance monoidTactic :: Monoid (Tactic j d e) where
  mempty = idT

