module Facet.Context
( -- * Contexts
  Context(..)
, Entry(..)
, entryDef
, entryType
, empty
, (|>)
, level
, (!)
, lookupIndex
, toEnv
, Suffix
, (<><)
, restore
, replace
) where

import           Data.Foldable (foldl')
import qualified Data.IntMap as IntMap
import           Data.Maybe (fromMaybe)
import           Facet.Core
import           Facet.Name
import qualified Facet.Stack as S
import           Facet.Syntax
import           GHC.Stack
import           Prelude hiding (lookup)

newtype Context = Context { elems :: S.Stack Entry }

data Entry
  -- FIXME: constructor names are unclear; Tm is typing, Ty is meta.
  -- FIXME: record implicitness in the context.
  -- FIXME: record sort in the context.
  = Tm Name Type
  | Ty Meta (Maybe Type) Type

entryDef :: Entry -> Maybe Type
entryDef = \case
  Tm _   _ -> Nothing
  Ty _ v _ -> v

entryType :: Entry -> Type
entryType = \case
  Tm _   t -> t
  Ty _ _ t -> t


empty :: Context
empty = Context S.Nil

(|>) :: Context -> Entry -> Context
Context as |> a = Context (as S.:> a)

infixl 5 |>

level :: Context -> Level
level (Context es) = go 0 es
  where
  go n S.Nil          = n
  go n (es S.:> Tm{}) = go (n + 1) es
  go n (es S.:> Ty{}) = go  n      es

(!) :: HasCallStack => Context -> Index -> Entry
Context es' ! Index i' = withFrozenCallStack $ go es' i'
  where
  go (es S.:> e@Tm{}) i
    | i == 0            = e
    | otherwise         = go es (i - 1)
  go (es S.:> _)      i = go es i
  go _                _ = error $ "Facet.Context.!: index (" <> show i' <> ") out of bounds (" <> show (length es') <> ")"

lookupIndex :: Name -> Context -> Maybe (Index, Type)
lookupIndex n = go (Index 0) . elems
  where
  go _ S.Nil          = Nothing
  go i (cs S.:> Tm n' t)
    | n == n'         = Just (i, t)
    | otherwise       = go (succ i) cs
  go i (cs S.:> Ty{}) = go i cs


-- | Construct an environment suitable for evaluation from a 'Context'.
toEnv :: Context -> (S.Stack Value, IntMap.IntMap Value)
toEnv c = (locals 0 (elems c), metas (elems c))
  where
  d = level c
  locals i = \case
    S.Nil            -> S.Nil
    bs S.:> Tm _   _ -> locals (succ i) bs S.:> free (indexToLevel d i)
    bs S.:> Ty _ _ _ -> locals i bs
  metas = \case
    S.Nil            -> mempty
    bs S.:> Tm _   _ -> metas bs
    bs S.:> Ty m v _ -> IntMap.insert (getMeta m) (fromMaybe (metavar m) v) (metas bs)


type Suffix = [Meta :=: Maybe Type ::: Type]

(<><) :: Context -> Suffix -> Context
(<><) = foldl' (\ gamma (n :=: v ::: _T) -> gamma |> Ty n v _T)

infixl 5 <><

restore :: Applicative m => m (Maybe Suffix)
restore = pure Nothing

replace :: Applicative m => Suffix -> m (Maybe Suffix)
replace a = pure (Just a)
