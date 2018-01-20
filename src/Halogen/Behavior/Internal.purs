module Halogen.Behavior.Internal where

import Prelude

import CSS (CSS, render, renderedInline)
import Control.Monad.Eff (Eff)
import Control.Monad.Eff.Ref (REF, Ref, newRef, readRef)
import DOM (DOM)
import DOM.Node.Types (Element)
import Data.Foreign (typeOf)
import Data.Function.Uncurried as Fn
import Data.Maybe (Maybe(..))
import Data.Record (insert)
import Data.Symbol (class IsSymbol, SProxy(..))
import Halogen.HTML.Core (class IsProp, PropValue, toPropValue)
import Halogen.HTML.Properties (IProp(..))
import Halogen.VDom.Util as Util
import Type.Row (class ListToRow, class RowLacks, class RowToList, Cons, Nil, RLProxy(..), kind RowList)
import Unsafe.Coerce (unsafeCoerce)
import Unsafe.Reference (unsafeRefEq)

renderCSS :: CSS -> Maybe String
renderCSS = renderedInline <<< render

mapIProp :: forall attrs a b. (a -> b) -> IProp attrs a -> IProp attrs b
mapIProp f (IProp p) = IProp (map f <$> p)

expandAttr ::
  forall attrs attrs' extra.
    Union attrs extra attrs' =>
  IProp attrs ~> IProp attrs'
expandAttr = unsafeCoerce

expandAttrs ::
  forall attrs attrs' extra a.
    Union attrs extra attrs' =>
  Array (IProp attrs a) -> Array (IProp attrs' a)
expandAttrs = unsafeCoerce

eqProp :: forall p. IsProp p => p -> p -> Boolean
eqProp a b = unsafeRefEq (toPropValue a) (toPropValue b)

eqMProp :: forall p. IsProp p => Maybe p -> Maybe p -> Boolean
eqMProp (Just p1) (Just p2) = eqProp p1 p2
eqMProp Nothing Nothing = true
eqMProp _ _ = false

class Nothings (row :: # Type) where
  aWholeLotOfNothing :: Record row
class (RowToList row rl, ListToRow rl row) <= NothingsRL (rl :: RowList) (row :: # Type) | rl -> row where
  aWholeLotOfNothingRL :: RLProxy rl -> Record row
instance nothingsImpl :: (RowToList row rl, ListToRow rl row, NothingsRL rl row) => Nothings row where
  aWholeLotOfNothing = aWholeLotOfNothingRL (RLProxy :: RLProxy rl)
instance nothingsNil :: NothingsRL Nil () where
  aWholeLotOfNothingRL _ = {}
instance nothingsCons ::
  ( IsSymbol label
  , RowCons label (Maybe ty) row' row
  , RowLacks label row'
  , RowToList row (Cons label (Maybe ty) rl)
  , NothingsRL rl row'
  ) => NothingsRL (Cons label (Maybe ty) rl) row where
    aWholeLotOfNothingRL _ = insert (SProxy :: SProxy label) Nothing
      (aWholeLotOfNothingRL (RLProxy :: RLProxy rl) :: Record row')

-- allow mutation in ref?
newtype AroundState partial = AroundState
  { insideState :: Record partial
  , outsideState :: Maybe (Ref (Record partial))
  }

uninitializedAS :: forall partial. Nothings partial => AroundState partial
uninitializedAS = AroundState { insideState: aWholeLotOfNothing, outsideState: Nothing }

initialize :: forall partial eff. AroundState partial -> Eff ( ref :: REF | eff ) (AroundState partial)
initialize (AroundState { insideState }) =
  newRef insideState <#>
    AroundState <<< { insideState, outsideState: _ } <<< Just

snapshot :: forall partial eff. AroundState partial -> Eff ( ref :: REF | eff ) (AroundState partial)
snapshot a@(AroundState { outsideState: Nothing }) = pure a
snapshot (AroundState { outsideState: Just ref }) =
  readRef ref <#> \insideState ->
    AroundState { insideState, outsideState: Just ref }


setProperty ∷ ∀ eff. Fn.Fn3 String PropValue Element (Eff ( dom ∷ DOM | eff) Unit)
setProperty = Util.unsafeSetAny

unsafeGetProperty ∷ Fn.Fn2 String Element PropValue
unsafeGetProperty = Util.unsafeGetAny

removeProperty ∷ ∀ eff. Fn.Fn2 String Element (Eff ( dom ∷ DOM | eff) Unit)
removeProperty = Fn.mkFn2 \key el →
  case typeOf (Fn.runFn2 Util.unsafeGetAny key el) of
    "string" → Fn.runFn3 Util.unsafeSetAny key "" el
    _        → Fn.runFn3 Util.unsafeSetAny key Util.jsUndefined el
