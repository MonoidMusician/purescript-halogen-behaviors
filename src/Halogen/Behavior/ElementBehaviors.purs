module Halogen.Behavior.ElementBehaviors where

import Prelude

import Control.Monad.Eff (Eff)
import Control.Monad.Eff.Unsafe (unsafeCoerceEff)
import DOM.Event.Types (FocusEvent, MouseEvent)
import Data.Either (Either(..))
import Data.Maybe (Maybe)
import Data.Record (get)
import Data.Record.Builder as B
import Data.Symbol (class IsSymbol, SProxy(..))
import Data.Tuple (Tuple(..))
import Data.Variant (class VariantMatchCases, Variant, case_, expand, inj, on)
import FRP (FRP)
import FRP.Behavior (ABehavior, Behavior, step, unfold)
import FRP.Event (Event, create)
import Halogen.Behavior.Internal (expandAttrs, mapIProp)
import Halogen.HTML.Events as HE
import Halogen.HTML.Properties (IProp)
import Type.Row (class ListToRow, class RowLacks, class RowToList, Cons, Nil, RLProxy(..), RProxy, kind RowList)
import Unsafe.Coerce (unsafeCoerce)

class ElementBehaviors
  (attrs :: # Type)
  (behaviors :: # Type) -- Behavior t
  (callbacks :: # Type) -- t -> Eff ( frp :: FRP )
  (internals :: # Type) -- t
  | behaviors -> callbacks internals
  where
    mkBehaviors :: forall e. RProxy attrs -> Eff ( frp :: FRP | e )
      (Tuple (Record behaviors) (Record callbacks))
    update :: forall e.
      RProxy behaviors ->
      RProxy attrs ->
      Record callbacks ->
      Variant internals ->
      Eff ( frp :: FRP | e ) Unit
    allAttrs :: RProxy behaviors -> Array (IProp attrs (Variant internals))

instance elementBehaviors ::
  ( RowToList behaviors rl
  , ElementBehaviorsRL attrs rl behaviors callbacks internals
  ) => ElementBehaviors attrs   behaviors callbacks internals
  where
    mkBehaviors r = initializeRL (RLProxy :: RLProxy rl) r <#>
      \(Tuple b cb) -> Tuple (B.build b {}) (B.build cb {})
    update _ r cbs = updateRL (RLProxy :: RLProxy rl) r (mkDeletor cbs)
    allAttrs _ = attrsRL (RLProxy :: RLProxy rl)

newtype Deletor r = Deletor (Record r)
mkDeletor :: forall r. Record r -> Deletor r
mkDeletor = Deletor

split :: forall s t r' r. IsSymbol s => RowCons s t r' r => RowLacks s r' =>
  SProxy s -> Deletor r -> Tuple t (Deletor r')
split k d@(Deletor r) = Tuple (get k r) (unsafeCoerce d)

class ElementBehaviorsRL
  (attrs :: # Type)
  (rl :: RowList)
  (behaviors :: # Type) -- Behavior t
  (callbacks :: # Type) -- t -> Eff ( frp :: FRP )
  (internals :: # Type) -- t
  | rl -> behaviors callbacks internals
  where
    initializeRL :: forall e.
      RLProxy rl ->
      RProxy attrs ->
      Eff ( frp :: FRP | e )
        (Tuple
          (B.Builder {} { | behaviors })
          (B.Builder {} { | callbacks })
        )
    updateRL :: forall e.
      RLProxy rl ->
      RProxy attrs ->
      Deletor callbacks ->
      Variant internals ->
      Eff ( frp :: FRP | e ) Unit
    attrsRL ::
      RLProxy rl ->
      Array (IProp attrs (Variant internals))

instance elementBehaviorsNil ::
  ElementBehaviorsRL attrs Nil () () ()
  where
    initializeRL _ _ = pure (Tuple id id)
    updateRL _ _ _ v = case_ v
    attrsRL _ = []

instance elementBehaviorsCons ::
  ( ElementBehavior attrs' s t i
  , Union attrs' unused attrs
  , RowCons s (Behavior t) behaviors' behaviors
  , RowCons s (i -> Eff ( frp :: FRP ) Unit) callbacks' callbacks
  , RowCons s i internals' internals
  , RowLacks s behaviors'
  , RowLacks s callbacks'
  , RowLacks s internals'
  , RowToList behaviors (Cons s (ABehavior Event t) rl)
  , ListToRow (Cons s (ABehavior Event t) rl) behaviors
  , Union internals' whymustwehavethis internals
  , RowToList callbacks crl
  , VariantMatchCases crl internals (Eff ( frp :: FRP ) Unit)
  , ElementBehaviorsRL attrs rl behaviors' callbacks' internals'
  ) => ElementBehaviorsRL attrs
    (Cons s (ABehavior Event t) rl)
    behaviors callbacks internals
  where
    initializeRL _ r = do
      Tuple b' cb' <- initializeRL (RLProxy :: RLProxy rl) r
      { event, push: cb } <- create
      let b = process s event
      pure $ Tuple
        (b' >>> B.insert s b)
        (cb' >>> B.insert s (unsafeCoerceEff <<< cb))
      where s = SProxy :: SProxy s
    updateRL _ r cbs =
      on s (unsafeCoerceEff <<< cb) $
        updateRL (RLProxy :: RLProxy rl) r cbs'
      where
        s = SProxy :: SProxy s
        Tuple cb cbs' = split s cbs
    attrsRL _ = (mapIProp expand <$> attrsRL (RLProxy :: RLProxy rl)) <> expandAttrs (attrs s q)
      where
        s = SProxy :: SProxy s
        q :: i -> (forall e. e -> Maybe (Variant internals))
        q v = \_ -> pure (inj s v)

class IsSymbol name <= ElementBehavior
  (attrs :: # Type)
  (name :: Symbol)
  (value :: Type)
  (internal :: Type)
  | name -> attrs value internal
  where
    process :: SProxy name -> Event internal -> Behavior value
    attrs :: forall q.
      SProxy name ->
      (internal -> (forall e. e -> Maybe q)) ->
      Array (IProp attrs q)

instance focusElementBehavior ::
  ElementBehavior
    ( onFocus :: FocusEvent, onBlur :: FocusEvent )
    "focus"
    Boolean
    Boolean
  where
    process _ = step false
    attrs _ q =
      [ HE.onFocus (q true)
      , HE.onBlur (q false)
      ]

instance hoverElementBehavior ::
  ElementBehavior
    ( onMouseOver :: MouseEvent, onMouseOut :: MouseEvent )
    "hover"
    Boolean
    Boolean
  where
    process _ = step false
    attrs _ q =
      [ HE.onMouseOver (q true)
      , HE.onMouseOut (q false)
      ]

data PreciseFocus
  = HereFocused
  | ChildFocused
  | Unfocused

instance preciseFocusElementBehavior ::
  ElementBehavior
    ( onFocus :: FocusEvent, onBlur :: FocusEvent
    , onFocusIn :: FocusEvent, onFocusOut :: FocusEvent
    )
    "preciseFocus"
    PreciseFocus
    (Either Boolean Boolean)
  where
    process _ e = unfold next e (Tuple false false) <#> case _ of
      Tuple true _ -> HereFocused
      Tuple _ true -> ChildFocused
      Tuple false false -> Unfocused
      where
        next (Left h)  (Tuple _ c) = Tuple h c
        next (Right c) (Tuple h _) = Tuple h c
    attrs _ q =
      [ HE.onFocus $ q $ Left true
      , HE.onBlur $ q $ Left false
      , HE.onFocusIn $ q $ Right true
      , HE.onFocusOut $ q $ Right false
      ]

data Precise
  = Here
  | Child
  | None

instance preciseHoverElementBehavior ::
  ElementBehavior
    ( onMouseOver :: MouseEvent, onMouseOut :: MouseEvent
    , onMouseEnter :: MouseEvent, onMouseLeave :: MouseEvent
    )
    "preciseHover"
    Precise
    (Either Boolean Boolean)
  where
    process _ e = unfold next e (Tuple false false) <#> case _ of
      Tuple _ true -> Child
      Tuple true _ -> Here
      Tuple false false -> None
      where
        next (Left h)  (Tuple _ c) = Tuple h c
        next (Right c) (Tuple h _) = Tuple h c
    attrs _ q =
      [ HE.onMouseOver $ q $ Left true
      , HE.onMouseOut $ q $ Left false
      , HE.onMouseEnter $ q $ Right true
      , HE.onMouseLeave $ q $ Right false
      ]
