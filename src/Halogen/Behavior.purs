module Halogen.Behavior where

import Prelude

import Control.Monad.Aff.Class (class MonadAff)
import Control.Monad.Eff (Eff)
import Control.Monad.Eff.AVar (AVAR)
import Control.Monad.Eff.Ref (REF, Ref, modifyRef, newRef, readRef)
import Control.Monad.Except (runExcept)
import Control.Monad.Maybe.Trans (MaybeT(..), runMaybeT)
import Control.MonadZero (guard)
import DOM (DOM)
import DOM.Event.Event (target)
import DOM.HTML.HTMLInputElement (value)
import DOM.HTML.Types (htmlElementToElement, readHTMLInputElement)
import DOM.Node.Types (Element)
import Data.Const (Const)
import Data.Foldable (for_)
import Data.Foreign (toForeign, typeOf)
import Data.Function.Uncurried as Fn
import Data.Int (even, round)
import Data.Maybe (Maybe(..))
import Data.Record (delete, get, insert, set)
import Data.Set (size)
import Data.String (joinWith)
import Data.Symbol (class IsSymbol, SProxy(..), reflectSymbol)
import Data.Tuple (Tuple(..))
import Data.Variant (Variant, case_, expand, inj, on)
import FRP (FRP)
import FRP.Behavior (ABehavior, Behavior, animate)
import FRP.Behavior.Mouse (buttons)
import FRP.Behavior.Keyboard (key)
import FRP.Behavior.Time (seconds)
import FRP.Event (Event)
import Halogen (RefLabel(..))
import Halogen as H
import Halogen.Aff (awaitBody, runHalogenAff)
import Halogen.HTML (class IsProp)
import Halogen.HTML as HH
import Halogen.HTML.Core (toPropValue)
import Halogen.HTML.Events as HE
import Halogen.HTML.Properties (IProp(..))
import Halogen.HTML.Properties as HP
import Halogen.Query.EventSource (eventSource')
import Halogen.VDom.DOM.Prop (Prop(..), PropValue)
import Halogen.VDom.Driver (runUI)
import Halogen.VDom.Util as Util
import Type.Row (class ListToRow, class RowLacks, class RowToList, Cons, Nil, RLProxy(..), kind RowList)
import Unsafe.Coerce (unsafeCoerce)
import Unsafe.Reference (unsafeRefEq)

type State partial i =
  { value :: i
  , as :: AroundState partial
  }
initialState :: forall partial i. Nothings partial => i -> State partial i
initialState =
  { value: _
  , as: uninitializedAS
  }

data Query partial i o a
  = Initialize a
  | Finalize a
  | Receive i a
  | Lift o a
  | UpdateProp (Variant partial) a

type SubscribeCancel eff v = (v -> Eff eff Unit) -> Eff eff (Eff eff Unit)

class Nothings partial <= MultiAttrBehavior
  (allowed :: # Type) -- IsProp p => p
  (partial :: # Type) -- Maybe p
  (behaviors :: # Type) -- Behavior (Maybe p)
  | allowed -> partial behaviors
  , partial -> allowed behaviors
  where
    subscribe :: forall e. Record behaviors -> SubscribeCancel ( frp :: FRP | e ) (Variant partial)
    handle :: forall e. Element -> Variant partial -> Eff ( dom :: DOM | e ) Unit
    toProps :: forall i. Record partial -> Array (IProp allowed i)
    shouldUpdate :: forall e. Ref (Record partial) -> Variant partial -> Eff ( ref :: REF | e ) Boolean
instance mab ::
  -- Use both RowToList and ListToRow for inference purposes
  ( RowToList allowed arl
  , ListToRow arl allowed
  , RowToList partial prl
  , ListToRow prl partial
  , RowToList behaviors brl
  , ListToRow brl behaviors
  , NothingsRL prl partial
  , MultiAttrBehaviorRL arl prl brl allowed partial behaviors
  ) => MultiAttrBehavior allowed partial behaviors where
    subscribe = subscribeRL (RLProxy :: RLProxy arl)
    handle = handleRL (RLProxy :: RLProxy arl)
    toProps = toPropsRL (RLProxy :: RLProxy arl)
    shouldUpdate = shouldUpdateRL (RLProxy :: RLProxy arl)

class
  ( NothingsRL prl partial
  , RowToList allowed arl, ListToRow arl allowed
  , RowToList behaviors brl -- , ListToRow brl behaviors
  ) <= MultiAttrBehaviorRL
  (arl :: RowList)
  (prl :: RowList)
  (brl :: RowList)
  (allowed :: # Type) -- IsProp p => p
  (partial :: # Type) -- Maybe p
  (behaviors :: # Type) -- Behavior (Maybe p)
  | arl -> allowed
  , prl -> partial
  , brl -> behaviors
  , arl -> prl brl
  , prl -> arl brl
  , brl -> arl prl
  where
    subscribeRL :: forall e. RLProxy arl -> Record behaviors -> SubscribeCancel ( frp :: FRP | e ) (Variant partial)
    handleRL :: forall e. RLProxy arl -> Element -> Variant partial -> Eff ( dom :: DOM | e ) Unit
    toPropsRL :: forall i. RLProxy arl -> Record partial -> Array (IProp allowed i)
    shouldUpdateRL :: forall e. RLProxy arl -> Ref (Record partial) -> Variant partial -> Eff ( ref :: REF | e ) Boolean
instance mabNil :: MultiAttrBehaviorRL Nil Nil Nil () () () where
  subscribeRL _ {} cb = pure (pure unit)
  handleRL _ _ = case_
  toPropsRL _ {} = []
  shouldUpdateRL _ _ = case_
instance mabCons ::
  ( IsSymbol label
  , IsProp p
  , RowLacks label allowed'
  , RowLacks label partial'
  , RowLacks label behaviors'
  , RowCons label p allowed' allowed
  , RowCons label (Maybe p) partial' partial
  , RowCons label (Behavior (Maybe p)) behaviors' behaviors
  , Union partial' one partial
  , RowToList allowed (Cons label p arl)
  -- , ListToRow (Cons label p arl) allowed
  , RowToList partial (Cons label (Maybe p) prl)
  -- , ListToRow (Cons label (Maybe p) prl) partial
  , RowToList behaviors (Cons label (Behavior (Maybe p)) brl)
  -- , ListToRow (Cons label (Behavior (Maybe p)) brl) behaviors
  -- , Nothings partial
  -- , NothingsRL (Cons label (Maybe p) prl) partial
  , MultiAttrBehaviorRL arl prl brl allowed' partial' behaviors'
  ) => MultiAttrBehaviorRL
    (Cons label p arl)
    (Cons label (Maybe p) prl)
    (Cons label (ABehavior Event (Maybe p)) brl)
    allowed partial behaviors where
      subscribeRL _ r cb = do
        c1 <- subscribeRL (RLProxy :: RLProxy arl) (delete k r) (expand >>> cb)
        c2 <- animate (get k r) (inj k >>> cb)
        pure (c1 *> c2)
        where k = SProxy :: SProxy label
      handleRL _ el = handleRL (RLProxy :: RLProxy arl) el
        # on k case _ of
          Just v -> Fn.runFn3 setProperty propName (toPropValue v) el
          Nothing -> Fn.runFn2 removeProperty propName el
        where
          k = (SProxy :: SProxy label)
          propName = reflectSymbol k # case _ of
            "class" -> "className"
            "for" -> "htmlFor"
            n -> n
      toPropsRL _ r = case get k r of
        Nothing -> other
        Just v -> other <> [IProp (Property (reflectSymbol k) (toPropValue v))]
        where
          k = (SProxy :: SProxy label)
          exp = unsafeCoerce :: (forall i. Array (IProp allowed' i) -> Array (IProp allowed i))
          other = exp $ toPropsRL (RLProxy :: RLProxy arl) (delete k r)
      shouldUpdateRL _ ref = handleOther # on k handleThis
        where
          k = (SProxy :: SProxy label)
          handleThis = \v -> do
            rec <- readRef ref
            if get k rec `eqMProp` v
              then pure false
              else do
                modifyRef ref (set k v)
                pure true
          handleOther = unsafeCoerce (shouldUpdateRL (RLProxy :: RLProxy arl)) ref

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

behavioralComponent ::
  forall m allowed i o required partial behaviors eff other.
    MonadAff ( dom :: DOM, frp :: FRP, ref :: REF, avar :: AVAR | eff ) m =>
    MultiAttrBehavior required partial behaviors =>
    Union required other allowed =>
    Nothings partial =>
  HH.Node allowed Void o ->
  (
    (Array (HH.IProp other o) -> Array (HH.HTML Void o) -> HH.HTML Void o) ->
    i ->
    HH.HTML Void o
  ) ->
  Record behaviors ->
  H.Component HH.HTML (Query partial i o) i o m
behavioralComponent node renderWith behavior =
  H.lifecycleComponent
    { initialState
    , receiver: HE.input Receive
    , initializer: HE.input_ Initialize unit
    , finalizer: HE.input_ Finalize unit
    , render
    , eval
    }
  where
    label = RefLabel "behavioral-component"
    addRefProps = ([HP.ref label] <> _)
    expand1 = unsafeCoerce :: (Array (HH.IProp other o) -> Array (HH.IProp allowed o))
    expand2 = unsafeCoerce :: (Array (HH.IProp required o) -> Array (HH.IProp allowed o))

    -- Render the component. Delegates to the passed in renderer,
    -- lifts all communication from it.
    render :: State partial i -> H.HTML Void (Query partial i o)
    render { value, as: (AroundState { insideState: latest }) } = (Lift <@> unit) <$>
      let
        props = addRefProps (toProps latest)
        renderer attrs = node (expand1 attrs <> expand2 props)
      in renderWith renderer value

    eval :: Query partial i o ~> H.HalogenM (State partial i) (Query partial i o) (Const Void) Void o m
    -- Initialize the component.
    eval (Initialize a) = a <$ do
      -- Run the canceller, just in case ....
      eval (Finalize unit)
      -- Create a ref from the latest style
      as <- H.gets _.as >>= initialize >>> H.liftEff
      -- And store the ref and canceller in state!
      H.modify (_ { as = as })
      -- Start animating the behavior
      H.subscribe $ eventSource' (subscribe behavior)
        (Just <<< (UpdateProp <@> H.Listening))
    -- Update for a new input for the renderer.
    eval (Receive s a) = a <$ do
      as <- H.gets _.as >>= snapshot >>> H.liftEff
      H.modify (_ { value = s, as = as })
    -- Destroy the component.
    eval (Finalize a) = pure a
    -- Raise a query from the HTML to this component's output.
    eval (Lift q a) = a <$ do
      H.raise q
    -- Secretely set the style directly on the element, update the reference.
    -- Should *not* write to state.
    eval (UpdateProp mprop a) = a <$ runMaybeT do
      -- Set the style directly on the DOM element
      el <- htmlElementToElement <$> MaybeT (H.getHTMLElementRef label)
      ref <- MaybeT $ H.gets \{as: AroundState { outsideState }} -> outsideState
      shouldupdate <- H.liftEff $ shouldUpdate ref mprop
      guard shouldupdate
      H.liftEff $ handle el mprop

setProperty ∷ ∀ eff. Fn.Fn3 String PropValue Element (Eff (dom ∷ DOM | eff) Unit)
setProperty = Util.unsafeSetAny

unsafeGetProperty ∷ Fn.Fn2 String Element PropValue
unsafeGetProperty = Util.unsafeGetAny

removeProperty ∷ ∀ eff. Fn.Fn2 String Element (Eff (dom ∷ DOM | eff) Unit)
removeProperty = Fn.mkFn2 \key el →
  case typeOf (Fn.runFn2 Util.unsafeGetAny key el) of
    "string" → Fn.runFn3 Util.unsafeSetAny key "" el
    _        → Fn.runFn3 Util.unsafeSetAny key Util.jsUndefined el

main :: _
main = runHalogenAff $ awaitBody >>= runUI parent unit
  where
    pressed = buttons <#> size >>> (_ > 0)
    blink = seconds <#> round >>> even
    spacebar = key 32
    colorName = blink <#> if _ then "orange" else "rebeccapurple"
    italic = pressed <#> if _ then "italic" else "normal"
    combine coleur italicite = joinWith "; "
      [ "color: " <> coleur
      , "font-style: " <> italicite
      ]
    b =
      { "style": map Just $ combine <$> colorName <*> italic
      , "class": spacebar <#> if _ then Just "align-right" else Nothing
      }
    help = "Hold a mouse button down anywhere on the page to make this text italic!"
    component' = behavioralComponent HH.div <@> b $ \el t ->
      el [] [ HH.h1_ [ HH.text t ] ]
    parent = H.parentComponent
      { render: \v ->
        HH.div_
          [ HH.input [ HP.value v, HE.onInput (HE.input Tuple) ]
          , HH.slot unit component' v (absurd)
          ]
      , eval: \(Tuple e a) -> a <$ do
          for_ (runExcept $ target e # toForeign # readHTMLInputElement)
            (value >>> H.liftEff >=> H.put)
      , initialState: const help
      , receiver: const Nothing
      }
