module Halogen.Behavior where

import Prelude

import Control.Monad.Aff.Class (class MonadAff)
import Control.Monad.Eff (Eff)
import Control.Monad.Eff.AVar (AVAR)
import Control.Monad.Eff.Ref (REF, Ref, modifyRef, newRef, readRef)
import Control.Monad.Eff.Uncurried as EffFn
import Control.Monad.Eff.Unsafe (unsafeCoerceEff)
import Control.Monad.Except (runExcept)
import Control.Monad.Maybe.Trans (MaybeT(..), runMaybeT)
import Control.Monad.ST (ST)
import Control.MonadZero (guard)
import DOM (DOM)
import DOM.Event.Event (target)
import DOM.Event.Types (FocusEvent, MouseEvent)
import DOM.HTML.HTMLInputElement (value)
import DOM.HTML.Types (htmlElementToElement, readHTMLInputElement)
import DOM.Node.Types (Element)
import Data.Array.ST (emptySTArray, pokeSTArray, pushSTArray, unsafeFreeze)
import Data.Const (Const)
import Data.Either (Either(..))
import Data.Either.Nested (Either2)
import Data.Foldable (for_, traverse_)
import Data.Foreign (toForeign, typeOf)
import Data.Function.Uncurried as Fn
import Data.Functor.Coproduct.Nested (Coproduct2)
import Data.Int (even, round)
import Data.Maybe (Maybe(..))
import Data.Record (delete, get, insert, set)
import Data.Record.Builder as B
import Data.Set (size)
import Data.String (joinWith)
import Data.Symbol (class IsSymbol, SProxy(..), reflectSymbol)
import Data.Tuple (Tuple(..))
import Data.Variant (class VariantMatchCases, Variant, case_, expand, inj, on)
import FRP (FRP)
import FRP.Behavior (ABehavior, Behavior, animate, step, unfold)
import FRP.Behavior.Keyboard (key)
import FRP.Behavior.Mouse (buttons)
import FRP.Behavior.Time (seconds)
import FRP.Event (Event)
import Halogen (RefLabel(..))
import Halogen as H
import Halogen.Aff (awaitBody, runHalogenAff)
import Halogen.Component.ChildPath as CP
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
import Type.Row (class ListToRow, class RowLacks, class RowToList, Cons, Nil, RLProxy(..), RProxy(..), kind RowList)
import Unsafe.Coerce (unsafeCoerce)
import Unsafe.Reference (unsafeRefEq)

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

mapIProp :: forall attrs a b. (a -> b) -> IProp attrs a -> IProp attrs b
mapIProp f (IProp p) = IProp (map f <$> p)

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
      { event, push: cb } <- subject
      let b = process s event
      pure $ Tuple
        (b' >>> B.insert s b)
        (cb' >>> B.insert s (unsafeCoerce (EffFn.runEffFn1 cb)))
      where s = SProxy :: SProxy s
    updateRL _ r cbs =
      on s (unsafeCoerce cb) $
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

type State callbacks partial i =
  { value :: i
  , as :: AroundState partial
  , pushers :: Maybe (Record callbacks)
  }
initialState :: forall callbacks partial i. Nothings partial => i -> State callbacks partial i
initialState =
  { value: _
  , as: uninitializedAS
  , pushers: Nothing
  }

data Query internals partial i o a
  = Initialize a
  | Finalize a
  | Receive i a
  | Lift o a
  | UpdateProp (Variant partial) a
  | UpdateBehavior (Variant internals) a

type SubscribeCancel eff v = (v -> Eff eff Unit) -> Eff eff (Eff eff Unit)

class Nothings partial <= MultiAttrBehavior
  (required :: # Type) -- IsProp p => p
  (partial :: # Type) -- Maybe p
  (behaviors :: # Type) -- Behavior (Maybe p)
  | required -> partial behaviors
  , partial -> required behaviors
  where
    subscribe :: forall e. Record behaviors -> SubscribeCancel ( frp :: FRP | e ) (Variant partial)
    handle :: forall e. Element -> Variant partial -> Eff ( dom :: DOM | e ) Unit
    toProps :: forall i. Record partial -> Array (IProp required i)
    shouldUpdate :: forall e. Ref (Record partial) -> Variant partial -> Eff ( ref :: REF | e ) Boolean
instance mab ::
  -- Use both RowToList and ListToRow for inference purposes
  ( RowToList required arl
  , ListToRow arl required
  , RowToList partial prl
  , ListToRow prl partial
  , RowToList behaviors brl
  , ListToRow brl behaviors
  , NothingsRL prl partial
  , MultiAttrBehaviorRL arl prl brl required partial behaviors
  ) => MultiAttrBehavior required partial behaviors where
    subscribe = subscribeRL (RLProxy :: RLProxy arl)
    handle = handleRL (RLProxy :: RLProxy arl)
    toProps = toPropsRL (RLProxy :: RLProxy arl)
    shouldUpdate = shouldUpdateRL (RLProxy :: RLProxy arl)

class
  ( NothingsRL prl partial
  , RowToList required arl, ListToRow arl required
  , RowToList behaviors brl -- , ListToRow brl behaviors
  ) <= MultiAttrBehaviorRL
  (arl :: RowList)
  (prl :: RowList)
  (brl :: RowList)
  (required :: # Type) -- IsProp p => p
  (partial :: # Type) -- Maybe p
  (behaviors :: # Type) -- Behavior (Maybe p)
  | arl -> required
  , prl -> partial
  , brl -> behaviors
  , arl -> prl brl
  , prl -> arl brl
  , brl -> arl prl
  where
    subscribeRL :: forall e. RLProxy arl -> Record behaviors -> SubscribeCancel ( frp :: FRP | e ) (Variant partial)
    handleRL :: forall e. RLProxy arl -> Element -> Variant partial -> Eff ( dom :: DOM | e ) Unit
    toPropsRL :: forall i. RLProxy arl -> Record partial -> Array (IProp required i)
    shouldUpdateRL :: forall e. RLProxy arl -> Ref (Record partial) -> Variant partial -> Eff ( ref :: REF | e ) Boolean
instance mabNil :: MultiAttrBehaviorRL Nil Nil Nil () () () where
  subscribeRL _ {} cb = pure (pure unit)
  handleRL _ _ = case_
  toPropsRL _ {} = []
  shouldUpdateRL _ _ = case_
instance mabCons ::
  ( IsSymbol label
  , IsProp p
  , RowLacks label required'
  , RowLacks label partial'
  , RowLacks label behaviors'
  , RowCons label p required' required
  , RowCons label (Maybe p) partial' partial
  , RowCons label (Behavior (Maybe p)) behaviors' behaviors
  , Union partial' one partial
  , RowToList required (Cons label p arl)
  -- , ListToRow (Cons label p arl) required
  , RowToList partial (Cons label (Maybe p) prl)
  -- , ListToRow (Cons label (Maybe p) prl) partial
  , RowToList behaviors (Cons label (Behavior (Maybe p)) brl)
  -- , ListToRow (Cons label (Behavior (Maybe p)) brl) behaviors
  -- , Nothings partial
  -- , NothingsRL (Cons label (Maybe p) prl) partial
  , MultiAttrBehaviorRL arl prl brl required' partial' behaviors'
  ) => MultiAttrBehaviorRL
    (Cons label p arl)
    (Cons label (Maybe p) prl)
    (Cons label (ABehavior Event (Maybe p)) brl)
    required partial behaviors where
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
          exp = unsafeCoerce :: (forall i. Array (IProp required' i) -> Array (IProp required i))
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

subject :: forall a eff.
  Eff ( frp :: FRP | eff )
  { event :: Event a, push :: EffFn.EffFn1 ( frp :: FRP | eff ) a Unit }
subject = unsafeCoerce subject'
subject' :: forall a eff.
  Eff ( frp :: FRP | eff )
    { event ::
        EffFn.EffFn1 ( frp :: FRP | eff )
          (EffFn.EffFn1 ( frp :: FRP | eff ) a Unit)
          (Eff ( frp :: FRP | eff ) Unit)
    , push :: EffFn.EffFn1 ( frp :: FRP | eff ) a Unit
    }
subject' = do
  subs <- noST emptySTArray
  pure
    { event: EffFn.mkEffFn1 \sub -> noST do
        i <- pushSTArray subs sub
        pure $ void $ noST do
          pokeSTArray subs (i-1) noop
    , push: EffFn.mkEffFn1 \a -> do
        noST (unsafeFreeze subs) >>= traverse_ (EffFn.runEffFn1 <@> a)
    }
  where
    noop = EffFn.mkEffFn1 (pure (pure unit))
    -- Shh. You see nothing.
    noST :: forall h e. Eff ( st :: ST h | e ) ~> Eff e
    noST = unsafeCoerceEff

behavioralComponent ::
  forall m all i o required partial behaviors eff ebehaviors callbacks internals other rl.
    MonadAff ( dom :: DOM, frp :: FRP, ref :: REF, avar :: AVAR | eff ) m =>
    MultiAttrBehavior required partial behaviors =>
    -- ElementBehaviors all ebehaviors callbacks internals =>
    RowToList ebehaviors rl =>
    ElementBehaviorsRL all rl ebehaviors callbacks internals =>
    Union required other all =>
    Nothings partial =>
  -- Warning: leaky abstraction
  HH.Node (all) Void (Query internals partial i o Unit) ->
  (
    -- Still leaking
    (
      Array (HH.IProp other o) ->
      Array (HH.HTML Void o) ->
      H.HTML Void (Query internals partial i o)
    ) ->
    i ->
    -- Leaked
    H.HTML Void (Query internals partial i o)
  ) ->
  (
    Record ebehaviors ->
    Record behaviors
  ) ->
  H.Component HH.HTML (Query internals partial i o) i o m
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
    expand1 = unsafeCoerce :: (Array (HH.IProp other o) -> Array (HH.IProp (all) o))
    expand2 = unsafeCoerce :: (Array (HH.IProp required o) -> Array (HH.IProp (all) o))
    events :: Array (H.IProp (all) (Query internals partial i o))
    events = mapIProp (UpdateBehavior <@> unit) <$> attrsRL (RLProxy :: RLProxy rl)
    lifting :: Array (HH.IProp (all) o) -> Array (H.IProp (all) (Query internals partial i o))
    lifting = map (mapIProp (Lift <@> unit))

    -- Render the component. Delegates to the passed in renderer,
    -- lifts all communication from it.
    render :: State callbacks partial i -> H.HTML Void (Query internals partial i o)
    render { value, as: (AroundState { insideState: latest }), pushers } =
      let
        props = addRefProps (toProps latest)
        renderer attrs children =
          node (events <> lifting (expand1 attrs <> expand2 props))
          (map (Lift <@> unit) <$> children)
      in renderWith renderer value

    eval :: Query internals partial i o ~> H.HalogenM (State callbacks partial i) (Query internals partial i o) (Const Void) Void o m
    -- Initialize the component.
    eval (Initialize a) = a <$ do
      -- Run the finalizer, just in case ....
      eval (Finalize unit)
      -- Create a ref from the latest style
      as <- H.gets _.as >>= initialize >>> H.liftEff
      -- And store it in state!
      H.modify (_ { as = as })
      Tuple status pushers <- H.liftEff $ mkBehaviors (RProxy :: RProxy all)
      H.modify (_ { pushers = Just pushers })
      -- Start animating the behavior
      H.subscribe $ eventSource' (subscribe (behavior status))
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
    eval (UpdateBehavior which a) = a <$ runMaybeT do
      pushers <- MaybeT $ H.gets _.pushers
      H.liftEff $ update (RProxy :: RProxy ebehaviors) (RProxy :: RProxy all) pushers which

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
    b :: { focus :: Behavior Boolean, hover :: Behavior Boolean } -> { "style" :: Behavior (Maybe String), "class" :: Behavior (Maybe String) }
    b { focus, hover } =
      { "style": map Just $ combine <$> colorName <*> italic
      , "class": spacebar <#> if _ then Just "align-right" else Nothing
      }
    help = "Hold a mouse button down anywhere on the page to make this text italic!"
    component1 = behavioralComponent HH.div <@> b $ \el t ->
      el [] [ HH.h1_ [ HH.text t ] ]
    inputColor :: { focus :: Behavior Boolean, hover :: Behavior Boolean } -> { style :: Behavior (Maybe String) }
    inputColor { focus, hover } = { style: _ } $ map Just $
      (\f h -> "color: " <>
        if f
        then if h then "purple" else "blue"
        else if h then "red" else "black"
      ) <$> focus <*> hover
    component2 = behavioralComponent (\a _ -> HH.input a) <@> inputColor $ \el v ->
      el [ HP.value v, HE.onInput (HE.input Tuple) ] []
    parent = H.parentComponent
      { render: \v ->
        HH.div_
          [ HH.slot' cp_cp2 unit component2 v pure
          , HH.slot' CP.cp1 unit component1 v absurd
          ]
      , eval: \(Tuple e a) -> a <$ do
          for_ (runExcept $ target e # toForeign # readHTMLInputElement)
            (value >>> H.liftEff >=> H.put)
      , initialState: const help
      , receiver: const Nothing
      }
      where
        -- Give a finite type to the slot
        cp_cp2 = CP.cp2 :: forall f g a b. CP.ChildPath g (Coproduct2 f g) b (Either2 a b)
