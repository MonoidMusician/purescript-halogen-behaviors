module Halogen.Behavior where

import Prelude

import Control.Monad.Aff.Class (class MonadAff)
import Control.Monad.Eff (Eff)
import Control.Monad.Eff.AVar (AVAR)
import Control.Monad.Eff.Exception (EXCEPTION)
import Control.Monad.Eff.Ref (REF)
import Control.Monad.Except (runExcept)
import Control.Monad.Maybe.Trans (MaybeT(..), runMaybeT)
import Control.MonadZero (guard)
import DOM (DOM)
import DOM.Event.Event (target)
import DOM.HTML.HTMLInputElement (value)
import DOM.HTML.Types (htmlElementToElement, readHTMLInputElement)
import Data.Bifunctor (bimap)
import Data.Const (Const)
import Data.Either.Nested (Either2)
import Data.Foldable (for_)
import Data.Foreign (toForeign)
import Data.Functor.Coproduct.Nested (Coproduct2)
import Data.Int (even, round)
import Data.Maybe (Maybe(..))
import Data.Set (size)
import Data.String (joinWith)
import Data.Tuple (Tuple(..))
import Data.Variant (Variant)
import FRP (FRP)
import FRP.Behavior (Behavior)
import FRP.Behavior.Keyboard (key)
import FRP.Behavior.Mouse (buttons)
import FRP.Behavior.Time (seconds)
import Halogen (RefLabel(..))
import Halogen as H
import Halogen.Aff (awaitBody, runHalogenAff)
import Halogen.Behavior.ElementBehaviors (class ElementBehaviors, Precise(..), allAttrs, mkBehaviors, update)
import Halogen.Behavior.Internal (class Nothings, AroundState(..), initialize, mapIProp, snapshot, uninitializedAS)
import Halogen.Behavior.Internal.MultiAttrBehavior (class MultiAttrBehavior, handle, shouldUpdate, subscribe, toProps)
import Halogen.Component.ChildPath as CP
import Halogen.HTML as HH
import Halogen.HTML.Events as HE
import Halogen.HTML.Properties as HP
import Halogen.Query.EventSource (eventSource')
import Halogen.VDom.Driver (runUI)
import Type.Row (RProxy(..))
import Unsafe.Coerce (unsafeCoerce)

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

type SimpleHTML m o = HH.HTML (H.ComponentSlot HH.HTML (Const Void) m Void o) o
type SimpleHTML1 m q = SimpleHTML m (q Unit)

behavioralComponent ::
  forall m all i o required partial behaviors eff ebehaviors callbacks internals other rl.
    MonadAff ( dom :: DOM, frp :: FRP, ref :: REF, avar :: AVAR | eff ) m =>
    MultiAttrBehavior required partial behaviors =>
    ElementBehaviors all ebehaviors callbacks internals =>
    Union required other all =>
    Nothings partial =>
  (forall w q. HH.Node all w q) ->
  (forall q.
    (o -> q Unit) ->
    (
      Array (HH.IProp other o) ->
      Array (SimpleHTML m o) ->
      SimpleHTML1 m q
    ) ->
    i ->
    SimpleHTML1 m q
  ) ->
  (
    Record ebehaviors ->
    Record behaviors
  ) ->
  H.Component HH.HTML (Query internals partial i o) i o m
behavioralComponent = behavioralParentComponent

behavioralParentComponent ::
  forall g p m all i o required partial behaviors eff ebehaviors callbacks internals other rl.
    MonadAff ( dom :: DOM, frp :: FRP, ref :: REF, avar :: AVAR | eff ) m =>
    MultiAttrBehavior required partial behaviors =>
    ElementBehaviors all ebehaviors callbacks internals =>
    Union required other all =>
    Nothings partial =>
    Ord p =>
  (forall w q. HH.Node all w q) ->
  (forall q.
    (o -> q Unit) ->
    (
      Array (HH.IProp other o) ->
      Array (HH.HTML (H.ComponentSlot HH.HTML g m p o) o) ->
      H.ParentHTML q g p m
    ) ->
    i ->
    H.ParentHTML q g p m
  ) ->
  (
    Record ebehaviors ->
    Record behaviors
  ) ->
  H.Component HH.HTML (Query internals partial i o) i o m
behavioralParentComponent node renderWith behavior =
  H.lifecycleParentComponent
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
    events :: Array (H.IProp all (Query internals partial i o))
    events = mapIProp (UpdateBehavior <@> unit) <$> allAttrs (RProxy :: RProxy ebehaviors)
    lift1 :: o -> Query internals partial i o Unit
    lift1 = Lift <@> unit
    adapt :: HH.HTML (H.ComponentSlot HH.HTML g m p o) o -> H.ParentHTML (Query internals partial i o) g p m
    adapt = bimap (map lift1) lift1
    lifting :: Array (HH.IProp all o) -> Array (H.IProp all (Query internals partial i o))
    lifting = map (mapIProp (lift1))

    -- Render the component. Delegates to the passed in renderer,
    -- lifts all communication from it.
    render :: State callbacks partial i -> H.ParentHTML (Query internals partial i o) g p m
    render { value, as: (AroundState { insideState: latest }), pushers } =
      let
        props = addRefProps (toProps latest)
        renderer attrs children =
          node (events <> lifting (expand1 attrs <> expand2 props))
          (adapt <$> children)
      in renderWith lift1 renderer value

    eval :: Query internals partial i o ~> H.HalogenM (State callbacks partial i) (Query internals partial i o) g p o m
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

main :: forall e.
  Eff
    ( avar :: AVAR
    , ref :: REF
    , exception :: EXCEPTION
    , dom :: DOM
    , frp :: FRP
    | e
    )
    Unit
main = runHalogenAff $ awaitBody >>= runUI parent unit
  where
    pressed = buttons <#> size >>> (_ > 0)
    blink = seconds <#> round >>> even
    spacebar = key 32
    colorName = blink <#> if _ then "orange" else "rebeccapurple"
    italic = pressed <#> if _ then "italic" else "normal"
    combine focusedWhere coleur italicite = joinWith "; " $
      [ "color: " <> coleur
      , "font-style: " <> italicite
      ] <> case focusedWhere of
        Here -> [ "font-weight: normal" ]
        Child -> [ "font-decoration: underline" ]
        None -> [ "text-transform: capitalize" ]
    b :: { preciseHover :: Behavior Precise, hover :: Behavior Boolean } -> { "style" :: Behavior (Maybe String), "class" :: Behavior (Maybe String) }
    b { preciseHover, hover } =
      { "style": map Just $ combine <$> preciseHover <*> colorName <*> italic
      , "class": spacebar <#> if _ then Just "align-right" else Nothing
      }
    help = "Hold a mouse button down anywhere on the page to make this text italic!"
    component1 = (behavioralComponent HH.h1 <@> b) \_ el t ->
      el [] [ HH.text t, HH.span_ [ HH.text " my span" ] ]
    inputColor :: { focus :: Behavior Boolean, hover :: Behavior Boolean } -> { style :: Behavior (Maybe String) }
    inputColor { focus, hover } = { style: _ } $ map Just $
      (\f h -> "color: " <>
        if f
        then if h then "purple" else "blue"
        else if h then "red" else "black"
      ) <$> focus <*> hover
    component2 = (behavioralComponent (\a _ -> HH.input a) <@> inputColor) \_ el v ->
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
