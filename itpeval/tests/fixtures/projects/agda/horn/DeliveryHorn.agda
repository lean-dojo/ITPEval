{-# OPTIONS --safe #-}
module DeliveryHorn where

deliver : {Item : Set} (item : Item) (Ready Permitted Delivered Complete Extra : Item → Set)
  → Ready item → Permitted item → (Ready item → Permitted item → Delivered item)
  → (Delivered item → Complete item) → Extra item → Complete item
deliver item Ready Permitted Delivered Complete Extra ready permitted transit finish extra =
  finish (transit ready permitted)
