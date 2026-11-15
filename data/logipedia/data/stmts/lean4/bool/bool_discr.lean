-- Statement-only formalization of Logipedia corpus artifact "bool.bool_discr"
-- (catalog title "bool.bool_discr"): equality of two Booleans entails the nested
-- discriminator proposition selected by their values. This file contains no proof.

theorem bool.bool_discr (x y : Bool) :
    x = y →
      match x with
      | true =>
          match y with
          | true => ∀ P : Prop, P → P
          | false => ∀ P : Prop, P
      | false =>
          match y with
          | true => ∀ P : Prop, P
          | false => ∀ P : Prop, P → P := sorry
