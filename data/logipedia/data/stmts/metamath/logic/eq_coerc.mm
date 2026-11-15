$(
  Statement-only formalization of the Logipedia corpus artifact
  logic.eq_coerc, catalog title "logic.eq_coerc": the module's polymorphic
  equality specialized to propositions transports truth from the first
  proposition to the second. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  LogLogicEqProp ph ps represents the fixed source proposition
  logic.eq Prop A B. Its $a declaration supplies only wff syntax.
  Metamath's wff metavariables ph and ps range schematically over the
  universally quantified source propositions A and B. The nested
  implications preserve the curried assumptions A -> logic.eq Prop A B -> B.
  The final $a declaration is the native unproved statement encoding; this
  database contains no $p proof declaration.
$)

$c LogLogicEqProp $.

logipedia-logic-eq-prop-syntax $a wff
  LogLogicEqProp ph ps
$.

logipedia-logic-eq-coerc $a |-
  ( ph -> ( LogLogicEqProp ph ps -> ps ) )
$.
