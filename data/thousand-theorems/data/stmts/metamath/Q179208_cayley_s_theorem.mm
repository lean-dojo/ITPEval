$(
  Statement-only formalization of Thousand Theorems corpus artifact Q179208
  (thousand-theorems__metamath__Q179208), "Cayley's theorem": every group with
  a faithful action is isomorphic, via its induced permutation representation,
  to that representation's range subgroup. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  In SetMM, A e. ( G GrpAct H ) says that A is a group action of the arbitrary
  group G on the arbitrary set H. Q179208ActionHom G H A is the curried map
  sending each group element g to the permutation h |-> A(g,h). Its being a
  one-to-one function into Base ` ( SymGrp ` H ) is exactly faithfulness.
  Restricting SymGrp ` H to the range of this homomorphism gives the range
  subgroup. The final declaration asserts that this same induced map is a
  group isomorphism onto that subgroup.

  The auxiliary declarations are syntax and a faithful definition. The final
  $a declaration is the unproved corpus statement; there is no $p statement.
$)

$c Q179208ActionHom $.

q179208-action-hom-syntax $a class ( Q179208ActionHom G H A ) $.

${
  $d A G H x y $.

  q179208-action-hom-definition $a |- ( Q179208ActionHom G H A ) =
    ( x e. ( Base ` G ) |->
      ( y e. H |-> ( A ` <. x , y >. ) ) )
  $.
$}

${
  $d A G H $.

  thousand-theorems-q179208-cayley-s-theorem $a |- (
    A. G A. H A. A
      (
        (
          A e. ( G GrpAct H )
          /\
          ( Q179208ActionHom G H A ) :
            ( Base ` G ) -1-1-> ( Base ` ( SymGrp ` H ) )
        )
        ->
        ( Q179208ActionHom G H A ) e.
          (
            G GrpIso
            (
              ( SymGrp ` H ) |`s
              ran ( Q179208ActionHom G H A )
            )
          )
      )
  ) $.
$}
