$(
  Statement-only formalization of Thousand Theorems corpus artifact Q656198
  (thousand-theorems__metamath__Q656198), "Maschke's theorem": over a field
  whose characteristic does not annihilate the order of a finite group, every
  submodule of every module over the corresponding group algebra has a
  complementary submodule. This file contains no proof.
$)

$[ lib/set.mm $]

$(
  K is an arbitrary SetMM field and G an arbitrary finite SetMM group.
  SetMM's ( K MndRing G ) is the finitely-supported function ring on Base G
  with convolution, exactly the group algebra K[G]. Q656198NatCast is the
  repeated-addition natural-number cast into K, so its nonvanishing at the
  finite cardinality of Base G is precisely the source NeZero assumption.

  M ranges over arbitrary left modules whose scalar ring is K MndRing G.
  P and Q range over their actual linear subspaces. The complement condition
  says their intersection is the zero submodule and every vector is a sum of
  one vector from each; this is bidirectionally equivalent to IsCompl P Q in
  the submodule lattice.

  The final declaration is the single unproved corpus statement. The preceding
  declarations are syntax and a faithful definition, and this database
  contains no $p proof statement.
$)

$c Q656198NatCast $.

q656198-natural-cast-syntax
  $a class ( Q656198NatCast K N ) $.

q656198-natural-cast-definition $a |-
  ( Q656198NatCast K N )
  =
  ( N ( .g ` K ) ( 1r ` K ) )
$.

${
  $d G K M N P Q m p q $.

  thousand-theorems-q656198-maschke-s-theorem $a |- (
    A. K A. G
      (
        (
          K e. Field
          /\
          G e. Grp
          /\
          ( Base ` G ) e. Fin
          /\
          (
            Q656198NatCast K ( # ` ( Base ` G ) )
          ) =/= ( 0g ` K )
        )
        ->
        A. M
          (
            (
              M e. LMod
              /\
              ( Scalar ` M ) = ( K MndRing G )
            )
            ->
            A. P e. ( LSubSp ` M )
              E. Q e. ( LSubSp ` M )
                (
                  ( P i^i Q ) = { ( 0g ` M ) }
                  /\
                  A. m e. ( Base ` M )
                    E. p e. P E. q e. Q
                      m = ( p ( +g ` M ) q )
                )
          )
      )
  ) $.
$}
