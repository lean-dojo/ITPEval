$(
  Statement-only formalization of Thousand Theorems corpus artifact Q2226800
  (thousand-theorems__metamath__Q2226800), "Schur-Zassenhaus theorem": a
  normal subgroup whose order is coprime to its index has a left complement.
  This file contains no proof.
$)

$[ lib/set.mm $]

$(
  In SetMM, G e. Grp is an arbitrary group, N e. ( NrmSGrp ` G ) is a
  normal subgroup, and H e. ( SubGrp ` G ) is a subgroup. Lean's Nat.card
  returns zero for an infinite type, whereas SetMM's # returns +oo for an
  infinite set. Q2226800Card and Q2226800Index therefore preserve the source's
  zero-on-infinite convention for the order of N and the cardinality of its
  left-coset quotient.

  The conclusion says that every element g of G has a unique factorization
  g = h n with h in H and n in N. This is exactly the source definition of
  Subgroup.IsComplement' H N as bijectivity of multiplication H x N -> G.
  The auxiliary definitions and final corpus declaration are unproved $a
  statements; this database contains no $p proof statement.
$)

$c Q2226800Card Q2226800Index $.

q2226800-card-syntax $a class ( Q2226800Card N ) $.
q2226800-index-syntax $a class ( Q2226800Index G N ) $.

${
  q2226800-card-definition $a |- ( Q2226800Card N ) =
    if (
      N e. Fin
      ,
      ( # ` N )
      ,
      0
    )
  $.
$}

${
  $d G N $.

  q2226800-index-definition $a |- ( Q2226800Index G N ) =
    if (
      ( ( Base ` G ) /. ( G ~QG N ) ) e. Fin
      ,
      ( # ` ( ( Base ` G ) /. ( G ~QG N ) ) )
      ,
      0
    )
  $.
$}

${
  $d G H N g h i j n $.

  thousand-theorems-q2226800-schur-zassenhaus $a |- (
    A. G A. N
      (
        (
          G e. Grp
          /\
          N e. ( NrmSGrp ` G )
          /\
          (
            ( Q2226800Card N )
            gcd
            ( Q2226800Index G N )
          )
          =
          1
        )
        ->
        E. H e. ( SubGrp ` G )
          A. g e. ( Base ` G )
            E. h e. H E. n e. N
              (
                ( h ( +g ` G ) n ) = g
                /\
                A. i e. H A. j e. N
                  (
                    ( i ( +g ` G ) j ) = g
                    ->
                    (
                      i = h
                      /\
                      j = n
                    )
                  )
              )
      )
  ) $.
$}
