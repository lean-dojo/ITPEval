$(
  Statement-only formalization of "The Ballot Problem" from Hundred Theorems
  item 030: the exact count and uniform proportion of binary vote sequences
  in which candidate A is strictly ahead after every nonempty prefix. This
  file contains no proof.
$)

$[ library/set.mm $]

$(
  The included set.mm library supplies the standard natural numbers NN0,
  finite words, function application, finite intervals, restricted set
  abstraction, finite set size, and ordinary arithmetic and order.

  A ballot with p votes for A and q votes for B is represented by a word w
  over { 0 , 1 } of length p + q.  The symbol 1 represents A and 0 represents
  B.  Both prescribed vote counts are stated explicitly.  A valid ballot also
  has more 1 entries than 0 entries in every prefix of length m, for
  1 <= m <= p + q.

  The first unproved $a assertion is the natural-number counting identity.
  Its conditional if ( q <_ p , p - q , 0 ) explicitly renders truncated
  natural subtraction, including the p < q edge cases.  The second assertion
  is the uniform finite-cardinality ratio form under q < p.  There are no $p
  proof statements in this file.
$)

$(
  For all natural p and q,

    (p + q) * number-of-valid-ballots
      = (p - q) * number-of-all-ballots.
$)
hundred-theorems-030-ballot-counting $a
  |- A. p e. NN0
       A. q e. NN0
         (
           ( ( p + q ) x.
             ( # `
               { w e.
                 { w e. Word { 0 , 1 } |
                   ( ( # ` w ) = ( p + q ) /\
                     ( ( # `
                         { i e. ( 0 ..^ ( # ` w ) ) | ( w ` i ) = 1 }
                       ) = p /\
                       ( # `
                         { i e. ( 0 ..^ ( # ` w ) ) | ( w ` i ) = 0 }
                       ) = q
                     )
                   )
                 } |
                 A. m e. ( 1 ... ( p + q ) )
                   ( ( # `
                       { i e. ( 0 ..^ m ) | ( w ` i ) = 0 }
                     ) <
                     ( # `
                       { i e. ( 0 ..^ m ) | ( w ` i ) = 1 }
                     )
                   )
               }
             )
           )
           =
           ( ( if ( q <_ p , ( p - q ) , 0 ) ) x.
             ( # `
               { w e. Word { 0 , 1 } |
                 ( ( # ` w ) = ( p + q ) /\
                   ( ( # `
                       { i e. ( 0 ..^ ( # ` w ) ) | ( w ` i ) = 1 }
                     ) = p /\
                     ( # `
                       { i e. ( 0 ..^ ( # ` w ) ) | ( w ` i ) = 0 }
                     ) = q
                   )
                 )
               }
             )
           )
         )
$.

$(
  If q < p, the uniform proportion of ballots in which A is strictly ahead
  after every nonempty prefix is (p - q) / (p + q).
$)
hundred-theorems-030-ballot-probability $a
  |- A. q e. NN0
       A. p e. NN0
         ( q < p ->
           (
             ( ( # `
                 { w e.
                   { w e. Word { 0 , 1 } |
                     ( ( # ` w ) = ( p + q ) /\
                       ( ( # `
                           { i e. ( 0 ..^ ( # ` w ) ) | ( w ` i ) = 1 }
                         ) = p /\
                         ( # `
                           { i e. ( 0 ..^ ( # ` w ) ) | ( w ` i ) = 0 }
                         ) = q
                       )
                     )
                   } |
                   A. m e. ( 1 ... ( p + q ) )
                     ( ( # `
                         { i e. ( 0 ..^ m ) | ( w ` i ) = 0 }
                       ) <
                       ( # `
                         { i e. ( 0 ..^ m ) | ( w ` i ) = 1 }
                       )
                     )
                 }
               ) /
               ( # `
                 { w e. Word { 0 , 1 } |
                   ( ( # ` w ) = ( p + q ) /\
                     ( ( # `
                         { i e. ( 0 ..^ ( # ` w ) ) | ( w ` i ) = 1 }
                       ) = p /\
                       ( # `
                         { i e. ( 0 ..^ ( # ` w ) ) | ( w ` i ) = 0 }
                       ) = q
                     )
                   )
                 }
               )
             )
             =
             ( ( p - q ) / ( p + q ) )
           )
         )
$.
