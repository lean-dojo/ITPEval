$(
  Statement-only formalization of "Koenigsberg Bridges Problem" from the
  Hundred Theorems corpus, artifact 054: the fixed four-landmass,
  seven-bridge multigraph has no Eulerian trail. This file contains no proof.
$)

$[ library/set.mm $]

$(
  The landmasses are 0 through 3 and the seven distinct bridge objects are
  coded by 0 through 6. A putative Eulerian trail is represented by a
  bijection p from the seven trail positions onto the bridge objects and a
  function q giving the eight successive landmasses. For every position i,
  the unordered pair of consecutive q-values must be the endpoint pair of
  bridge p(i):

    0 : {0,1}   1 : {0,2}   2 : {0,3}   3 : {1,2}
    4 : {1,2}   5 : {2,3}   6 : {2,3}.

  Thus parallel bridges remain distinct, bridge order and traversal
  orientation are internally quantified, and every bridge is used exactly
  once. The assertion below is unproved.
$)

${
  $d i p q $.

  hundred-theorems-054-konigsberg-bridges $a
    |- -.
       E. p E. q
         (
           (
             p : ( 0 ... 6 ) -1-1-onto-> ( 0 ... 6 )
             /\
             q : ( 0 ... 7 ) --> ( 0 ... 3 )
           )
           /\
           A. i e. ( 0 ... 6 )
             (
               (
                 ( ( p ` i ) = 0 /\
                   { ( q ` i ) , ( q ` ( i + 1 ) ) } = { 0 , 1 } )
                 \/
                 ( ( p ` i ) = 1 /\
                   { ( q ` i ) , ( q ` ( i + 1 ) ) } = { 0 , 2 } )
               )
               \/
               (
                 (
                   ( ( p ` i ) = 2 /\
                     { ( q ` i ) , ( q ` ( i + 1 ) ) } = { 0 , 3 } )
                   \/
                   ( ( p ` i ) = 3 /\
                     { ( q ` i ) , ( q ` ( i + 1 ) ) } = { 1 , 2 } )
                 )
                 \/
                 (
                   ( ( p ` i ) = 4 /\
                     { ( q ` i ) , ( q ` ( i + 1 ) ) } = { 1 , 2 } )
                   \/
                   (
                     ( ( p ` i ) = 5 /\
                       { ( q ` i ) , ( q ` ( i + 1 ) ) } = { 2 , 3 } )
                     \/
                     ( ( p ` i ) = 6 /\
                       { ( q ` i ) , ( q ` ( i + 1 ) ) } = { 2 , 3 } )
                   )
                 )
               )
             )
         )
  $.
$}
