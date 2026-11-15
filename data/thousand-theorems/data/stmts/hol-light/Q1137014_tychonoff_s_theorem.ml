(*
  Statement-only formalization of Thousand Theorems corpus artifact Q1137014
  (thousand-theorems__hol-light__Q1137014), "Tychonoff's theorem": an
  arbitrary, possibly empty indexed product of compact subsets of topological
  spaces is compact in the product topology. This file contains no proof.
*)

let Q1137014_TYCHONOFF_S_THEOREM =
  `let is_topology =
     \(carrier:A->bool) (opens:(A->bool)->bool).
       opens {} /\
       opens carrier /\
       (!topology_set:A->bool.
          opens topology_set ==> topology_set SUBSET carrier) /\
       (!topology_family:(A->bool)->bool.
          (!family_member:A->bool.
             family_member IN topology_family ==> opens family_member)
          ==> opens (UNIONS topology_family)) /\
       (!intersection_left intersection_right:A->bool.
          opens intersection_left /\ opens intersection_right
          ==> opens (intersection_left INTER intersection_right)) in
   let is_compact =
     \(compact_carrier:A->bool) (compact_opens:(A->bool)->bool)
      (compact_subset:A->bool).
       compact_subset SUBSET compact_carrier /\
       !open_cover:(A->bool)->bool.
         (!cover_member:A->bool.
            cover_member IN open_cover ==> compact_opens cover_member) /\
         compact_subset SUBSET UNIONS open_cover
         ==> ?finite_subcover:(A->bool)->bool.
               finite_subcover SUBSET open_cover /\
               FINITE finite_subcover /\
               compact_subset SUBSET UNIONS finite_subcover in
   let extensional =
     \(extensional_indices:K->bool) (extensional_function:K->A).
       !extensional_index:K.
         ~(extensional_index IN extensional_indices)
         ==> extensional_function extensional_index = (ARB:A) in
   let product_carrier =
     \(carrier_indices:K->bool) (fibers:K->A->bool).
       {carrier_function:K->A |
          extensional carrier_indices carrier_function /\
          !carrier_index:K.
            carrier_index IN carrier_indices
            ==> carrier_function carrier_index IN fibers carrier_index} in
   let product_open =
     \(open_indices:K->bool) (open_fibers:K->A->bool)
      (coordinate_opens:K->(A->bool)->bool)
      (W:(K->A)->bool).
       W SUBSET
         product_carrier open_indices open_fibers /\
       !product_point:K->A.
         product_point IN W
         ==> ?finite_coordinates:K->bool.
               FINITE finite_coordinates /\
               finite_coordinates SUBSET open_indices /\
               ?basic_sets:K->A->bool.
                 (!basic_index:K.
                    basic_index IN finite_coordinates
                    ==> coordinate_opens basic_index (basic_sets basic_index) /\
                        product_point basic_index IN basic_sets basic_index) /\
                 {basic_point:K->A |
                    basic_point IN
                      product_carrier open_indices open_fibers /\
                    !basic_coordinate:K.
                      basic_coordinate IN finite_coordinates
                      ==> basic_point basic_coordinate IN
                          basic_sets basic_coordinate}
                 SUBSET W in
   let is_product_compact =
     \(product_compact_carrier:(K->A)->bool)
      (product_opens:((K->A)->bool)->bool)
      (product_compact_subset:(K->A)->bool).
       product_compact_subset SUBSET product_compact_carrier /\
       !product_cover:((K->A)->bool)->bool.
         (!product_cover_member:(K->A)->bool.
            product_cover_member IN product_cover
            ==> product_opens product_cover_member) /\
         product_compact_subset SUBSET UNIONS product_cover
         ==> ?product_finite_subcover:((K->A)->bool)->bool.
               product_finite_subcover SUBSET product_cover /\
               FINITE product_finite_subcover /\
               product_compact_subset SUBSET
                 UNIONS product_finite_subcover in
   !idx:K->bool.
   !spaces:K->A->bool.
   !space_opens:K->(A->bool)->bool.
   !compact_sets:K->A->bool.
     (!index:K.
        index IN idx
        ==> is_topology (spaces index) (space_opens index) /\
            is_compact
              (spaces index) (space_opens index) (compact_sets index))
     ==> is_product_compact
           (product_carrier idx spaces)
           (product_open idx spaces space_opens)
           (product_carrier idx compact_sets)`;;
