(*
  Statement-only formalization of the NTP4VC corpus artifact
  pearl/schorr_waite_via_recursion_SchorrWaite_schorr_waiteqtvc: the
  recursive Schorr-Waite graph-traversal verification condition for
  arbitrary-size memory blocks, including body, recursion, loop-invariant,
  pointer-update, marking, and final reachability obligations. This file
  contains no proof.
*)

open HolKernel Parse boolLib bossLib;
open integerTheory pred_setTheory relationTheory;

Datatype:
  swr_color =
    SWRWhite
  | SWRBlack (int option)
End

Datatype:
  swr_memory =
    SWRMemory ('loc -> int) ('loc -> int -> 'loc) ('loc -> swr_color)
End

val swr_block_size_def = Define `
  swr_block_size (SWRMemory blockSize accessor colors) = blockSize`;

val swr_accessor_def = Define `
  swr_accessor (SWRMemory blockSize accessor colors) = accessor`;

val swr_colors_def = Define `
  swr_colors (SWRMemory blockSize accessor colors) = colors`;

val swr_update_def = Define `
  swr_update (old : 'a -> 'b) key value =
    \query. if query = key then value else old query`;

val swr_update_accessor_def = Define `
  swr_update_accessor
      (old : 'loc -> int -> 'loc) location index value =
    swr_update old location
      (swr_update (old location) index value)`;

val swr_black_def = Define `
  swr_black color <=> color <> SWRWhite`;

val swr_not_black_def = Define `
  swr_not_black color <=> ~(swr_black color)`;

val swr_color_index_case_def = Define `
  swr_color_index_case color property <=>
    case color of
      SWRWhite => F
    | SWRBlack NONE => F
    | SWRBlack (SOME index) => property index`;

val swr_block_size_equal_def = Define `
  swr_block_size_equal firstMemory secondMemory <=>
    swr_block_size firstMemory = swr_block_size secondMemory`;

val swr_colors_equal_def = Define `
  swr_colors_equal firstMemory secondMemory <=>
    swr_colors firstMemory = swr_colors secondMemory`;

val swr_accessor_equal_def = Define `
  swr_accessor_equal firstMemory secondMemory <=>
    swr_accessor firstMemory = swr_accessor secondMemory`;

val swr_valid_index_def = Define `
  swr_valid_index null current location index <=>
    location <> null /\
    (0 : int) <= index /\
    index < swr_block_size current location`;

val swr_color_index_valid_def = Define `
  swr_color_index_valid current location <=>
    swr_color_index_case
      (swr_colors current location)
      (\index.
        (0 : int) <= index /\
        index < swr_block_size current location)`;

val swr_edge_def = Define `
  swr_edge null current from to <=>
    from <> null /\
    ?index : int.
      (0 : int) <= index /\
      index < swr_block_size current from /\
      swr_accessor current from index = to`;

val swr_path_def = Define `
  swr_path null current from to <=>
    RTC (swr_edge null current) from to`;

val swr_well_colored_on_def = Define `
  swr_well_colored_on null graph gray initial coloring <=>
    FINITE graph /\
    FINITE gray /\
    gray SUBSET graph /\
    (!x y.
      x IN graph /\
      swr_edge null initial x y /\
      y <> null /\
      swr_black (coloring x)
      ==>
      x IN gray \/ swr_black (coloring y)) /\
    (!x. x IN gray ==> swr_black (coloring x))`;

val swr_unchanged_def = Define `
  swr_unchanged null old new <=>
    !location index.
      swr_valid_index null old location index
      ==>
      swr_accessor new location index =
      swr_accessor old location index`;

val swr_stop_condition_def = Define `
  swr_stop_condition null current pointer target answer <=>
    if pointer = null then
      if target = null then answer
      else answer = swr_black (swr_colors current target)
    else
      ~answer`;

val swr_target_done_condition_def = Define `
  swr_target_done_condition null current target answer <=>
    if target = null then answer
    else answer = swr_black (swr_colors current target)`;

val swr_body_pre_def = Define `
  swr_body_pre null current pointer target <=>
    pointer <> null /\
    (target = null \/ swr_black (swr_colors current target))
    ==>
    swr_color_index_valid current pointer`;

val swr_pop_swing_post_def = Define `
  swr_pop_swing_post old pointer target new newPointer newTarget <=>
    swr_color_index_case
      (swr_colors old pointer)
      (\oldIndex.
        let nextIndex = oldIndex + (1 : int) in
        if nextIndex = swr_block_size old pointer then
          newTarget = pointer /\
          newPointer = swr_accessor old pointer oldIndex /\
          swr_colors_equal new old /\
          swr_accessor new =
            swr_update_accessor
              (swr_accessor old) pointer oldIndex target
        else
          newPointer = pointer /\
          newTarget = swr_accessor old pointer nextIndex /\
          swr_colors new =
            swr_update
              (swr_colors old) pointer (SWRBlack (SOME nextIndex)) /\
          swr_accessor new =
            swr_update_accessor
              (swr_update_accessor
                (swr_accessor old)
                pointer
                nextIndex
                (swr_accessor old pointer oldIndex))
              pointer
              oldIndex
              target)`;

val swr_body_normal_def = Define `
  swr_body_normal null old pointer target new newPointer newTarget <=>
    (pointer <> null \/
     (target <> null /\ swr_not_black (swr_colors old target))) /\
    (target <> null /\
     swr_not_black (swr_colors old target) /\
     swr_block_size old target = (0 : int)
     ==>
     swr_colors new =
       swr_update (swr_colors old) target (SWRBlack NONE) /\
     newTarget = target /\
     newPointer = pointer /\
     swr_accessor_equal new old) /\
    (target <> null /\
     swr_not_black (swr_colors old target) /\
     (0 : int) < swr_block_size old target
     ==>
     swr_colors new =
       swr_update (swr_colors old) target (SWRBlack (SOME (0 : int))) /\
     newTarget = swr_accessor old target (0 : int) /\
     newPointer = target /\
     swr_accessor new =
       swr_update_accessor
         (swr_accessor old) target (0 : int) pointer) /\
    (target = null \/ swr_black (swr_colors old target)
     ==>
     swr_pop_swing_post old pointer target new newPointer newTarget)`;

val swr_body_raises_def = Define `
  swr_body_raises null old pointer target new <=>
    pointer = null /\
    (target = null \/ swr_black (swr_colors old target)) /\
    swr_colors_equal new old /\
    swr_accessor_equal new old`;

val swr_black_body_branch_def = Define `
  swr_black_body_branch null old pointer target <=>
    pointer <> null /\
    swr_color_index_case
      (swr_colors old pointer)
      (\oldIndex.
        pointer <> null /\
        ((0 : int) <= swr_block_size old pointer
         ==>
         let nextIndex = oldIndex + (1 : int) in
         if nextIndex = swr_block_size old pointer then
           swr_valid_index null old pointer oldIndex /\
           swr_valid_index null old pointer oldIndex /\
           (!new.
             swr_block_size_equal new old /\
             swr_colors_equal new old
             ==>
             swr_accessor new =
               swr_update_accessor
                 (swr_accessor old) pointer oldIndex target
             ==>
             swr_body_normal
               null old pointer target new
               (swr_accessor old pointer oldIndex) pointer)
         else
           swr_valid_index null old pointer nextIndex /\
           swr_valid_index null old pointer oldIndex /\
           swr_valid_index null old pointer nextIndex /\
           (!afterFirstWrite.
             swr_block_size_equal afterFirstWrite old /\
             swr_colors_equal afterFirstWrite old
             ==>
             swr_accessor afterFirstWrite =
               swr_update_accessor
                 (swr_accessor old)
                 pointer
                 nextIndex
                 (swr_accessor old pointer oldIndex)
             ==>
             swr_valid_index
               null afterFirstWrite pointer oldIndex /\
             (!afterSecondWrite.
               swr_block_size_equal afterSecondWrite afterFirstWrite /\
               swr_colors_equal afterSecondWrite afterFirstWrite
               ==>
               swr_accessor afterSecondWrite =
                 swr_update_accessor
                   (swr_accessor afterFirstWrite)
                   pointer
                   oldIndex
                   target
               ==>
               swr_valid_index
                 null afterSecondWrite pointer nextIndex /\
               (!new.
                 swr_block_size_equal new afterSecondWrite /\
                 swr_accessor_equal new afterSecondWrite
                 ==>
                 swr_colors new =
                   swr_update
                     (swr_colors afterSecondWrite)
                     pointer
                     (SWRBlack (SOME nextIndex))
                 ==>
                 swr_body_normal
                   null old pointer target new pointer
                   (swr_accessor old pointer nextIndex))))))`;

val swr_white_body_branch_def = Define `
  swr_white_body_branch null old pointer target <=>
    target <> null /\
    ((0 : int) <= swr_block_size old target
     ==>
     if swr_block_size old target = (0 : int) then
       target <> null /\
       swr_block_size old target = (0 : int) /\
       (!new.
         swr_block_size_equal new old /\
         swr_accessor_equal new old
         ==>
         swr_colors new =
           swr_update (swr_colors old) target (SWRBlack NONE)
         ==>
         swr_body_normal null old pointer target new pointer target)
     else
       swr_valid_index null old target (0 : int) /\
       swr_valid_index null old target (0 : int) /\
       (!afterWrite.
         swr_block_size_equal afterWrite old /\
         swr_colors_equal afterWrite old
         ==>
         swr_accessor afterWrite =
           swr_update_accessor
             (swr_accessor old) target (0 : int) pointer
         ==>
         swr_valid_index null afterWrite target (0 : int) /\
         (!new.
           swr_block_size_equal new afterWrite /\
           swr_accessor_equal new afterWrite
           ==>
           swr_colors new =
             swr_update
               (swr_colors afterWrite)
               target
               (SWRBlack (SOME (0 : int)))
           ==>
           swr_body_normal
             null old pointer target new target
             (swr_accessor old target (0 : int)))))`;

val swr_body_implementation_vc_def = Define `
  swr_body_implementation_vc null initial <=>
    !pointer target current.
      swr_block_size_equal current initial
      ==>
      swr_body_pre null current pointer target
      ==>
      !stopAnswer.
        swr_stop_condition null current pointer target stopAnswer
        ==>
        if stopAnswer then
          pointer = null /\
          (target = null \/ swr_black (swr_colors current target))
        else
          !doneAnswer.
            swr_target_done_condition
              null current target doneAnswer
            ==>
            if doneAnswer then
              swr_black_body_branch null current pointer target
            else
              swr_white_body_branch null current pointer target`;

val swr_unmarked_accessors_unchanged_def = Define `
  swr_unmarked_accessors_unchanged null initial current <=>
    !location index.
      location <> null /\
      swr_not_black (swr_colors current location) /\
      (0 : int) <= index /\
      index < swr_block_size current location
      ==>
      swr_accessor current location index =
      swr_accessor initial location index`;

val swr_aux_pre_def = Define `
  swr_aux_pre null graph gray initial current target <=>
    swr_well_colored_on
      null graph gray initial (swr_colors current) /\
    target IN graph /\
    swr_unmarked_accessors_unchanged null initial current`;

val swr_preserve_colors_def = Define `
  swr_preserve_colors null initial old new target <=>
    !location.
      location <> null
      ==>
      (~(swr_path null initial target location) \/
       swr_black (swr_colors old location))
      ==>
      swr_colors new location = swr_colors old location`;

val swr_aux_stable_post_def = Define `
  swr_aux_stable_post null graph gray initial old target new <=>
    swr_unchanged null old new /\
    swr_well_colored_on
      null graph gray initial (swr_colors new) /\
    (swr_black (swr_colors new target) \/ target = null) /\
    swr_preserve_colors null initial old new target`;

val swr_aux_post_def = Define `
  swr_aux_post
      null graph gray initial old pointer target
      new newPointer newTarget <=>
    newTarget = target /\
    newPointer = pointer /\
    swr_unchanged null old new /\
    swr_well_colored_on
      null graph gray initial (swr_colors new) /\
    (swr_black (swr_colors new newTarget) \/ newTarget = null) /\
    swr_preserve_colors null initial old new newTarget`;

val swr_variant_decrease_def = Define `
  swr_variant_decrease graph gray largerGray <=>
    FINITE graph /\
    FINITE gray /\
    FINITE largerGray /\
    (0 : int) <= &(CARD graph) - &(CARD gray) /\
    &(CARD graph) - &(CARD largerGray) <
      &(CARD graph) - &(CARD gray)`;

val swr_loop_invariant_def = Define `
  swr_loop_invariant
      null graph largerGray initial loopEntry entryPointer entryTarget
      blockSize index current pointer target <=>
    swr_well_colored_on
      null graph largerGray initial (swr_colors current) /\
    pointer = entryTarget /\
    target = swr_accessor initial pointer index /\
    swr_colors current pointer = SWRBlack (SOME index) /\
    (!otherIndex.
      (0 : int) <= otherIndex /\
      otherIndex < blockSize /\
      otherIndex <> index
      ==>
      swr_accessor current pointer otherIndex =
      swr_accessor loopEntry pointer otherIndex) /\
    swr_accessor current pointer index = entryPointer /\
    (!location otherIndex.
      location <> null /\
      location <> pointer /\
      (0 : int) <= otherIndex /\
      otherIndex < swr_block_size current location
      ==>
      swr_accessor current location otherIndex =
      swr_accessor loopEntry location otherIndex) /\
    (!otherIndex.
      (0 : int) <= otherIndex /\ otherIndex < index
      ==>
      let location = swr_accessor current pointer otherIndex in
      location = null \/ swr_black (swr_colors current location)) /\
    (!location.
      location <> null
      ==>
      (~(swr_path null initial pointer location) \/
       swr_black (swr_colors loopEntry location))
      ==>
      swr_colors current location =
      swr_colors loopEntry location)`;

val swr_explore_then_body_def = Define `
  swr_explore_then_body
      null graph gray largerGray initial current pointer target
      (continuation :
        'loc swr_memory -> 'loc -> 'loc -> bool) <=>
    swr_variant_decrease graph gray largerGray /\
    swr_aux_pre null graph largerGray initial current target /\
    (!afterAux.
      swr_block_size_equal afterAux current
      ==>
      swr_aux_stable_post
        null graph largerGray initial current target afterAux
      ==>
      swr_body_pre null afterAux pointer target /\
      (!newPointer newTarget afterBody.
        swr_block_size_equal afterBody afterAux
        ==>
        swr_body_normal
          null afterAux pointer target afterBody newPointer newTarget
        ==>
        continuation afterBody newPointer newTarget /\
        ~(swr_body_raises
          null afterAux pointer target afterBody)))`;

val swr_loop_vc_def = Define `
  swr_loop_vc
      null graph gray largerGray initial loopEntry entryPointer entryTarget
      blockSize afterFirstBody firstPointer firstTarget <=>
    let upper = blockSize - (2 : int) in
    let finalIndex = upper + (1 : int) in
    ((0 : int) <= finalIndex
     ==>
     swr_loop_invariant
       null graph largerGray initial loopEntry entryPointer entryTarget
       blockSize (0 : int) afterFirstBody firstPointer firstTarget /\
     (!pointer target current index.
       swr_block_size_equal current afterFirstBody
       ==>
       (0 : int) <= index /\
       index <= upper /\
       swr_loop_invariant
         null graph largerGray initial loopEntry entryPointer entryTarget
         blockSize index current pointer target
       ==>
       swr_explore_then_body
         null graph gray largerGray initial current pointer target
         (\next nextPointer nextTarget.
           swr_loop_invariant
             null graph largerGray initial loopEntry
             entryPointer entryTarget blockSize
             (index + (1 : int))
             next nextPointer nextTarget))) /\
    ((!pointer target current.
       swr_block_size_equal current afterFirstBody
       ==>
       swr_loop_invariant
         null graph largerGray initial loopEntry entryPointer entryTarget
         blockSize finalIndex current pointer target
       ==>
       swr_explore_then_body
         null graph gray largerGray initial current pointer target
         (\next nextPointer nextTarget.
           swr_aux_post
             null graph gray initial loopEntry entryPointer entryTarget
             next nextPointer nextTarget)) /\
     (finalIndex < (0 : int)
      ==>
      swr_explore_then_body
        null graph gray largerGray initial
        afterFirstBody firstPointer firstTarget
        (\next nextPointer nextTarget.
          swr_aux_post
            null graph gray initial loopEntry entryPointer entryTarget
            next nextPointer nextTarget)))`;

val swr_aux_implementation_vc_def = Define `
  swr_aux_implementation_vc null graph initial <=>
    !pointer target current.
      swr_block_size_equal current initial
      ==>
      !gray.
        swr_aux_pre null graph gray initial current target
        ==>
        !doneAnswer.
          swr_target_done_condition
            null current target doneAnswer
          ==>
          if doneAnswer then
            swr_unchanged null current current /\
            swr_well_colored_on
              null graph gray initial (swr_colors current) /\
            (swr_black (swr_colors current target) \/ target = null)
          else
            target <> null /\
            ((0 : int) <= swr_block_size current target
             ==>
             let blockSize = swr_block_size current target in
             let largerGray = target INSERT gray in
             swr_body_pre null current pointer target /\
             (!newPointer newTarget afterFirstBody.
               swr_block_size_equal afterFirstBody current
               ==>
               swr_body_normal
                 null current pointer target afterFirstBody
                 newPointer newTarget
               ==>
               if blockSize <> (0 : int) then
                 swr_loop_vc
                   null graph gray largerGray initial current
                   pointer target blockSize afterFirstBody
                   newPointer newTarget
               else
                 swr_aux_post
                   null graph gray initial current pointer target
                   afterFirstBody newPointer newTarget /\
                 ~(swr_body_raises
                   null current pointer target afterFirstBody)))`;

val swr_final_post_def = Define `
  swr_final_post null initial root final <=>
    swr_unchanged null initial final /\
    (!location.
      swr_path null initial root location /\
      location <> null
      ==>
      swr_black (swr_colors final location)) /\
    (!location.
      ~(swr_path null initial root location) /\
      location <> null
      ==>
      swr_colors final location =
      swr_colors initial location)`;

val swr_main_vc_def = Define `
  swr_main_vc null graph initial root <=>
    swr_well_colored_on
      null graph {} initial (swr_colors initial) /\
    root IN graph /\
    (!afterAux.
      swr_block_size_equal afterAux initial
      ==>
      swr_aux_stable_post
        null graph {} initial initial root afterAux
      ==>
      swr_body_pre null afterAux null root /\
      (!newPointer newTarget afterBody.
        swr_block_size_equal afterBody afterAux
        ==>
        ~(swr_body_normal
          null afterAux null root afterBody newPointer newTarget) /\
        (swr_body_raises null afterAux null root afterBody
         ==>
         swr_final_post null initial root afterBody)))`;

val pearl_schorr_waite_via_recursion_SchorrWaite_schorr_waite_vc =
  ``!(null : 'loc) root
      (graph : 'loc set)
      (initial : 'loc swr_memory).
      FINITE graph /\
      root IN graph /\
      (!location index.
        location IN graph /\
        location <> null /\
        (0 : int) <= index /\
        index < swr_block_size initial location
        ==>
        swr_accessor initial location index IN graph) /\
      (!location.
        location IN graph
        ==>
        swr_not_black (swr_colors initial location))
      ==>
      swr_body_implementation_vc null initial /\
      swr_aux_implementation_vc null graph initial /\
      swr_main_vc null graph initial root``;
