(*
  Statement-only formalization of NTP4VC corpus artifact
  pearl/multiprecision/base_info_BaseInfo_wmpn_base_power_of_two_pqtvc:
  the verification condition for recognizing powers of two from 2 through
  256 and returning their exponents in a 32-bit word. This file contains no
  proof.
*)

let base_info_output = open_out "/dev/null";;
let base_info_formatter = Format.formatter_of_out_channel base_info_output;;
let base_info_previous_file_loader = !Hol_loader.file_loader;;
Hol_loader.file_loader :=
  (fun path -> Toploop.use_file base_info_formatter path);;
let base_info_words_loaded =
  Toploop.use_file base_info_formatter "Library/words.ml";;
Hol_loader.file_loader := base_info_previous_file_loader;;
Format.pp_print_flush base_info_formatter ();;
close_out base_info_output;;
if not base_info_words_loaded then failwith "failed to load Library/words.ml";;

let statement =
  `!b:int64. !o1:bool. !result:int32.
     (&2:int) <= (&(val b):int)
     ==>
     (&(val b):int) <= (&256:int)
     ==>
     ((&(val b):int) = (&(val (word 2:int64)):int) ==> o1 = T)
     ==>
     (o1 = T ==> b = (word 2:int64))
     ==>
     (if o1 = T then
        result = (word 1:int32)
      else
        ?o2:bool.
          (((&(val b):int) = (&(val (word 4:int64)):int) ==> o2 = T) /\
           (o2 = T ==> b = (word 4:int64))) /\
          (if o2 = T then
             result = (word 2:int32)
           else
             ?o3:bool.
               (((&(val b):int) = (&(val (word 8:int64)):int)
                  ==> o3 = T) /\
                (o3 = T ==> b = (word 8:int64))) /\
               (if o3 = T then
                  result = (word 3:int32)
                else
                  ?o4:bool.
                    (((&(val b):int) = (&(val (word 16:int64)):int)
                       ==> o4 = T) /\
                     (o4 = T ==> b = (word 16:int64))) /\
                    (if o4 = T then
                       result = (word 4:int32)
                     else
                       ?o5:bool.
                         (((&(val b):int) = (&(val (word 32:int64)):int)
                            ==> o5 = T) /\
                          (o5 = T ==> b = (word 32:int64))) /\
                         (if o5 = T then
                            result = (word 5:int32)
                          else
                            ?o6:bool.
                              (((&(val b):int) =
                                 (&(val (word 64:int64)):int)
                                 ==> o6 = T) /\
                               (o6 = T ==> b = (word 64:int64))) /\
                              (if o6 = T then
                                 result = (word 6:int32)
                               else
                                 ?o7:bool.
                                   (((&(val b):int) =
                                      (&(val (word 128:int64)):int)
                                      ==> o7 = T) /\
                                    (o7 = T ==> b = (word 128:int64))) /\
                                   (if o7 = T then
                                      result = (word 7:int32)
                                    else
                                      ?o8:bool.
                                        (((&(val b):int) =
                                           (&(val (word 256:int64)):int)
                                           ==> o8 = T) /\
                                         (o8 = T ==>
                                          b = (word 256:int64))) /\
                                        (if o8 = T then
                                           result = (word 8:int32)
                                         else
                                           result = (word 0:int32)))))))))
     ==>
     (&0:int) <= (&(val result):int) /\
     (&(val result):int) <= (&8:int) /\
     (~((&(val result):int) = (&0:int))
      ==> (&2:int) pow (val result) = (&(val b):int)) /\
     ((&(val result):int) = (&0:int)
      ==> !n:int.
            (&0:int) <= n
            ==> ~((&2:int) pow (num_of_int n) = (&(val b):int)))`;;
