(*
  Statement-only formalization of PutnamBench corpus artifact putnam_2008_a6:
  a universal logarithmic-length sequence in every finite nontrivial group
  whose ordered subsequence products represent every group element. This file
  contains no proof.
*)

let transc_output = open_out "/dev/null";;
let transc_formatter = Format.formatter_of_out_channel transc_output;;
let previous_file_loader = !Hol_loader.file_loader;;
let previous_verbose = !verbose;;
verbose := false;;
Hol_loader.file_loader := (fun path -> Toploop.use_file transc_formatter path);;
let transc_loaded = Toploop.use_file transc_formatter "Library/transc.ml";;
Hol_loader.file_loader := previous_file_loader;;
verbose := previous_verbose;;
Format.pp_print_flush transc_formatter ();;
close_out transc_output;;
if not transc_loaded then failwith "failed to load Library/transc.ml";;

let statement =
  `let is_group =
     \(carrier:A->bool) (gmul:A->A->A) (ginv:A->A) (gid:A).
       gid IN carrier /\
       (!x:A. x IN carrier ==> ginv x IN carrier) /\
       (!x y:A.
          x IN carrier /\ y IN carrier
          ==> gmul x y IN carrier) /\
       (!x y z:A.
          x IN carrier /\ y IN carrier /\ z IN carrier
          ==> gmul x (gmul y z) = gmul (gmul x y) z) /\
       (!x:A.
          x IN carrier
          ==> gmul gid x = x /\ gmul x gid = x) /\
       (!x:A.
          x IN carrier
          ==> gmul (ginv x) x = gid /\ gmul x (ginv x) = gid) in
   let is_subsequence =
     \(t:A list) (s:A list).
       ?pick:num->num.
         (!i:num.
            i < LENGTH t
            ==> pick i < LENGTH s /\ EL i t = EL (pick i) s) /\
         (!i j:num.
            i < j /\ j < LENGTH t
            ==> pick i < pick j) in
   ?c:real.
     &0 < c /\
     !carrier:A->bool.
       !gmul:A->A->A.
         !ginv:A->A.
           !gid:A.
             is_group carrier gmul ginv gid /\
             FINITE carrier /\
             1 < CARD carrier
             ==>
             ?s:A list.
               (!x:A. MEM x s ==> x IN carrier) /\
               &(LENGTH s) <= c * ln (&(CARD carrier)) /\
               !g:A.
                 g IN carrier
                 ==> ?t:A list.
                       is_subsequence t s /\
                       ITLIST gmul t gid = g`;;
