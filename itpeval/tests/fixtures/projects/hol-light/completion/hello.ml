let itpeval_target = prove (`p ==> p`, ITAUT_TAC);;
let () =
  if hyp itpeval_target = [] && aconv (concl itpeval_target) `p ==> p`
  then print_endline "ITPEVAL_TARGET_CLOSED"
  else failwith "target shape or hypotheses changed";;
