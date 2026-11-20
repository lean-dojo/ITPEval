open HolKernel Parse boolLib bossLib;
val _ = new_theory "hello";
val itpeval_target = store_thm ("itpeval_target", ``p ==> p``, PROVE_TAC []);
val _ = if null (hyp itpeval_target) andalso aconv (concl itpeval_target) ``p ==> p``
        then let val out = TextIO.openOut "itpeval-target-witness"
             in TextIO.output (out, "itpeval_target"); TextIO.closeOut out end else raise Fail "target shape or hypotheses changed";
val _ = export_theory ();
