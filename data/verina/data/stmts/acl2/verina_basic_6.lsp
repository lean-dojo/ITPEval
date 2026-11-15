;; Statement-only formalization of VERINA corpus artifact verina_basic_6,
;; catalog title "minOfThree": a deterministic integer program returns one of
;; three inputs that is less than or equal to all three. This file contains no
;; proof.

(in-package "ACL2")

;; The source precondition is True. The three Int binder domains remain
;; explicit in the final correctness proposition.

(defun verina-basic-6-min-of-three-precond (a b c)
  (declare (ignore a b c))
  t)

;; The proof-valued precondition argument has no computational effect and is
;; erased. The nested tests and their order exactly preserve the source
;; implementation, including its choices when inputs are equal.

(defun verina-basic-6-min-of-three (a b c)
  (if (and
       (<= a b)
       (<= a c))
      a
    (if (and
         (<= b a)
         (<= b c))
        b
      c)))

;; This is the complete source postcondition: the result is a lower bound for
;; all three inputs and is equal to one of them.

(defun verina-basic-6-min-of-three-postcond
    (a b c result)
  (and
   (integerp a)
   (integerp b)
   (integerp c)
   (integerp result)
   (<= result a)
   (<= result b)
   (<= result c)
   (or
    (equal result a)
    (equal result b)
    (equal result c))))

;; This predicate is the unproved final correctness proposition. It quantifies
;; over all three complete Int domains, assumes exactly the source True
;; precondition, and applies the complete postcondition to the exact executable
;; result.

(defun-sk verina-basic-6-min-of-three-spec-satisfied-statement ()
  (forall (a b c)
    (implies
     (and
      (integerp a)
      (integerp b)
      (integerp c)
      (verina-basic-6-min-of-three-precond a b c))
     (verina-basic-6-min-of-three-postcond
      a
      b
      c
      (verina-basic-6-min-of-three a b c)))))

(value-triple :itpeval-statement-checked)
:q
