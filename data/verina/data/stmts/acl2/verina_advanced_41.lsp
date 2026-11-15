;; Statement-only formalization of VERINA corpus artifact verina_advanced_41,
;; "maxOfThree": the deterministic integer program returns one of three inputs
;; and a value at least as large as each input. This file contains no proof.

(in-package "ACL2")

;; The source precondition is True. The Int binder domains are explicit in the
;; final correctness statement.

(defun verina-advanced-41-max-of-three-precond (a b c)
  (declare (ignore a b c))
  t)

;; This preserves the source's ordered conditional computation: choose a when
;; it is at least b and c, otherwise choose b when it is at least a and c, and
;; otherwise choose c. The proof-valued precondition argument is erased because
;; it has no computational effect.

(defun verina-advanced-41-max-of-three (a b c)
  (if (and (>= a b)
           (>= a c))
      a
    (if (and (>= b a)
             (>= b c))
        b
      c)))

(defun verina-advanced-41-max-of-three-postcond
    (a b c result)
  (and
   (integerp a)
   (integerp b)
   (integerp c)
   (integerp result)
   (>= result a)
   (>= result b)
   (>= result c)
   (or
    (equal result a)
    (equal result b)
    (equal result c))))

;; This predicate is the unproved final correctness proposition. Its antecedent
;; preserves the three Int binders and True precondition; its conclusion applies
;; the complete postcondition to the exact executable result.

(defun verina-advanced-41-max-of-three-spec-satisfied-statement
    (a b c)
  (implies
   (and
    (integerp a)
    (integerp b)
    (integerp c)
    (verina-advanced-41-max-of-three-precond a b c))
   (verina-advanced-41-max-of-three-postcond
    a
    b
    c
    (verina-advanced-41-max-of-three a b c))))

(value-triple :itpeval-statement-checked)
:q
