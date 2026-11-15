;; Statement-only formalization of VERINA corpus artifact verina_basic_26,
;; catalog title "isEven": a deterministic integer program returns true
;; exactly when its input has remainder zero modulo two. This file contains
;; no proof.

(in-package "ACL2")

;; The source precondition is True. The Int binder domain remains explicit in
;; the final correctness statement.

(defun verina-basic-26-is-even-precond (n)
  (declare (ignore n))
  t)

;; With positive divisor two, ACL2 MOD and Lean Int.emod agree on every
;; integer. EQUAL returns exactly ACL2's Boolean values T or NIL, so this
;; preserves the source implementation n % 2 == 0. The proof-valued
;; precondition argument is computationally irrelevant and is erased.

(defun verina-basic-26-is-even (n)
  (equal (mod n 2) 0))

(defun verina-basic-26-bool-p (result)
  (or
   (equal result t)
   (equal result nil)))

;; This preserves both source postcondition implications: a true result
;; implies zero remainder, while a false result implies nonzero remainder.

(defun verina-basic-26-is-even-postcond (n result)
  (and
   (integerp n)
   (verina-basic-26-bool-p result)
   (implies
    result
    (equal (mod n 2) 0))
   (implies
    (not result)
    (not (equal (mod n 2) 0)))))

;; This predicate is the unproved final correctness proposition. It quantifies
;; over the full integer domain, applies the True precondition, and connects
;; the complete postcondition to the exact executable result.

(defun-sk verina-basic-26-is-even-spec-satisfied-statement ()
  (forall (n)
    (implies
     (and
      (integerp n)
      (verina-basic-26-is-even-precond n))
     (verina-basic-26-is-even-postcond
      n
      (verina-basic-26-is-even n)))))

(value-triple :itpeval-statement-checked)
:q
