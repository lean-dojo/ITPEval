;; Statement-only formalization of VERINA corpus artifact verina_basic_74,
;; catalog title "maxArray": a deterministic nonempty integer-array scan
;; returns an array element that is greater than or equal to every array
;; element. This file contains no proof.

(in-package "ACL2")

;; Finite Lean Array Int values are represented bijectively by proper ACL2
;; lists whose elements range over all integers.

(defun verina-basic-74-int-array-p (a)
  (declare (xargs :measure (acl2-count a)))
  (if (consp a)
      (and
       (integerp (car a))
       (verina-basic-74-int-array-p (cdr a)))
    (equal a nil)))

;; Array.get! at a natural index returns the indexed integer when it is in
;; bounds and the inhabited Int default zero otherwise.

(defun verina-basic-74-get-default-zero (a index)
  (if (and
       (natp index)
       (< index (len a)))
      (nth index a)
    0))

;; The source precondition a.size > 0 is exactly list nonemptiness.

(defun verina-basic-74-max-array-precond (a)
  (< 0 (len a)))

;; This is the source maxArray_aux recursion. INDEX identifies the next array
;; entry to inspect. When it is in bounds, NEW-CURRENT is the larger of the
;; carried value and a[index], and the recursion advances by one; otherwise it
;; returns the carried value.

(defun verina-basic-74-max-array-aux (a index current)
  (declare
   (xargs
    :measure
    (nfix (- (len a) (nfix index)))))
  (if (and
       (natp index)
       (< index (len a)))
      (let* ((entry
              (verina-basic-74-get-default-zero
               a
               index))
             (new-current
              (if (> current entry)
                  current
                entry)))
        (verina-basic-74-max-array-aux
         a
         (+ index 1)
         new-current))
    current))

;; The proof-valued precondition argument is computationally irrelevant and is
;; erased. This preserves the exact source call maxArray_aux a 1 a[0]!.

(defun verina-basic-74-max-array (a)
  (verina-basic-74-max-array-aux
   a
   1
   (verina-basic-74-get-default-zero a 0)))

;; This preserves the first source postcondition conjunct and its universal
;; Nat index binder: RESULT is at least every in-bounds array entry.

(defun-sk verina-basic-74-upper-bound-at-every-index-p
    (a result)
  (forall (k)
    (implies
     (and
      (natp k)
      (< k (len a)))
     (>=
      result
      (verina-basic-74-get-default-zero a k)))))

;; This preserves the second source postcondition conjunct and its existential
;; Nat index binder: RESULT equals at least one in-bounds array entry.

(defun-sk verina-basic-74-result-occurs-p (a result)
  (exists (k)
    (and
     (natp k)
     (< k (len a))
     (equal
      result
      (verina-basic-74-get-default-zero a k)))))

;; This is the complete source postcondition. Its proof-valued precondition
;; argument is unused in the Lean body and is erased here.

(defun verina-basic-74-max-array-postcond (a result)
  (and
   (verina-basic-74-int-array-p a)
   (integerp result)
   (verina-basic-74-upper-bound-at-every-index-p
    a
    result)
   (verina-basic-74-result-occurs-p a result)))

;; This predicate is the unproved final correctness proposition. It quantifies
;; over the complete Array Int domain, assumes exactly the source nonempty
;; precondition, and applies the complete postcondition to the exact executable
;; result.

(defun-sk verina-basic-74-max-array-spec-satisfied-statement ()
  (forall (a)
    (implies
     (and
      (verina-basic-74-int-array-p a)
      (verina-basic-74-max-array-precond a))
     (verina-basic-74-max-array-postcond
      a
      (verina-basic-74-max-array a)))))

(value-triple :itpeval-statement-checked)
:q
