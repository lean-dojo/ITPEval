;; Statement-only formalization of VERINA corpus artifact verina_basic_75,
;; catalog title "minArray": a deterministic nonempty integer-array scan
;; returns an array element that is less than or equal to every array element.
;; This file contains no proof.

(in-package "ACL2")

;; Finite Lean Array Int values are represented bijectively by proper ACL2
;; lists whose elements range over all integers.

(defun verina-basic-75-int-array-p (a)
  (declare (xargs :measure (acl2-count a)))
  (if (consp a)
      (and
       (integerp (car a))
       (verina-basic-75-int-array-p (cdr a)))
    (equal a nil)))

;; Array.get! at a natural index returns the indexed integer when it is in
;; bounds and the inhabited Int default zero otherwise.

(defun verina-basic-75-get-default-zero (a index)
  (if (and
       (natp index)
       (< index (len a)))
      (nth index a)
    0))

;; The source precondition a.size > 0 is exactly list nonemptiness.

(defun verina-basic-75-min-array-precond (a)
  (< 0 (len a)))

;; This is the source loop recursion. INDEX identifies the next array entry
;; to inspect. When it is in bounds, NEW-MIN is the lesser of the carried
;; value and a[index], and the recursion advances by one; otherwise it returns
;; the carried value.

(defun verina-basic-75-loop (a index current-min)
  (declare
   (xargs
    :measure
    (nfix (- (len a) (nfix index)))))
  (if (and
       (natp index)
       (< index (len a)))
      (let* ((entry
              (verina-basic-75-get-default-zero
               a
               index))
             (new-min
              (if (> current-min entry)
                  entry
                current-min)))
        (verina-basic-75-loop
         a
         (+ index 1)
         new-min))
    current-min))

;; The proof-valued precondition argument is computationally irrelevant and is
;; erased. This preserves the exact source call loop a 1 a[0]!.

(defun verina-basic-75-min-array (a)
  (verina-basic-75-loop
   a
   1
   (verina-basic-75-get-default-zero a 0)))

;; This preserves the first source postcondition conjunct and its universal
;; Nat index binder: RESULT is at most every in-bounds array entry.

(defun-sk verina-basic-75-lower-bound-at-every-index-p
    (a result)
  (forall (i)
    (implies
     (and
      (natp i)
      (< i (len a)))
     (<=
      result
      (verina-basic-75-get-default-zero a i)))))

;; This preserves the second source postcondition conjunct and its existential
;; Nat index binder: RESULT equals at least one in-bounds array entry.

(defun-sk verina-basic-75-result-occurs-p (a result)
  (exists (i)
    (and
     (natp i)
     (< i (len a))
     (equal
      result
      (verina-basic-75-get-default-zero a i)))))

;; This is the complete source postcondition. Its proof-valued precondition
;; argument is unused in the Lean body and is erased here.

(defun verina-basic-75-min-array-postcond (a result)
  (and
   (verina-basic-75-int-array-p a)
   (integerp result)
   (verina-basic-75-lower-bound-at-every-index-p
    a
    result)
   (verina-basic-75-result-occurs-p a result)))

;; This predicate is the unproved final correctness proposition. It quantifies
;; over the complete Array Int domain, assumes exactly the source nonempty
;; precondition, and applies the complete postcondition to the exact executable
;; result.

(defun-sk verina-basic-75-min-array-spec-satisfied-statement ()
  (forall (a)
    (implies
     (and
      (verina-basic-75-int-array-p a)
      (verina-basic-75-min-array-precond a))
     (verina-basic-75-min-array-postcond
      a
      (verina-basic-75-min-array a)))))

(value-triple :itpeval-statement-checked)
:q
