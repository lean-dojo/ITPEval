;; Statement-only formalization of VERINA corpus artifact verina_basic_30,
;; catalog title "elementWiseModulo": a deterministic integer-array program
;; computes the Euclidean remainder of each first-array entry by the
;; corresponding nonzero second-array entry. This file contains no proof.

(in-package "ACL2")

;; Finite Lean Array Int values are represented bijectively by proper ACL2
;; lists whose elements range over all integers.

(defun verina-basic-30-int-array-p (array)
  (declare (xargs :measure (acl2-count array)))
  (if (consp array)
      (and
       (integerp (car array))
       (verina-basic-30-int-array-p (cdr array)))
    (equal array nil)))

;; This structural scan is the source universal condition that every entry of
;; the second array is nonzero.

(defun verina-basic-30-all-nonzero-p (array)
  (declare (xargs :measure (acl2-count array)))
  (if (consp array)
      (and
       (not (equal (car array) 0))
       (verina-basic-30-all-nonzero-p (cdr array)))
    (equal array nil)))

;; The source precondition requires equal positive lengths and a nonzero
;; divisor at every index. The Array Int domains remain explicit in the final
;; correctness proposition.

(defun verina-basic-30-element-wise-modulo-precond (a b)
  (and
   (equal (len a) (len b))
   (< 0 (len a))
   (verina-basic-30-all-nonzero-p b)))

;; Lean Int modulo is Euclidean: for a nonzero divisor D its result is
;; nonnegative and less than |D|, independently of D's sign. ACL2 MOD agrees
;; when given the positive magnitude. The zero branch also preserves Lean's
;; total definition, although the source precondition excludes it.

(defun verina-basic-30-divisor-magnitude (divisor)
  (if (< divisor 0)
      (- divisor)
    divisor))

(defun verina-basic-30-int-emod (dividend divisor)
  (if (equal divisor 0)
      dividend
    (mod
     dividend
     (verina-basic-30-divisor-magnitude divisor))))

;; This structural recursion is exactly Array.mapIdx
;; (fun i x => x % b[i]!) on inputs satisfying the equal-length precondition:
;; it traverses both arrays in index order and produces one exact remainder
;; for every entry of A. The proof-valued precondition argument is erased.

(defun verina-basic-30-element-wise-modulo (a b)
  (declare (xargs :measure (acl2-count a)))
  (if (and
       (consp a)
       (consp b))
      (cons
       (verina-basic-30-int-emod
        (car a)
        (car b))
       (verina-basic-30-element-wise-modulo
        (cdr a)
        (cdr b)))
    nil))

;; Under the postcondition's result-length equation and the precondition's
;; equal input lengths, this aligned scan is exactly the bounded source
;; universal quantifier over all result indices.

(defun verina-basic-30-pointwise-modulo-p (a b result)
  (declare (xargs :measure (acl2-count result)))
  (if (consp result)
      (and
       (consp a)
       (consp b)
       (equal
        (car result)
        (verina-basic-30-int-emod
         (car a)
         (car b)))
       (verina-basic-30-pointwise-modulo-p
        (cdr a)
        (cdr b)
        (cdr result)))
    (equal result nil)))

;; This is the complete source postcondition: the result is an Array Int of
;; the same size as A, and every result entry is the corresponding Euclidean
;; integer remainder.

(defun verina-basic-30-element-wise-modulo-postcond
    (a b result)
  (and
   (verina-basic-30-int-array-p a)
   (verina-basic-30-int-array-p b)
   (verina-basic-30-int-array-p result)
   (equal (len result) (len a))
   (verina-basic-30-pointwise-modulo-p
    a
    b
    result)))

;; This predicate is the unproved final correctness proposition. It quantifies
;; over both complete Array Int domains, applies the full source precondition,
;; and connects the complete postcondition to the exact executable result.

(defun-sk
    verina-basic-30-element-wise-modulo-spec-satisfied-statement ()
  (forall (a b)
    (implies
     (and
      (verina-basic-30-int-array-p a)
      (verina-basic-30-int-array-p b)
      (verina-basic-30-element-wise-modulo-precond
       a
       b))
     (verina-basic-30-element-wise-modulo-postcond
      a
      b
      (verina-basic-30-element-wise-modulo
       a
       b)))))

(value-triple :itpeval-statement-checked)
:q
