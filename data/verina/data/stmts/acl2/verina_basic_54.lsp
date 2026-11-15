;; Statement-only formalization of VERINA corpus artifact verina_basic_54,
;; catalog title "CanyonSearch": a deterministic two-pointer search of two
;; nonempty nondecreasing integer arrays computes their minimum pairwise
;; absolute difference. This file contains no proof.

(in-package "ACL2")

;; Finite Lean Array Int values are represented bijectively by proper ACL2
;; lists whose elements range over all integers.

(defun verina-basic-54-int-array-p (a)
  (declare (xargs :measure (acl2-count a)))
  (if (consp a)
      (and
       (integerp (car a))
       (verina-basic-54-int-array-p (cdr a)))
    (equal a nil)))

;; These predicates are exactly List.Pairwise (fun x y => x <= y): each head
;; is at most every later entry, recursively for every suffix.

(defun verina-basic-54-head-at-most-all-p
    (head remaining)
  (declare (xargs :measure (acl2-count remaining)))
  (if (consp remaining)
      (and
       (<= head (car remaining))
       (verina-basic-54-head-at-most-all-p
        head
        (cdr remaining)))
    (equal remaining nil)))

(defun verina-basic-54-pairwise-nondecreasing-p (a)
  (declare (xargs :measure (acl2-count a)))
  (if (consp a)
      (and
       (verina-basic-54-head-at-most-all-p
        (car a)
        (cdr a))
       (verina-basic-54-pairwise-nondecreasing-p
        (cdr a)))
    (equal a nil)))

;; Array.size > 0 is nonemptiness in the list representation. Together with
;; the two Pairwise predicates this is exactly the source precondition.

(defun verina-basic-54-canyon-search-precond (a b)
  (and
   (consp a)
   (consp b)
   (verina-basic-54-pairwise-nondecreasing-p a)
   (verina-basic-54-pairwise-nondecreasing-p b)))

;; Array.get! on Array Int returns the indexed entry when it is present and
;; the inhabited integer default zero otherwise.

(defun verina-basic-54-array-read (index a)
  (declare (xargs :measure (nfix index)))
  (if (not (natp index))
      0
    (if (consp a)
        (if (zp index)
            (car a)
          (verina-basic-54-array-read
           (- index 1)
           (cdr a)))
      0)))

;; On an integer this is Lean Int.natAbs, with a natural-number result.

(defun verina-basic-54-int-nat-abs (x)
  (if (< x 0)
      (- x)
    x))

;; The fuel is the source termination measure
;; a.size + b.size - m - n. When both natural indices are in bounds this
;; measure is positive and decreases by one in either recursive branch, so
;; fuel cannot expire before the source base case. The wrapper therefore
;; computes exactly canyonSearchAux on its typed domain.

(defun verina-basic-54-canyon-search-aux-fuel
    (a b m n d fuel)
  (declare (xargs :measure (nfix fuel)))
  (if (or
       (zp fuel)
       (not (natp m))
       (not (natp n))
       (not (natp d)))
      (nfix d)
    (if (and
         (< m (len a))
         (< n (len b)))
        (let* ((a-value
                (verina-basic-54-array-read m a))
               (b-value
                (verina-basic-54-array-read n b))
               (diff
                (verina-basic-54-int-nat-abs
                 (- a-value b-value)))
               (new-d
                (if (< diff d)
                    diff
                  d)))
          (if (<= a-value b-value)
              (verina-basic-54-canyon-search-aux-fuel
               a
               b
               (+ m 1)
               n
               new-d
               (- fuel 1))
            (verina-basic-54-canyon-search-aux-fuel
             a
             b
             m
             (+ n 1)
             new-d
             (- fuel 1))))
      d)))

(defun verina-basic-54-canyon-search-aux
    (a b m n d)
  (verina-basic-54-canyon-search-aux-fuel
   a
   b
   m
   n
   d
   (nfix
    (-
     (+ (len a) (len b))
     (+ m n)))))

;; The proof-valued precondition argument is computationally irrelevant and
;; is erased. The initial branch and the call at indices zero reproduce the
;; complete executable CanyonSearch definition, including get! defaults.

(defun verina-basic-54-canyon-search (a b)
  (let* ((a-zero
          (verina-basic-54-array-read 0 a))
         (b-zero
          (verina-basic-54-array-read 0 b))
         (init
          (if (< a-zero b-zero)
              (verina-basic-54-int-nat-abs
               (- b-zero a-zero))
            (verina-basic-54-int-nat-abs
             (- a-zero b-zero)))))
    (verina-basic-54-canyon-search-aux
     a
     b
     0
     0
     init)))

;; These two recursive predicates are the nested Array.any in the source
;; postcondition: the result must equal the absolute difference of some pair.

(defun verina-basic-54-difference-attained-in-b-p
    (a-value b result)
  (declare (xargs :measure (acl2-count b)))
  (if (consp b)
      (or
       (equal
        result
        (verina-basic-54-int-nat-abs
         (- a-value (car b))))
       (verina-basic-54-difference-attained-in-b-p
        a-value
        (cdr b)
        result))
    nil))

(defun verina-basic-54-difference-attained-p
    (a b result)
  (declare (xargs :measure (acl2-count a)))
  (if (consp a)
      (or
       (verina-basic-54-difference-attained-in-b-p
        (car a)
        b
        result)
       (verina-basic-54-difference-attained-p
        (cdr a)
        b
        result))
    nil))

;; These two predicates are the nested Array.all in the source postcondition:
;; the result is no larger than the absolute difference of every pair.

(defun verina-basic-54-at-most-all-differences-in-b-p
    (a-value b result)
  (declare (xargs :measure (acl2-count b)))
  (if (consp b)
      (and
       (<=
        result
        (verina-basic-54-int-nat-abs
         (- a-value (car b))))
       (verina-basic-54-at-most-all-differences-in-b-p
        a-value
        (cdr b)
        result))
    (equal b nil)))

(defun verina-basic-54-at-most-all-differences-p
    (a b result)
  (declare (xargs :measure (acl2-count a)))
  (if (consp a)
      (and
       (verina-basic-54-at-most-all-differences-in-b-p
        (car a)
        b
        result)
       (verina-basic-54-at-most-all-differences-p
        (cdr a)
        b
        result))
    (equal a nil)))

;; This is the complete source postcondition. The explicit domain predicates
;; preserve the Array Int and Nat binder types; the proof-valued precondition
;; argument is unused and erased.

(defun verina-basic-54-canyon-search-postcond
    (a b result)
  (and
   (verina-basic-54-int-array-p a)
   (verina-basic-54-int-array-p b)
   (natp result)
   (verina-basic-54-difference-attained-p
    a
    b
    result)
   (verina-basic-54-at-most-all-differences-p
    a
    b
    result)))

;; This predicate is the unproved final correctness proposition. It quantifies
;; over all finite integer arrays, assumes exactly the source nonemptiness and
;; sortedness precondition, and applies the complete postcondition to the exact
;; executable result.

(defun-sk
    verina-basic-54-canyon-search-spec-satisfied-statement
    ()
  (forall (a b)
    (implies
     (and
      (verina-basic-54-int-array-p a)
      (verina-basic-54-int-array-p b)
      (verina-basic-54-canyon-search-precond
       a
       b))
     (verina-basic-54-canyon-search-postcond
      a
      b
      (verina-basic-54-canyon-search a b)))))

(value-triple :itpeval-statement-checked)
:q
