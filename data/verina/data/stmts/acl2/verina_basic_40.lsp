;; Statement-only formalization of VERINA corpus artifact verina_basic_40,
;; catalog title "secondSmallest": a deterministic integer-array scan returns
;; the least value strictly greater than the array minimum, under the
;; assumption that two distinct values occur. This file contains no proof.

(in-package "ACL2")

;; Finite Lean Array Int values are represented bijectively by proper ACL2
;; lists whose elements range over all integers.

(defun verina-basic-40-int-array-p (s)
  (declare (xargs :measure (acl2-count s)))
  (if (consp s)
      (and
       (integerp (car s))
       (verina-basic-40-int-array-p (cdr s)))
    (equal s nil)))

;; Array.get! at a natural index returns the indexed integer when it is in
;; bounds and the inhabited Int default zero otherwise.

(defun verina-basic-40-get-default-zero (s index)
  (if (and
       (natp index)
       (< index (len s)))
      (nth index s)
    0))

;; This is the source precondition's bounded existential over two distinct
;; array entries, with both Nat index domains explicit.

(defun-sk verina-basic-40-has-two-distinct-values-p (s)
  (exists (i j)
    (and
     (natp i)
     (natp j)
     (< i (len s))
     (< j (len s))
     (not
      (equal
       (verina-basic-40-get-default-zero s i)
       (verina-basic-40-get-default-zero s j))))))

(defun verina-basic-40-second-smallest-precond (s)
  (and
   (< 1 (len s))
   (verina-basic-40-has-two-distinct-values-p s)))

;; Option Nat is represented by :none or the tagged dotted pair
;; (:some . index), preserving absence distinctly from every natural index.

(defun verina-basic-40-option-nat-p (option)
  (or
   (equal option :none)
   (and
    (consp option)
    (equal (car option) :some)
    (natp (cdr option)))))

;; This recursion preserves the source state exactly: I is the next index,
;; MIN-IDX points to the smallest value seen, and SECOND-IDX is absent until a
;; distinct larger value has been seen and thereafter points to the smallest
;; such value. The terminal absent branch is Lean's panic! value at Int, namely
;; the inhabited default zero.

(defun verina-basic-40-second-smallest-aux
    (s i min-idx second-idx)
  (declare
   (xargs
    :measure
    (nfix (- (len s) (nfix i)))))
  (if (not (natp i))
      0
    (if (<= (len s) i)
        (if (equal second-idx :none)
            0
          (verina-basic-40-get-default-zero
           s
           (cdr second-idx)))
      (let* ((x
              (verina-basic-40-get-default-zero s i))
             (m
              (verina-basic-40-get-default-zero
               s
               min-idx)))
        (if (equal second-idx :none)
            (if (< x m)
                (verina-basic-40-second-smallest-aux
                 s
                 (+ i 1)
                 i
                 (cons :some min-idx))
              (if (> x m)
                  (verina-basic-40-second-smallest-aux
                   s
                   (+ i 1)
                   min-idx
                   (cons :some i))
                (verina-basic-40-second-smallest-aux
                 s
                 (+ i 1)
                 min-idx
                 :none)))
          (let* ((si (cdr second-idx))
                 (second-min
                  (verina-basic-40-get-default-zero
                   s
                   si)))
            (if (< x m)
                (verina-basic-40-second-smallest-aux
                 s
                 (+ i 1)
                 i
                 (cons :some min-idx))
              (if (and
                   (< x second-min)
                   (> x m))
                  (verina-basic-40-second-smallest-aux
                   s
                   (+ i 1)
                   min-idx
                   (cons :some i))
                (verina-basic-40-second-smallest-aux
                 s
                 (+ i 1)
                 min-idx
                 (cons :some si))))))))))

;; The proof-valued precondition argument has no computational effect and is
;; erased. These initial values are exactly the source call
;; secondSmallestAux s 1 0 none.

(defun verina-basic-40-second-smallest (s)
  (verina-basic-40-second-smallest-aux
   s
   1
   0
   :none))

;; This is the first existential conjunct of the source postcondition: RESULT
;; occurs at an in-bounds natural index.

(defun-sk verina-basic-40-result-occurs-p (s result)
  (exists (i)
    (and
     (natp i)
     (< i (len s))
     (equal
      (verina-basic-40-get-default-zero s i)
      result))))

;; For a fixed lower witness J, this preserves the source universal Nat
;; binder: every array value distinct from s[J] is at least RESULT.

(defun-sk
    verina-basic-40-all-values-distinct-from-witness-at-least-p
    (s result j)
  (forall (k)
    (implies
     (and
      (natp k)
      (< k (len s)))
     (implies
      (not
       (equal
        (verina-basic-40-get-default-zero s k)
        (verina-basic-40-get-default-zero s j)))
      (>=
       (verina-basic-40-get-default-zero s k)
       result)))))

;; This is the second existential conjunct: an in-bounds entry is strictly
;; below RESULT, and every value different from that witness is no smaller
;; than RESULT.

(defun-sk verina-basic-40-lower-witness-p (s result)
  (exists (j)
    (and
     (natp j)
     (< j (len s))
     (<
      (verina-basic-40-get-default-zero s j)
      result)
     (verina-basic-40-all-values-distinct-from-witness-at-least-p
      s
      result
      j))))

;; This is the complete source postcondition. Its proof-valued precondition
;; argument is unused in the Lean body and is erased here.

(defun verina-basic-40-second-smallest-postcond
    (s result)
  (and
   (verina-basic-40-int-array-p s)
   (integerp result)
   (verina-basic-40-result-occurs-p s result)
   (verina-basic-40-lower-witness-p s result)))

;; This predicate is the unproved final correctness proposition. It quantifies
;; over the complete Array Int domain, applies the full source precondition,
;; and connects the complete postcondition to the exact executable result.

(defun-sk
    verina-basic-40-second-smallest-spec-satisfied-statement
    ()
  (forall (s)
    (implies
     (and
      (verina-basic-40-int-array-p s)
      (verina-basic-40-second-smallest-precond s))
     (verina-basic-40-second-smallest-postcond
      s
      (verina-basic-40-second-smallest s)))))

(value-triple :itpeval-statement-checked)
:q
