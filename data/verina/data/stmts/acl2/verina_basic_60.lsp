;; Statement-only formalization of VERINA corpus artifact verina_basic_60,
;; catalog title "FindEvenNumbers": a deterministic integer-array program
;; scans left to right and returns exactly the even entries in input order.
;; This file contains no proof.

(in-package "ACL2")

;; Finite Lean Array Int values are represented bijectively by proper ACL2
;; lists whose elements range over all integers.

(defun verina-basic-60-int-array-p (arr)
  (declare (xargs :measure (acl2-count arr)))
  (if (consp arr)
      (and
       (integerp (car arr))
       (verina-basic-60-int-array-p (cdr arr)))
    (equal arr nil)))

;; With positive divisor two, ACL2 MOD and Lean Int.emod agree on every
;; integer, so this is exactly the source Boolean helper isEven.

(defun verina-basic-60-is-even (n)
  (equal (mod n 2) 0))

;; The source precondition is True. The Array Int binder domain remains
;; explicit in the final correctness proposition.

(defun verina-basic-60-find-even-numbers-precond (arr)
  (declare (ignore arr))
  t)

;; This is Array.getD with integer default zero. The final proposition invokes
;; it only at natural indices, as required by the source loop's Nat index.

(defun verina-basic-60-array-read (index arr)
  (declare (xargs :measure (nfix index)))
  (if (not (natp index))
      0
    (if (consp arr)
        (if (zp index)
            (car arr)
          (verina-basic-60-array-read
           (- index 1)
           (cdr arr)))
      0)))

;; This is exact natural-number suffix removal. It supplies the source loop's
;; unprocessed array suffix beginning at INDEX.

(defun verina-basic-60-drop (count arr)
  (declare (xargs :measure (nfix count)))
  (if (and
       (natp count)
       (< 0 count)
       (consp arr))
      (verina-basic-60-drop
       (- count 1)
       (cdr arr))
    arr))

;; REMAINING is the suffix of ARR beginning at INDEX. Its nonemptiness is
;; exactly the source guard INDEX < ARR.size. Each iteration reads ARR with
;; getD, tests isEven, and represents Array.push by appending to ACC.

(defun verina-basic-60-find-even-numbers-loop-scan
    (arr index acc remaining)
  (declare (xargs :measure (acl2-count remaining)))
  (if (consp remaining)
      (let ((value
             (verina-basic-60-array-read index arr)))
        (verina-basic-60-find-even-numbers-loop-scan
         arr
         (+ index 1)
         (if (verina-basic-60-is-even value)
             (append acc (cons value nil))
           acc)
         (cdr remaining)))
    acc))

;; This preserves the complete source-local loop signature and computation on
;; its typed Nat index and Array Int accumulator.

(defun verina-basic-60-find-even-numbers-loop
    (arr index acc)
  (verina-basic-60-find-even-numbers-loop-scan
   arr
   index
   acc
   (verina-basic-60-drop index arr)))

;; Array.mkEmpty 0 is the empty list representation. The proof-valued True
;; precondition argument is computationally irrelevant and is erased.

(defun verina-basic-60-find-even-numbers (arr)
  (verina-basic-60-find-even-numbers-loop
   arr
   0
   nil))

;; This recursion is result.all isEven.

(defun verina-basic-60-all-even-p (result)
  (declare (xargs :measure (acl2-count result)))
  (if (consp result)
      (and
       (verina-basic-60-is-even (car result))
       (verina-basic-60-all-even-p (cdr result)))
    (equal result nil)))

;; This greedy equality scan is equivalent to Lean List.Sublist: RESULT can be
;; obtained from ARR by deleting entries without changing the retained order.

(defun verina-basic-60-sublist-p (result arr)
  (declare (xargs :measure (acl2-count arr)))
  (if (consp result)
      (if (consp arr)
          (if (equal (car result) (car arr))
              (verina-basic-60-sublist-p
               (cdr result)
               (cdr arr))
            (verina-basic-60-sublist-p
             result
             (cdr arr)))
        nil)
    (equal result nil)))

;; This is arr.toList.countP isEven.

(defun verina-basic-60-count-even (arr)
  (declare (xargs :measure (acl2-count arr)))
  (if (consp arr)
      (+
       (if (verina-basic-60-is-even (car arr)) 1 0)
       (verina-basic-60-count-even (cdr arr)))
    0))

;; This is the complete source postcondition. The proof-valued precondition
;; argument is unused and therefore erased.

(defun verina-basic-60-find-even-numbers-postcond
    (arr result)
  (and
   (verina-basic-60-int-array-p arr)
   (verina-basic-60-int-array-p result)
   (verina-basic-60-all-even-p result)
   (verina-basic-60-sublist-p result arr)
   (equal
    (len result)
    (verina-basic-60-count-even arr))))

;; This predicate is the unproved final correctness proposition. It quantifies
;; over every finite integer array, assumes exactly the source True
;; precondition, and applies the complete postcondition to the exact executable
;; result.

(defun-sk
    verina-basic-60-find-even-numbers-spec-satisfied-statement
    ()
  (forall (arr)
    (implies
     (and
      (verina-basic-60-int-array-p arr)
      (verina-basic-60-find-even-numbers-precond arr))
     (verina-basic-60-find-even-numbers-postcond
      arr
      (verina-basic-60-find-even-numbers arr)))))

(value-triple :itpeval-statement-checked)
:q
