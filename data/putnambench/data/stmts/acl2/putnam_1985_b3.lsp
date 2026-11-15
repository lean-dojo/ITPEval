;; Statement-only formalization of PutnamBench corpus artifact putnam_1985_b3:
;; every positive-integer array in which each positive integer occurs exactly
;; eight times has an entry a(m,n) greater than m*n at positive indices. This
;; file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; DEFSTUB introduces an arbitrary binary function conservatively. ACL2
;; functional instantiation makes the theorem generic over every array
;; satisfying the hypotheses, without APPLY$'s tame-function restriction.

(defstub putnam-1985-b3-array (m n) t)

(defun putnam-1985-b3-array-value (m n)
  (putnam-1985-b3-array m n))

(defun-sk putnam-1985-b3-positive-array-p ()
  (forall (m n)
    (implies
     (and
      (natp m)
      (natp n))
     (and
      (natp (putnam-1985-b3-array-value m n))
      (< 0 (putnam-1985-b3-array-value m n))))))

;; A duplicate-free list of length eight enumerates a fiber exactly when each
;; listed positive pair maps to K and every positive pair mapping to K occurs
;; in the list. This is equivalent to cardinality eight without bounding the
;; index domain or exposing the enumeration as a statement parameter.

(defun putnam-1985-b3-positive-pair-p (pair)
  (and
   (consp pair)
   (posp (car pair))
   (posp (cdr pair))))

(defun putnam-1985-b3-pairs-map-to-p (k pairs)
  (if (consp pairs)
      (and
       (putnam-1985-b3-positive-pair-p (car pairs))
       (equal
        (putnam-1985-b3-array-value
         (car (car pairs)) (cdr (car pairs)))
        k)
       (putnam-1985-b3-pairs-map-to-p
        k (cdr pairs)))
    (equal pairs nil)))

(defun-sk putnam-1985-b3-all-preimages-listed-p
    (k pairs)
  (forall (m n)
    (implies
     (and
      (posp m)
      (posp n)
     (equal
       (putnam-1985-b3-array-value m n)
       k))
     (member-equal (cons m n) pairs))))

(defun putnam-1985-b3-eight-preimage-witnesses-p
    (k pairs)
  (and
   (true-listp pairs)
   (equal (len pairs) 8)
   (no-duplicatesp-equal pairs)
   (putnam-1985-b3-pairs-map-to-p k pairs)
   (putnam-1985-b3-all-preimages-listed-p
    k pairs)))

(defun-sk putnam-1985-b3-exactly-eight-preimages-p
    (k)
  (exists (pairs)
    (putnam-1985-b3-eight-preimage-witnesses-p
     k pairs)))

(defun-sk putnam-1985-b3-each-positive-occurs-eight-times-p
    ()
  (forall (k)
    (implies
     (posp k)
     (putnam-1985-b3-exactly-eight-preimages-p
      k))))

(defun-sk putnam-1985-b3-large-entry-exists-p ()
  (exists (m n)
    (and
     (posp m)
     (posp n)
     (<
      (* m n)
      (putnam-1985-b3-array-value m n)))))

(defun putnambench-putnam-1985-b3-statement ()
  (implies
   (and
    (putnam-1985-b3-positive-array-p)
    (putnam-1985-b3-each-positive-occurs-eight-times-p))
   (putnam-1985-b3-large-entry-exists-p)))

(value-triple :itpeval-statement-checked)
:q
