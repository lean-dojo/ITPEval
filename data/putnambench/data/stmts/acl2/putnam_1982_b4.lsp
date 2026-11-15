;; Statement-only formalization of PutnamBench corpus artifact putnam_1982_b4:
;; two divisibility claims for nonempty finite sets of distinct integers,
;; including the positive-set characterization as an initial interval. This
;; file contains no proof.

(in-package "ACL2")

;; A duplicate-free true list of integers is a bijective representation of a
;; finite integer set after forgetting enumeration order.
(defun putnam-1982-b4-integer-list-p (elements)
  (if (consp elements)
      (and (integerp (car elements))
           (putnam-1982-b4-integer-list-p (cdr elements)))
    (equal elements nil)))

(defun putnam-1982-b4-product (elements)
  (if (consp elements)
      (* (car elements)
         (putnam-1982-b4-product (cdr elements)))
    1))

(defun putnam-1982-b4-shifted-product (elements k)
  (if (consp elements)
      (* (+ (car elements) k)
         (putnam-1982-b4-shifted-product (cdr elements) k))
    1))

;; For nonzero D, the shifted product modulo |D| depends only on k modulo
;; |D|. Thus checking these residues is equivalent to checking every integer
;; k in the source divisibility hypothesis.
(defun putnam-1982-b4-all-residues-divisible-p
    (elements modulus remaining)
  (declare (xargs :measure (nfix remaining)))
  (if (zp remaining)
      t
    (let ((k (- remaining 1)))
      (and
       (equal
        (mod (putnam-1982-b4-shifted-product elements k)
             modulus)
        0)
       (putnam-1982-b4-all-residues-divisible-p
        elements modulus k)))))

(defun putnam-1982-b4-hypothesis-p (elements)
  (let* ((product (putnam-1982-b4-product elements))
         (modulus (abs product)))
    (and
     (consp elements)
     (not (equal product 0))
     (putnam-1982-b4-all-residues-divisible-p
      elements modulus modulus))))

(defun putnam-1982-b4-all-positive-p (elements)
  (if (consp elements)
      (and (< 0 (car elements))
           (putnam-1982-b4-all-positive-p (cdr elements)))
    (equal elements nil)))

;; For a duplicate-free list of length BOUND, containment in [1, BOUND] is
;; equivalent to equality of the represented set with {1, ..., BOUND}.
(defun putnam-1982-b4-initial-interval-p (elements bound)
  (if (consp elements)
      (and
       (integerp (car elements))
       (<= 1 (car elements))
       (<= (car elements) bound)
       (putnam-1982-b4-initial-interval-p
        (cdr elements) bound))
    (equal elements nil)))

(defun putnambench-putnam-1982-b4-statement (elements)
  (implies
   (and
    (true-listp elements)
    (no-duplicatesp-equal elements)
    (putnam-1982-b4-integer-list-p elements)
    (putnam-1982-b4-hypothesis-p elements))
   (and
    (or (member-equal 1 elements)
        (member-equal -1 elements))
    (implies
     (putnam-1982-b4-all-positive-p elements)
     (putnam-1982-b4-initial-interval-p
      elements (len elements))))))

(value-triple :itpeval-statement-checked)
:q
