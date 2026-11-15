;; Statement-only formalization of PutnamBench corpus artifact putnam_1992_b1:
;; the least number of distinct averages of two distinct elements of an
;; n-element real set, for n >= 2, is 2n - 3. This file contains no proof.

(in-package "ACL2")

;; A finite set of reals is represented by rational coordinate vectors in a
;; basis of its finite-dimensional Q-span. Equality of points and equality of
;; pair sums are preserved by this representation. Conversely, any finite
;; family of rational vectors embeds into the reals by evaluating coordinates
;; at a Q-linearly independent real tuple, again preserving exactly those
;; equalities. Finally, division by 2 is injective, so distinct pair sums and
;; distinct pair averages have the same cardinality. Thus this is a
;; bidirectional encoding of arbitrary finite real sets, not a restriction to
;; rational points.

(defun putnam-1992-b1-rational-vector-p (vector width)
  (if (consp vector)
      (and (rationalp (car vector))
           (putnam-1992-b1-rational-vector-p
            (cdr vector) (- width 1)))
    (and (equal vector nil)
         (equal width 0))))

(defun putnam-1992-b1-point-list-p (points width)
  (if (consp points)
      (and (putnam-1992-b1-rational-vector-p
            (car points) width)
           (putnam-1992-b1-point-list-p
            (cdr points) width))
    (equal points nil)))

(defun putnam-1992-b1-vector-add (left right)
  (if (and (consp left) (consp right))
      (cons (+ (car left) (car right))
            (putnam-1992-b1-vector-add
             (cdr left) (cdr right)))
    nil))

(defun putnam-1992-b1-sums-with-first (point remaining)
  (if (consp remaining)
      (cons (putnam-1992-b1-vector-add
             point (car remaining))
            (putnam-1992-b1-sums-with-first
             point (cdr remaining)))
    nil))

(defun putnam-1992-b1-pair-sums (points)
  (if (consp points)
      (append
       (putnam-1992-b1-sums-with-first
        (car points) (cdr points))
       (putnam-1992-b1-pair-sums (cdr points)))
    nil))

(defun putnam-1992-b1-distinct-values (values)
  (if (consp values)
      (if (member-equal (car values) (cdr values))
          (putnam-1992-b1-distinct-values (cdr values))
        (cons (car values)
              (putnam-1992-b1-distinct-values
               (cdr values))))
    nil))

(defun putnam-1992-b1-average-count (points)
  (len
   (putnam-1992-b1-distinct-values
    (putnam-1992-b1-pair-sums points))))

(defun putnam-1992-b1-witness-points (count)
  (declare (xargs :measure (nfix count)))
  (if (zp count)
      nil
    (cons (list (- count 1))
          (putnam-1992-b1-witness-points
           (- count 1)))))

(defun putnam-1992-b1-solution (n)
  (- (* 2 n) 3))

;; The first conjunct is the universal lower bound for every n-element real
;; set. The second constructs the real set {0,...,n-1}, whose distinct
;; pair-average count is 2n-3, and therefore supplies the internal witness
;; that the lower bound is attained.
(defun putnambench-putnam-1992-b1-statement
    (n points width)
  (implies
   (and (natp n)
        (<= 2 n))
   (and
    (implies
     (and
      (natp width)
      (true-listp points)
      (equal (len points) n)
      (putnam-1992-b1-point-list-p points width)
      (no-duplicatesp-equal points))
     (<=
      (putnam-1992-b1-solution n)
      (putnam-1992-b1-average-count points)))
    (equal
     (putnam-1992-b1-average-count
      (putnam-1992-b1-witness-points n))
     (putnam-1992-b1-solution n)))))

(value-triple :itpeval-statement-checked)
:q
