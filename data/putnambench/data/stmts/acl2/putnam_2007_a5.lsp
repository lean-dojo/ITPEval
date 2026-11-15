;; Statement-only formalization of PutnamBench corpus artifact putnam_2007_a5:
;; in a finite group, the number of elements of prime order p is either zero
;; or congruent to -1 modulo p. This file contains no proof.

(in-package "ACL2")

;; A duplicate-free carrier and a complete multiplication table represent an
;; arbitrary finite group up to relabeling. The group predicate checks the
;; axioms on every carrier element and keeps inverse witnesses internal.

(defun putnam-2007-a5-set-list-p (xs)
  (if (consp xs)
      (and
       (not (member-equal (car xs) (cdr xs)))
       (putnam-2007-a5-set-list-p (cdr xs)))
    (equal xs nil)))

(defun putnam-2007-a5-binary-table-p (table carrier)
  (if (consp table)
      (let* ((entry (car table))
             (arguments (car entry))
             (value (cdr entry)))
        (and
         (consp entry)
         (true-listp arguments)
         (equal (len arguments) 2)
         (member-equal (car arguments) carrier)
         (member-equal (cadr arguments) carrier)
         (member-equal value carrier)
         (not (assoc-equal arguments (cdr table)))
         (putnam-2007-a5-binary-table-p
          (cdr table) carrier)))
    (equal table nil)))

(defun putnam-2007-a5-multiply (left right table)
  (cdr (assoc-equal (list left right) table)))

(defun putnam-2007-a5-associative-z-p
    (zs x y table)
  (if (endp zs)
      t
    (let* ((z (car zs))
           (xy (putnam-2007-a5-multiply x y table))
           (yz (putnam-2007-a5-multiply y z table)))
      (and
       (equal
        (putnam-2007-a5-multiply xy z table)
        (putnam-2007-a5-multiply x yz table))
       (putnam-2007-a5-associative-z-p
        (cdr zs) x y table)))))

(defun putnam-2007-a5-group-y-axioms-p
    (ys carrier x table)
  (if (endp ys)
      t
    (let ((y (car ys)))
      (and
       (assoc-equal (list x y) table)
       (putnam-2007-a5-associative-z-p
        carrier x y table)
       (putnam-2007-a5-group-y-axioms-p
        (cdr ys) carrier x table)))))

(defun putnam-2007-a5-inverse-exists-p
    (x candidates one table)
  (if (endp candidates)
      nil
    (or
     (and
      (equal
       (putnam-2007-a5-multiply x (car candidates) table)
       one)
      (equal
       (putnam-2007-a5-multiply (car candidates) x table)
       one))
     (putnam-2007-a5-inverse-exists-p
      x (cdr candidates) one table))))

(defun putnam-2007-a5-group-x-axioms-p
    (xs carrier one table)
  (if (endp xs)
      t
    (let ((x (car xs)))
      (and
       (equal
        (putnam-2007-a5-multiply one x table)
        x)
       (equal
        (putnam-2007-a5-multiply x one table)
        x)
       (putnam-2007-a5-inverse-exists-p
        x carrier one table)
       (putnam-2007-a5-group-y-axioms-p
        carrier carrier x table)
       (putnam-2007-a5-group-x-axioms-p
        (cdr xs) carrier one table)))))

(defun putnam-2007-a5-finite-group-p
    (carrier one table)
  (and
   (putnam-2007-a5-set-list-p carrier)
   (consp carrier)
   (member-equal one carrier)
   (putnam-2007-a5-binary-table-p table carrier)
   (putnam-2007-a5-group-x-axioms-p
    carrier carrier one table)))

(defun putnam-2007-a5-power
    (element exponent one table)
  (declare (xargs :measure (nfix exponent)))
  (if (zp exponent)
      one
    (putnam-2007-a5-multiply
     element
     (putnam-2007-a5-power
      element (- exponent 1) one table)
     table)))

;; In a finite group, every element order is at most the carrier cardinality.
;; Searching exponents 1 through |G| therefore returns the exact order rather
;; than a bounded approximation.

(defun putnam-2007-a5-order-search
    (element exponent remaining one table)
  (declare (xargs :measure (nfix remaining)))
  (if (zp remaining)
      0
    (if (equal
         (putnam-2007-a5-power
          element exponent one table)
         one)
        exponent
      (putnam-2007-a5-order-search
       element
       (+ exponent 1)
       (- remaining 1)
       one
       table))))

(defun putnam-2007-a5-element-order
    (element carrier one table)
  (putnam-2007-a5-order-search
   element 1 (len carrier) one table))

(defun putnam-2007-a5-count-order
    (elements carrier one table p)
  (if (endp elements)
      0
    (+
     (if (equal
          (putnam-2007-a5-element-order
           (car elements) carrier one table)
          p)
         1
       0)
     (putnam-2007-a5-count-order
      (cdr elements) carrier one table p))))

(defun putnam-2007-a5-no-divisor-from-p (number divisor)
  (declare (xargs :measure (nfix (- number divisor))))
  (if (and (natp number)
           (natp divisor)
           (<= 2 divisor)
           (< divisor number))
      (and
       (not (equal (mod number divisor) 0))
       (putnam-2007-a5-no-divisor-from-p
        number (+ divisor 1)))
    t))

(defun putnam-2007-a5-primep (number)
  (and
   (natp number)
   (< 1 number)
   (putnam-2007-a5-no-divisor-from-p number 2)))

(defun putnambench-putnam-2007-a5-statement
    (carrier one table p n)
  (implies
   (and
    (putnam-2007-a5-finite-group-p
     carrier one table)
    (putnam-2007-a5-primep p)
    (natp n)
    (equal
     n
     (putnam-2007-a5-count-order
      carrier carrier one table p)))
   (or
    (equal n 0)
    (equal (mod (+ n 1) p) 0))))

(value-triple :itpeval-statement-checked)
:q
