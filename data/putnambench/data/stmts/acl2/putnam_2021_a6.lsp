;; Statement-only formalization of PutnamBench corpus artifact putnam_2021_a6:
;; every integer polynomial with coefficients in {0,1} that factors into two
;; nonconstant integer polynomials has a composite value at 2. This file
;; contains no proof.

(in-package "ACL2")

;; Coefficients are stored in ascending degree order. NIL is the zero
;; polynomial, and every nonzero polynomial has its unique representation
;; with a nonzero final coefficient.
(defun putnam-2021-a6-integer-coefficient-list-p (coefficients)
  (if (consp coefficients)
      (and
       (integerp (car coefficients))
       (putnam-2021-a6-integer-coefficient-list-p
        (cdr coefficients)))
    (equal coefficients nil)))

(defun putnam-2021-a6-integer-polynomial-p (coefficients)
  (and
   (putnam-2021-a6-integer-coefficient-list-p coefficients)
   (or
    (endp coefficients)
    (not (equal (car (last coefficients)) 0)))))

(defun putnam-2021-a6-zero-one-coefficients-p (coefficients)
  (if (consp coefficients)
      (and
       (or
        (equal (car coefficients) 0)
        (equal (car coefficients) 1))
       (putnam-2021-a6-zero-one-coefficients-p
        (cdr coefficients)))
    (equal coefficients nil)))

(defun putnam-2021-a6-trim (coefficients)
  (if (consp coefficients)
      (let ((tail
             (putnam-2021-a6-trim (cdr coefficients))))
        (if (and
             (equal (car coefficients) 0)
             (endp tail))
            nil
          (cons (car coefficients) tail)))
    nil))

(defun putnam-2021-a6-poly-cons (coefficient tail)
  (if (and
       (equal coefficient 0)
       (endp tail))
      nil
    (cons coefficient tail)))

(defun putnam-2021-a6-poly-add (left right)
  (declare
   (xargs :measure (+ (acl2-count left) (acl2-count right))))
  (cond
   ((endp left) right)
   ((endp right) left)
   (t
    (putnam-2021-a6-poly-cons
     (+ (car left) (car right))
     (putnam-2021-a6-poly-add
      (cdr left) (cdr right))))))

(defun putnam-2021-a6-poly-scale (scalar polynomial)
  (if (endp polynomial)
      nil
    (putnam-2021-a6-poly-cons
     (* scalar (car polynomial))
     (putnam-2021-a6-poly-scale
      scalar (cdr polynomial)))))

(defun putnam-2021-a6-poly-shift (polynomial)
  (if (endp polynomial)
      nil
    (cons 0 polynomial)))

(defun putnam-2021-a6-poly-multiply (left right)
  (if (endp left)
      nil
    (putnam-2021-a6-poly-add
     (putnam-2021-a6-poly-scale
      (car left) right)
     (putnam-2021-a6-poly-shift
      (putnam-2021-a6-poly-multiply
       (cdr left) right)))))

(defun putnam-2021-a6-poly-evaluate (coefficients value)
  (if (consp coefficients)
      (+ (car coefficients)
         (* value
            (putnam-2021-a6-poly-evaluate
             (cdr coefficients) value)))
    0))

;; A code enumerates all coefficient vectors of the requested length with
;; entries from -BOUND through BOUND. Trimming gives every integer polynomial
;; of degree below LENGTH.
(defun putnam-2021-a6-coefficients-from-code
    (code length bound)
  (declare (xargs :measure (nfix length)))
  (if (zp length)
      nil
    (let ((base (+ 1 (* 2 (nfix bound)))))
      (cons
       (- (mod (nfix code) base) (nfix bound))
       (putnam-2021-a6-coefficients-from-code
        (floor (nfix code) base)
        (- length 1)
        bound)))))

(defun putnam-2021-a6-monic-nonconstant-p (polynomial)
  (and
   (putnam-2021-a6-integer-polynomial-p polynomial)
   (consp (cdr polynomial))
   (equal (car (last polynomial)) 1)))

;; For a monic 0/1 polynomial P of degree N, every complex root has modulus
;; at most 2. A monic factor of degree D has each coefficient bounded by
;; 3^D, hence by 4^N. Thus the finite searches below are exactly the source
;; existential quantifiers over nonconstant integer factors; no witness is
;; exposed as a statement parameter.
(defun putnam-2021-a6-factor-with-right-code-p
    (polynomial left bound coefficient-count right-code-count)
  (declare (xargs :measure (nfix right-code-count)))
  (if (zp right-code-count)
      nil
    (let* ((code (- right-code-count 1))
           (right
            (putnam-2021-a6-trim
             (putnam-2021-a6-coefficients-from-code
              code coefficient-count bound))))
      (or
       (and
        (putnam-2021-a6-monic-nonconstant-p right)
        (equal
         polynomial
         (putnam-2021-a6-poly-multiply left right)))
       (putnam-2021-a6-factor-with-right-code-p
        polynomial left bound coefficient-count code)))))

(defun putnam-2021-a6-factor-pair-through-codes-p
    (polynomial bound coefficient-count
                right-code-count left-code-count)
  (declare (xargs :measure (nfix left-code-count)))
  (if (zp left-code-count)
      nil
    (let* ((code (- left-code-count 1))
           (left
            (putnam-2021-a6-trim
             (putnam-2021-a6-coefficients-from-code
              code coefficient-count bound))))
      (or
       (and
        (putnam-2021-a6-monic-nonconstant-p left)
        (putnam-2021-a6-factor-with-right-code-p
         polynomial left bound coefficient-count
         right-code-count))
       (putnam-2021-a6-factor-pair-through-codes-p
        polynomial bound coefficient-count
        right-code-count code)))))

(defun putnam-2021-a6-reducible-p (polynomial)
  (let* ((degree
          (if (consp polynomial)
              (- (len polynomial) 1)
            0))
         (coefficient-count (+ degree 1))
         (bound (expt 4 degree))
         (base (+ 1 (* 2 bound)))
         (code-count (expt base coefficient-count)))
    (putnam-2021-a6-factor-pair-through-codes-p
     polynomial bound coefficient-count code-count code-count)))

;; On positive integers, this is the standard definition of primality.
(defun putnam-2021-a6-no-divisor-from-p (number divisor)
  (declare (xargs :measure (nfix (- number divisor))))
  (if (and
       (natp number)
       (natp divisor)
       (<= 2 divisor)
       (< divisor number))
      (and
       (not (equal (mod number divisor) 0))
       (putnam-2021-a6-no-divisor-from-p
        number (+ divisor 1)))
    t))

(defun putnam-2021-a6-primep (number)
  (and
   (natp number)
   (< 1 number)
   (putnam-2021-a6-no-divisor-from-p number 2)))

;; ACL2 universally closes COEFFICIENTS, matching the source quantification
;; over all integer polynomials.
(defun putnambench-putnam-2021-a6-statement (coefficients)
  (implies
   (and
    (putnam-2021-a6-integer-polynomial-p coefficients)
    (putnam-2021-a6-zero-one-coefficients-p coefficients)
    (putnam-2021-a6-reducible-p coefficients))
   (let ((value
          (putnam-2021-a6-poly-evaluate coefficients 2)))
     (and
      (not (equal value 0))
      (not (equal value 1))
      (not (putnam-2021-a6-primep value))))))

(value-triple :itpeval-statement-checked)
:q
