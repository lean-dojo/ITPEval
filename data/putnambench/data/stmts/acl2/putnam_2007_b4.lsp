;; Statement-only formalization of PutnamBench corpus artifact putnam_2007_b4:
;; for positive n, exactly 2^(n+1) ordered pairs of real polynomials P,Q
;; satisfy P^2+Q^2=X^(2n)+1 and degree(P)>degree(Q). This file contains no
;; proof and does not prescribe or construct the qualifying pairs.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; The scalar symbols present an arbitrary real-closed ordered field.
;; For every fixed n, the source is a first-order algebraic statement about
;; finitely many polynomial coefficients. Completeness of real-closed fields
;; therefore transfers it exactly between this carrier and the real numbers.

(defstub p2007b4-scalar-p (x) t)
(defstub p2007b4-add-op (x y) t)
(defstub p2007b4-multiply-op (x y) t)
(defstub p2007b4-negate-op (x) t)
(defstub p2007b4-inverse-op (x) t)
(defstub p2007b4-less-op (x y) t)
(defstub p2007b4-zero () t)
(defstub p2007b4-one () t)

(defun p2007b4-add (x y)
  (p2007b4-add-op x y))

(defun p2007b4-multiply (x y)
  (p2007b4-multiply-op x y))

(defun p2007b4-negate (x)
  (p2007b4-negate-op x))

(defun p2007b4-inverse (x)
  (p2007b4-inverse-op x))

(defun p2007b4-less (x y)
  (if (p2007b4-less-op x y) t nil))

(defun-sk p2007b4-field-laws-p ()
  (forall (x y z)
    (implies
     (and
      (p2007b4-scalar-p x)
      (p2007b4-scalar-p y)
      (p2007b4-scalar-p z))
     (and
      (p2007b4-scalar-p (p2007b4-add x y))
      (p2007b4-scalar-p (p2007b4-multiply x y))
      (p2007b4-scalar-p (p2007b4-negate x))
      (implies
       (not (equal x (p2007b4-zero)))
       (p2007b4-scalar-p (p2007b4-inverse x)))
      (equal
       (p2007b4-add (p2007b4-add x y) z)
       (p2007b4-add x (p2007b4-add y z)))
      (equal
       (p2007b4-add x y)
       (p2007b4-add y x))
      (equal
       (p2007b4-add x (p2007b4-zero))
       x)
      (equal
       (p2007b4-add x (p2007b4-negate x))
       (p2007b4-zero))
      (equal
       (p2007b4-multiply
        (p2007b4-multiply x y) z)
       (p2007b4-multiply
        x (p2007b4-multiply y z)))
      (equal
       (p2007b4-multiply x y)
       (p2007b4-multiply y x))
      (equal
       (p2007b4-multiply x (p2007b4-one))
       x)
      (implies
       (not (equal x (p2007b4-zero)))
       (equal
        (p2007b4-multiply x (p2007b4-inverse x))
        (p2007b4-one)))
      (equal
       (p2007b4-multiply x (p2007b4-add y z))
       (p2007b4-add
        (p2007b4-multiply x y)
        (p2007b4-multiply x z)))))))

(defun-sk p2007b4-order-laws-p ()
  (forall (x y z)
    (implies
     (and
      (p2007b4-scalar-p x)
      (p2007b4-scalar-p y)
      (p2007b4-scalar-p z))
     (and
      (not (p2007b4-less x x))
      (or
       (equal x y)
       (p2007b4-less x y)
       (p2007b4-less y x))
      (implies
       (and
        (p2007b4-less x y)
        (p2007b4-less y z))
       (p2007b4-less x z))
      (implies
       (p2007b4-less x y)
       (p2007b4-less
        (p2007b4-add x z)
        (p2007b4-add y z)))
      (implies
       (and
        (p2007b4-less (p2007b4-zero) x)
        (p2007b4-less (p2007b4-zero) y))
       (p2007b4-less
        (p2007b4-zero)
        (p2007b4-multiply x y)))))))

(defun p2007b4-coefficient-list-p (coefficients)
  (if (consp coefficients)
      (and
       (p2007b4-scalar-p (car coefficients))
       (p2007b4-coefficient-list-p
        (cdr coefficients)))
    (equal coefficients nil)))

;; Coefficients use increasing degree order.
(defun p2007b4-polynomial-value (coefficients x)
  (if (consp coefficients)
      (p2007b4-add
       (car coefficients)
       (p2007b4-multiply
        x
        (p2007b4-polynomial-value
         (cdr coefficients) x)))
    (p2007b4-zero)))

(defun p2007b4-polynomial-p (coefficients)
  (and
   (true-listp coefficients)
   (p2007b4-coefficient-list-p coefficients)))

(defun p2007b4-odd-degree-polynomial-p (coefficients)
  (and
   (p2007b4-polynomial-p coefficients)
   (consp coefficients)
   (evenp (len coefficients))
   (not
    (equal
     (car (last coefficients))
     (p2007b4-zero)))))

(defun-sk p2007b4-square-root-exists-p (x)
  (exists (root)
    (and
     (p2007b4-scalar-p root)
     (equal
      (p2007b4-multiply root root)
      x))))

(defun-sk p2007b4-positive-square-roots-p ()
  (forall (x)
    (implies
     (and
      (p2007b4-scalar-p x)
      (p2007b4-less (p2007b4-zero) x))
     (p2007b4-square-root-exists-p x))))

(defun-sk p2007b4-polynomial-root-exists-p
    (coefficients)
  (exists (root)
    (and
     (p2007b4-scalar-p root)
     (equal
      (p2007b4-polynomial-value
       coefficients root)
      (p2007b4-zero)))))

(defun-sk p2007b4-odd-polynomial-roots-p ()
  (forall (coefficients)
    (implies
     (p2007b4-odd-degree-polynomial-p coefficients)
     (p2007b4-polynomial-root-exists-p
      coefficients))))

(defun p2007b4-real-closed-field-p ()
  (and
   (p2007b4-scalar-p (p2007b4-zero))
   (p2007b4-scalar-p (p2007b4-one))
   (not (equal (p2007b4-zero) (p2007b4-one)))
   (p2007b4-less (p2007b4-zero) (p2007b4-one))
   (p2007b4-field-laws-p)
   (p2007b4-order-laws-p)
   (p2007b4-positive-square-roots-p)
   (p2007b4-odd-polynomial-roots-p)))

;; Canonical real polynomials have no trailing zero coefficient. NIL is the
;; unique zero polynomial.

(defun p2007b4-canonical-polynomial-p (coefficients)
  (and
   (p2007b4-polynomial-p coefficients)
   (or
    (endp coefficients)
    (not
     (equal
      (car (last coefficients))
      (p2007b4-zero))))))

(defun p2007b4-polynomial-normalize (coefficients)
  (if (consp coefficients)
      (let ((tail
             (p2007b4-polynomial-normalize
              (cdr coefficients))))
        (if (and
             (endp tail)
             (equal (car coefficients)
                    (p2007b4-zero)))
            nil
          (cons (car coefficients) tail)))
    nil))

(defun p2007b4-polynomial-add-raw (left right)
  (cond
   ((endp left) right)
   ((endp right) left)
   (t
    (cons
     (p2007b4-add (car left) (car right))
     (p2007b4-polynomial-add-raw
      (cdr left) (cdr right))))))

(defun p2007b4-polynomial-add (left right)
  (p2007b4-polynomial-normalize
   (p2007b4-polynomial-add-raw left right)))

(defun p2007b4-polynomial-scale (scalar polynomial)
  (if (consp polynomial)
      (cons
       (p2007b4-multiply scalar (car polynomial))
       (p2007b4-polynomial-scale
        scalar (cdr polynomial)))
    nil))

(defun p2007b4-polynomial-shift (polynomial)
  (if (consp polynomial)
      (cons (p2007b4-zero) polynomial)
    nil))

(defun p2007b4-polynomial-multiply (left right)
  (if (consp left)
      (p2007b4-polynomial-add
       (p2007b4-polynomial-scale
        (car left) right)
       (p2007b4-polynomial-shift
        (p2007b4-polynomial-multiply
         (cdr left) right)))
    nil))

(defun p2007b4-zero-coefficients (count)
  (declare (xargs :measure (nfix count)))
  (if (zp count)
      nil
    (cons
     (p2007b4-zero)
     (p2007b4-zero-coefficients (- count 1)))))

(defun p2007b4-target-polynomial (n)
  (if (posp n)
      (cons
       (p2007b4-one)
       (append
        (p2007b4-zero-coefficients
         (- (* 2 n) 1))
        (list (p2007b4-one))))
    nil))

(defun p2007b4-degree-greater-p (left right)
  (and
   (consp left)
   (or
    (endp right)
    (< (len right) (len left)))))

(defun p2007b4-qualifying-p (n p q)
  (and
   (posp n)
   (p2007b4-canonical-polynomial-p p)
   (p2007b4-canonical-polynomial-p q)
   (p2007b4-degree-greater-p p q)
   (equal
    (p2007b4-polynomial-add
     (p2007b4-polynomial-multiply p p)
     (p2007b4-polynomial-multiply q q))
    (p2007b4-target-polynomial n))))

(defun p2007b4-pair-p (pair n)
  (and
   (true-listp pair)
   (equal (len pair) 2)
   (p2007b4-qualifying-p
    n (nth 0 pair) (nth 1 pair))))

(defun p2007b4-distinct-from-list-p (pair pairs)
  (if (consp pairs)
      (and
       (not (equal pair (car pairs)))
       (p2007b4-distinct-from-list-p
        pair (cdr pairs)))
    (equal pairs nil)))

(defun p2007b4-distinct-qualifying-list-p (pairs n)
  (if (consp pairs)
      (and
       (p2007b4-pair-p (car pairs) n)
       (p2007b4-distinct-from-list-p
        (car pairs) (cdr pairs))
       (p2007b4-distinct-qualifying-list-p
        (cdr pairs) n))
    (equal pairs nil)))

(defun-sk p2007b4-covers-all-qualifying-p (pairs n)
  (forall (p q)
    (implies
     (p2007b4-qualifying-p n p q)
     (member-equal (list p q) pairs))))

(defun p2007b4-exact-enumeration-p (pairs n)
  (and
   (true-listp pairs)
   (equal (len pairs) (expt 2 (+ n 1)))
   (p2007b4-distinct-qualifying-list-p pairs n)
   (p2007b4-covers-all-qualifying-p pairs n)))

(defun-sk p2007b4-exact-cardinality-p (n)
  (exists (pairs)
    (p2007b4-exact-enumeration-p pairs n)))

(defun putnambench-putnam-2007-b4-statement (n)
  (implies
   (and
    (posp n)
    (p2007b4-real-closed-field-p))
   (p2007b4-exact-cardinality-p n)))

(value-triple :itpeval-statement-checked)
:q
