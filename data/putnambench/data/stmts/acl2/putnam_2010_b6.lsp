;; Statement-only formalization of PutnamBench corpus artifact putnam_2010_b6:
;; an n-by-n real matrix whose first n+1 ordinary powers equal its entrywise
;; powers has that equality for every positive exponent. This file contains
;; no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; A finite tuple of real algebraic numbers is represented in one field
;; Q(alpha).  ALPHA is the unique real root, in a rational isolating interval,
;; of PRIMITIVE.  Each matrix entry is a rational polynomial in ALPHA.
;;
;; For fixed n and a fixed counterexample exponent k, the hypothesis and the
;; failure of the conclusion are a finite system of polynomial equalities and
;; inequalities over Q.  Real-closed-field completeness says that such a
;; system has a real solution exactly when it has a real-algebraic solution.
;; Thus quantifying over these exact representations preserves arbitrary real
;; matrices; it does not restrict the theorem to rational matrices.  The ACL2
;; argument K is universally quantified, preserving "for every k >= 1".

;; Rational polynomials in alpha use descending coefficient order.

(defun putnam-2010-b6-rp-p (polynomial)
  (if (consp polynomial)
      (and (rationalp (car polynomial))
           (putnam-2010-b6-rp-p (cdr polynomial)))
    (equal polynomial nil)))

(defun putnam-2010-b6-rp-normalize (polynomial)
  (if (consp polynomial)
      (if (equal (car polynomial) 0)
          (putnam-2010-b6-rp-normalize (cdr polynomial))
        polynomial)
    nil))

(defun putnam-2010-b6-rp-negate (polynomial)
  (if (consp polynomial)
      (cons (- (car polynomial))
            (putnam-2010-b6-rp-negate (cdr polynomial)))
    nil))

(defun putnam-2010-b6-rp-add-raw (left right)
  (declare
   (xargs :measure (+ (acl2-count left) (acl2-count right))))
  (cond
   ((endp left) right)
   ((endp right) left)
   ((< (len left) (len right))
    (cons (car right)
          (putnam-2010-b6-rp-add-raw left (cdr right))))
   ((< (len right) (len left))
    (cons (car left)
          (putnam-2010-b6-rp-add-raw (cdr left) right)))
   (t
    (cons (+ (car left) (car right))
          (putnam-2010-b6-rp-add-raw
           (cdr left) (cdr right))))))

(defun putnam-2010-b6-rp-add (left right)
  (putnam-2010-b6-rp-normalize
   (putnam-2010-b6-rp-add-raw left right)))

(defun putnam-2010-b6-rp-subtract (left right)
  (putnam-2010-b6-rp-add
   left
   (putnam-2010-b6-rp-negate right)))

(defun putnam-2010-b6-rp-scale (coefficient polynomial)
  (if (consp polynomial)
      (cons (* coefficient (car polynomial))
            (putnam-2010-b6-rp-scale
             coefficient (cdr polynomial)))
    nil))

(defun putnam-2010-b6-zeroes (count)
  (declare (xargs :measure (nfix count)))
  (if (zp count)
      nil
    (cons 0
          (putnam-2010-b6-zeroes (- count 1)))))

(defun putnam-2010-b6-rp-scale-shift
    (coefficient polynomial shift)
  (append
   (putnam-2010-b6-rp-scale coefficient polynomial)
   (putnam-2010-b6-zeroes shift)))

(defun putnam-2010-b6-rp-multiply-raw (left right)
  (if (consp left)
      (putnam-2010-b6-rp-add
       (putnam-2010-b6-rp-scale-shift
        (car left) right (len (cdr left)))
       (putnam-2010-b6-rp-multiply-raw (cdr left) right))
    nil))

(defun putnam-2010-b6-rp-multiply (left right)
  (putnam-2010-b6-rp-normalize
   (putnam-2010-b6-rp-multiply-raw left right)))

(defun putnam-2010-b6-rp-eval-aux
    (polynomial value accumulator)
  (if (consp polynomial)
      (putnam-2010-b6-rp-eval-aux
       (cdr polynomial)
       value
       (+ (* accumulator value) (car polynomial)))
    accumulator))

(defun putnam-2010-b6-rp-eval (polynomial value)
  (putnam-2010-b6-rp-eval-aux polynomial value 0))

(defun putnam-2010-b6-rp-derivative-aux
    (polynomial degree)
  (if (consp polynomial)
      (if (zp degree)
          nil
        (cons
         (* degree (car polynomial))
         (putnam-2010-b6-rp-derivative-aux
          (cdr polynomial) (- degree 1))))
    nil))

(defun putnam-2010-b6-rp-derivative (polynomial)
  (let ((normalized
         (putnam-2010-b6-rp-normalize polynomial)))
    (putnam-2010-b6-rp-normalize
     (putnam-2010-b6-rp-derivative-aux
      normalized
      (nfix (- (len normalized) 1))))))

(defun putnam-2010-b6-rp-remainder-fuel
    (left right fuel)
  (declare (xargs :measure (nfix fuel)))
  (let ((left (putnam-2010-b6-rp-normalize left))
        (right (putnam-2010-b6-rp-normalize right)))
    (if (or (zp fuel)
            (endp right)
            (< (len left) (len right)))
        left
      (putnam-2010-b6-rp-remainder-fuel
       (putnam-2010-b6-rp-subtract
        left
        (putnam-2010-b6-rp-scale-shift
         (/ (car left) (car right))
         right
         (- (len left) (len right))))
       right
       (- fuel 1)))))

(defun putnam-2010-b6-rp-remainder (left right)
  (putnam-2010-b6-rp-remainder-fuel
   left
   right
   (+ 1 (len (putnam-2010-b6-rp-normalize left)))))

(defun putnam-2010-b6-rp-sturm-tail
    (previous current fuel)
  (declare (xargs :measure (nfix fuel)))
  (let ((current
         (putnam-2010-b6-rp-normalize current)))
    (if (or (zp fuel) (endp current))
        nil
      (cons
       current
       (putnam-2010-b6-rp-sturm-tail
        current
        (putnam-2010-b6-rp-negate
         (putnam-2010-b6-rp-remainder
          previous current))
        (- fuel 1))))))

(defun putnam-2010-b6-rp-sturm-sequence
    (polynomial derivative)
  (let ((polynomial
         (putnam-2010-b6-rp-normalize polynomial))
        (derivative
         (putnam-2010-b6-rp-normalize derivative)))
    (if (endp polynomial)
        nil
      (cons
       polynomial
       (if (endp derivative)
           nil
         (cons
          derivative
          (putnam-2010-b6-rp-sturm-tail
           polynomial
           derivative
           (+ 1 (len polynomial) (len derivative)))))))))

(defun putnam-2010-b6-rational-sign (value)
  (cond ((< value 0) -1)
        ((< 0 value) 1)
        (t 0)))

(defun putnam-2010-b6-rp-variations-aux
    (polynomials value previous-sign)
  (if (consp polynomials)
      (let ((sign
             (putnam-2010-b6-rational-sign
              (putnam-2010-b6-rp-eval
               (car polynomials) value))))
        (if (equal sign 0)
            (putnam-2010-b6-rp-variations-aux
             (cdr polynomials) value previous-sign)
          (+ (if (and (not (equal previous-sign 0))
                      (not (equal sign previous-sign)))
                 1
               0)
             (putnam-2010-b6-rp-variations-aux
              (cdr polynomials) value sign))))
    0))

(defun putnam-2010-b6-rp-variations
    (polynomials value)
  (putnam-2010-b6-rp-variations-aux
   polynomials value 0))

(defun putnam-2010-b6-rp-cauchy-index
    (polynomial query lower upper)
  (let ((sequence
         (putnam-2010-b6-rp-sturm-sequence
          polynomial query)))
    (- (putnam-2010-b6-rp-variations sequence lower)
       (putnam-2010-b6-rp-variations sequence upper))))

(defun putnam-2010-b6-rp-root-count
    (polynomial lower upper)
  (putnam-2010-b6-rp-cauchy-index
   polynomial
   (putnam-2010-b6-rp-derivative polynomial)
   lower
   upper))

(defun putnam-2010-b6-primitive-p
    (primitive lower upper)
  (and
   (putnam-2010-b6-rp-p primitive)
   (consp (putnam-2010-b6-rp-normalize primitive))
   (rationalp lower)
   (rationalp upper)
   (< lower upper)
   (not
    (equal
     (putnam-2010-b6-rp-eval primitive lower)
     0))
   (not
    (equal
     (putnam-2010-b6-rp-eval primitive upper)
     0))
   (equal
    (putnam-2010-b6-rp-root-count
     primitive lower upper)
    1)))

;; This Sturm-Tarski query is the sign of VALUE(alpha).

(defun putnam-2010-b6-algebraic-sign
    (primitive lower upper value)
  (putnam-2010-b6-rp-cauchy-index
   primitive
   (putnam-2010-b6-rp-multiply
    (putnam-2010-b6-rp-derivative primitive)
    value)
   lower
   upper))

(defun putnam-2010-b6-algebraic-equal-p
    (primitive lower upper left right)
  (equal
   (putnam-2010-b6-algebraic-sign
    primitive
    lower
    upper
    (putnam-2010-b6-rp-subtract left right))
   0))

(defun putnam-2010-b6-algebraic-row-p
    (row dimension)
  (if (consp row)
      (and
       (natp dimension)
       (< 0 dimension)
       (putnam-2010-b6-rp-p (car row))
       (putnam-2010-b6-algebraic-row-p
        (cdr row) (- dimension 1)))
    (and
     (equal row nil)
     (equal dimension 0))))

(defun putnam-2010-b6-row-p (row dimension)
  (and
   (true-listp row)
   (equal (len row) dimension)
   (putnam-2010-b6-algebraic-row-p row dimension)))

(defun putnam-2010-b6-matrix-rows-p
    (matrix dimension)
  (if (consp matrix)
      (and
       (putnam-2010-b6-row-p (car matrix) dimension)
       (putnam-2010-b6-matrix-rows-p
        (cdr matrix) dimension))
    (equal matrix nil)))

(defun putnam-2010-b6-matrix-p (matrix dimension)
  (and
   (true-listp matrix)
   (equal (len matrix) dimension)
   (putnam-2010-b6-matrix-rows-p
    matrix dimension)))

(defun putnam-2010-b6-rp-power (value exponent)
  (declare (xargs :measure (nfix exponent)))
  (if (zp exponent)
      (list 1)
    (putnam-2010-b6-rp-multiply
     value
     (putnam-2010-b6-rp-power
      value (- exponent 1)))))

(defun putnam-2010-b6-entrywise-row-power
    (row exponent)
  (if (consp row)
      (cons
       (putnam-2010-b6-rp-power
        (car row) exponent)
       (putnam-2010-b6-entrywise-row-power
        (cdr row) exponent))
    nil))

(defun putnam-2010-b6-entrywise-power
    (matrix exponent)
  (if (consp matrix)
      (cons
       (putnam-2010-b6-entrywise-row-power
        (car matrix) exponent)
       (putnam-2010-b6-entrywise-power
        (cdr matrix) exponent))
    nil))

(defun putnam-2010-b6-first-column (matrix)
  (if (consp matrix)
      (cons (caar matrix)
            (putnam-2010-b6-first-column
             (cdr matrix)))
    nil))

(defun putnam-2010-b6-rest-columns (matrix)
  (if (consp matrix)
      (cons (cdar matrix)
            (putnam-2010-b6-rest-columns
             (cdr matrix)))
    nil))

(defun putnam-2010-b6-transpose (matrix)
  (if (or (endp matrix) (endp (car matrix)))
      nil
    (cons
     (putnam-2010-b6-first-column matrix)
     (putnam-2010-b6-transpose
      (putnam-2010-b6-rest-columns matrix)))))

(defun putnam-2010-b6-dot-product (left right)
  (if (or (endp left) (endp right))
      nil
    (putnam-2010-b6-rp-add
     (putnam-2010-b6-rp-multiply
      (car left) (car right))
     (putnam-2010-b6-dot-product
      (cdr left) (cdr right)))))

(defun putnam-2010-b6-row-times-columns
    (row columns)
  (if (consp columns)
      (cons
       (putnam-2010-b6-dot-product
        row (car columns))
       (putnam-2010-b6-row-times-columns
        row (cdr columns)))
    nil))

(defun putnam-2010-b6-matrix-times-columns
    (matrix columns)
  (if (consp matrix)
      (cons
       (putnam-2010-b6-row-times-columns
        (car matrix) columns)
       (putnam-2010-b6-matrix-times-columns
        (cdr matrix) columns))
    nil))

(defun putnam-2010-b6-matrix-multiply (left right)
  (putnam-2010-b6-matrix-times-columns
   left
   (putnam-2010-b6-transpose right)))

(defun putnam-2010-b6-identity-row
    (row column count)
  (declare (xargs :measure (nfix count)))
  (if (zp count)
      nil
    (cons
     (if (equal row column) (list 1) nil)
     (putnam-2010-b6-identity-row
      row (+ column 1) (- count 1)))))

(defun putnam-2010-b6-identity-rows
    (row count dimension)
  (declare (xargs :measure (nfix count)))
  (if (zp count)
      nil
      (cons
       (putnam-2010-b6-identity-row row 0 dimension)
       (putnam-2010-b6-identity-rows
        (+ row 1) (- count 1) dimension))))

(defun putnam-2010-b6-identity-matrix (dimension)
  (putnam-2010-b6-identity-rows
   0 dimension dimension))

(defun putnam-2010-b6-matrix-power
    (matrix exponent dimension)
  (declare (xargs :measure (nfix exponent)))
  (if (zp exponent)
      (putnam-2010-b6-identity-matrix dimension)
    (putnam-2010-b6-matrix-multiply
     matrix
     (putnam-2010-b6-matrix-power
      matrix (- exponent 1) dimension))))

(defun putnam-2010-b6-rows-equal-p
    (primitive lower upper left right)
  (if (consp left)
      (and
       (consp right)
       (putnam-2010-b6-algebraic-equal-p
        primitive lower upper (car left) (car right))
       (putnam-2010-b6-rows-equal-p
        primitive lower upper (cdr left) (cdr right)))
    (equal right nil)))

(defun putnam-2010-b6-matrices-equal-p
    (primitive lower upper left right)
  (if (consp left)
      (and
       (consp right)
       (putnam-2010-b6-rows-equal-p
        primitive lower upper (car left) (car right))
       (putnam-2010-b6-matrices-equal-p
        primitive lower upper (cdr left) (cdr right)))
    (equal right nil)))

(defun putnam-2010-b6-power-equality-p
    (primitive lower upper matrix dimension exponent)
  (putnam-2010-b6-matrices-equal-p
   primitive
   lower
   upper
   (putnam-2010-b6-matrix-power
    matrix exponent dimension)
   (putnam-2010-b6-entrywise-power
    matrix exponent)))

(defun putnam-2010-b6-initial-equalities-p
    (primitive lower upper matrix dimension exponent count)
  (declare (xargs :measure (nfix count)))
  (if (zp count)
      t
    (and
     (putnam-2010-b6-power-equality-p
      primitive lower upper matrix dimension exponent)
     (putnam-2010-b6-initial-equalities-p
      primitive
      lower
      upper
      matrix
      dimension
      (+ exponent 1)
      (- count 1)))))

(defun putnambench-putnam-2010-b6-statement
    (n primitive lower upper matrix k)
  (implies
   (and
    (natp n)
    (< 0 n)
    (putnam-2010-b6-primitive-p
     primitive lower upper)
    (putnam-2010-b6-matrix-p matrix n)
    (putnam-2010-b6-initial-equalities-p
     primitive lower upper matrix n 1 (+ n 1)))
   (implies
    (and (natp k) (< 0 k))
    (putnam-2010-b6-power-equality-p
     primitive lower upper matrix n k))))

(value-triple :itpeval-statement-checked)
:q
