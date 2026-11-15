;; Statement-only formalization of PutnamBench corpus artifact putnam_1991_a3:
;; a real polynomial of degree n >= 2 has n increasing real roots whose
;; adjacent midpoints are roots of its derivative exactly when it is a
;; quadratic with two distinct real roots. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Both sides of the source equivalence are first-order formulas over real
;; closed fields. Any real counterexample therefore has real algebraic
;; coordinates. A finite tuple of real algebraic numbers lies in Q(alpha)
;; for one real algebraic alpha. Rational polynomials in alpha represent the
;; coefficients and roots below, and Sturm-Tarski queries decide their signs
;; exactly. Thus universal closure of the final predicate detects precisely
;; the arbitrary-real counterexamples, without restricting them to rationals.
;;
;; The existential equivalence is split into two equivalent universal
;; directions. An arbitrary root-list witness implies membership in the
;; stated solution set. Conversely, any two distinct roots witnessing that a
;; quadratic belongs to the solution set give the canonical increasing
;; two-root list. A finite list is equivalent to the used prefix of the
;; source function Nat -> Real.

;; Rational polynomials in alpha use descending coefficient order.

(defun putnam-1991-a3-rp-p (polynomial)
  (if (consp polynomial)
      (and (rationalp (car polynomial))
           (putnam-1991-a3-rp-p (cdr polynomial)))
    (equal polynomial nil)))

(defun putnam-1991-a3-rp-normalize (polynomial)
  (if (consp polynomial)
      (if (equal (car polynomial) 0)
          (putnam-1991-a3-rp-normalize (cdr polynomial))
        polynomial)
    nil))

(defun putnam-1991-a3-rp-negate (polynomial)
  (if (consp polynomial)
      (cons (- (car polynomial))
            (putnam-1991-a3-rp-negate (cdr polynomial)))
    nil))

(defun putnam-1991-a3-rp-add-raw (left right)
  (declare
   (xargs :measure (+ (acl2-count left) (acl2-count right))))
  (cond
   ((endp left) right)
   ((endp right) left)
   ((< (len left) (len right))
    (cons (car right)
          (putnam-1991-a3-rp-add-raw left (cdr right))))
   ((< (len right) (len left))
    (cons (car left)
          (putnam-1991-a3-rp-add-raw (cdr left) right)))
   (t
    (cons (+ (car left) (car right))
          (putnam-1991-a3-rp-add-raw
           (cdr left) (cdr right))))))

(defun putnam-1991-a3-rp-add (left right)
  (putnam-1991-a3-rp-normalize
   (putnam-1991-a3-rp-add-raw left right)))

(defun putnam-1991-a3-rp-subtract (left right)
  (putnam-1991-a3-rp-add
   left (putnam-1991-a3-rp-negate right)))

(defun putnam-1991-a3-rp-scale (coefficient polynomial)
  (if (consp polynomial)
      (cons (* coefficient (car polynomial))
            (putnam-1991-a3-rp-scale
             coefficient (cdr polynomial)))
    nil))

(defun putnam-1991-a3-zeroes (count)
  (declare (xargs :measure (nfix count)))
  (if (zp count)
      nil
    (cons 0 (putnam-1991-a3-zeroes (- count 1)))))

(defun putnam-1991-a3-rp-scale-shift
    (coefficient polynomial shift)
  (append
   (putnam-1991-a3-rp-scale coefficient polynomial)
   (putnam-1991-a3-zeroes shift)))

(defun putnam-1991-a3-rp-multiply-raw (left right)
  (if (consp left)
      (putnam-1991-a3-rp-add
       (putnam-1991-a3-rp-scale-shift
        (car left) right (len (cdr left)))
       (putnam-1991-a3-rp-multiply-raw (cdr left) right))
    nil))

(defun putnam-1991-a3-rp-multiply (left right)
  (putnam-1991-a3-rp-normalize
   (putnam-1991-a3-rp-multiply-raw left right)))

(defun putnam-1991-a3-rp-eval-aux
    (polynomial x accumulator)
  (if (consp polynomial)
      (putnam-1991-a3-rp-eval-aux
       (cdr polynomial)
       x
       (+ (* accumulator x) (car polynomial)))
    accumulator))

(defun putnam-1991-a3-rp-eval (polynomial x)
  (putnam-1991-a3-rp-eval-aux polynomial x 0))

(defun putnam-1991-a3-rp-derivative-aux
    (polynomial degree)
  (if (consp polynomial)
      (if (zp degree)
          nil
        (cons
         (* degree (car polynomial))
         (putnam-1991-a3-rp-derivative-aux
          (cdr polynomial) (- degree 1))))
    nil))

(defun putnam-1991-a3-rp-derivative (polynomial)
  (let ((normalized
         (putnam-1991-a3-rp-normalize polynomial)))
    (putnam-1991-a3-rp-normalize
     (putnam-1991-a3-rp-derivative-aux
      normalized
      (nfix (- (len normalized) 1))))))

(defun putnam-1991-a3-rp-remainder-fuel
    (left right fuel)
  (declare (xargs :measure (nfix fuel)))
  (let ((left (putnam-1991-a3-rp-normalize left))
        (right (putnam-1991-a3-rp-normalize right)))
    (if (or (zp fuel)
            (endp right)
            (< (len left) (len right)))
        left
      (putnam-1991-a3-rp-remainder-fuel
       (putnam-1991-a3-rp-subtract
        left
        (putnam-1991-a3-rp-scale-shift
         (/ (car left) (car right))
         right
         (- (len left) (len right))))
       right
       (- fuel 1)))))

(defun putnam-1991-a3-rp-remainder (left right)
  (putnam-1991-a3-rp-remainder-fuel
   left
   right
   (+ 1 (len (putnam-1991-a3-rp-normalize left)))))

(defun putnam-1991-a3-rp-sturm-tail
    (previous current fuel)
  (declare (xargs :measure (nfix fuel)))
  (let ((current
         (putnam-1991-a3-rp-normalize current)))
    (if (or (zp fuel) (endp current))
        nil
      (cons
       current
       (putnam-1991-a3-rp-sturm-tail
        current
        (putnam-1991-a3-rp-negate
         (putnam-1991-a3-rp-remainder previous current))
        (- fuel 1))))))

(defun putnam-1991-a3-rp-sturm-sequence
    (polynomial query)
  (let ((polynomial
         (putnam-1991-a3-rp-normalize polynomial))
        (query
         (putnam-1991-a3-rp-normalize query)))
    (if (endp polynomial)
        nil
      (cons
       polynomial
       (if (endp query)
           nil
         (cons
          query
          (putnam-1991-a3-rp-sturm-tail
           polynomial
           query
           (+ 1 (len polynomial) (len query)))))))))

(defun putnam-1991-a3-rational-sign (value)
  (cond ((< value 0) -1)
        ((< 0 value) 1)
        (t 0)))

(defun putnam-1991-a3-rp-variations-aux
    (polynomials x previous-sign)
  (if (consp polynomials)
      (let ((sign
             (putnam-1991-a3-rational-sign
              (putnam-1991-a3-rp-eval
               (car polynomials) x))))
        (if (equal sign 0)
            (putnam-1991-a3-rp-variations-aux
             (cdr polynomials) x previous-sign)
          (+ (if (and (not (equal previous-sign 0))
                      (not (equal sign previous-sign)))
                 1
               0)
             (putnam-1991-a3-rp-variations-aux
              (cdr polynomials) x sign))))
    0))

(defun putnam-1991-a3-rp-variations (polynomials x)
  (putnam-1991-a3-rp-variations-aux
   polynomials x 0))

(defun putnam-1991-a3-rp-cauchy-index
    (polynomial query lower upper)
  (let ((sequence
         (putnam-1991-a3-rp-sturm-sequence
          polynomial query)))
    (- (putnam-1991-a3-rp-variations sequence lower)
       (putnam-1991-a3-rp-variations sequence upper))))

(defun putnam-1991-a3-rp-root-count
    (polynomial lower upper)
  (putnam-1991-a3-rp-cauchy-index
   polynomial
   (putnam-1991-a3-rp-derivative polynomial)
   lower
   upper))

(defun putnam-1991-a3-primitive-p
    (primitive lower upper)
  (and
   (putnam-1991-a3-rp-p primitive)
   (consp (putnam-1991-a3-rp-normalize primitive))
   (rationalp lower)
   (rationalp upper)
   (< lower upper)
   (not (equal
         (putnam-1991-a3-rp-eval primitive lower)
         0))
   (not (equal
         (putnam-1991-a3-rp-eval primitive upper)
         0))
   (equal
    (putnam-1991-a3-rp-root-count
     primitive lower upper)
    1)
   (not
    (equal
     (putnam-1991-a3-rp-cauchy-index
      primitive
      (putnam-1991-a3-rp-multiply
       (putnam-1991-a3-rp-derivative primitive)
       (putnam-1991-a3-rp-derivative primitive))
      lower
      upper)
     0))))

;; For the unique isolated simple root alpha, this is sign(VALUE(alpha)).
(defun putnam-1991-a3-algebraic-sign
    (primitive lower upper value)
  (putnam-1991-a3-rp-cauchy-index
   primitive
   (putnam-1991-a3-rp-multiply
    (putnam-1991-a3-rp-derivative primitive)
    value)
   lower
   upper))

(defun putnam-1991-a3-algebraic-zero-p
    (primitive lower upper value)
  (equal
   (putnam-1991-a3-algebraic-sign
    primitive lower upper value)
   0))

(defun putnam-1991-a3-algebraic-less-p
    (primitive lower upper left right)
  (equal
   (putnam-1991-a3-algebraic-sign
    primitive
    lower
    upper
    (putnam-1991-a3-rp-subtract left right))
   -1))

;; The source polynomial uses ascending powers of x. Each coefficient is a
;; rational polynomial in alpha.

(defun putnam-1991-a3-coefficient-list-p (coefficients)
  (if (consp coefficients)
      (and
       (putnam-1991-a3-rp-p (car coefficients))
       (putnam-1991-a3-coefficient-list-p
        (cdr coefficients)))
    (equal coefficients nil)))

(defun putnam-1991-a3-polynomial-p
    (primitive lower upper coefficients n)
  (and
   (natp n)
   (consp coefficients)
   (putnam-1991-a3-coefficient-list-p coefficients)
   (equal (len coefficients) (+ n 1))
   (not
    (putnam-1991-a3-algebraic-zero-p
     primitive lower upper
     (car (last coefficients))))))

(defun putnam-1991-a3-polynomial-value
    (coefficients x)
  (if (consp coefficients)
      (putnam-1991-a3-rp-add
       (car coefficients)
       (putnam-1991-a3-rp-multiply
        x
        (putnam-1991-a3-polynomial-value
         (cdr coefficients) x)))
    nil))

(defun putnam-1991-a3-polynomial-derivative-aux
    (coefficients multiplier)
  (if (consp coefficients)
      (cons
       (putnam-1991-a3-rp-scale
        multiplier (car coefficients))
       (putnam-1991-a3-polynomial-derivative-aux
        (cdr coefficients) (+ multiplier 1)))
    nil))

(defun putnam-1991-a3-polynomial-derivative
    (coefficients)
  (putnam-1991-a3-polynomial-derivative-aux
   (cdr coefficients) 1))

(defun putnam-1991-a3-root-p
    (primitive lower upper coefficients root)
  (and
   (putnam-1991-a3-rp-p root)
   (putnam-1991-a3-algebraic-zero-p
    primitive
    lower
    upper
    (putnam-1991-a3-polynomial-value
     coefficients root))))

(defun putnam-1991-a3-root-list-p (roots count)
  (declare (xargs :measure (nfix count)))
  (if (zp count)
      (equal roots nil)
    (and
     (consp roots)
     (putnam-1991-a3-rp-p (car roots))
     (putnam-1991-a3-root-list-p
      (cdr roots) (- count 1)))))

(defun putnam-1991-a3-roots-increasing-p
    (primitive lower upper roots)
  (if (and (consp roots) (consp (cdr roots)))
      (and
       (putnam-1991-a3-algebraic-less-p
        primitive lower upper (car roots) (cadr roots))
       (putnam-1991-a3-roots-increasing-p
        primitive lower upper (cdr roots)))
    t))

(defun putnam-1991-a3-all-roots-p
    (primitive lower upper coefficients roots)
  (if (consp roots)
      (and
       (putnam-1991-a3-root-p
        primitive lower upper coefficients (car roots))
       (putnam-1991-a3-all-roots-p
        primitive lower upper coefficients (cdr roots)))
    (equal roots nil)))

(defun putnam-1991-a3-midpoint (left right)
  (putnam-1991-a3-rp-scale
   1/2
   (putnam-1991-a3-rp-add left right)))

(defun putnam-1991-a3-derivative-midpoints-p
    (primitive lower upper derivative roots)
  (if (and (consp roots) (consp (cdr roots)))
      (and
       (putnam-1991-a3-algebraic-zero-p
        primitive
        lower
        upper
        (putnam-1991-a3-polynomial-value
         derivative
         (putnam-1991-a3-midpoint
          (car roots) (cadr roots))))
       (putnam-1991-a3-derivative-midpoints-p
        primitive lower upper derivative (cdr roots)))
    t))

(defun putnam-1991-a3-root-configuration-p
    (primitive lower upper coefficients n roots)
  (and
   (natp n)
   (<= 2 n)
   (putnam-1991-a3-root-list-p roots n)
   (putnam-1991-a3-roots-increasing-p
    primitive lower upper roots)
   (putnam-1991-a3-all-roots-p
    primitive lower upper coefficients roots)
   (putnam-1991-a3-derivative-midpoints-p
    primitive
    lower
    upper
    (putnam-1991-a3-polynomial-derivative coefficients)
    roots)))

(defun putnam-1991-a3-distinct-root-pair-p
    (primitive lower upper coefficients left right)
  (and
   (putnam-1991-a3-root-p
    primitive lower upper coefficients left)
   (putnam-1991-a3-root-p
    primitive lower upper coefficients right)
   (not
    (putnam-1991-a3-algebraic-zero-p
     primitive
     lower
     upper
     (putnam-1991-a3-rp-subtract left right)))))

(defun putnam-1991-a3-ordered-pair
    (primitive lower upper left right)
  (if (putnam-1991-a3-algebraic-less-p
       primitive lower upper left right)
      (list left right)
    (list right left)))

(defun putnambench-putnam-1991-a3-statement
    (primitive lower upper coefficients n roots left-root right-root)
  (implies
   (and
    (putnam-1991-a3-primitive-p primitive lower upper)
    (putnam-1991-a3-polynomial-p
     primitive lower upper coefficients n)
    (<= 2 n))
   (and
    ;; Existential root configuration implies the stated classification.
    (implies
     (putnam-1991-a3-root-configuration-p
      primitive lower upper coefficients n roots)
     (and
      (equal n 2)
      (putnam-1991-a3-distinct-root-pair-p
       primitive
       lower
       upper
       coefficients
       (car roots)
       (cadr roots))))
    ;; Every witness for the solution-set membership supplies the canonical
    ;; existential root configuration.
    (implies
     (and
      (equal n 2)
      (putnam-1991-a3-rp-p left-root)
      (putnam-1991-a3-rp-p right-root)
      (putnam-1991-a3-distinct-root-pair-p
       primitive
       lower
       upper
       coefficients
       left-root
       right-root))
     (putnam-1991-a3-root-configuration-p
      primitive
      lower
      upper
      coefficients
      n
      (putnam-1991-a3-ordered-pair
       primitive lower upper left-root right-root))))))

(value-triple :itpeval-statement-checked)
:q
