;; Statement-only formalization of thousand-theorems corpus artifact Q657482,
;; "Abel-Ruffini theorem": there exists a complex number algebraic over the
;; rationals that is not obtainable from rational numbers by field operations
;; and extraction of positive-degree roots. This file contains no proof.
;;
;; An algebraic complex number is represented exactly by rational polynomials
;; for its real and imaginary parts in one real algebraic primitive element.
;; A nonconstant rational polynomial and rational isolating interval select
;; that primitive element, and Sturm root counts decide equality and order exactly. Every
;; algebraic complex number has such a representation. Every finite radical
;; certificate also has a common primitive-element representation; an exact
;; embedding into that common field recodes the target number. Consequently
;; the predicate below is bidirectionally equivalent to the source existential
;; over algebraic elements of the usual complex numbers.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Polynomials are proper lists of rational coefficients in ascending degree
;; order. The empty list is the zero polynomial.

(defun q657482-rational-polynomial-p (polynomial)
  (if (consp polynomial)
      (and
       (rationalp (car polynomial))
       (q657482-rational-polynomial-p (cdr polynomial)))
    (equal polynomial nil)))

(defun q657482-poly-normalize (coefficients)
  (if (consp coefficients)
      (let ((tail
             (q657482-poly-normalize (cdr coefficients))))
        (if (and
             (equal (car coefficients) 0)
             (not (consp tail)))
            nil
          (cons (car coefficients) tail)))
    nil))

(defun q657482-poly-add (left right)
  (cond
   ((consp left)
    (if (consp right)
        (cons
         (+ (car left) (car right))
         (q657482-poly-add (cdr left) (cdr right)))
      left))
   (t right)))

(defun q657482-poly-scale (scalar polynomial)
  (if (consp polynomial)
      (cons
       (* scalar (car polynomial))
       (q657482-poly-scale scalar (cdr polynomial)))
    nil))

(defun q657482-poly-negate (polynomial)
  (q657482-poly-scale -1 polynomial))

(defun q657482-poly-subtract (left right)
  (q657482-poly-normalize
   (q657482-poly-add
    left
    (q657482-poly-negate right))))

(defun q657482-poly-multiply (left right)
  (if (consp left)
      (q657482-poly-normalize
       (q657482-poly-add
        (q657482-poly-scale (car left) right)
        (cons
         0
         (q657482-poly-multiply (cdr left) right))))
    nil))

(defun q657482-poly-compose (outer inner)
  (if (consp outer)
      (q657482-poly-normalize
       (q657482-poly-add
        (list (car outer))
        (q657482-poly-multiply
         inner
         (q657482-poly-compose (cdr outer) inner))))
    nil))

(defun q657482-poly-derivative-aux (coefficients degree)
  (if (consp coefficients)
      (cons
       (* degree (car coefficients))
       (q657482-poly-derivative-aux
        (cdr coefficients) (+ degree 1)))
    nil))

(defun q657482-poly-derivative (polynomial)
  (if (consp polynomial)
      (q657482-poly-normalize
       (q657482-poly-derivative-aux
        (cdr polynomial) 1))
    nil))

(defun q657482-zero-list (count)
  (declare (xargs :measure (nfix count)))
  (if (zp count)
      nil
    (cons
     0
     (q657482-zero-list (- count 1)))))

(defun q657482-poly-monomial (coefficient degree)
  (if (equal coefficient 0)
      nil
    (append
     (q657482-zero-list degree)
     (list coefficient))))

(defun q657482-poly-degree (polynomial)
  (let ((normalized
         (q657482-poly-normalize polynomial)))
    (if (consp normalized)
        (- (len normalized) 1)
      0)))

(defun q657482-poly-leading-coefficient (polynomial)
  (let ((normalized
         (q657482-poly-normalize polynomial)))
    (if (consp normalized)
        (nth (q657482-poly-degree normalized) normalized)
      0)))

;; The step bound makes polynomial long division total. Every nonterminal
;; division step lowers the current remainder degree.

(defun q657482-poly-divmod-steps
    (remainder divisor quotient steps)
  (declare (xargs :measure (nfix steps)))
  (if (zp steps)
      (cons
       (q657482-poly-normalize quotient)
       (q657482-poly-normalize remainder))
    (let* ((normalized-remainder
            (q657482-poly-normalize remainder))
           (normalized-divisor
            (q657482-poly-normalize divisor)))
      (if (or
           (not (consp normalized-remainder))
           (not (consp normalized-divisor))
           (<
            (q657482-poly-degree normalized-remainder)
            (q657482-poly-degree normalized-divisor)))
          (cons
           (q657482-poly-normalize quotient)
           normalized-remainder)
        (let* ((degree-difference
                (-
                 (q657482-poly-degree normalized-remainder)
                 (q657482-poly-degree normalized-divisor)))
               (coefficient
                (/
                 (q657482-poly-leading-coefficient
                  normalized-remainder)
                 (q657482-poly-leading-coefficient
                  normalized-divisor)))
               (term
                (q657482-poly-monomial
                 coefficient degree-difference)))
          (q657482-poly-divmod-steps
           (q657482-poly-subtract
            normalized-remainder
            (q657482-poly-multiply
             term normalized-divisor))
           normalized-divisor
           (q657482-poly-add quotient term)
           (- steps 1)))))))

(defun q657482-poly-divmod (dividend divisor)
  (q657482-poly-divmod-steps
   dividend
   divisor
   nil
   (+ 1
      (len (q657482-poly-normalize dividend)))))

(defun q657482-poly-remainder (dividend divisor)
  (cdr (q657482-poly-divmod dividend divisor)))

(defun q657482-poly-gcd-steps (left right steps)
  (declare (xargs :measure (nfix steps)))
  (let ((normalized-left
         (q657482-poly-normalize left))
        (normalized-right
         (q657482-poly-normalize right)))
    (if (or
         (zp steps)
         (not (consp normalized-right)))
        normalized-left
      (q657482-poly-gcd-steps
       normalized-right
       (q657482-poly-remainder
        normalized-left normalized-right)
       (- steps 1)))))

(defun q657482-poly-gcd (left right)
  (q657482-poly-gcd-steps
   left
   right
   (+ 2
      (len (q657482-poly-normalize left))
      (len (q657482-poly-normalize right)))))

(defun q657482-sturm-tail (previous current steps)
  (declare (xargs :measure (nfix steps)))
  (let ((normalized-current
         (q657482-poly-normalize current)))
    (if (or
         (zp steps)
         (not (consp normalized-current)))
        nil
      (cons
       normalized-current
       (q657482-sturm-tail
        normalized-current
        (q657482-poly-negate
         (q657482-poly-remainder
          previous normalized-current))
        (- steps 1))))))

(defun q657482-sturm-chain (polynomial)
  (let ((normalized
         (q657482-poly-normalize polynomial)))
    (if (consp normalized)
        (cons
         normalized
         (q657482-sturm-tail
          normalized
          (q657482-poly-derivative normalized)
          (+ 1 (len normalized))))
      nil)))

(defun q657482-poly-evaluate (polynomial value)
  (if (consp polynomial)
      (+
       (car polynomial)
       (* value
          (q657482-poly-evaluate
           (cdr polynomial) value)))
    0))

(defun q657482-chain-values-at (chain value)
  (if (consp chain)
      (cons
       (q657482-poly-evaluate (car chain) value)
       (q657482-chain-values-at (cdr chain) value))
    nil))

(defun q657482-sign (value)
  (cond
   ((< value 0) -1)
   ((< 0 value) 1)
   (t 0)))

(defun q657482-sign-variations-aux
    (values previous-sign)
  (if (consp values)
      (let ((current-sign
             (q657482-sign (car values))))
        (cond
         ((equal current-sign 0)
          (q657482-sign-variations-aux
           (cdr values) previous-sign))
         ((equal previous-sign 0)
          (q657482-sign-variations-aux
           (cdr values) current-sign))
         (t
          (+
           (if (equal current-sign previous-sign) 0 1)
           (q657482-sign-variations-aux
            (cdr values) current-sign)))))
    0))

(defun q657482-sign-variations (values)
  (q657482-sign-variations-aux values 0))

(defun q657482-open-root-count
    (polynomial lower upper)
  (let ((chain
         (q657482-sturm-chain polynomial)))
    (-
     (q657482-sign-variations
      (q657482-chain-values-at chain lower))
     (q657482-sign-variations
      (q657482-chain-values-at chain upper)))))

(defun q657482-isolates-one-root-p
    (polynomial lower upper)
  (let ((normalized
         (q657482-poly-normalize polynomial)))
    (and
     (q657482-rational-polynomial-p normalized)
     (consp normalized)
     (< 0 (q657482-poly-degree normalized))
     (rationalp lower)
     (rationalp upper)
     (< lower upper)
     (not
      (equal
       (q657482-poly-evaluate normalized lower)
       0))
     (not
      (equal
       (q657482-poly-evaluate normalized upper)
       0))
     (equal
      (q657482-open-root-count normalized lower upper)
      1))))

(defun q657482-root-free-p
    (polynomial lower upper)
  (let ((normalized
         (q657482-poly-normalize polynomial)))
    (and
     (q657482-rational-polynomial-p normalized)
     (consp normalized)
     (rationalp lower)
     (rationalp upper)
     (< lower upper)
     (not
      (equal
       (q657482-poly-evaluate normalized lower)
       0))
     (not
      (equal
       (q657482-poly-evaluate normalized upper)
       0))
     (equal
      (q657482-open-root-count normalized lower upper)
      0))))

;; The selected root of primitive is a zero of value exactly when their gcd
;; has the same unique root in the isolating interval.

(defun q657482-zero-at-isolated-root-p
    (primitive value lower upper)
  (let ((normalized-value
         (q657482-poly-normalize value)))
    (or
     (not (consp normalized-value))
     (q657482-isolates-one-root-p
      (q657482-poly-gcd primitive normalized-value)
      lower
      upper))))

;; A certificate interval may always be refined until every nonzero polynomial
;; tested for order has constant sign throughout the interval.

(defun q657482-sign-decidable-p
    (primitive value lower upper)
  (or
   (q657482-zero-at-isolated-root-p
    primitive value lower upper)
   (q657482-root-free-p value lower upper)))

(defun q657482-sign-at-isolated-root
    (primitive value lower upper)
  (if (q657482-zero-at-isolated-root-p
       primitive value lower upper)
      0
    (q657482-sign
     (q657482-poly-evaluate value lower))))

(defun q657482-positive-at-isolated-root-p
    (primitive value lower upper)
  (and
   (q657482-sign-decidable-p
    primitive value lower upper)
   (equal
    (q657482-sign-at-isolated-root
     primitive value lower upper)
    1)))

;; A complex value over the selected primitive is a pair of rational
;; polynomials giving its real and imaginary parts.

(defun q657482-complex-polynomial-p (value)
  (and
   (true-listp value)
   (equal (len value) 2)
   (q657482-rational-polynomial-p (nth 0 value))
   (q657482-rational-polynomial-p (nth 1 value))))

(defun q657482-complex-zero ()
  (list nil nil))

(defun q657482-complex-one ()
  (list (list 1) nil))

(defun q657482-complex-rational (value)
  (list (list value) nil))

(defun q657482-complex-negate (value)
  (list
   (q657482-poly-negate (nth 0 value))
   (q657482-poly-negate (nth 1 value))))

(defun q657482-complex-add (left right)
  (list
   (q657482-poly-add (nth 0 left) (nth 0 right))
   (q657482-poly-add (nth 1 left) (nth 1 right))))

(defun q657482-complex-multiply (left right)
  (list
   (q657482-poly-subtract
    (q657482-poly-multiply
     (nth 0 left) (nth 0 right))
    (q657482-poly-multiply
     (nth 1 left) (nth 1 right)))
   (q657482-poly-add
    (q657482-poly-multiply
     (nth 0 left) (nth 1 right))
    (q657482-poly-multiply
     (nth 1 left) (nth 0 right)))))

(defun q657482-complex-power (value exponent)
  (declare (xargs :measure (nfix exponent)))
  (if (zp exponent)
      (q657482-complex-one)
    (q657482-complex-multiply
     value
     (q657482-complex-power value (- exponent 1)))))

(defun q657482-complex-compose (value substitution)
  (list
   (q657482-poly-compose (nth 0 value) substitution)
   (q657482-poly-compose (nth 1 value) substitution)))

(defun q657482-complex-equal-p
    (primitive left right lower upper)
  (and
   (q657482-zero-at-isolated-root-p
    primitive
    (q657482-poly-subtract
     (nth 0 left) (nth 0 right))
    lower upper)
   (q657482-zero-at-isolated-root-p
    primitive
    (q657482-poly-subtract
     (nth 1 left) (nth 1 right))
    lower upper)))

(defun q657482-complex-zero-p
    (primitive value lower upper)
  (q657482-complex-equal-p
   primitive value (q657482-complex-zero) lower upper))

;; A five-component code consists of the primitive polynomial, its isolating
;; interval, and the real and imaginary polynomials. This codes exactly the
;; algebraic complex numbers: polynomial evaluation in an algebraic real is
;; algebraic, while the primitive-element theorem supplies such a code for
;; the real and imaginary parts of every algebraic complex number.

(defun q657482-algebraic-complex-code-p (number)
  (and
   (true-listp number)
   (equal (len number) 5)
   (q657482-isolates-one-root-p
    (nth 0 number) (nth 1 number) (nth 2 number))
   (q657482-rational-polynomial-p (nth 3 number))
   (q657482-rational-polynomial-p (nth 4 number))))

(defun q657482-number-value (number)
  (list (nth 3 number) (nth 4 number)))

;; A radical certificate is a finite topological derivation. Each step is a
;; pair whose car is an instruction and whose cdr is the exact complex output.
;; Natural-number arguments index earlier outputs, with zero denoting the most
;; recent one. The instructions present Mathlib's solvableByRad closure:
;; rational constants, field operations, and positive-degree root extraction.

(defun q657482-radical-step-p
    (primitive lower upper step previous-values)
  (let ((instruction (car step))
        (output (cdr step)))
    (and
     (consp step)
     (true-listp instruction)
     (consp instruction)
     (q657482-complex-polynomial-p output)
     (cond
      ((equal (car instruction) :rational)
       (and
        (equal (len instruction) 2)
        (rationalp (cadr instruction))
        (q657482-complex-equal-p
         primitive
         output
         (q657482-complex-rational (cadr instruction))
         lower upper)))
      ((equal (car instruction) :negate)
       (let ((index (cadr instruction)))
         (and
          (equal (len instruction) 2)
          (natp index)
          (< index (len previous-values))
          (q657482-complex-equal-p
           primitive
           output
           (q657482-complex-negate
            (nth index previous-values))
           lower upper))))
      ((equal (car instruction) :add)
       (let ((left-index (cadr instruction))
             (right-index (caddr instruction)))
         (and
          (equal (len instruction) 3)
          (natp left-index)
          (natp right-index)
          (< left-index (len previous-values))
          (< right-index (len previous-values))
          (q657482-complex-equal-p
           primitive
           output
           (q657482-complex-add
            (nth left-index previous-values)
            (nth right-index previous-values))
           lower upper))))
      ((equal (car instruction) :multiply)
       (let ((left-index (cadr instruction))
             (right-index (caddr instruction)))
         (and
          (equal (len instruction) 3)
          (natp left-index)
          (natp right-index)
          (< left-index (len previous-values))
          (< right-index (len previous-values))
          (q657482-complex-equal-p
           primitive
           output
           (q657482-complex-multiply
            (nth left-index previous-values)
            (nth right-index previous-values))
           lower upper))))
      ((equal (car instruction) :inverse)
       (let* ((index (cadr instruction))
              (argument (nth index previous-values)))
         (and
          (equal (len instruction) 2)
          (natp index)
          (< index (len previous-values))
          (if
           (q657482-complex-zero-p
            primitive argument lower upper)
           (q657482-complex-zero-p
            primitive output lower upper)
           (q657482-complex-equal-p
            primitive
            (q657482-complex-multiply argument output)
            (q657482-complex-one)
            lower upper)))))
      ((equal (car instruction) :root)
       (let ((degree (cadr instruction))
             (index (caddr instruction)))
         (and
          (equal (len instruction) 3)
          (natp degree)
          (< 0 degree)
          (natp index)
          (< index (len previous-values))
          (q657482-complex-equal-p
           primitive
           (q657482-complex-power output degree)
           (nth index previous-values)
           lower upper))))
      (t nil)))))

(defun q657482-radical-derivation-p
    (primitive lower upper steps previous-values)
  (if (consp steps)
      (let* ((step (car steps))
             (output (cdr step)))
        (and
         (q657482-radical-step-p
          primitive lower upper step previous-values)
         (q657482-radical-derivation-p
          primitive lower upper
          (cdr steps)
          (cons output previous-values))))
    (equal steps nil)))

(defun q657482-radical-derivation-final-value (steps)
  (if (consp steps)
      (if (consp (cdr steps))
          (q657482-radical-derivation-final-value
           (cdr steps))
        (cdr (car steps)))
    nil))

;; A radical certificate may require algebraic intermediates outside the
;; field used by the target's original code. The joint primitive contains both
;; fields. The embedding polynomial maps the original primitive into it; the
;; defining polynomial and isolating inequalities select the same original
;; root, and composition then recodes the target value exactly.

(defun q657482-solvable-witness-p
    (number joint-primitive joint-lower joint-upper embedding
            derivation)
  (let* ((original-primitive (nth 0 number))
         (original-lower (nth 1 number))
         (original-upper (nth 2 number))
         (original-value (q657482-number-value number))
         (recoded-value
          (q657482-complex-compose original-value embedding))
         (output
          (q657482-radical-derivation-final-value
           derivation)))
    (and
     (q657482-algebraic-complex-code-p number)
     (q657482-isolates-one-root-p
      joint-primitive joint-lower joint-upper)
     (q657482-rational-polynomial-p embedding)
     (q657482-zero-at-isolated-root-p
      joint-primitive
      (q657482-poly-compose
       original-primitive embedding)
      joint-lower joint-upper)
     (q657482-positive-at-isolated-root-p
      joint-primitive
      (q657482-poly-subtract
       embedding (list original-lower))
      joint-lower joint-upper)
     (q657482-positive-at-isolated-root-p
      joint-primitive
      (q657482-poly-subtract
       (list original-upper) embedding)
      joint-lower joint-upper)
     (consp derivation)
     (q657482-radical-derivation-p
      joint-primitive joint-lower joint-upper derivation nil)
     (q657482-complex-equal-p
      joint-primitive output recoded-value
      joint-lower joint-upper))))

(defun-sk q657482-solvable-by-radicals-p (number)
  (exists
   (joint-primitive joint-lower joint-upper embedding
                    derivation)
   (q657482-solvable-witness-p
    number joint-primitive joint-lower joint-upper embedding
    derivation)))

(defun-sk thousand-theorems-q657482-abel-ruffini-theorem-statement ()
  (exists (number)
    (and
     (q657482-algebraic-complex-code-p number)
     (not (q657482-solvable-by-radicals-p number)))))

(value-triple :itpeval-statement-checked)
:q
