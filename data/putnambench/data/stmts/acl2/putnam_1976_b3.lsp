;; Statement-only formalization of PutnamBench corpus artifact putnam_1976_b3:
;; lower bounds for the probability of intersecting a finite sequence of
;; high-probability events with pairwise independence whenever their indices
;; differ by more than one. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Standard ACL2 has no primitive real sort. A rational polynomial and a
;; rational isolating interval select one real algebraic number alpha. The
;; parameter a, recurrence values, and atom probabilities are rational
;; polynomials in alpha. Every finite algebraic-real tuple has such a common
;; primitive-element representation. Conversely every valid representation
;; denotes a real tuple. For each fixed n, all hypotheses and the negation of
;; the conclusion are first-order over real closed fields, so transfer between
;; the reals and the real algebraic numbers makes this representation
;; bidirectionally equivalent to the arbitrary-real statement.

(defun putnam-1976-b3-rational-polynomial-p (polynomial)
  (if (consp polynomial)
      (and (rationalp (car polynomial))
           (putnam-1976-b3-rational-polynomial-p (cdr polynomial)))
    (equal polynomial nil)))

(defun putnam-1976-b3-polynomial-list-p (polynomials)
  (if (consp polynomials)
      (and
       (putnam-1976-b3-rational-polynomial-p (car polynomials))
       (putnam-1976-b3-polynomial-list-p (cdr polynomials)))
    (equal polynomials nil)))

(defun putnam-1976-b3-poly-normalize (coefficients)
  (if (consp coefficients)
      (let ((tail
             (putnam-1976-b3-poly-normalize
              (cdr coefficients))))
        (if (and (equal (car coefficients) 0)
                 (not (consp tail)))
            nil
          (cons (car coefficients) tail)))
    nil))

(defun putnam-1976-b3-poly-add (left right)
  (cond
   ((consp left)
    (if (consp right)
        (cons (+ (car left) (car right))
              (putnam-1976-b3-poly-add
               (cdr left) (cdr right)))
      left))
   (t right)))

(defun putnam-1976-b3-poly-scale (scalar polynomial)
  (if (consp polynomial)
      (cons (* scalar (car polynomial))
            (putnam-1976-b3-poly-scale
             scalar (cdr polynomial)))
    nil))

(defun putnam-1976-b3-poly-negate (polynomial)
  (putnam-1976-b3-poly-scale -1 polynomial))

(defun putnam-1976-b3-poly-subtract (left right)
  (putnam-1976-b3-poly-normalize
   (putnam-1976-b3-poly-add
    left
    (putnam-1976-b3-poly-negate right))))

(defun putnam-1976-b3-poly-multiply (left right)
  (if (consp left)
      (putnam-1976-b3-poly-normalize
       (putnam-1976-b3-poly-add
        (putnam-1976-b3-poly-scale (car left) right)
        (cons 0
              (putnam-1976-b3-poly-multiply
               (cdr left) right))))
    nil))

(defun putnam-1976-b3-poly-derivative-aux
    (coefficients degree)
  (if (consp coefficients)
      (cons (* degree (car coefficients))
            (putnam-1976-b3-poly-derivative-aux
             (cdr coefficients) (+ degree 1)))
    nil))

(defun putnam-1976-b3-poly-derivative (polynomial)
  (if (consp polynomial)
      (putnam-1976-b3-poly-normalize
       (putnam-1976-b3-poly-derivative-aux
        (cdr polynomial) 1))
    nil))

(defun putnam-1976-b3-zero-list (count)
  (declare (xargs :measure (nfix count)))
  (if (zp count)
      nil
    (cons 0
          (putnam-1976-b3-zero-list (- count 1)))))

(defun putnam-1976-b3-poly-monomial (coefficient degree)
  (if (equal coefficient 0)
      nil
    (append
     (putnam-1976-b3-zero-list degree)
     (list coefficient))))

(defun putnam-1976-b3-poly-degree (polynomial)
  (let ((normalized
         (putnam-1976-b3-poly-normalize polynomial)))
    (if (consp normalized)
        (- (len normalized) 1)
      0)))

(defun putnam-1976-b3-poly-leading-coefficient (polynomial)
  (let ((normalized
         (putnam-1976-b3-poly-normalize polynomial)))
    (if (consp normalized)
        (nth (putnam-1976-b3-poly-degree normalized)
             normalized)
      0)))

(defun putnam-1976-b3-poly-divmod-steps
    (remainder divisor quotient steps)
  (declare (xargs :measure (nfix steps)))
  (if (zp steps)
      (cons
       (putnam-1976-b3-poly-normalize quotient)
       (putnam-1976-b3-poly-normalize remainder))
    (let* ((normalized-remainder
            (putnam-1976-b3-poly-normalize remainder))
           (normalized-divisor
            (putnam-1976-b3-poly-normalize divisor)))
      (if (or (not (consp normalized-remainder))
              (not (consp normalized-divisor))
              (< (putnam-1976-b3-poly-degree
                  normalized-remainder)
                 (putnam-1976-b3-poly-degree
                  normalized-divisor)))
          (cons
           (putnam-1976-b3-poly-normalize quotient)
           normalized-remainder)
        (let* ((degree-difference
                (- (putnam-1976-b3-poly-degree
                    normalized-remainder)
                   (putnam-1976-b3-poly-degree
                    normalized-divisor)))
               (coefficient
                (/ (putnam-1976-b3-poly-leading-coefficient
                    normalized-remainder)
                   (putnam-1976-b3-poly-leading-coefficient
                    normalized-divisor)))
               (term
                (putnam-1976-b3-poly-monomial
                 coefficient degree-difference)))
          (putnam-1976-b3-poly-divmod-steps
           (putnam-1976-b3-poly-subtract
            normalized-remainder
            (putnam-1976-b3-poly-multiply
             term normalized-divisor))
           normalized-divisor
           (putnam-1976-b3-poly-add quotient term)
           (- steps 1)))))))

(defun putnam-1976-b3-poly-divmod (dividend divisor)
  (putnam-1976-b3-poly-divmod-steps
   dividend
   divisor
   nil
   (+ 1 (len (putnam-1976-b3-poly-normalize dividend)))))

(defun putnam-1976-b3-poly-remainder (dividend divisor)
  (cdr (putnam-1976-b3-poly-divmod dividend divisor)))

(defun putnam-1976-b3-poly-gcd-steps (left right steps)
  (declare (xargs :measure (nfix steps)))
  (let ((normalized-left
         (putnam-1976-b3-poly-normalize left))
        (normalized-right
         (putnam-1976-b3-poly-normalize right)))
    (if (or (zp steps)
            (not (consp normalized-right)))
        normalized-left
      (putnam-1976-b3-poly-gcd-steps
       normalized-right
       (putnam-1976-b3-poly-remainder
        normalized-left normalized-right)
       (- steps 1)))))

(defun putnam-1976-b3-poly-gcd (left right)
  (putnam-1976-b3-poly-gcd-steps
   left
   right
   (+ 2
      (len (putnam-1976-b3-poly-normalize left))
      (len (putnam-1976-b3-poly-normalize right)))))

(defun putnam-1976-b3-sturm-tail
    (previous current steps)
  (declare (xargs :measure (nfix steps)))
  (let ((normalized-current
         (putnam-1976-b3-poly-normalize current)))
    (if (or (zp steps)
            (not (consp normalized-current)))
        nil
      (cons
       normalized-current
       (putnam-1976-b3-sturm-tail
        normalized-current
        (putnam-1976-b3-poly-negate
         (putnam-1976-b3-poly-remainder
          previous normalized-current))
        (- steps 1))))))

(defun putnam-1976-b3-sturm-chain (polynomial)
  (let ((normalized
         (putnam-1976-b3-poly-normalize polynomial)))
    (if (consp normalized)
        (cons
         normalized
         (putnam-1976-b3-sturm-tail
          normalized
          (putnam-1976-b3-poly-derivative normalized)
          (+ 1 (len normalized))))
      nil)))

(defun putnam-1976-b3-poly-evaluate (polynomial value)
  (if (consp polynomial)
      (+ (car polynomial)
         (* value
            (putnam-1976-b3-poly-evaluate
             (cdr polynomial) value)))
    0))

(defun putnam-1976-b3-chain-values-at (chain value)
  (if (consp chain)
      (cons
       (putnam-1976-b3-poly-evaluate (car chain) value)
       (putnam-1976-b3-chain-values-at
        (cdr chain) value))
    nil))

(defun putnam-1976-b3-sign (value)
  (cond
   ((< value 0) -1)
   ((< 0 value) 1)
   (t 0)))

(defun putnam-1976-b3-sign-variations-aux
    (values previous-sign)
  (if (consp values)
      (let ((current-sign
             (putnam-1976-b3-sign (car values))))
        (cond
         ((equal current-sign 0)
          (putnam-1976-b3-sign-variations-aux
           (cdr values) previous-sign))
         ((equal previous-sign 0)
          (putnam-1976-b3-sign-variations-aux
           (cdr values) current-sign))
         (t
          (+ (if (equal current-sign previous-sign) 0 1)
             (putnam-1976-b3-sign-variations-aux
              (cdr values) current-sign)))))
    0))

(defun putnam-1976-b3-sign-variations (values)
  (putnam-1976-b3-sign-variations-aux values 0))

(defun putnam-1976-b3-open-root-count
    (polynomial lower upper)
  (let ((chain
         (putnam-1976-b3-sturm-chain polynomial)))
    (- (putnam-1976-b3-sign-variations
        (putnam-1976-b3-chain-values-at chain lower))
       (putnam-1976-b3-sign-variations
        (putnam-1976-b3-chain-values-at chain upper)))))

(defun putnam-1976-b3-isolates-one-root-p
    (polynomial lower upper)
  (let ((normalized
         (putnam-1976-b3-poly-normalize polynomial)))
    (and
     (putnam-1976-b3-rational-polynomial-p normalized)
     (consp normalized)
     (< 0 (putnam-1976-b3-poly-degree normalized))
     (rationalp lower)
     (rationalp upper)
     (< lower upper)
     (not (equal
           (putnam-1976-b3-poly-evaluate normalized lower)
           0))
     (not (equal
           (putnam-1976-b3-poly-evaluate normalized upper)
           0))
     (equal
      (putnam-1976-b3-open-root-count
       normalized lower upper)
      1))))

(defun putnam-1976-b3-root-free-p
    (polynomial lower upper)
  (let ((normalized
         (putnam-1976-b3-poly-normalize polynomial)))
    (and
     (putnam-1976-b3-rational-polynomial-p normalized)
     (consp normalized)
     (rationalp lower)
     (rationalp upper)
     (< lower upper)
     (not (equal
           (putnam-1976-b3-poly-evaluate normalized lower)
           0))
     (not (equal
           (putnam-1976-b3-poly-evaluate normalized upper)
           0))
     (equal
      (putnam-1976-b3-open-root-count
       normalized lower upper)
      0))))

(defun putnam-1976-b3-zero-at-root-p
    (primitive value lower upper)
  (let ((normalized-value
         (putnam-1976-b3-poly-normalize value)))
    (or
     (not (consp normalized-value))
     (putnam-1976-b3-isolates-one-root-p
      (putnam-1976-b3-poly-gcd primitive normalized-value)
      lower
      upper))))

(defun putnam-1976-b3-sign-decidable-p
    (primitive value lower upper)
  (or
   (putnam-1976-b3-zero-at-root-p
    primitive value lower upper)
   (putnam-1976-b3-root-free-p value lower upper)))

(defun putnam-1976-b3-sign-at-root
    (primitive value lower upper)
  (if (putnam-1976-b3-zero-at-root-p
       primitive value lower upper)
      0
    (putnam-1976-b3-sign
     (putnam-1976-b3-poly-evaluate value lower))))

(defun putnam-1976-b3-positive-at-root-p
    (primitive value lower upper)
  (and
   (putnam-1976-b3-sign-decidable-p
    primitive value lower upper)
   (equal
    (putnam-1976-b3-sign-at-root
     primitive value lower upper)
    1)))

(defun putnam-1976-b3-nonnegative-at-root-p
    (primitive value lower upper)
  (and
   (putnam-1976-b3-sign-decidable-p
    primitive value lower upper)
   (not
    (equal
     (putnam-1976-b3-sign-at-root
      primitive value lower upper)
     -1))))

;; The finite family of source events is observed only through its joint law.
;; MASSES lists the probabilities of the 2^n Boolean truth assignments. Every
;; measurable source family induces exactly such masses. Conversely the same
;; list is realized on the finite Boolean sample space, so this removes no
;; probability space or event family relevant to the statement.

(defun putnam-1976-b3-bit-p (index bit)
  (equal
   (mod (floor index (expt 2 bit)) 2)
   1))

(defun putnam-1976-b3-sum-event-aux
    (masses index event-index)
  (if (consp masses)
      (putnam-1976-b3-poly-add
       (if (putnam-1976-b3-bit-p index event-index)
           (car masses)
         nil)
       (putnam-1976-b3-sum-event-aux
        (cdr masses) (+ index 1) event-index))
    nil))

(defun putnam-1976-b3-sum-event
    (masses event-index)
  (putnam-1976-b3-sum-event-aux
   masses 0 event-index))

(defun putnam-1976-b3-sum-two-events-aux
    (masses index first second)
  (if (consp masses)
      (putnam-1976-b3-poly-add
       (if (and
            (putnam-1976-b3-bit-p index first)
            (putnam-1976-b3-bit-p index second))
           (car masses)
         nil)
       (putnam-1976-b3-sum-two-events-aux
        (cdr masses) (+ index 1) first second))
    nil))

(defun putnam-1976-b3-sum-two-events
    (masses first second)
  (putnam-1976-b3-sum-two-events-aux
   masses 0 first second))

(defun putnam-1976-b3-poly-sum (polynomials)
  (if (consp polynomials)
      (putnam-1976-b3-poly-add
       (car polynomials)
       (putnam-1976-b3-poly-sum (cdr polynomials)))
    nil))

(defun putnam-1976-b3-all-nonnegative-p
    (primitive values lower upper)
  (if (consp values)
      (and
       (putnam-1976-b3-nonnegative-at-root-p
        primitive (car values) lower upper)
       (putnam-1976-b3-all-nonnegative-p
        primitive (cdr values) lower upper))
    (equal values nil)))

(defun putnam-1976-b3-all-positive-p
    (primitive values lower upper)
  (if (consp values)
      (and
       (putnam-1976-b3-positive-at-root-p
        primitive (car values) lower upper)
       (putnam-1976-b3-all-positive-p
        primitive (cdr values) lower upper))
    (equal values nil)))

(defun putnam-1976-b3-natural-range (count)
  (declare (xargs :measure (nfix count)))
  (if (zp count)
      nil
    (cons (- count 1)
          (putnam-1976-b3-natural-range (- count 1)))))

;; U-VALUES contains u_0 through u_n. The recurrence and initial values give
;; a unique infinite extension. Under 0 <= a < 1/4 that extension is positive:
;; its characteristic roots are nonnegative and
;; u_k = (r_1^(k+2)-r_2^(k+2))/(r_1-r_2), with the repeated-root limit at
;; a = 1/4. Thus checking the represented prefix is bidirectionally equivalent
;; to retaining the source sequence and its global positivity assumption.

(defun putnam-1976-b3-recurrence-p
    (primitive values a lower upper)
  (if (and (consp values)
           (consp (cdr values))
           (consp (cddr values)))
      (and
       (putnam-1976-b3-zero-at-root-p
        primitive
        (putnam-1976-b3-poly-subtract
         (caddr values)
         (putnam-1976-b3-poly-subtract
          (cadr values)
          (putnam-1976-b3-poly-multiply
           a (car values))))
        lower
        upper)
       (putnam-1976-b3-recurrence-p
        primitive (cdr values) a lower upper))
    t))

(defun putnam-1976-b3-event-bounds-p
    (primitive masses a lower upper indices)
  (if (consp indices)
    (let* ((event-index (car indices))
           (event-probability
            (putnam-1976-b3-sum-event
             masses event-index))
           (one-minus-a
            (putnam-1976-b3-poly-subtract
             (list 1) a))
           (gap
            (putnam-1976-b3-poly-subtract
             event-probability one-minus-a)))
      (and
       (putnam-1976-b3-nonnegative-at-root-p
        primitive gap lower upper)
       (putnam-1976-b3-event-bounds-p
        primitive masses a lower upper (cdr indices))))
    (equal indices nil)))

(defun putnam-1976-b3-pairwise-row-p
    (primitive masses event-index lower upper other-indices)
  (if (consp other-indices)
    (let* ((other-index (car other-indices))
           (intersection
            (putnam-1976-b3-sum-two-events
             masses event-index other-index))
           (product
            (putnam-1976-b3-poly-multiply
             (putnam-1976-b3-sum-event
              masses event-index)
             (putnam-1976-b3-sum-event
              masses other-index))))
      (and
       (if (< 1 (abs (- event-index other-index)))
           (putnam-1976-b3-zero-at-root-p
            primitive
            (putnam-1976-b3-poly-subtract
             intersection product)
            lower
            upper)
         t)
       (putnam-1976-b3-pairwise-row-p
        primitive
        masses
        event-index
        lower
        upper
        (cdr other-indices))))
    (equal other-indices nil)))

(defun putnam-1976-b3-pairwise-independence-p
    (primitive masses lower upper indices all-indices)
  (if (consp indices)
    (let ((event-index (car indices)))
      (and
       (putnam-1976-b3-pairwise-row-p
        primitive
        masses
        event-index
        lower
        upper
        all-indices)
       (putnam-1976-b3-pairwise-independence-p
        primitive
        masses
        lower
        upper
        (cdr indices)
        all-indices)))
    (equal indices nil)))

(defun putnam-1976-b3-common-context-p
    (primitive lower upper n a u-values masses)
  (let* ((quarter-minus-a
          (putnam-1976-b3-poly-subtract
           (list 1/4) a))
         (total-gap
          (putnam-1976-b3-poly-subtract
           (putnam-1976-b3-poly-sum masses)
           (list 1)))
         (u-zero-gap
          (putnam-1976-b3-poly-subtract
           (car u-values) (list 1)))
         (u-one-gap
          (putnam-1976-b3-poly-subtract
           (cadr u-values)
           (putnam-1976-b3-poly-subtract
            (list 1) a))))
    (and
     (putnam-1976-b3-isolates-one-root-p
      primitive lower upper)
     (natp n)
     (< 0 n)
     (putnam-1976-b3-rational-polynomial-p a)
     (putnam-1976-b3-polynomial-list-p u-values)
     (equal (len u-values) (+ n 1))
     (putnam-1976-b3-polynomial-list-p masses)
     (equal (len masses) (expt 2 n))
     (putnam-1976-b3-nonnegative-at-root-p
      primitive a lower upper)
     (putnam-1976-b3-positive-at-root-p
      primitive quarter-minus-a lower upper)
     (putnam-1976-b3-zero-at-root-p
      primitive u-zero-gap lower upper)
     (putnam-1976-b3-zero-at-root-p
      primitive u-one-gap lower upper)
     (putnam-1976-b3-recurrence-p
      primitive u-values a lower upper)
     (putnam-1976-b3-all-positive-p
      primitive u-values lower upper)
     (putnam-1976-b3-all-nonnegative-p
      primitive masses lower upper)
     (putnam-1976-b3-zero-at-root-p
      primitive total-gap lower upper)
     (putnam-1976-b3-event-bounds-p
      primitive
      masses
      a
      lower
      upper
      (putnam-1976-b3-natural-range n)))))

(defun putnam-1976-b3-conclusion-p
    (primitive lower upper n u-values masses)
  (let* ((all-events-probability
          (nth (- (expt 2 n) 1) masses))
         (gap
          (putnam-1976-b3-poly-subtract
           all-events-probability
           (nth n u-values))))
    (putnam-1976-b3-nonnegative-at-root-p
     primitive gap lower upper)))

(defun putnambench-putnam-1976-b3-statement
    (primitive lower upper n a u-values masses)
  (implies
   (and
    (putnam-1976-b3-common-context-p
     primitive lower upper n a u-values masses)
    (putnam-1976-b3-pairwise-independence-p
     primitive
     masses
     lower
     upper
     (putnam-1976-b3-natural-range n)
     (putnam-1976-b3-natural-range n)))
   (putnam-1976-b3-conclusion-p
    primitive lower upper n u-values masses)))

(value-triple :itpeval-statement-checked)
:q
