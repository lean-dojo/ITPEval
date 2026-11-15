;; Statement-only formalization of miniF2F corpus artifact imo_1973_p3:
;; if a reciprocal quartic x^4+a*x^3+b*x^2+a*x+1 has a real root, then
;; 4/5 is at most a^2+b^2. This file contains no proof.
;;
;; Standard ACL2 has no primitive arbitrary-real sort. This encoding does not
;; restrict the source variables to rationals: one rational polynomial and a
;; rational isolating interval select a real algebraic primitive alpha, while
;; rational polynomials in alpha encode a, b, and x. Sturm-Tarski queries
;; decide equality and order exactly. Every finite tuple of real algebraic
;; numbers has such a common primitive representation, and every valid
;; representation denotes an actual real tuple.
;;
;; A real counterexample exists iff an algebraic-real counterexample exists,
;; by real-closed-field transfer. Also, since the conclusion is independent of
;; x, (exists x, P(x)) -> Q is equivalent to forall x, P(x) -> Q. Therefore
;; the universally quantified ACL2 arguments below preserve both the internal
;; root existential and the full real domains bidirectionally.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Polynomials in alpha use descending rational coefficient order.
(defun imo-1973-p3-rational-polynomial-p (polynomial)
  (if (consp polynomial)
      (and (rationalp (car polynomial))
           (imo-1973-p3-rational-polynomial-p (cdr polynomial)))
    (equal polynomial nil)))

(defun imo-1973-p3-poly-normalize (polynomial)
  (if (consp polynomial)
      (if (equal (car polynomial) 0)
          (imo-1973-p3-poly-normalize (cdr polynomial))
        polynomial)
    nil))

(defun imo-1973-p3-poly-negate (polynomial)
  (if (consp polynomial)
      (cons (- (car polynomial))
            (imo-1973-p3-poly-negate (cdr polynomial)))
    nil))

(defun imo-1973-p3-poly-add-raw (left right)
  (declare (xargs :measure (+ (acl2-count left) (acl2-count right))))
  (cond
   ((endp left) right)
   ((endp right) left)
   ((< (len left) (len right))
    (cons (car right)
          (imo-1973-p3-poly-add-raw left (cdr right))))
   ((< (len right) (len left))
    (cons (car left)
          (imo-1973-p3-poly-add-raw (cdr left) right)))
   (t
    (cons (+ (car left) (car right))
          (imo-1973-p3-poly-add-raw (cdr left) (cdr right))))))

(defun imo-1973-p3-poly-add (left right)
  (imo-1973-p3-poly-normalize
   (imo-1973-p3-poly-add-raw left right)))

(defun imo-1973-p3-poly-subtract (left right)
  (imo-1973-p3-poly-add
   left (imo-1973-p3-poly-negate right)))

(defun imo-1973-p3-poly-scale (coefficient polynomial)
  (if (consp polynomial)
      (cons (* coefficient (car polynomial))
            (imo-1973-p3-poly-scale coefficient (cdr polynomial)))
    nil))

(defun imo-1973-p3-zeroes (count)
  (declare (xargs :measure (nfix count)))
  (if (zp count)
      nil
    (cons 0 (imo-1973-p3-zeroes (- count 1)))))

(defun imo-1973-p3-poly-scale-shift
    (coefficient polynomial shift)
  (append
   (imo-1973-p3-poly-scale coefficient polynomial)
   (imo-1973-p3-zeroes shift)))

(defun imo-1973-p3-poly-multiply-raw (left right)
  (if (consp left)
      (imo-1973-p3-poly-add
       (imo-1973-p3-poly-scale-shift
        (car left) right (len (cdr left)))
       (imo-1973-p3-poly-multiply-raw (cdr left) right))
    nil))

(defun imo-1973-p3-poly-multiply (left right)
  (imo-1973-p3-poly-normalize
   (imo-1973-p3-poly-multiply-raw left right)))

(defun imo-1973-p3-poly-square (polynomial)
  (imo-1973-p3-poly-multiply polynomial polynomial))

(defun imo-1973-p3-poly-evaluate-aux
    (polynomial value accumulator)
  (if (consp polynomial)
      (imo-1973-p3-poly-evaluate-aux
       (cdr polynomial)
       value
       (+ (* accumulator value) (car polynomial)))
    accumulator))

(defun imo-1973-p3-poly-evaluate (polynomial value)
  (imo-1973-p3-poly-evaluate-aux polynomial value 0))

(defun imo-1973-p3-poly-derivative-aux
    (polynomial degree)
  (if (consp polynomial)
      (if (zp degree)
          nil
        (cons (* degree (car polynomial))
              (imo-1973-p3-poly-derivative-aux
               (cdr polynomial) (- degree 1))))
    nil))

(defun imo-1973-p3-poly-derivative (polynomial)
  (let ((normalized
         (imo-1973-p3-poly-normalize polynomial)))
    (imo-1973-p3-poly-normalize
     (imo-1973-p3-poly-derivative-aux
      normalized
      (nfix (- (len normalized) 1))))))

(defun imo-1973-p3-poly-remainder-steps
    (dividend divisor steps)
  (declare (xargs :measure (nfix steps)))
  (let ((dividend
         (imo-1973-p3-poly-normalize dividend))
        (divisor
         (imo-1973-p3-poly-normalize divisor)))
    (if (or (zp steps)
            (endp divisor)
            (< (len dividend) (len divisor)))
        dividend
      (imo-1973-p3-poly-remainder-steps
       (imo-1973-p3-poly-subtract
        dividend
        (imo-1973-p3-poly-scale-shift
         (/ (car dividend) (car divisor))
         divisor
         (- (len dividend) (len divisor))))
       divisor
       (- steps 1)))))

(defun imo-1973-p3-poly-remainder (dividend divisor)
  (imo-1973-p3-poly-remainder-steps
   dividend
   divisor
   (+ 1 (len (imo-1973-p3-poly-normalize dividend)))))

(defun imo-1973-p3-sturm-tail (previous current steps)
  (declare (xargs :measure (nfix steps)))
  (let ((current
         (imo-1973-p3-poly-normalize current)))
    (if (or (zp steps) (endp current))
        nil
      (cons
       current
       (imo-1973-p3-sturm-tail
        current
        (imo-1973-p3-poly-negate
         (imo-1973-p3-poly-remainder previous current))
        (- steps 1))))))

(defun imo-1973-p3-sturm-sequence (first second)
  (let ((first
         (imo-1973-p3-poly-normalize first))
        (second
         (imo-1973-p3-poly-normalize second)))
    (if (endp first)
        nil
      (cons
       first
       (if (endp second)
           nil
         (cons
          second
          (imo-1973-p3-sturm-tail
           first second (+ 1 (len first) (len second)))))))))

(defun imo-1973-p3-rational-sign (value)
  (cond
   ((< value 0) -1)
   ((< 0 value) 1)
   (t 0)))

(defun imo-1973-p3-sign-variations-aux
    (polynomials value previous-sign)
  (if (consp polynomials)
      (let ((current-sign
             (imo-1973-p3-rational-sign
              (imo-1973-p3-poly-evaluate
               (car polynomials) value))))
        (if (equal current-sign 0)
            (imo-1973-p3-sign-variations-aux
             (cdr polynomials) value previous-sign)
          (+ (if (and (not (equal previous-sign 0))
                      (not (equal current-sign previous-sign)))
                 1
               0)
             (imo-1973-p3-sign-variations-aux
              (cdr polynomials) value current-sign))))
    0))

(defun imo-1973-p3-sign-variations (polynomials value)
  (imo-1973-p3-sign-variations-aux polynomials value 0))

(defun imo-1973-p3-cauchy-index
    (first second lower upper)
  (let ((sequence
         (imo-1973-p3-sturm-sequence first second)))
    (- (imo-1973-p3-sign-variations sequence lower)
       (imo-1973-p3-sign-variations sequence upper))))

(defun imo-1973-p3-root-count (polynomial lower upper)
  (imo-1973-p3-cauchy-index
   polynomial
   (imo-1973-p3-poly-derivative polynomial)
   lower
   upper))

(defun imo-1973-p3-primitive-p
    (primitive lower upper)
  (and
   (imo-1973-p3-rational-polynomial-p primitive)
   (consp (imo-1973-p3-poly-normalize primitive))
   (rationalp lower)
   (rationalp upper)
   (< lower upper)
   (not
    (equal
     (imo-1973-p3-poly-evaluate primitive lower)
     0))
   (not
    (equal
     (imo-1973-p3-poly-evaluate primitive upper)
     0))
   (equal
    (imo-1973-p3-root-count primitive lower upper)
    1)
   ;; The unique selected root is simple, as required by the sign query.
   (not
    (equal
     (imo-1973-p3-cauchy-index
      primitive
      (imo-1973-p3-poly-square
       (imo-1973-p3-poly-derivative primitive))
      lower
      upper)
     0))))

;; At the unique isolated simple root alpha, this Sturm-Tarski query is the
;; sign of VALUE(alpha).
(defun imo-1973-p3-algebraic-sign
    (primitive lower upper value)
  (imo-1973-p3-cauchy-index
   primitive
   (imo-1973-p3-poly-multiply
    (imo-1973-p3-poly-derivative primitive)
    value)
   lower
   upper))

(defun imo-1973-p3-statement
    (primitive lower upper a b x)
  (let* ((x-square
          (imo-1973-p3-poly-square x))
         (x-cube
          (imo-1973-p3-poly-multiply x-square x))
         (x-fourth
          (imo-1973-p3-poly-square x-square))
         (quartic-value
          (imo-1973-p3-poly-add
           (imo-1973-p3-poly-add
            (imo-1973-p3-poly-add
             (imo-1973-p3-poly-add
              x-fourth
              (imo-1973-p3-poly-multiply a x-cube))
             (imo-1973-p3-poly-multiply b x-square))
            (imo-1973-p3-poly-multiply a x))
           (list 1)))
         (scaled-bound-difference
          (imo-1973-p3-poly-subtract
           (imo-1973-p3-poly-scale
            5
            (imo-1973-p3-poly-add
             (imo-1973-p3-poly-square a)
             (imo-1973-p3-poly-square b)))
           (list 4))))
    (implies
     (and
      (imo-1973-p3-primitive-p primitive lower upper)
      (imo-1973-p3-rational-polynomial-p a)
      (imo-1973-p3-rational-polynomial-p b)
      (imo-1973-p3-rational-polynomial-p x)
      (equal
       (imo-1973-p3-algebraic-sign
        primitive lower upper quartic-value)
       0))
     (<=
      0
      (imo-1973-p3-algebraic-sign
       primitive lower upper scaled-bound-difference)))))

(value-triple :itpeval-statement-checked)
:q
