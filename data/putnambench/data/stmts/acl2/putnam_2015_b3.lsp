;; Statement-only formalization of PutnamBench corpus artifact putnam_2015_b3:
;; classification of real 2 by 2 arithmetic-progression matrices having a
;; higher power whose entries again form an arithmetic progression. This file
;; contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; A rational polynomial and isolating interval encode one real algebraic
;; number alpha. Rational functions of alpha encode all four entries, and
;; every finite tuple of real algebraic numbers admits such a common
;; primitive-element representation. Sturm-Tarski signs decide equality of
;; represented values exactly.
;;
;; Restricting counterexamples to real algebraic entries is bidirectionally
;; exact here. If the left-to-right implication fails, its particular natural
;; exponent leaves a finite system of polynomial equalities and inequalities,
;; so real-closed-field transfer supplies an algebraic counterexample. For the
;; other direction, the displayed solution is the union of two homogeneous
;; one-parameter families; replacing a parameter by a nonzero algebraic value
;; preserves every arithmetic-progression equality in every matrix power.
;; Thus an arbitrary-real counterexample exists exactly when an algebraic one
;; exists. The exponent witness remains internally and unboundedly quantified.

;; Rational polynomials in alpha use descending coefficient order.

(defun putnam-2015-b3-rp-p (p)
  (if (consp p)
      (and (rationalp (car p))
           (putnam-2015-b3-rp-p (cdr p)))
    (equal p nil)))

(defun putnam-2015-b3-rp-normalize (p)
  (if (consp p)
      (if (equal (car p) 0)
          (putnam-2015-b3-rp-normalize (cdr p))
        p)
    nil))

(defun putnam-2015-b3-rp-neg (p)
  (if (consp p)
      (cons (- (car p))
            (putnam-2015-b3-rp-neg (cdr p)))
    nil))

(defun putnam-2015-b3-rp-add-raw (p q)
  (declare (xargs :measure (+ (acl2-count p) (acl2-count q))))
  (cond
   ((endp p) q)
   ((endp q) p)
   ((< (len p) (len q))
    (cons (car q)
          (putnam-2015-b3-rp-add-raw p (cdr q))))
   ((< (len q) (len p))
    (cons (car p)
          (putnam-2015-b3-rp-add-raw (cdr p) q)))
   (t
    (cons (+ (car p) (car q))
          (putnam-2015-b3-rp-add-raw (cdr p) (cdr q))))))

(defun putnam-2015-b3-rp-add (p q)
  (putnam-2015-b3-rp-normalize
   (putnam-2015-b3-rp-add-raw p q)))

(defun putnam-2015-b3-rp-sub (p q)
  (putnam-2015-b3-rp-add
   p (putnam-2015-b3-rp-neg q)))

(defun putnam-2015-b3-rp-scale (c p)
  (if (consp p)
      (cons (* c (car p))
            (putnam-2015-b3-rp-scale c (cdr p)))
    nil))

(defun putnam-2015-b3-zeroes (n)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      nil
    (cons 0 (putnam-2015-b3-zeroes (- n 1)))))

(defun putnam-2015-b3-rp-scale-shift (c p shift)
  (append (putnam-2015-b3-rp-scale c p)
          (putnam-2015-b3-zeroes shift)))

(defun putnam-2015-b3-rp-mul-raw (p q)
  (if (consp p)
      (putnam-2015-b3-rp-add
       (putnam-2015-b3-rp-scale-shift
        (car p) q (len (cdr p)))
       (putnam-2015-b3-rp-mul-raw (cdr p) q))
    nil))

(defun putnam-2015-b3-rp-mul (p q)
  (putnam-2015-b3-rp-normalize
   (putnam-2015-b3-rp-mul-raw p q)))

(defun putnam-2015-b3-rp-eval-aux (p x accumulator)
  (if (consp p)
      (putnam-2015-b3-rp-eval-aux
       (cdr p) x (+ (* accumulator x) (car p)))
    accumulator))

(defun putnam-2015-b3-rp-eval (p x)
  (putnam-2015-b3-rp-eval-aux p x 0))

(defun putnam-2015-b3-rp-derivative-aux (p degree)
  (if (consp p)
      (if (zp degree)
          nil
        (cons (* degree (car p))
              (putnam-2015-b3-rp-derivative-aux
               (cdr p) (- degree 1))))
    nil))

(defun putnam-2015-b3-rp-derivative (p)
  (let ((p (putnam-2015-b3-rp-normalize p)))
    (putnam-2015-b3-rp-normalize
     (putnam-2015-b3-rp-derivative-aux
      p (nfix (- (len p) 1))))))

(defun putnam-2015-b3-rp-rem-fuel (p q fuel)
  (declare (xargs :measure (nfix fuel)))
  (let ((p (putnam-2015-b3-rp-normalize p))
        (q (putnam-2015-b3-rp-normalize q)))
    (if (or (zp fuel)
            (endp q)
            (< (len p) (len q)))
        p
      (putnam-2015-b3-rp-rem-fuel
       (putnam-2015-b3-rp-sub
        p
        (putnam-2015-b3-rp-scale-shift
         (/ (car p) (car q))
         q
         (- (len p) (len q))))
       q
       (- fuel 1)))))

(defun putnam-2015-b3-rp-rem (p q)
  (putnam-2015-b3-rp-rem-fuel
   p q (+ 1 (len (putnam-2015-b3-rp-normalize p)))))

(defun putnam-2015-b3-rp-sturm-tail (previous current fuel)
  (declare (xargs :measure (nfix fuel)))
  (let ((current (putnam-2015-b3-rp-normalize current)))
    (if (or (zp fuel) (endp current))
        nil
      (cons
       current
       (putnam-2015-b3-rp-sturm-tail
        current
        (putnam-2015-b3-rp-neg
         (putnam-2015-b3-rp-rem previous current))
        (- fuel 1))))))

(defun putnam-2015-b3-rp-sturm-sequence (p q)
  (let ((p (putnam-2015-b3-rp-normalize p))
        (q (putnam-2015-b3-rp-normalize q)))
    (if (endp p)
        nil
      (cons
       p
       (if (endp q)
           nil
         (cons
          q
          (putnam-2015-b3-rp-sturm-tail
           p q (+ 1 (len p) (len q)))))))))

(defun putnam-2015-b3-rational-sign (x)
  (cond ((< x 0) -1)
        ((< 0 x) 1)
        (t 0)))

(defun putnam-2015-b3-rp-variations-aux
    (polynomials x previous-sign)
  (if (consp polynomials)
      (let ((sign
             (putnam-2015-b3-rational-sign
              (putnam-2015-b3-rp-eval (car polynomials) x))))
        (if (equal sign 0)
            (putnam-2015-b3-rp-variations-aux
             (cdr polynomials) x previous-sign)
          (+ (if (and (not (equal previous-sign 0))
                      (not (equal sign previous-sign)))
                 1
               0)
             (putnam-2015-b3-rp-variations-aux
              (cdr polynomials) x sign))))
    0))

(defun putnam-2015-b3-rp-variations (polynomials x)
  (putnam-2015-b3-rp-variations-aux polynomials x 0))

(defun putnam-2015-b3-rp-cauchy-index (p q lower upper)
  (let ((sequence
         (putnam-2015-b3-rp-sturm-sequence p q)))
    (- (putnam-2015-b3-rp-variations sequence lower)
       (putnam-2015-b3-rp-variations sequence upper))))

(defun putnam-2015-b3-rp-root-count (p lower upper)
  (putnam-2015-b3-rp-cauchy-index
   p (putnam-2015-b3-rp-derivative p) lower upper))

(defun putnam-2015-b3-primitive-p (primitive lower upper)
  (and
   (putnam-2015-b3-rp-p primitive)
   (consp (putnam-2015-b3-rp-normalize primitive))
   (rationalp lower)
   (rationalp upper)
   (< lower upper)
   (not (equal (putnam-2015-b3-rp-eval primitive lower) 0))
   (not (equal (putnam-2015-b3-rp-eval primitive upper) 0))
   (equal
    (putnam-2015-b3-rp-root-count primitive lower upper)
    1)))

;; The Sturm-Tarski query over the single isolated root alpha is sign(g(alpha)).
(defun putnam-2015-b3-alg-sign
    (primitive lower upper g)
  (putnam-2015-b3-rp-cauchy-index
   primitive
   (putnam-2015-b3-rp-mul
    (putnam-2015-b3-rp-derivative primitive)
    g)
   lower
   upper))

;; A field element is (numerator denominator), evaluated at alpha.

(defun putnam-2015-b3-rf-numerator (value)
  (car value))

(defun putnam-2015-b3-rf-denominator (value)
  (cadr value))

(defun putnam-2015-b3-rf-code-p
    (primitive lower upper value)
  (and
   (true-listp value)
   (equal (len value) 2)
   (putnam-2015-b3-rp-p
    (putnam-2015-b3-rf-numerator value))
   (putnam-2015-b3-rp-p
    (putnam-2015-b3-rf-denominator value))
   (not
    (equal
     (putnam-2015-b3-alg-sign
      primitive lower upper
      (putnam-2015-b3-rf-denominator value))
     0))))

(defun putnam-2015-b3-rf-list-p
    (primitive lower upper values)
  (if (consp values)
      (and
       (putnam-2015-b3-rf-code-p
        primitive lower upper (car values))
       (putnam-2015-b3-rf-list-p
        primitive lower upper (cdr values)))
    (equal values nil)))

(defun putnam-2015-b3-rf-zero ()
  (list nil (list 1)))

(defun putnam-2015-b3-rf-one ()
  (list (list 1) (list 1)))

(defun putnam-2015-b3-rf-integer (value)
  (if (equal value 0)
      (putnam-2015-b3-rf-zero)
    (list (list value) (list 1))))

(defun putnam-2015-b3-rf-neg (value)
  (list
   (putnam-2015-b3-rp-neg
    (putnam-2015-b3-rf-numerator value))
   (putnam-2015-b3-rf-denominator value)))

(defun putnam-2015-b3-rf-add (left right)
  (list
   (putnam-2015-b3-rp-add
    (putnam-2015-b3-rp-mul
     (putnam-2015-b3-rf-numerator left)
     (putnam-2015-b3-rf-denominator right))
    (putnam-2015-b3-rp-mul
     (putnam-2015-b3-rf-numerator right)
     (putnam-2015-b3-rf-denominator left)))
   (putnam-2015-b3-rp-mul
    (putnam-2015-b3-rf-denominator left)
    (putnam-2015-b3-rf-denominator right))))

(defun putnam-2015-b3-rf-sub (left right)
  (putnam-2015-b3-rf-add
   left (putnam-2015-b3-rf-neg right)))

(defun putnam-2015-b3-rf-mul (left right)
  (list
   (putnam-2015-b3-rp-mul
    (putnam-2015-b3-rf-numerator left)
    (putnam-2015-b3-rf-numerator right))
   (putnam-2015-b3-rp-mul
    (putnam-2015-b3-rf-denominator left)
    (putnam-2015-b3-rf-denominator right))))

(defun putnam-2015-b3-rf-div (left right)
  (list
   (putnam-2015-b3-rp-mul
    (putnam-2015-b3-rf-numerator left)
    (putnam-2015-b3-rf-denominator right))
   (putnam-2015-b3-rp-mul
    (putnam-2015-b3-rf-denominator left)
    (putnam-2015-b3-rf-numerator right))))

(defun putnam-2015-b3-rf-sign
    (primitive lower upper value)
  (putnam-2015-b3-alg-sign
   primitive lower upper
   (putnam-2015-b3-rp-mul
    (putnam-2015-b3-rf-numerator value)
    (putnam-2015-b3-rf-denominator value))))

(defun putnam-2015-b3-rf-zero-p
    (primitive lower upper value)
  (equal
   (putnam-2015-b3-rf-sign
    primitive lower upper value)
   0))

(defun putnam-2015-b3-matrix-p
    (primitive lower upper matrix)
  (and
   (true-listp matrix)
   (equal (len matrix) 4)
   (putnam-2015-b3-rf-list-p
    primitive lower upper matrix)))

(defun putnam-2015-b3-matrix-multiply (left right)
  (let ((a (nth 0 left))
        (b (nth 1 left))
        (c (nth 2 left))
        (d (nth 3 left))
        (e (nth 0 right))
        (f (nth 1 right))
        (g (nth 2 right))
        (h (nth 3 right)))
    (list
     (putnam-2015-b3-rf-add
      (putnam-2015-b3-rf-mul a e)
      (putnam-2015-b3-rf-mul b g))
     (putnam-2015-b3-rf-add
      (putnam-2015-b3-rf-mul a f)
      (putnam-2015-b3-rf-mul b h))
     (putnam-2015-b3-rf-add
      (putnam-2015-b3-rf-mul c e)
      (putnam-2015-b3-rf-mul d g))
     (putnam-2015-b3-rf-add
      (putnam-2015-b3-rf-mul c f)
      (putnam-2015-b3-rf-mul d h)))))

(defun putnam-2015-b3-identity-matrix ()
  (list
   (putnam-2015-b3-rf-one)
   (putnam-2015-b3-rf-zero)
   (putnam-2015-b3-rf-zero)
   (putnam-2015-b3-rf-one)))

(defun putnam-2015-b3-matrix-power (matrix exponent)
  (declare (xargs :measure (nfix exponent)))
  (if (zp exponent)
      (putnam-2015-b3-identity-matrix)
    (putnam-2015-b3-matrix-multiply
     (putnam-2015-b3-matrix-power matrix (- exponent 1))
     matrix)))

(defun putnam-2015-b3-arithmetic-progression-p
    (primitive lower upper matrix)
  (let* ((a (nth 0 matrix))
         (b (nth 1 matrix))
         (c (nth 2 matrix))
         (d (nth 3 matrix))
         (first-difference
          (putnam-2015-b3-rf-sub b a))
         (second-difference
          (putnam-2015-b3-rf-sub c b))
         (third-difference
          (putnam-2015-b3-rf-sub d c)))
    (and
     (putnam-2015-b3-rf-zero-p
      primitive lower upper
      (putnam-2015-b3-rf-sub
       first-difference second-difference))
     (putnam-2015-b3-rf-zero-p
      primitive lower upper
      (putnam-2015-b3-rf-sub
       second-difference third-difference)))))

(defun putnam-2015-b3-solution-p
    (primitive lower upper matrix)
  (let* ((a (nth 0 matrix))
         (b (nth 1 matrix))
         (c (nth 2 matrix))
         (d (nth 3 matrix))
         (three-b
          (putnam-2015-b3-rf-add
           b (putnam-2015-b3-rf-add b b))))
    (or
     (and
      (putnam-2015-b3-rf-zero-p
       primitive lower upper
       (putnam-2015-b3-rf-sub a b))
      (putnam-2015-b3-rf-zero-p
       primitive lower upper
       (putnam-2015-b3-rf-sub a c))
      (putnam-2015-b3-rf-zero-p
       primitive lower upper
       (putnam-2015-b3-rf-sub a d)))
     (and
      (putnam-2015-b3-rf-zero-p
       primitive lower upper
       (putnam-2015-b3-rf-sub a three-b))
      (putnam-2015-b3-rf-zero-p
       primitive lower upper
       (putnam-2015-b3-rf-add b c))
      (putnam-2015-b3-rf-zero-p
       primitive lower upper
       (putnam-2015-b3-rf-add a d))))))

(defun-sk putnam-2015-b3-power-witness-exists-p
    (primitive lower upper matrix)
  (exists
   (exponent)
    (and
     (natp exponent)
     (< 1 exponent)
     (putnam-2015-b3-arithmetic-progression-p
      primitive lower upper
      (putnam-2015-b3-matrix-power matrix exponent)))))

(defun putnambench-putnam-2015-b3-statement
    (primitive lower upper matrix)
  (implies
   (and
    (putnam-2015-b3-primitive-p primitive lower upper)
    (putnam-2015-b3-matrix-p
     primitive lower upper matrix))
   (iff
    (and
     (putnam-2015-b3-arithmetic-progression-p
      primitive lower upper matrix)
     (putnam-2015-b3-power-witness-exists-p
      primitive lower upper matrix))
    (putnam-2015-b3-solution-p
     primitive lower upper matrix))))

(value-triple :itpeval-statement-checked)
:q
