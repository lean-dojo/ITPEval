;; Statement-only formalization of PutnamBench corpus artifact putnam_2003_a2:
;; the geometric mean of coordinatewise sums of two finite nonnegative real
;; sequences dominates the sum of their geometric means. This file contains
;; no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; For each positive list length n, introduce the unique nonnegative n-th
;; roots x, y, and z of product(a_i), product(b_i), and product(a_i+b_i).
;; The source inequality is then exactly x+y <= z. The root variables below
;; are universally quantified graph variables constrained by these defining
;; equations, not existential witnesses moved out of the conclusion.
;;
;; This reformulation is first-order over real closed fields for each n.
;; Consequently a real counterexample exists iff a real-algebraic one exists.
;; Every finite tuple of real algebraic entries and roots lies in Q(alpha) for
;; one real algebraic alpha. Rational polynomials in alpha, with alpha given
;; by a rational isolating interval, therefore preserve the arbitrary real
;; domain rather than restricting the source sequences to rational inputs.
;; Sturm-Tarski queries decide equality and order exactly.

;; Rational polynomials in alpha use descending coefficient order.

(defun putnam-2003-a2-rp-p (p)
  (if (consp p)
      (and (rationalp (car p))
           (putnam-2003-a2-rp-p (cdr p)))
    (equal p nil)))

(defun putnam-2003-a2-rp-normalize (p)
  (if (consp p)
      (if (equal (car p) 0)
          (putnam-2003-a2-rp-normalize (cdr p))
        p)
    nil))

(defun putnam-2003-a2-rp-neg (p)
  (if (consp p)
      (cons (- (car p))
            (putnam-2003-a2-rp-neg (cdr p)))
    nil))

(defun putnam-2003-a2-rp-add-raw (p q)
  (declare (xargs :measure (+ (acl2-count p) (acl2-count q))))
  (cond
   ((endp p) q)
   ((endp q) p)
   ((< (len p) (len q))
    (cons (car q)
          (putnam-2003-a2-rp-add-raw p (cdr q))))
   ((< (len q) (len p))
    (cons (car p)
          (putnam-2003-a2-rp-add-raw (cdr p) q)))
   (t
    (cons (+ (car p) (car q))
          (putnam-2003-a2-rp-add-raw (cdr p) (cdr q))))))

(defun putnam-2003-a2-rp-add (p q)
  (putnam-2003-a2-rp-normalize
   (putnam-2003-a2-rp-add-raw p q)))

(defun putnam-2003-a2-rp-sub (p q)
  (putnam-2003-a2-rp-add
   p (putnam-2003-a2-rp-neg q)))

(defun putnam-2003-a2-rp-scale (coefficient p)
  (if (consp p)
      (cons (* coefficient (car p))
            (putnam-2003-a2-rp-scale coefficient (cdr p)))
    nil))

(defun putnam-2003-a2-zeroes (n)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      nil
    (cons 0 (putnam-2003-a2-zeroes (- n 1)))))

(defun putnam-2003-a2-rp-scale-shift (coefficient p shift)
  (append
   (putnam-2003-a2-rp-scale coefficient p)
   (putnam-2003-a2-zeroes shift)))

(defun putnam-2003-a2-rp-mul-raw (p q)
  (if (consp p)
      (putnam-2003-a2-rp-add
       (putnam-2003-a2-rp-scale-shift
        (car p) q (len (cdr p)))
       (putnam-2003-a2-rp-mul-raw (cdr p) q))
    nil))

(defun putnam-2003-a2-rp-mul (p q)
  (putnam-2003-a2-rp-normalize
   (putnam-2003-a2-rp-mul-raw p q)))

(defun putnam-2003-a2-rp-eval-aux (p x accumulator)
  (if (consp p)
      (putnam-2003-a2-rp-eval-aux
       (cdr p) x (+ (* accumulator x) (car p)))
    accumulator))

(defun putnam-2003-a2-rp-eval (p x)
  (putnam-2003-a2-rp-eval-aux p x 0))

(defun putnam-2003-a2-rp-derivative-aux (p degree)
  (if (consp p)
      (if (zp degree)
          nil
        (cons (* degree (car p))
              (putnam-2003-a2-rp-derivative-aux
               (cdr p) (- degree 1))))
    nil))

(defun putnam-2003-a2-rp-derivative (p)
  (let ((p (putnam-2003-a2-rp-normalize p)))
    (putnam-2003-a2-rp-normalize
     (putnam-2003-a2-rp-derivative-aux
      p (nfix (- (len p) 1))))))

(defun putnam-2003-a2-rp-rem-fuel (p q fuel)
  (declare (xargs :measure (nfix fuel)))
  (let ((p (putnam-2003-a2-rp-normalize p))
        (q (putnam-2003-a2-rp-normalize q)))
    (if (or (zp fuel)
            (endp q)
            (< (len p) (len q)))
        p
      (putnam-2003-a2-rp-rem-fuel
       (putnam-2003-a2-rp-sub
        p
        (putnam-2003-a2-rp-scale-shift
         (/ (car p) (car q))
         q
         (- (len p) (len q))))
       q
       (- fuel 1)))))

(defun putnam-2003-a2-rp-rem (p q)
  (putnam-2003-a2-rp-rem-fuel
   p q (+ 1 (len (putnam-2003-a2-rp-normalize p)))))

(defun putnam-2003-a2-rp-sturm-tail (previous current fuel)
  (declare (xargs :measure (nfix fuel)))
  (let ((current (putnam-2003-a2-rp-normalize current)))
    (if (or (zp fuel) (endp current))
        nil
      (cons
       current
       (putnam-2003-a2-rp-sturm-tail
        current
        (putnam-2003-a2-rp-neg
         (putnam-2003-a2-rp-rem previous current))
        (- fuel 1))))))

(defun putnam-2003-a2-rp-sturm-sequence (p q)
  (let ((p (putnam-2003-a2-rp-normalize p))
        (q (putnam-2003-a2-rp-normalize q)))
    (if (endp p)
        nil
      (cons
       p
       (if (endp q)
           nil
         (cons
          q
          (putnam-2003-a2-rp-sturm-tail
           p q (+ 1 (len p) (len q)))))))))

(defun putnam-2003-a2-rational-sign (x)
  (cond ((< x 0) -1)
        ((< 0 x) 1)
        (t 0)))

(defun putnam-2003-a2-rp-variations-aux
    (polynomials x previous-sign)
  (if (consp polynomials)
      (let ((sign
             (putnam-2003-a2-rational-sign
              (putnam-2003-a2-rp-eval
               (car polynomials) x))))
        (if (equal sign 0)
            (putnam-2003-a2-rp-variations-aux
             (cdr polynomials) x previous-sign)
          (+ (if (and (not (equal previous-sign 0))
                      (not (equal sign previous-sign)))
                 1
               0)
             (putnam-2003-a2-rp-variations-aux
              (cdr polynomials) x sign))))
    0))

(defun putnam-2003-a2-rp-variations (polynomials x)
  (putnam-2003-a2-rp-variations-aux polynomials x 0))

(defun putnam-2003-a2-rp-cauchy-index (p q lower upper)
  (let ((sequence
         (putnam-2003-a2-rp-sturm-sequence p q)))
    (- (putnam-2003-a2-rp-variations sequence lower)
       (putnam-2003-a2-rp-variations sequence upper))))

(defun putnam-2003-a2-rp-root-count (p lower upper)
  (putnam-2003-a2-rp-cauchy-index
   p (putnam-2003-a2-rp-derivative p) lower upper))

(defun putnam-2003-a2-primitive-p (primitive lower upper)
  (and
   (putnam-2003-a2-rp-p primitive)
   (consp (putnam-2003-a2-rp-normalize primitive))
   (rationalp lower)
   (rationalp upper)
   (< lower upper)
   (not (equal
         (putnam-2003-a2-rp-eval primitive lower) 0))
   (not (equal
         (putnam-2003-a2-rp-eval primitive upper) 0))
   (equal
    (putnam-2003-a2-rp-root-count primitive lower upper)
    1)
   (not
    (equal
     (putnam-2003-a2-rp-cauchy-index
      primitive
      (putnam-2003-a2-rp-mul
       (putnam-2003-a2-rp-derivative primitive)
       (putnam-2003-a2-rp-derivative primitive))
      lower
      upper)
     0))))

;; For the isolated simple root alpha, this query is sign(value(alpha)).
(defun putnam-2003-a2-algebraic-sign
    (primitive lower upper value)
  (putnam-2003-a2-rp-cauchy-index
   primitive
   (putnam-2003-a2-rp-mul
    (putnam-2003-a2-rp-derivative primitive)
    value)
   lower
   upper))

(defun putnam-2003-a2-algebraic-equal-p
    (primitive lower upper left right)
  (equal
   (putnam-2003-a2-algebraic-sign
    primitive lower upper
    (putnam-2003-a2-rp-sub left right))
   0))

(defun putnam-2003-a2-algebraic-nonnegative-p
    (primitive lower upper value)
  (not
   (equal
    (putnam-2003-a2-algebraic-sign
     primitive lower upper value)
    -1)))

(defun putnam-2003-a2-algebraic-list-p (values)
  (if (consp values)
      (and
       (putnam-2003-a2-rp-p (car values))
       (putnam-2003-a2-algebraic-list-p (cdr values)))
    (equal values nil)))

(defun putnam-2003-a2-nonnegative-list-p
    (primitive lower upper values)
  (if (consp values)
      (and
       (putnam-2003-a2-algebraic-nonnegative-p
        primitive lower upper (car values))
       (putnam-2003-a2-nonnegative-list-p
        primitive lower upper (cdr values)))
    (equal values nil)))

(defun putnam-2003-a2-pointwise-sum (left right)
  (if (and (consp left) (consp right))
      (cons
       (putnam-2003-a2-rp-add (car left) (car right))
       (putnam-2003-a2-pointwise-sum
        (cdr left) (cdr right)))
    nil))

(defun putnam-2003-a2-product (values)
  (if (consp values)
      (putnam-2003-a2-rp-mul
       (car values)
       (putnam-2003-a2-product (cdr values)))
    (list 1)))

(defun putnam-2003-a2-power (value exponent)
  (declare (xargs :measure (nfix exponent)))
  (if (zp exponent)
      (list 1)
    (putnam-2003-a2-rp-mul
     value
     (putnam-2003-a2-power value (- exponent 1)))))

(defun putnam-2003-a2-nonnegative-root-p
    (primitive lower upper radicand exponent root)
  (and
   (putnam-2003-a2-algebraic-nonnegative-p
    primitive lower upper root)
   (putnam-2003-a2-algebraic-equal-p
    primitive lower upper
    (putnam-2003-a2-power root exponent)
    radicand)))

(defun putnambench-putnam-2003-a2-statement
    (primitive lower upper a b a-root b-root sum-root)
  (let* ((n (len a))
         (a-product (putnam-2003-a2-product a))
         (b-product (putnam-2003-a2-product b))
         (sum-product
          (putnam-2003-a2-product
           (putnam-2003-a2-pointwise-sum a b))))
    (implies
     (and
      (putnam-2003-a2-primitive-p primitive lower upper)
      (consp a)
      (equal (len b) n)
      (putnam-2003-a2-algebraic-list-p a)
      (putnam-2003-a2-algebraic-list-p b)
      (putnam-2003-a2-nonnegative-list-p
       primitive lower upper a)
      (putnam-2003-a2-nonnegative-list-p
       primitive lower upper b)
      (putnam-2003-a2-rp-p a-root)
      (putnam-2003-a2-rp-p b-root)
      (putnam-2003-a2-rp-p sum-root)
      (putnam-2003-a2-nonnegative-root-p
       primitive lower upper a-product n a-root)
      (putnam-2003-a2-nonnegative-root-p
       primitive lower upper b-product n b-root)
      (putnam-2003-a2-nonnegative-root-p
       primitive lower upper sum-product n sum-root))
     (putnam-2003-a2-algebraic-nonnegative-p
      primitive lower upper
      (putnam-2003-a2-rp-sub
       sum-root
       (putnam-2003-a2-rp-add a-root b-root))))))

(value-triple :itpeval-statement-checked)
:q
