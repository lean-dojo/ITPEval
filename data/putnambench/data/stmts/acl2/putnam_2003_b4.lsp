;; Statement-only formalization of PutnamBench corpus artifact putnam_2003_b4:
;; rationality of the sum of two roots of an integer quartic, when distinct
;; from the other two roots' sum, forces their product to be rational. This
;; file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Every root of the nonzero integer quartic is real algebraic. Every finite
;; tuple of real algebraic numbers lies in Q(alpha) for one real algebraic
;; alpha. A rational polynomial and rational isolating interval encode alpha,
;; and rational polynomials in alpha encode the four roots. Sturm-Tarski
;; queries decide equality exactly, so this covers all source root tuples
;; without restricting them to rational roots.
;;
;; Expanding a*(z-r1)*(z-r2)*(z-r3)*(z-r4) gives the four Vieta identities
;; used below, which are equivalent to the source's universal polynomial
;; identity. If s=r1+r2 is rational and t=r3+r4 differs from s, then
;;
;;   u = c/a-s*t = r1*r2+r3*r4,
;;   v = -d/a   = (r1*r2)*t+(r3*r4)*s,
;;   r1*r2      = (v-s*u)/(t-s).
;;
;; The rational witness s occurs universally in the ACL2 statement:
;; forall s, (s rational and s=r1+r2) implies the conclusion. This is
;; logically equivalent to the source implication whose antecedent says that
;; r1+r2 is rational. The conclusion keeps its rational witness existentially
;; quantified inside a separate predicate.

;; Rational polynomials use descending coefficient order.

(defun putnam-2003-b4-rp-p (p)
  (if (consp p)
      (and (rationalp (car p))
           (putnam-2003-b4-rp-p (cdr p)))
    (equal p nil)))

(defun putnam-2003-b4-rp-normalize (p)
  (if (consp p)
      (if (equal (car p) 0)
          (putnam-2003-b4-rp-normalize (cdr p))
        p)
    nil))

(defun putnam-2003-b4-rp-neg (p)
  (if (consp p)
      (cons (- (car p))
            (putnam-2003-b4-rp-neg (cdr p)))
    nil))

(defun putnam-2003-b4-rp-add-raw (p q)
  (declare (xargs :measure (+ (acl2-count p) (acl2-count q))))
  (cond
   ((endp p) q)
   ((endp q) p)
   ((< (len p) (len q))
    (cons (car q)
          (putnam-2003-b4-rp-add-raw p (cdr q))))
   ((< (len q) (len p))
    (cons (car p)
          (putnam-2003-b4-rp-add-raw (cdr p) q)))
   (t
    (cons (+ (car p) (car q))
          (putnam-2003-b4-rp-add-raw (cdr p) (cdr q))))))

(defun putnam-2003-b4-rp-add (p q)
  (putnam-2003-b4-rp-normalize
   (putnam-2003-b4-rp-add-raw p q)))

(defun putnam-2003-b4-rp-sub (p q)
  (putnam-2003-b4-rp-add p (putnam-2003-b4-rp-neg q)))

(defun putnam-2003-b4-rp-scale (c p)
  (if (consp p)
      (cons (* c (car p))
            (putnam-2003-b4-rp-scale c (cdr p)))
    nil))

(defun putnam-2003-b4-zeroes (n)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      nil
    (cons 0 (putnam-2003-b4-zeroes (- n 1)))))

(defun putnam-2003-b4-rp-scale-shift (c p shift)
  (append (putnam-2003-b4-rp-scale c p)
          (putnam-2003-b4-zeroes shift)))

(defun putnam-2003-b4-rp-mul-raw (p q)
  (if (consp p)
      (putnam-2003-b4-rp-add
       (putnam-2003-b4-rp-scale-shift
        (car p) q (len (cdr p)))
       (putnam-2003-b4-rp-mul-raw (cdr p) q))
    nil))

(defun putnam-2003-b4-rp-mul (p q)
  (putnam-2003-b4-rp-normalize
   (putnam-2003-b4-rp-mul-raw p q)))

(defun putnam-2003-b4-rp-eval-aux (p x accumulator)
  (if (consp p)
      (putnam-2003-b4-rp-eval-aux
       (cdr p) x (+ (* accumulator x) (car p)))
    accumulator))

(defun putnam-2003-b4-rp-eval (p x)
  (putnam-2003-b4-rp-eval-aux p x 0))

(defun putnam-2003-b4-rp-derivative-aux (p degree)
  (if (consp p)
      (if (zp degree)
          nil
        (cons (* degree (car p))
              (putnam-2003-b4-rp-derivative-aux
               (cdr p) (- degree 1))))
    nil))

(defun putnam-2003-b4-rp-derivative (p)
  (let ((p (putnam-2003-b4-rp-normalize p)))
    (putnam-2003-b4-rp-normalize
     (putnam-2003-b4-rp-derivative-aux
      p (nfix (- (len p) 1))))))

(defun putnam-2003-b4-rp-rem-fuel (p q fuel)
  (declare (xargs :measure (nfix fuel)))
  (let ((p (putnam-2003-b4-rp-normalize p))
        (q (putnam-2003-b4-rp-normalize q)))
    (if (or (zp fuel)
            (endp q)
            (< (len p) (len q)))
        p
      (putnam-2003-b4-rp-rem-fuel
       (putnam-2003-b4-rp-sub
        p
        (putnam-2003-b4-rp-scale-shift
         (/ (car p) (car q))
         q
         (- (len p) (len q))))
       q
       (- fuel 1)))))

(defun putnam-2003-b4-rp-rem (p q)
  (putnam-2003-b4-rp-rem-fuel
   p q (+ 1 (len (putnam-2003-b4-rp-normalize p)))))

(defun putnam-2003-b4-rp-sturm-tail (previous current fuel)
  (declare (xargs :measure (nfix fuel)))
  (let ((current (putnam-2003-b4-rp-normalize current)))
    (if (or (zp fuel) (endp current))
        nil
      (cons
       current
       (putnam-2003-b4-rp-sturm-tail
        current
        (putnam-2003-b4-rp-neg
         (putnam-2003-b4-rp-rem previous current))
        (- fuel 1))))))

(defun putnam-2003-b4-rp-sturm-sequence (p q)
  (let ((p (putnam-2003-b4-rp-normalize p))
        (q (putnam-2003-b4-rp-normalize q)))
    (if (endp p)
        nil
      (cons
       p
       (if (endp q)
           nil
         (cons
          q
          (putnam-2003-b4-rp-sturm-tail
           p q (+ 1 (len p) (len q)))))))))

(defun putnam-2003-b4-rational-sign (x)
  (cond ((< x 0) -1)
        ((< 0 x) 1)
        (t 0)))

(defun putnam-2003-b4-rp-variations-aux
    (polynomials x previous-sign)
  (if (consp polynomials)
      (let ((sign
             (putnam-2003-b4-rational-sign
              (putnam-2003-b4-rp-eval (car polynomials) x))))
        (if (equal sign 0)
            (putnam-2003-b4-rp-variations-aux
             (cdr polynomials) x previous-sign)
          (+ (if (and (not (equal previous-sign 0))
                      (not (equal sign previous-sign)))
                 1
               0)
             (putnam-2003-b4-rp-variations-aux
              (cdr polynomials) x sign))))
    0))

(defun putnam-2003-b4-rp-variations (polynomials x)
  (putnam-2003-b4-rp-variations-aux polynomials x 0))

(defun putnam-2003-b4-rp-cauchy-index (p q lower upper)
  (let ((sequence
         (putnam-2003-b4-rp-sturm-sequence p q)))
    (- (putnam-2003-b4-rp-variations sequence lower)
       (putnam-2003-b4-rp-variations sequence upper))))

(defun putnam-2003-b4-rp-root-count (p lower upper)
  (putnam-2003-b4-rp-cauchy-index
   p (putnam-2003-b4-rp-derivative p) lower upper))

(defun putnam-2003-b4-primitive-p (primitive lower upper)
  (and
   (putnam-2003-b4-rp-p primitive)
   (consp (putnam-2003-b4-rp-normalize primitive))
   (rationalp lower)
   (rationalp upper)
   (< lower upper)
   (not (equal (putnam-2003-b4-rp-eval primitive lower) 0))
   (not (equal (putnam-2003-b4-rp-eval primitive upper) 0))
   (equal
    (putnam-2003-b4-rp-root-count primitive lower upper)
    1)
   (not
    (equal
     (putnam-2003-b4-rp-cauchy-index
      primitive
      (putnam-2003-b4-rp-mul
       (putnam-2003-b4-rp-derivative primitive)
       (putnam-2003-b4-rp-derivative primitive))
      lower
      upper)
     0))))

;; For the isolated simple root alpha, this query is sign(g(alpha)).
(defun putnam-2003-b4-alg-sign (primitive lower upper g)
  (putnam-2003-b4-rp-cauchy-index
   primitive
   (putnam-2003-b4-rp-mul
    (putnam-2003-b4-rp-derivative primitive)
    g)
   lower
   upper))

(defun putnam-2003-b4-alg-equal-p
    (primitive lower upper left right)
  (equal
   (putnam-2003-b4-alg-sign
    primitive lower upper
    (putnam-2003-b4-rp-sub left right))
   0))

(defun putnam-2003-b4-root-sum (r1 r2 r3 r4)
  (putnam-2003-b4-rp-add
   r1
   (putnam-2003-b4-rp-add
    r2 (putnam-2003-b4-rp-add r3 r4))))

(defun putnam-2003-b4-pair-sum (r1 r2 r3 r4)
  (putnam-2003-b4-rp-add
   (putnam-2003-b4-rp-mul r1 r2)
   (putnam-2003-b4-rp-add
    (putnam-2003-b4-rp-mul r1 r3)
    (putnam-2003-b4-rp-add
     (putnam-2003-b4-rp-mul r1 r4)
     (putnam-2003-b4-rp-add
      (putnam-2003-b4-rp-mul r2 r3)
      (putnam-2003-b4-rp-add
       (putnam-2003-b4-rp-mul r2 r4)
       (putnam-2003-b4-rp-mul r3 r4)))))))

(defun putnam-2003-b4-triple-sum (r1 r2 r3 r4)
  (putnam-2003-b4-rp-add
   (putnam-2003-b4-rp-mul
    (putnam-2003-b4-rp-mul r1 r2) r3)
   (putnam-2003-b4-rp-add
    (putnam-2003-b4-rp-mul
     (putnam-2003-b4-rp-mul r1 r2) r4)
    (putnam-2003-b4-rp-add
     (putnam-2003-b4-rp-mul
      (putnam-2003-b4-rp-mul r1 r3) r4)
     (putnam-2003-b4-rp-mul
      (putnam-2003-b4-rp-mul r2 r3) r4)))))

(defun putnam-2003-b4-root-product (r1 r2 r3 r4)
  (putnam-2003-b4-rp-mul
   (putnam-2003-b4-rp-mul r1 r2)
   (putnam-2003-b4-rp-mul r3 r4)))

(defun putnam-2003-b4-vieta-p
    (primitive lower upper a b c d e r1 r2 r3 r4)
  (and
   (putnam-2003-b4-alg-equal-p
    primitive lower upper
    (putnam-2003-b4-rp-add
     (putnam-2003-b4-rp-scale
      a (putnam-2003-b4-root-sum r1 r2 r3 r4))
     (list b))
    nil)
   (putnam-2003-b4-alg-equal-p
    primitive lower upper
    (putnam-2003-b4-rp-sub
     (putnam-2003-b4-rp-scale
      a (putnam-2003-b4-pair-sum r1 r2 r3 r4))
     (list c))
    nil)
   (putnam-2003-b4-alg-equal-p
    primitive lower upper
    (putnam-2003-b4-rp-add
     (putnam-2003-b4-rp-scale
      a (putnam-2003-b4-triple-sum r1 r2 r3 r4))
     (list d))
    nil)
   (putnam-2003-b4-alg-equal-p
    primitive lower upper
    (putnam-2003-b4-rp-sub
     (putnam-2003-b4-rp-scale
      a (putnam-2003-b4-root-product r1 r2 r3 r4))
     (list e))
    nil)))

(defun-sk putnam-2003-b4-rational-product-p
    (primitive lower upper product)
  (exists
   (q)
   (and
    (rationalp q)
    (putnam-2003-b4-alg-equal-p
     primitive lower upper product (list q)))))

(defun putnambench-putnam-2003-b4-statement
    (primitive lower upper a b c d e r1 r2 r3 r4 s)
  (implies
   (and
    (putnam-2003-b4-primitive-p primitive lower upper)
    (integerp a)
    (integerp b)
    (integerp c)
    (integerp d)
    (integerp e)
    (not (equal a 0))
    (putnam-2003-b4-rp-p r1)
    (putnam-2003-b4-rp-p r2)
    (putnam-2003-b4-rp-p r3)
    (putnam-2003-b4-rp-p r4)
    (putnam-2003-b4-vieta-p
     primitive lower upper a b c d e r1 r2 r3 r4)
    (rationalp s)
    (putnam-2003-b4-alg-equal-p
     primitive lower upper
     (putnam-2003-b4-rp-add r1 r2)
     (list s))
    (not
     (putnam-2003-b4-alg-equal-p
      primitive lower upper
      (putnam-2003-b4-rp-add r1 r2)
      (putnam-2003-b4-rp-add r3 r4))))
   (putnam-2003-b4-rational-product-p
    primitive lower upper
    (putnam-2003-b4-rp-mul r1 r2))))

(value-triple :itpeval-statement-checked)
:q
