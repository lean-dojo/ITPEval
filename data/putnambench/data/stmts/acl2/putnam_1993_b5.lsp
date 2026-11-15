;; Statement-only formalization of PutnamBench corpus artifact putnam_1993_b5:
;; no four points in the real Euclidean plane have all six pairwise distances
;; equal to odd integers. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; For fixed integer distance witnesses, existence of the four points is a
;; first-order condition over real closed fields. Hence a real configuration
;; exists exactly when one exists over the real algebraic numbers. Every
;; finite tuple of real algebraic coordinates lies in Q(alpha) for one real
;; algebraic alpha, so rational polynomials in alpha encode all four points
;; without restricting the source's arbitrary real domain.
;;
;; A distance equal to an odd integer is necessarily a positive odd integer,
;; and for a positive integer k it is equivalent to squared distance = k^2.
;; The source has only six unordered pairs. Moving those six existential
;; integer witnesses and the four points across the outer negation gives the
;; explicit DEFUN-SK universal closure below by exact finite quantifier
;; duality.

;; Rational polynomials in alpha use descending coefficient order.

(defun putnam-1993-b5-rp-p (p)
  (if (consp p)
      (and (rationalp (car p))
           (putnam-1993-b5-rp-p (cdr p)))
    (equal p nil)))

(defun putnam-1993-b5-rp-normalize (p)
  (if (consp p)
      (if (equal (car p) 0)
          (putnam-1993-b5-rp-normalize (cdr p))
        p)
    nil))

(defun putnam-1993-b5-rp-negate (p)
  (if (consp p)
      (cons (- (car p))
            (putnam-1993-b5-rp-negate (cdr p)))
    nil))

(defun putnam-1993-b5-rp-add-raw (p q)
  (declare (xargs :measure (+ (acl2-count p) (acl2-count q))))
  (cond
   ((endp p) q)
   ((endp q) p)
   ((< (len p) (len q))
    (cons (car q)
          (putnam-1993-b5-rp-add-raw p (cdr q))))
   ((< (len q) (len p))
    (cons (car p)
          (putnam-1993-b5-rp-add-raw (cdr p) q)))
   (t
    (cons (+ (car p) (car q))
          (putnam-1993-b5-rp-add-raw (cdr p) (cdr q))))))

(defun putnam-1993-b5-rp-add (p q)
  (putnam-1993-b5-rp-normalize
   (putnam-1993-b5-rp-add-raw p q)))

(defun putnam-1993-b5-rp-subtract (p q)
  (putnam-1993-b5-rp-add
   p (putnam-1993-b5-rp-negate q)))

(defun putnam-1993-b5-rp-scale (coefficient p)
  (if (consp p)
      (cons (* coefficient (car p))
            (putnam-1993-b5-rp-scale coefficient (cdr p)))
    nil))

(defun putnam-1993-b5-zeroes (n)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      nil
    (cons 0 (putnam-1993-b5-zeroes (- n 1)))))

(defun putnam-1993-b5-rp-scale-shift (coefficient p shift)
  (append
   (putnam-1993-b5-rp-scale coefficient p)
   (putnam-1993-b5-zeroes shift)))

(defun putnam-1993-b5-rp-multiply-raw (p q)
  (if (consp p)
      (putnam-1993-b5-rp-add
       (putnam-1993-b5-rp-scale-shift
        (car p) q (len (cdr p)))
       (putnam-1993-b5-rp-multiply-raw (cdr p) q))
    nil))

(defun putnam-1993-b5-rp-multiply (p q)
  (putnam-1993-b5-rp-normalize
   (putnam-1993-b5-rp-multiply-raw p q)))

(defun putnam-1993-b5-rp-square (p)
  (putnam-1993-b5-rp-multiply p p))

(defun putnam-1993-b5-rp-eval-aux (p x accumulator)
  (if (consp p)
      (putnam-1993-b5-rp-eval-aux
       (cdr p) x (+ (* accumulator x) (car p)))
    accumulator))

(defun putnam-1993-b5-rp-eval (p x)
  (putnam-1993-b5-rp-eval-aux p x 0))

(defun putnam-1993-b5-rp-derivative-aux (p degree)
  (if (consp p)
      (if (zp degree)
          nil
        (cons (* degree (car p))
              (putnam-1993-b5-rp-derivative-aux
               (cdr p) (- degree 1))))
    nil))

(defun putnam-1993-b5-rp-derivative (p)
  (let ((normalized (putnam-1993-b5-rp-normalize p)))
    (putnam-1993-b5-rp-normalize
     (putnam-1993-b5-rp-derivative-aux
      normalized
      (nfix (- (len normalized) 1))))))

(defun putnam-1993-b5-rp-remainder-fuel (p q fuel)
  (declare (xargs :measure (nfix fuel)))
  (let ((p (putnam-1993-b5-rp-normalize p))
        (q (putnam-1993-b5-rp-normalize q)))
    (if (or (zp fuel)
            (endp q)
            (< (len p) (len q)))
        p
      (putnam-1993-b5-rp-remainder-fuel
       (putnam-1993-b5-rp-subtract
        p
        (putnam-1993-b5-rp-scale-shift
         (/ (car p) (car q))
         q
         (- (len p) (len q))))
       q
       (- fuel 1)))))

(defun putnam-1993-b5-rp-remainder (p q)
  (putnam-1993-b5-rp-remainder-fuel
   p q (+ 1 (len (putnam-1993-b5-rp-normalize p)))))

(defun putnam-1993-b5-rp-sturm-tail (previous current fuel)
  (declare (xargs :measure (nfix fuel)))
  (let ((current (putnam-1993-b5-rp-normalize current)))
    (if (or (zp fuel) (endp current))
        nil
      (cons
       current
       (putnam-1993-b5-rp-sturm-tail
        current
        (putnam-1993-b5-rp-negate
         (putnam-1993-b5-rp-remainder previous current))
        (- fuel 1))))))

(defun putnam-1993-b5-rp-sturm-sequence (p q)
  (let ((p (putnam-1993-b5-rp-normalize p))
        (q (putnam-1993-b5-rp-normalize q)))
    (if (endp p)
        nil
      (cons
       p
       (if (endp q)
           nil
         (cons
          q
          (putnam-1993-b5-rp-sturm-tail
           p q (+ 1 (len p) (len q)))))))))

(defun putnam-1993-b5-rational-sign (x)
  (cond ((< x 0) -1)
        ((< 0 x) 1)
        (t 0)))

(defun putnam-1993-b5-rp-variations-aux
    (polynomials x previous-sign)
  (if (consp polynomials)
      (let ((sign
             (putnam-1993-b5-rational-sign
              (putnam-1993-b5-rp-eval
               (car polynomials) x))))
        (if (equal sign 0)
            (putnam-1993-b5-rp-variations-aux
             (cdr polynomials) x previous-sign)
          (+ (if (and (not (equal previous-sign 0))
                      (not (equal sign previous-sign)))
                 1
               0)
             (putnam-1993-b5-rp-variations-aux
              (cdr polynomials) x sign))))
    0))

(defun putnam-1993-b5-rp-variations (polynomials x)
  (putnam-1993-b5-rp-variations-aux polynomials x 0))

(defun putnam-1993-b5-rp-cauchy-index (p q lower upper)
  (let ((sequence
         (putnam-1993-b5-rp-sturm-sequence p q)))
    (- (putnam-1993-b5-rp-variations sequence lower)
       (putnam-1993-b5-rp-variations sequence upper))))

(defun putnam-1993-b5-rp-root-count (p lower upper)
  (putnam-1993-b5-rp-cauchy-index
   p (putnam-1993-b5-rp-derivative p) lower upper))

(defun putnam-1993-b5-primitive-p (primitive lower upper)
  (and
   (putnam-1993-b5-rp-p primitive)
   (consp (putnam-1993-b5-rp-normalize primitive))
   (rationalp lower)
   (rationalp upper)
   (< lower upper)
   (not (equal
         (putnam-1993-b5-rp-eval primitive lower) 0))
   (not (equal
         (putnam-1993-b5-rp-eval primitive upper) 0))
   (equal
    (putnam-1993-b5-rp-root-count primitive lower upper)
    1)
   (not
    (equal
     (putnam-1993-b5-rp-cauchy-index
      primitive
      (putnam-1993-b5-rp-multiply
       (putnam-1993-b5-rp-derivative primitive)
       (putnam-1993-b5-rp-derivative primitive))
      lower
      upper)
     0))))

;; For the isolated simple root alpha, this Sturm-Tarski query is the sign of
;; VALUE(alpha).
(defun putnam-1993-b5-algebraic-sign
    (primitive lower upper value)
  (putnam-1993-b5-rp-cauchy-index
   primitive
   (putnam-1993-b5-rp-multiply
    (putnam-1993-b5-rp-derivative primitive)
    value)
   lower
   upper))

(defun putnam-1993-b5-zero-at-alpha-p
    (primitive lower upper value)
  (equal
   (putnam-1993-b5-algebraic-sign
    primitive lower upper value)
   0))

(defun putnam-1993-b5-point-code-p (point)
  (and
   (true-listp point)
   (equal (len point) 2)
   (putnam-1993-b5-rp-p (nth 0 point))
   (putnam-1993-b5-rp-p (nth 1 point))))

(defun putnam-1993-b5-distance-squared (left right)
  (putnam-1993-b5-rp-add
   (putnam-1993-b5-rp-square
    (putnam-1993-b5-rp-subtract
     (nth 0 left) (nth 0 right)))
   (putnam-1993-b5-rp-square
    (putnam-1993-b5-rp-subtract
     (nth 1 left) (nth 1 right)))))

(defun putnam-1993-b5-distance-is-p
    (primitive lower upper left right distance)
  (putnam-1993-b5-zero-at-alpha-p
   primitive
   lower
   upper
   (putnam-1993-b5-rp-subtract
    (putnam-1993-b5-distance-squared left right)
    (list (* distance distance)))))

(defun putnam-1993-b5-positive-odd-integer-p (value)
  (and (integerp value)
       (< 0 value)
       (oddp value)))

(defun putnam-1993-b5-encoded-counterexample-p
    (primitive lower upper a b c d
               ab ac ad bc bd cd)
  (and
   (putnam-1993-b5-primitive-p primitive lower upper)
   (putnam-1993-b5-point-code-p a)
   (putnam-1993-b5-point-code-p b)
   (putnam-1993-b5-point-code-p c)
   (putnam-1993-b5-point-code-p d)
   (putnam-1993-b5-positive-odd-integer-p ab)
   (putnam-1993-b5-positive-odd-integer-p ac)
   (putnam-1993-b5-positive-odd-integer-p ad)
   (putnam-1993-b5-positive-odd-integer-p bc)
   (putnam-1993-b5-positive-odd-integer-p bd)
   (putnam-1993-b5-positive-odd-integer-p cd)
   (putnam-1993-b5-distance-is-p
    primitive lower upper a b ab)
   (putnam-1993-b5-distance-is-p
    primitive lower upper a c ac)
   (putnam-1993-b5-distance-is-p
    primitive lower upper a d ad)
   (putnam-1993-b5-distance-is-p
    primitive lower upper b c bc)
   (putnam-1993-b5-distance-is-p
    primitive lower upper b d bd)
   (putnam-1993-b5-distance-is-p
    primitive lower upper c d cd)))

(defun-sk putnambench-putnam-1993-b5-statement ()
  (forall
   (primitive lower upper a b c d
              ab ac ad bc bd cd)
   (not
    (putnam-1993-b5-encoded-counterexample-p
     primitive lower upper a b c d
     ab ac ad bc bd cd))))

(value-triple :itpeval-statement-checked)
:q
