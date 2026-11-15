;; Statement-only formalization of PutnamBench corpus artifact putnam_1983_b6:
;; a nontrivial complex root of unity of order dividing 2^n+1 admits two
;; integer polynomials whose squared values sum to -1. This file contains no
;; proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; If alpha has order d, then d>1 and d divides 2^n+1. Conversely every such
;; d has primitive complex d-th roots. An integer polynomial vanishes at one
;; primitive d-th root exactly when it is divisible by the cyclotomic
;; polynomial Phi_d; Galois conjugacy makes this independent of the chosen
;; primitive root. Thus D is an exact representation of the source alpha up
;; to the equivalence relevant to the conclusion, not a finite approximation.

(defun putnam-1983-b6-poly-normalize (coefficients)
  (if (consp coefficients)
      (let ((tail
             (putnam-1983-b6-poly-normalize
              (cdr coefficients))))
        (if (and (equal (car coefficients) 0)
                 (not (consp tail)))
            nil
          (cons (car coefficients) tail)))
    nil))

(defun putnam-1983-b6-poly-add (left right)
  (cond
   ((consp left)
    (if (consp right)
        (cons (+ (car left) (car right))
              (putnam-1983-b6-poly-add
               (cdr left) (cdr right)))
      left))
   (t right)))

(defun putnam-1983-b6-poly-scale (scalar polynomial)
  (if (consp polynomial)
      (cons (* scalar (car polynomial))
            (putnam-1983-b6-poly-scale
             scalar (cdr polynomial)))
    nil))

(defun putnam-1983-b6-poly-subtract (left right)
  (putnam-1983-b6-poly-normalize
   (putnam-1983-b6-poly-add
    left
    (putnam-1983-b6-poly-scale -1 right))))

(defun putnam-1983-b6-poly-shift (polynomial amount)
  (declare (xargs :measure (nfix amount)))
  (if (zp amount)
      polynomial
    (cons 0
          (putnam-1983-b6-poly-shift
           polynomial (- amount 1)))))

(defun putnam-1983-b6-poly-multiply (left right)
  (if (consp left)
      (putnam-1983-b6-poly-add
       (putnam-1983-b6-poly-scale (car left) right)
       (putnam-1983-b6-poly-shift
        (putnam-1983-b6-poly-multiply
         (cdr left) right)
        1))
    nil))

(defun putnam-1983-b6-x-power-minus-one (exponent)
  (if (zp exponent)
      nil
    (cons -1
          (putnam-1983-b6-poly-shift
           (list 1)
           (- exponent 1)))))

(defun putnam-1983-b6-no-divisor-through-p (n candidate)
  (declare (xargs :measure (nfix candidate)))
  (if (and (natp n)
           (natp candidate)
           (< 1 candidate))
      (and (not (equal (mod n candidate) 0))
           (putnam-1983-b6-no-divisor-through-p
            n (- candidate 1)))
    t))

(defun putnam-1983-b6-primep (n)
  (and (natp n)
       (< 1 n)
       (putnam-1983-b6-no-divisor-through-p
        n (- n 1))))

;; This trial-division definition is the ordinary Moebius function.
(defun putnam-1983-b6-moebius-through
    (n candidate odd-prime-count-p)
  (declare (xargs :measure (nfix candidate)))
  (if (zp candidate)
      (if odd-prime-count-p -1 1)
    (if (and
         (putnam-1983-b6-primep candidate)
         (equal (mod n candidate) 0))
        (if (equal
             (mod n (* candidate candidate))
             0)
            0
          (putnam-1983-b6-moebius-through
           n
           (- candidate 1)
           (not odd-prime-count-p)))
      (putnam-1983-b6-moebius-through
       n (- candidate 1) odd-prime-count-p))))

(defun putnam-1983-b6-moebius (n)
  (if (posp n)
      (putnam-1983-b6-moebius-through n n nil)
    0))

;; Phi_d = product_{k|d} (x^k-1)^mu(d/k). The two functions collect the
;; positive and negative Moebius exponents separately.
(defun putnam-1983-b6-cyclotomic-numerator-through
    (d candidate)
  (declare (xargs :measure (nfix candidate)))
  (if (zp candidate)
      (list 1)
    (let ((tail
           (putnam-1983-b6-cyclotomic-numerator-through
            d (- candidate 1))))
      (if (and
           (equal (mod d candidate) 0)
           (equal
            (putnam-1983-b6-moebius
             (floor d candidate))
            1))
          (putnam-1983-b6-poly-multiply
           (putnam-1983-b6-x-power-minus-one candidate)
           tail)
        tail))))

(defun putnam-1983-b6-cyclotomic-denominator-through
    (d candidate)
  (declare (xargs :measure (nfix candidate)))
  (if (zp candidate)
      (list 1)
    (let ((tail
           (putnam-1983-b6-cyclotomic-denominator-through
            d (- candidate 1))))
      (if (and
           (equal (mod d candidate) 0)
           (equal
            (putnam-1983-b6-moebius
             (floor d candidate))
            -1))
          (putnam-1983-b6-poly-multiply
           (putnam-1983-b6-x-power-minus-one candidate)
           tail)
        tail))))

(defun putnam-1983-b6-poly-leading-coefficient (polynomial)
  (if (consp polynomial)
      (if (consp (cdr polynomial))
          (putnam-1983-b6-poly-leading-coefficient
           (cdr polynomial))
        (car polynomial))
    0))

(defun putnam-1983-b6-poly-monomial (coefficient exponent)
  (putnam-1983-b6-poly-shift
   (list coefficient)
   exponent))

;; The denominator above is monic and divides the numerator. The explicit
;; step bound makes long division a total ACL2 function.
(defun putnam-1983-b6-poly-divide-monic-steps
    (numerator denominator steps)
  (declare (xargs :measure (nfix steps)))
  (let* ((numerator
          (putnam-1983-b6-poly-normalize numerator))
         (denominator
          (putnam-1983-b6-poly-normalize denominator)))
    (if (or (zp steps)
            (not (consp denominator))
            (< (len numerator) (len denominator)))
        nil
      (let* ((coefficient
              (putnam-1983-b6-poly-leading-coefficient
               numerator))
             (shift
              (- (len numerator) (len denominator)))
             (term
              (putnam-1983-b6-poly-monomial
               coefficient shift))
             (remainder
              (putnam-1983-b6-poly-subtract
               numerator
               (putnam-1983-b6-poly-multiply
                term denominator))))
        (putnam-1983-b6-poly-add
         term
         (putnam-1983-b6-poly-divide-monic-steps
          remainder denominator (- steps 1)))))))

(defun putnam-1983-b6-cyclotomic-polynomial (d)
  (if (posp d)
      (let* ((numerator
              (putnam-1983-b6-cyclotomic-numerator-through
               d d))
             (denominator
              (putnam-1983-b6-cyclotomic-denominator-through
               d d)))
        (putnam-1983-b6-poly-normalize
         (putnam-1983-b6-poly-divide-monic-steps
          numerator denominator (len numerator))))
    nil))

(defun putnam-1983-b6-integer-polynomial-p (coefficients)
  (if (consp coefficients)
      (and
       (integerp (car coefficients))
       (putnam-1983-b6-integer-polynomial-p
        (cdr coefficients)))
    (equal coefficients nil)))

;; In Z[x]/(Phi_d), the displayed identity is exactly
;; p(alpha)^2 + q(alpha)^2 = -1 for a primitive d-th root alpha. The
;; existential quotient R is internal to the conclusion and witnesses
;; divisibility by Phi_d; it is not an extra theorem parameter.
(defun putnam-1983-b6-polynomial-identity-p (d p q r)
  (equal
   (putnam-1983-b6-poly-normalize
    (putnam-1983-b6-poly-add
     (putnam-1983-b6-poly-multiply p p)
     (putnam-1983-b6-poly-add
      (putnam-1983-b6-poly-multiply q q)
      (list 1))))
   (putnam-1983-b6-poly-normalize
    (putnam-1983-b6-poly-multiply
     (putnam-1983-b6-cyclotomic-polynomial d)
     r))))

(defun-sk putnam-1983-b6-polynomial-witnesses-exist-p (d)
  (exists (p q r)
    (and
     (putnam-1983-b6-integer-polynomial-p p)
     (putnam-1983-b6-integer-polynomial-p q)
     (putnam-1983-b6-integer-polynomial-p r)
     (putnam-1983-b6-polynomial-identity-p d p q r))))

(defun putnambench-putnam-1983-b6-statement (n d)
  (implies
   (and
    (natp n)
    (< 0 n)
    (natp d)
    (< 1 d)
    (equal (mod (+ (expt 2 n) 1) d) 0))
   (putnam-1983-b6-polynomial-witnesses-exist-p d)))

(value-triple :itpeval-statement-checked)
:q
