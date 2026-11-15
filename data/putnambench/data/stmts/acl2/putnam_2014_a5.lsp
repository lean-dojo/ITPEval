;; Statement-only formalization of PutnamBench corpus artifact putnam_2014_a5:
;; the polynomials P_n(x) = 1 + 2*x + ... + n*x^(n-1) are relatively prime
;; for all distinct positive indices. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; The source hypotheses determine P_n extensionally, so the canonical
;; ascending coefficient list (1,2,...,n) below preserves that quantification.
;; Its coefficients are rational. For rational polynomials, coprimality over
;; Q, R, any real closed field, and C is equivalent: a rational Bezout
;; identity remains one after scalar extension, while a nonconstant common
;; divisor over Q remains common in every extension. Thus equality of the
;; exact monic rational gcd with 1 is bidirectionally equivalent to each
;; source formulation, including the existential real-polynomial identity.

(defun putnam-2014-a5-poly-normalize (polynomial)
  (if (consp polynomial)
      (let ((tail
             (putnam-2014-a5-poly-normalize
              (cdr polynomial))))
        (if (and (equal (car polynomial) 0)
                 (not (consp tail)))
            nil
          (cons (car polynomial) tail)))
    nil))

(defun putnam-2014-a5-poly-add (left right)
  (cond
   ((consp left)
    (if (consp right)
        (cons (+ (car left) (car right))
              (putnam-2014-a5-poly-add
               (cdr left) (cdr right)))
      left))
   (t right)))

(defun putnam-2014-a5-poly-scale (scalar polynomial)
  (if (consp polynomial)
      (cons (* scalar (car polynomial))
            (putnam-2014-a5-poly-scale
             scalar (cdr polynomial)))
    nil))

(defun putnam-2014-a5-poly-negate (polynomial)
  (putnam-2014-a5-poly-scale -1 polynomial))

(defun putnam-2014-a5-poly-subtract (left right)
  (putnam-2014-a5-poly-normalize
   (putnam-2014-a5-poly-add
    left
    (putnam-2014-a5-poly-negate right))))

(defun putnam-2014-a5-zero-list (count)
  (declare (xargs :measure (nfix count)))
  (if (zp count)
      nil
    (cons 0
          (putnam-2014-a5-zero-list (- count 1)))))

(defun putnam-2014-a5-poly-monomial (coefficient degree)
  (if (equal coefficient 0)
      nil
    (append
     (putnam-2014-a5-zero-list degree)
     (list coefficient))))

(defun putnam-2014-a5-poly-degree (polynomial)
  (let ((normalized
         (putnam-2014-a5-poly-normalize polynomial)))
    (if (consp normalized)
        (- (len normalized) 1)
      0)))

(defun putnam-2014-a5-poly-leading-coefficient (polynomial)
  (let ((normalized
         (putnam-2014-a5-poly-normalize polynomial)))
    (if (consp normalized)
        (nth (putnam-2014-a5-poly-degree normalized)
             normalized)
      0)))

(defun putnam-2014-a5-poly-divmod-steps
    (remainder divisor quotient steps)
  (declare (xargs :measure (nfix steps)))
  (if (zp steps)
      (cons
       (putnam-2014-a5-poly-normalize quotient)
       (putnam-2014-a5-poly-normalize remainder))
    (let* ((normalized-remainder
            (putnam-2014-a5-poly-normalize remainder))
           (normalized-divisor
            (putnam-2014-a5-poly-normalize divisor)))
      (if (or (not (consp normalized-remainder))
              (not (consp normalized-divisor))
              (< (putnam-2014-a5-poly-degree
                  normalized-remainder)
                 (putnam-2014-a5-poly-degree
                  normalized-divisor)))
          (cons
           (putnam-2014-a5-poly-normalize quotient)
           normalized-remainder)
        (let* ((degree-difference
                (- (putnam-2014-a5-poly-degree
                    normalized-remainder)
                   (putnam-2014-a5-poly-degree
                    normalized-divisor)))
               (coefficient
                (/ (putnam-2014-a5-poly-leading-coefficient
                    normalized-remainder)
                   (putnam-2014-a5-poly-leading-coefficient
                    normalized-divisor)))
               (term
                (putnam-2014-a5-poly-monomial
                 coefficient degree-difference)))
          (putnam-2014-a5-poly-divmod-steps
           (putnam-2014-a5-poly-subtract
            normalized-remainder
            (putnam-2014-a5-poly-scale
             coefficient
             (append
              (putnam-2014-a5-zero-list degree-difference)
              normalized-divisor)))
           normalized-divisor
           (putnam-2014-a5-poly-add quotient term)
           (- steps 1)))))))

(defun putnam-2014-a5-poly-divmod (dividend divisor)
  (putnam-2014-a5-poly-divmod-steps
   dividend
   divisor
   nil
   (+ 1
      (len (putnam-2014-a5-poly-normalize dividend)))))

(defun putnam-2014-a5-poly-remainder (dividend divisor)
  (cdr (putnam-2014-a5-poly-divmod dividend divisor)))

(defun putnam-2014-a5-poly-gcd-steps (left right steps)
  (declare (xargs :measure (nfix steps)))
  (let ((normalized-left
         (putnam-2014-a5-poly-normalize left))
        (normalized-right
         (putnam-2014-a5-poly-normalize right)))
    (if (or (zp steps)
            (not (consp normalized-right)))
        normalized-left
      (putnam-2014-a5-poly-gcd-steps
       normalized-right
       (putnam-2014-a5-poly-remainder
        normalized-left normalized-right)
       (- steps 1)))))

(defun putnam-2014-a5-poly-gcd (left right)
  (putnam-2014-a5-poly-gcd-steps
   left
   right
   (+ 2
      (len (putnam-2014-a5-poly-normalize left))
      (len (putnam-2014-a5-poly-normalize right)))))

(defun putnam-2014-a5-poly-monic (polynomial)
  (let* ((normalized
          (putnam-2014-a5-poly-normalize polynomial))
         (leading-coefficient
          (putnam-2014-a5-poly-leading-coefficient normalized)))
    (if (consp normalized)
        (putnam-2014-a5-poly-normalize
         (putnam-2014-a5-poly-scale
          (/ 1 leading-coefficient)
          normalized))
      nil)))

(defun putnam-2014-a5-polynomial-from (coefficient count)
  (declare (xargs :measure (nfix count)))
  (if (zp count)
      nil
    (cons coefficient
          (putnam-2014-a5-polynomial-from
           (+ coefficient 1)
           (- count 1)))))

(defun putnam-2014-a5-polynomial (n)
  (putnam-2014-a5-polynomial-from 1 n))

(defun putnambench-putnam-2014-a5-statement (j k)
  (implies
   (and (natp j)
        (natp k)
        (< 0 j)
        (< 0 k)
        (not (equal j k)))
   (equal
    (putnam-2014-a5-poly-monic
     (putnam-2014-a5-poly-gcd
      (putnam-2014-a5-polynomial j)
      (putnam-2014-a5-polynomial k)))
    (list 1))))

(value-triple :itpeval-statement-checked)
:q
