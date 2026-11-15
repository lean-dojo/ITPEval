;; Statement-only formalization of PutnamBench corpus artifact putnam_1972_b5:
;; for four noncoplanar points in real three-space, equality of two pairs of
;; opposite angles implies equality of the corresponding opposite side
;; lengths. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Noncoplanarity is the nonvanishing of a 3-by-3 determinant. Under that
;; hypothesis all rays in the four angles are nonzero. Equality of two such
;; angles is therefore equivalent to equality of their cosines; after removing
;; the positive square-root denominators, this says that the two dot products
;; have the same sign and that their squared normalized values are equal.
;; Distance equality is equivalently equality of squared distances. Thus the
;; complete statement is a universal first-order sentence over real closed
;; fields.
;;
;; A real counterexample exists iff one exists over the real algebraic
;; numbers. Every finite algebraic coordinate tuple lies in Q(alpha) for one
;; real algebraic alpha. Rational polynomials in alpha encode the twelve
;; coordinates, and Sturm-Tarski queries decide their signs exactly.

;; Rational polynomials in alpha use descending coefficient order.

(defun putnam-1972-b5-rp-p (p)
  (if (consp p)
      (and (rationalp (car p))
           (putnam-1972-b5-rp-p (cdr p)))
    (equal p nil)))

(defun putnam-1972-b5-rp-normalize (p)
  (if (consp p)
      (if (equal (car p) 0)
          (putnam-1972-b5-rp-normalize (cdr p))
        p)
    nil))

(defun putnam-1972-b5-rp-negate (p)
  (if (consp p)
      (cons (- (car p))
            (putnam-1972-b5-rp-negate (cdr p)))
    nil))

(defun putnam-1972-b5-rp-add-raw (p q)
  (declare (xargs :measure (+ (acl2-count p) (acl2-count q))))
  (cond
   ((endp p) q)
   ((endp q) p)
   ((< (len p) (len q))
    (cons (car q)
          (putnam-1972-b5-rp-add-raw p (cdr q))))
   ((< (len q) (len p))
    (cons (car p)
          (putnam-1972-b5-rp-add-raw (cdr p) q)))
   (t
    (cons (+ (car p) (car q))
          (putnam-1972-b5-rp-add-raw (cdr p) (cdr q))))))

(defun putnam-1972-b5-rp-add (p q)
  (putnam-1972-b5-rp-normalize
   (putnam-1972-b5-rp-add-raw p q)))

(defun putnam-1972-b5-rp-subtract (p q)
  (putnam-1972-b5-rp-add
   p (putnam-1972-b5-rp-negate q)))

(defun putnam-1972-b5-rp-scale (coefficient p)
  (if (consp p)
      (cons (* coefficient (car p))
            (putnam-1972-b5-rp-scale coefficient (cdr p)))
    nil))

(defun putnam-1972-b5-zeroes (n)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      nil
    (cons 0 (putnam-1972-b5-zeroes (- n 1)))))

(defun putnam-1972-b5-rp-scale-shift (coefficient p shift)
  (append
   (putnam-1972-b5-rp-scale coefficient p)
   (putnam-1972-b5-zeroes shift)))

(defun putnam-1972-b5-rp-multiply-raw (p q)
  (if (consp p)
      (putnam-1972-b5-rp-add
       (putnam-1972-b5-rp-scale-shift
        (car p) q (len (cdr p)))
       (putnam-1972-b5-rp-multiply-raw (cdr p) q))
    nil))

(defun putnam-1972-b5-rp-multiply (p q)
  (putnam-1972-b5-rp-normalize
   (putnam-1972-b5-rp-multiply-raw p q)))

(defun putnam-1972-b5-rp-square (p)
  (putnam-1972-b5-rp-multiply p p))

(defun putnam-1972-b5-rp-eval-aux (p x accumulator)
  (if (consp p)
      (putnam-1972-b5-rp-eval-aux
       (cdr p) x (+ (* accumulator x) (car p)))
    accumulator))

(defun putnam-1972-b5-rp-eval (p x)
  (putnam-1972-b5-rp-eval-aux p x 0))

(defun putnam-1972-b5-rp-derivative-aux (p degree)
  (if (consp p)
      (if (zp degree)
          nil
        (cons (* degree (car p))
              (putnam-1972-b5-rp-derivative-aux
               (cdr p) (- degree 1))))
    nil))

(defun putnam-1972-b5-rp-derivative (p)
  (let ((normalized (putnam-1972-b5-rp-normalize p)))
    (putnam-1972-b5-rp-normalize
     (putnam-1972-b5-rp-derivative-aux
      normalized
      (nfix (- (len normalized) 1))))))

(defun putnam-1972-b5-rp-remainder-fuel (p q fuel)
  (declare (xargs :measure (nfix fuel)))
  (let ((p (putnam-1972-b5-rp-normalize p))
        (q (putnam-1972-b5-rp-normalize q)))
    (if (or (zp fuel)
            (endp q)
            (< (len p) (len q)))
        p
      (putnam-1972-b5-rp-remainder-fuel
       (putnam-1972-b5-rp-subtract
        p
        (putnam-1972-b5-rp-scale-shift
         (/ (car p) (car q))
         q
         (- (len p) (len q))))
       q
       (- fuel 1)))))

(defun putnam-1972-b5-rp-remainder (p q)
  (putnam-1972-b5-rp-remainder-fuel
   p q (+ 1 (len (putnam-1972-b5-rp-normalize p)))))

(defun putnam-1972-b5-rp-sturm-tail (previous current fuel)
  (declare (xargs :measure (nfix fuel)))
  (let ((current (putnam-1972-b5-rp-normalize current)))
    (if (or (zp fuel) (endp current))
        nil
      (cons
       current
       (putnam-1972-b5-rp-sturm-tail
        current
        (putnam-1972-b5-rp-negate
         (putnam-1972-b5-rp-remainder previous current))
        (- fuel 1))))))

(defun putnam-1972-b5-rp-sturm-sequence (p q)
  (let ((p (putnam-1972-b5-rp-normalize p))
        (q (putnam-1972-b5-rp-normalize q)))
    (if (endp p)
        nil
      (cons
       p
       (if (endp q)
           nil
         (cons
          q
          (putnam-1972-b5-rp-sturm-tail
           p q (+ 1 (len p) (len q)))))))))

(defun putnam-1972-b5-rational-sign (x)
  (cond ((< x 0) -1)
        ((< 0 x) 1)
        (t 0)))

(defun putnam-1972-b5-rp-variations-aux
    (polynomials x previous-sign)
  (if (consp polynomials)
      (let ((sign
             (putnam-1972-b5-rational-sign
              (putnam-1972-b5-rp-eval
               (car polynomials) x))))
        (if (equal sign 0)
            (putnam-1972-b5-rp-variations-aux
             (cdr polynomials) x previous-sign)
          (+ (if (and (not (equal previous-sign 0))
                      (not (equal sign previous-sign)))
                 1
               0)
             (putnam-1972-b5-rp-variations-aux
              (cdr polynomials) x sign))))
    0))

(defun putnam-1972-b5-rp-variations (polynomials x)
  (putnam-1972-b5-rp-variations-aux polynomials x 0))

(defun putnam-1972-b5-rp-cauchy-index (p q lower upper)
  (let ((sequence
         (putnam-1972-b5-rp-sturm-sequence p q)))
    (- (putnam-1972-b5-rp-variations sequence lower)
       (putnam-1972-b5-rp-variations sequence upper))))

(defun putnam-1972-b5-rp-root-count (p lower upper)
  (putnam-1972-b5-rp-cauchy-index
   p (putnam-1972-b5-rp-derivative p) lower upper))

(defun putnam-1972-b5-primitive-p (primitive lower upper)
  (and
   (putnam-1972-b5-rp-p primitive)
   (consp (putnam-1972-b5-rp-normalize primitive))
   (rationalp lower)
   (rationalp upper)
   (< lower upper)
   (not (equal
         (putnam-1972-b5-rp-eval primitive lower) 0))
   (not (equal
         (putnam-1972-b5-rp-eval primitive upper) 0))
   (equal
    (putnam-1972-b5-rp-root-count primitive lower upper)
    1)
   (not
    (equal
     (putnam-1972-b5-rp-cauchy-index
      primitive
      (putnam-1972-b5-rp-multiply
       (putnam-1972-b5-rp-derivative primitive)
       (putnam-1972-b5-rp-derivative primitive))
      lower
      upper)
     0))))

;; For the single isolated simple root alpha, this Sturm-Tarski query is the
;; sign of VALUE(alpha).
(defun putnam-1972-b5-algebraic-sign
    (primitive lower upper value)
  (putnam-1972-b5-rp-cauchy-index
   primitive
   (putnam-1972-b5-rp-multiply
    (putnam-1972-b5-rp-derivative primitive)
    value)
   lower
   upper))

(defun putnam-1972-b5-point-code-p (point)
  (and
   (true-listp point)
   (equal (len point) 3)
   (putnam-1972-b5-rp-p (nth 0 point))
   (putnam-1972-b5-rp-p (nth 1 point))
   (putnam-1972-b5-rp-p (nth 2 point))))

(defun putnam-1972-b5-vector-subtract (left right)
  (list
   (putnam-1972-b5-rp-subtract (nth 0 left) (nth 0 right))
   (putnam-1972-b5-rp-subtract (nth 1 left) (nth 1 right))
   (putnam-1972-b5-rp-subtract (nth 2 left) (nth 2 right))))

(defun putnam-1972-b5-dot-product (left right)
  (putnam-1972-b5-rp-add
   (putnam-1972-b5-rp-multiply
    (nth 0 left) (nth 0 right))
   (putnam-1972-b5-rp-add
    (putnam-1972-b5-rp-multiply
     (nth 1 left) (nth 1 right))
    (putnam-1972-b5-rp-multiply
     (nth 2 left) (nth 2 right)))))

(defun putnam-1972-b5-distance-squared (left right)
  (putnam-1972-b5-dot-product
   (putnam-1972-b5-vector-subtract left right)
   (putnam-1972-b5-vector-subtract left right)))

(defun putnam-1972-b5-determinant (u v w)
  (putnam-1972-b5-rp-add
   (putnam-1972-b5-rp-subtract
    (putnam-1972-b5-rp-multiply
     (nth 0 u)
     (putnam-1972-b5-rp-subtract
      (putnam-1972-b5-rp-multiply (nth 1 v) (nth 2 w))
      (putnam-1972-b5-rp-multiply (nth 2 v) (nth 1 w))))
    (putnam-1972-b5-rp-multiply
     (nth 1 u)
     (putnam-1972-b5-rp-subtract
      (putnam-1972-b5-rp-multiply (nth 0 v) (nth 2 w))
      (putnam-1972-b5-rp-multiply (nth 2 v) (nth 0 w)))))
   (putnam-1972-b5-rp-multiply
    (nth 2 u)
    (putnam-1972-b5-rp-subtract
     (putnam-1972-b5-rp-multiply (nth 0 v) (nth 1 w))
     (putnam-1972-b5-rp-multiply (nth 1 v) (nth 0 w))))))

(defun putnam-1972-b5-zero-at-alpha-p
    (primitive lower upper value)
  (equal
   (putnam-1972-b5-algebraic-sign
    primitive lower upper value)
   0))

(defun putnam-1972-b5-equal-at-alpha-p
    (primitive lower upper left right)
  (putnam-1972-b5-zero-at-alpha-p
   primitive lower upper
   (putnam-1972-b5-rp-subtract left right)))

(defun putnam-1972-b5-noncoplanar-p
    (primitive lower upper a b c d)
  (not
   (putnam-1972-b5-zero-at-alpha-p
    primitive
    lower
    upper
    (putnam-1972-b5-determinant
     (putnam-1972-b5-vector-subtract b a)
     (putnam-1972-b5-vector-subtract c a)
     (putnam-1972-b5-vector-subtract d a)))))

(defun putnam-1972-b5-angle-equal-p
    (primitive lower upper
               left vertex right
               other-left other-vertex other-right)
  (let* ((u (putnam-1972-b5-vector-subtract left vertex))
         (v (putnam-1972-b5-vector-subtract right vertex))
         (other-u
          (putnam-1972-b5-vector-subtract
           other-left other-vertex))
         (other-v
          (putnam-1972-b5-vector-subtract
           other-right other-vertex))
         (dot (putnam-1972-b5-dot-product u v))
         (other-dot
          (putnam-1972-b5-dot-product other-u other-v))
         (norm-product
          (putnam-1972-b5-rp-multiply
           (putnam-1972-b5-dot-product u u)
           (putnam-1972-b5-dot-product v v)))
         (other-norm-product
          (putnam-1972-b5-rp-multiply
           (putnam-1972-b5-dot-product other-u other-u)
           (putnam-1972-b5-dot-product other-v other-v)))
         (squared-cosine-difference
          (putnam-1972-b5-rp-subtract
           (putnam-1972-b5-rp-multiply
            (putnam-1972-b5-rp-square dot)
            other-norm-product)
           (putnam-1972-b5-rp-multiply
            (putnam-1972-b5-rp-square other-dot)
            norm-product))))
    (and
     (equal
      (putnam-1972-b5-algebraic-sign
       primitive lower upper dot)
      (putnam-1972-b5-algebraic-sign
       primitive lower upper other-dot))
     (putnam-1972-b5-zero-at-alpha-p
      primitive lower upper squared-cosine-difference))))

(defun putnambench-putnam-1972-b5-statement
    (primitive lower upper a b c d)
  (implies
   (and
    (putnam-1972-b5-primitive-p primitive lower upper)
    (putnam-1972-b5-point-code-p a)
    (putnam-1972-b5-point-code-p b)
    (putnam-1972-b5-point-code-p c)
    (putnam-1972-b5-point-code-p d)
    (putnam-1972-b5-noncoplanar-p
     primitive lower upper a b c d)
    (putnam-1972-b5-angle-equal-p
     primitive lower upper a b c c d a)
    (putnam-1972-b5-angle-equal-p
     primitive lower upper b c d d a b))
   (and
    (putnam-1972-b5-equal-at-alpha-p
     primitive lower upper
     (putnam-1972-b5-distance-squared a b)
     (putnam-1972-b5-distance-squared c d))
    (putnam-1972-b5-equal-at-alpha-p
     primitive lower upper
     (putnam-1972-b5-distance-squared b c)
     (putnam-1972-b5-distance-squared d a)))))

(value-triple :itpeval-statement-checked)
:q
