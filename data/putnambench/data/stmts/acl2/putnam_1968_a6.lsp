;; Statement-only formalization of PutnamBench artifact putnam_1968_a6:
;; the classification of nonconstant polynomials with all coefficients equal
;; to 1 or -1 and with every complex root real. This file contains no proof.

(in-package "ACL2")

(set-inhibit-output-lst '(prove proof-tree event summary))

;; Coefficients are stored in ascending degree order. Because membership in
;; both sides of the source set equality forces every coefficient to be 1 or
;; -1, canonical finite sign lists represent exactly all polynomials relevant
;; to that equality; polynomials with any other complex coefficient belong to
;; neither side.
;;
;; For a degree-n sign polynomial, every complex root has modulus strictly
;; less than 2: at modulus at least 2 the leading term has magnitude at least
;; 2^n, while all lower terms together have magnitude at most 2^n-1. Hence
;; Sturm's exact rational root count on (-2,2) counts all distinct real roots.
;; The polynomial has only real complex roots, including multiplicities, iff
;; this count equals degree(P)-degree(gcd(P,P')). Thus the predicate below is
;; bidirectionally equivalent to the source's universal complex-root condition
;; and does not sample or restrict the roots to rational values.

(defun putnam-1968-a6-sign-list-p (coefficients)
  (if (consp coefficients)
      (and (or (equal (car coefficients) 1)
               (equal (car coefficients) -1))
           (putnam-1968-a6-sign-list-p (cdr coefficients)))
    (equal coefficients nil)))

(defun putnam-1968-a6-rational-polynomial-p (polynomial)
  (if (consp polynomial)
      (and (rationalp (car polynomial))
           (putnam-1968-a6-rational-polynomial-p (cdr polynomial)))
    (equal polynomial nil)))

(defun putnam-1968-a6-poly-normalize (coefficients)
  (if (consp coefficients)
      (let ((tail
             (putnam-1968-a6-poly-normalize (cdr coefficients))))
        (if (and (equal (car coefficients) 0)
                 (not (consp tail)))
            nil
          (cons (car coefficients) tail)))
    nil))

(defun putnam-1968-a6-poly-add (left right)
  (cond
   ((consp left)
    (if (consp right)
        (cons (+ (car left) (car right))
              (putnam-1968-a6-poly-add (cdr left) (cdr right)))
      left))
   (t right)))

(defun putnam-1968-a6-poly-scale (scalar polynomial)
  (if (consp polynomial)
      (cons (* scalar (car polynomial))
            (putnam-1968-a6-poly-scale scalar (cdr polynomial)))
    nil))

(defun putnam-1968-a6-poly-subtract (left right)
  (putnam-1968-a6-poly-normalize
   (putnam-1968-a6-poly-add
    left
    (putnam-1968-a6-poly-scale -1 right))))

(defun putnam-1968-a6-poly-derivative-aux
    (coefficients degree)
  (if (consp coefficients)
      (cons (* degree (car coefficients))
            (putnam-1968-a6-poly-derivative-aux
             (cdr coefficients) (+ degree 1)))
    nil))

(defun putnam-1968-a6-poly-derivative (polynomial)
  (if (consp polynomial)
      (putnam-1968-a6-poly-normalize
       (putnam-1968-a6-poly-derivative-aux
        (cdr polynomial) 1))
    nil))

(defun putnam-1968-a6-zero-list (count)
  (declare (xargs :measure (nfix count)))
  (if (zp count)
      nil
    (cons 0
          (putnam-1968-a6-zero-list (- count 1)))))

(defun putnam-1968-a6-poly-monomial (coefficient degree)
  (if (equal coefficient 0)
      nil
    (append
     (putnam-1968-a6-zero-list degree)
     (list coefficient))))

(defun putnam-1968-a6-poly-degree (polynomial)
  (let ((normalized
         (putnam-1968-a6-poly-normalize polynomial)))
    (if (consp normalized)
        (- (len normalized) 1)
      0)))

(defun putnam-1968-a6-poly-leading-coefficient (polynomial)
  (let ((normalized
         (putnam-1968-a6-poly-normalize polynomial)))
    (if (consp normalized)
        (nth (putnam-1968-a6-poly-degree normalized)
             normalized)
      0)))

(defun putnam-1968-a6-poly-divmod-steps
    (remainder divisor quotient steps)
  (declare (xargs :measure (nfix steps)))
  (if (zp steps)
      (cons
       (putnam-1968-a6-poly-normalize quotient)
       (putnam-1968-a6-poly-normalize remainder))
    (let* ((normalized-remainder
            (putnam-1968-a6-poly-normalize remainder))
           (normalized-divisor
            (putnam-1968-a6-poly-normalize divisor)))
      (if (or (not (consp normalized-remainder))
              (not (consp normalized-divisor))
              (< (putnam-1968-a6-poly-degree normalized-remainder)
                 (putnam-1968-a6-poly-degree normalized-divisor)))
          (cons
           (putnam-1968-a6-poly-normalize quotient)
           normalized-remainder)
        (let* ((degree-difference
                (- (putnam-1968-a6-poly-degree
                    normalized-remainder)
                   (putnam-1968-a6-poly-degree
                    normalized-divisor)))
               (coefficient
                (/ (putnam-1968-a6-poly-leading-coefficient
                    normalized-remainder)
                   (putnam-1968-a6-poly-leading-coefficient
                    normalized-divisor)))
               (term
                (putnam-1968-a6-poly-monomial
                 coefficient degree-difference)))
          (putnam-1968-a6-poly-divmod-steps
           (putnam-1968-a6-poly-subtract
            normalized-remainder
            (putnam-1968-a6-poly-scale
             coefficient
             (append
              (putnam-1968-a6-zero-list degree-difference)
              normalized-divisor)))
           normalized-divisor
           (putnam-1968-a6-poly-add quotient term)
           (- steps 1)))))))

(defun putnam-1968-a6-poly-divmod (dividend divisor)
  (putnam-1968-a6-poly-divmod-steps
   dividend
   divisor
   nil
   (+ 1 (len (putnam-1968-a6-poly-normalize dividend)))))

(defun putnam-1968-a6-poly-remainder (dividend divisor)
  (cdr (putnam-1968-a6-poly-divmod dividend divisor)))

(defun putnam-1968-a6-poly-gcd-steps (left right steps)
  (declare (xargs :measure (nfix steps)))
  (let ((normalized-left
         (putnam-1968-a6-poly-normalize left))
        (normalized-right
         (putnam-1968-a6-poly-normalize right)))
    (if (or (zp steps)
            (not (consp normalized-right)))
        normalized-left
      (putnam-1968-a6-poly-gcd-steps
       normalized-right
       (putnam-1968-a6-poly-remainder
        normalized-left normalized-right)
       (- steps 1)))))

(defun putnam-1968-a6-poly-gcd (left right)
  (putnam-1968-a6-poly-gcd-steps
   left
   right
   (+ 2
      (len (putnam-1968-a6-poly-normalize left))
      (len (putnam-1968-a6-poly-normalize right)))))

(defun putnam-1968-a6-sturm-tail
    (previous current steps)
  (declare (xargs :measure (nfix steps)))
  (let ((normalized-current
         (putnam-1968-a6-poly-normalize current)))
    (if (or (zp steps)
            (not (consp normalized-current)))
        nil
      (cons
       normalized-current
       (putnam-1968-a6-sturm-tail
        normalized-current
        (putnam-1968-a6-poly-scale
         -1
         (putnam-1968-a6-poly-remainder
          previous normalized-current))
        (- steps 1))))))

(defun putnam-1968-a6-sturm-chain (polynomial)
  (let ((normalized
         (putnam-1968-a6-poly-normalize polynomial)))
    (if (consp normalized)
        (cons
         normalized
         (putnam-1968-a6-sturm-tail
          normalized
          (putnam-1968-a6-poly-derivative normalized)
          (+ 1 (len normalized))))
      nil)))

(defun putnam-1968-a6-poly-evaluate (polynomial value)
  (if (consp polynomial)
      (+ (car polynomial)
         (* value
            (putnam-1968-a6-poly-evaluate
             (cdr polynomial) value)))
    0))

(defun putnam-1968-a6-chain-values-at (chain value)
  (if (consp chain)
      (cons
       (putnam-1968-a6-poly-evaluate (car chain) value)
       (putnam-1968-a6-chain-values-at (cdr chain) value))
    nil))

(defun putnam-1968-a6-sign (value)
  (cond
   ((< value 0) -1)
   ((< 0 value) 1)
   (t 0)))

(defun putnam-1968-a6-sign-variations-aux
    (values previous-sign)
  (if (consp values)
      (let ((current-sign
             (putnam-1968-a6-sign (car values))))
        (cond
         ((equal current-sign 0)
          (putnam-1968-a6-sign-variations-aux
           (cdr values) previous-sign))
         ((equal previous-sign 0)
          (putnam-1968-a6-sign-variations-aux
           (cdr values) current-sign))
         (t
          (+ (if (equal current-sign previous-sign) 0 1)
             (putnam-1968-a6-sign-variations-aux
              (cdr values) current-sign)))))
    0))

(defun putnam-1968-a6-sign-variations (values)
  (putnam-1968-a6-sign-variations-aux values 0))

(defun putnam-1968-a6-open-root-count
    (polynomial lower upper)
  (let ((chain
         (putnam-1968-a6-sturm-chain polynomial)))
    (- (putnam-1968-a6-sign-variations
        (putnam-1968-a6-chain-values-at chain lower))
       (putnam-1968-a6-sign-variations
        (putnam-1968-a6-chain-values-at chain upper)))))

(defun putnam-1968-a6-all-roots-real-p (polynomial)
  (let* ((normalized
          (putnam-1968-a6-poly-normalize polynomial))
         (derivative
          (putnam-1968-a6-poly-derivative normalized))
         (common-factor
          (putnam-1968-a6-poly-gcd normalized derivative))
         (square-free-degree
          (- (putnam-1968-a6-poly-degree normalized)
             (putnam-1968-a6-poly-degree common-factor))))
    (and
     (putnam-1968-a6-rational-polynomial-p normalized)
     (consp normalized)
     (< 0 (putnam-1968-a6-poly-degree normalized))
     (not (equal
           (putnam-1968-a6-poly-evaluate normalized -2)
           0))
     (not (equal
           (putnam-1968-a6-poly-evaluate normalized 2)
           0))
     (equal
      (putnam-1968-a6-open-root-count normalized -2 2)
      square-free-degree))))

(defun putnam-1968-a6-negate-coefficients (coefficients)
  (if (consp coefficients)
      (cons (- (car coefficients))
            (putnam-1968-a6-negate-coefficients
             (cdr coefficients)))
    nil))

(defun putnam-1968-a6-base-solution-p (coefficients)
  (if (member-equal
       coefficients
       '((-1 1)
         (1 1)
         (-1 1 1)
         (-1 -1 1)
         (-1 -1 1 1)
         (1 -1 -1 1)))
      t
    nil))

(defun putnam-1968-a6-solution-p (coefficients)
  (or
   (putnam-1968-a6-base-solution-p coefficients)
   (putnam-1968-a6-base-solution-p
    (putnam-1968-a6-negate-coefficients coefficients))))

(defun putnambench-putnam-1968-a6-statement (coefficients)
  (equal
   (and
    (true-listp coefficients)
    (<= 2 (len coefficients))
    (putnam-1968-a6-sign-list-p coefficients)
    (putnam-1968-a6-all-roots-real-p coefficients))
   (putnam-1968-a6-solution-p coefficients)))

(value-triple :itpeval-statement-checked)
:q
